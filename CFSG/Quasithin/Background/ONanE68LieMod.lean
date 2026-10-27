module

public import CFSG.Quasithin.Background.ONanE68LieBar
public import CFSG.Quasithin.Background.E6ElevenStrong

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Odd

variable {G : Type} [Group G] [Finite G]

theorem odd_relIndex_twoPrimeResidual (X : Subgroup G) :
    ¬ 2 ∣ (twoPrimeResidual X).relIndex X := by
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf X
  have h1 : conjClosure T X = twoPrimeResidual X := conjClosure_eq_twoPrimeResidual hT
  have h2 : (twoPrimeResidual X).relIndex X ∣ T.relIndex X := by
    rw [← h1]
    exact Subgroup.relIndex_dvd_of_le_left X (le_conjClosure T X)
  intro hdvd
  exact hT.2.2 (hdvd.trans h2)

theorem odd_card_autI {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hres : twoPrimeResidual X ≤ Subgroup.centralizer (V : Set G)) :
    Odd (Nat.card (autI hV X)) := by
  rw [card_autI_eq hV hXN]
  have hle : twoPrimeResidual X ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (twoPrimeResidual_le_self X) hres
  have hdvd : (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X ∣
      (twoPrimeResidual X).relIndex X := Subgroup.relIndex_dvd_of_le_left X hle
  have hnd : ¬ 2 ∣ (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X := fun h2 =>
    odd_relIndex_twoPrimeResidual X (h2.trans hdvd)
  exact Nat.odd_iff.2 (by omega)

end Odd

section PiG

open scoped Classical in
noncomputable def piG {G : Type} [Group G] (L : Subgroup G) (y : G) : Bar.Qbar L :=
  if h : y ∈ L then piBar L ⟨y, h⟩ else 1

variable {G : Type} [Group G] {L : Subgroup G}

theorem piG_of_mem {y : G} (h : y ∈ L) : piG L y = piBar L ⟨y, h⟩ := by
  classical
  simp [piG, h]

theorem piG_mul {x y : G} (hx : x ∈ L) (hy : y ∈ L) : piG L (x * y) = piG L x * piG L y := by
  rw [piG_of_mem (L.mul_mem hx hy), piG_of_mem hx, piG_of_mem hy, ← map_mul]
  rfl

theorem piG_one : piG L (1 : G) = 1 := by
  rw [piG_of_mem L.one_mem]
  rfl

theorem piG_pow {x : G} (hx : x ∈ L) (n : ℕ) : piG L (x ^ n) = piG L x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, piG_one]
  | succ n ih => rw [pow_succ, piG_mul (L.pow_mem hx n) hx, ih, pow_succ]

theorem piG_inv {x : G} (hx : x ∈ L) : piG L x⁻¹ = (piG L x)⁻¹ := by
  rw [piG_of_mem (L.inv_mem hx), piG_of_mem hx, ← map_inv]
  rfl

end PiG

section Key

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G}

omit [Finite G] in
theorem centralizes_iff_of_odd (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hXL : X ≤ L)
    (hodd : Odd (Nat.card (autI hV X))) (hVN : V ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥V →* Bar.Qbar L) (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L) {y : G} (hy : y ∈ X) :
    y ∈ Subgroup.centralizer (V : Set G) ↔ ∀ a : ↥V, piG L y * θ a = θ a * piG L y := by
  have hyL : y ∈ L := hXL hy
  have hyx : piG L y = piBar L ⟨y, hyL⟩ := piG_of_mem hyL
  constructor
  · intro hyc a
    have hcomm : (y : G) * a = a * y := (Subgroup.mem_centralizer_iff.1 hyc a a.2).symm
    have h1 := theta_equivariant hVN θ hθ hZ0 ⟨y, hyL⟩ a a (by
      show (a : G) = y * a * y⁻¹
      rw [hcomm]
      group)
    rw [hyx]
    have h2 : θ a = piBar L ⟨y, hyL⟩ * θ a * (piBar L ⟨y, hyL⟩)⁻¹ := h1
    calc piBar L ⟨y, hyL⟩ * θ a = (piBar L ⟨y, hyL⟩ * θ a * (piBar L ⟨y, hyL⟩)⁻¹) *
          piBar L ⟨y, hyL⟩ := by group
      _ = θ a * piBar L ⟨y, hyL⟩ := by rw [← h2]
  · intro hcomm
    have hc : ∀ a : ↥V, ∃ b : ↥V, (b : G) = y * a * y⁻¹ ∧ θ b = θ a := by
      intro a
      have hb : y * (a : G) * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXN hy) a).1 a.2
      refine ⟨⟨_, hb⟩, rfl, ?_⟩
      have h1 := theta_equivariant hVN θ hθ hZ0 ⟨y, hyL⟩ a ⟨_, hb⟩ rfl
      rw [h1]
      have h2 := hcomm a
      rw [hyx] at h2
      calc piBar L ⟨y, hyL⟩ * θ a * (piBar L ⟨y, hyL⟩)⁻¹ =
          (θ a * piBar L ⟨y, hyL⟩) * (piBar L ⟨y, hyL⟩)⁻¹ := by rw [h2]
        _ = θ a := by group
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    set a' : ↥V := ⟨a, ha⟩ with ha'
    obtain ⟨b, hb, hθb⟩ := hc a'
    set c : G := y * a * y⁻¹ * a⁻¹ with hcdef
    have hcV : c ∈ V := by
      have hb' : y * a * y⁻¹ ∈ V := hb ▸ b.2
      exact V.mul_mem hb' (V.inv_mem ha)
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
      have h1 : θ (b * a'⁻¹) = 1 := by rw [map_mul, map_inv, hθb, mul_inv_cancel]
      have h2 := (theta_eq_one_iff hVN θ hθ hZ0 hperf (b * a'⁻¹)).1 h1
      have h3 : (((b * a'⁻¹ : ↥V)) : G) = c := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb, hcdef, ha']
      rwa [h3] at h2
    have hyc : ∀ l ∈ L, l * c = c * l := fun l hl => Subgroup.mem_centralizer_iff.1 hcC l hl
    have hyc' : y * c = c * y := hyc y hyL
    have hya : y * a * y⁻¹ = c * a := by rw [hcdef]; group
    have hpow : ∀ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = c ^ k * a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : y ^ (k + 1) * a * (y ^ (k + 1))⁻¹ =
            y * (y ^ k * a * (y ^ k)⁻¹) * y⁻¹ := by rw [pow_succ', mul_inv_rev]; group
        rw [e, ih]
        have e2 : y * (c ^ k * a) * y⁻¹ = (y * c ^ k * y⁻¹) * (y * a * y⁻¹) := by group
        have e3 : y * c ^ k * y⁻¹ = c ^ k := by
          have : y * c ^ k = c ^ k * y := (Commute.pow_right (show Commute y c from hyc') k).eq
          rw [this]
          group
        rw [e2, e3, hya, pow_succ']
        group
    set N := Nat.card (autI hV X) with hN
    have hyN : y ^ N ∈ Subgroup.centralizer (V : Set G) := by
      have hψ : convI hV ⟨y, hXN hy⟩ ∈ autI hV X := convI_mem_autI hV hy (hXN hy)
      have h1 : (⟨convI hV ⟨y, hXN hy⟩, hψ⟩ : ↥(autI hV X)) ^ N = 1 := pow_card_eq_one'
      have h2 : convI hV (⟨y, hXN hy⟩ ^ N) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val h1
      exact (convI_eq_one_iff hV _).1 h2
    have h1 : y ^ N * a * (y ^ N)⁻¹ = a := by
      have := Subgroup.mem_centralizer_iff.1 hyN a ha
      rw [← this]
      group
    rw [hpow N] at h1
    have hcN : c ^ N = 1 := by
      have : c ^ N * a = 1 * a := by rw [h1, one_mul]
      exact mul_right_cancel this
    have hc2 : c ^ 2 = 1 := hV.2 c hcV
    obtain ⟨m, hm⟩ := hodd
    have hc1 : c = 1 := by
      have : c ^ N = c := by
        rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul]
      rw [← this, hcN]
    have : y * a * y⁻¹ = a := by rw [hya, hc1, one_mul]
    calc a * y = (y * a * y⁻¹) * y := by rw [this]
      _ = y * a := by group

omit [Finite G] in
theorem autI_cyclic_of_singer (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hXL : X ≤ L)
    (hodd : Odd (Nat.card (autI hV X))) (hVN : V ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥V →* Bar.Qbar L) (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L) {x₀ : G}
    (hx₀ : x₀ ∈ X) {e : ℕ}
    (hpow : ∀ y ∈ X, ∃ j : ℕ, ∀ w ∈ θ.range,
      piG L y * w * (piG L y)⁻¹ = piG L x₀ ^ j * w * (piG L x₀ ^ j)⁻¹)
    (hord : ∀ j : ℕ, (∀ w ∈ θ.range, piG L x₀ ^ j * w = w * piG L x₀ ^ j) ↔ e ∣ j) :
    IsCyclic (autI hV X) ∧ Nat.card (autI hV X) = e := by
  classical
  set c₀ : MulAut (IntMod V hV) := convI hV ⟨x₀, hXN hx₀⟩ with hc₀
  have hkey : ∀ j : ℕ, c₀ ^ j = 1 ↔ e ∣ j := by
    intro j
    have h1 : c₀ ^ j = 1 ↔ x₀ ^ j ∈ Subgroup.centralizer (V : Set G) := by
      rw [hc₀, ← map_pow, convI_eq_one_iff]
      rfl
    rw [h1, centralizes_iff_of_odd hV hXN hXL hodd hVN θ hθ hZ0 hperf (X.pow_mem hx₀ j),
      ← hord j]
    constructor
    · rintro h w ⟨a, rfl⟩
      rw [← piG_pow (hXL hx₀)]
      exact h a
    · intro h a
      rw [piG_pow (hXL hx₀)]
      exact h (θ a) ⟨a, rfl⟩
  have hord' : orderOf c₀ = e := by
    refine Nat.dvd_antisymm ?_ ?_
    · exact orderOf_dvd_of_pow_eq_one ((hkey e).2 dvd_rfl)
    · exact (hkey (orderOf c₀)).1 (pow_orderOf_eq_one c₀)
  have hz : autI hV X = Subgroup.zpowers c₀ := by
    refine le_antisymm (fun φ hφ => ?_) (Subgroup.zpowers_le.2 (convI_mem_autI hV hx₀ (hXN hx₀)))
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨j, hj⟩ := hpow g hg
    set z : G := (x₀ ^ j)⁻¹ * g with hzdef
    have hzX : z ∈ X := X.mul_mem (X.inv_mem (X.pow_mem hx₀ j)) hg
    have hzc : z ∈ Subgroup.centralizer (V : Set G) := by
      rw [centralizes_iff_of_odd hV hXN hXL hodd hVN θ hθ hZ0 hperf hzX]
      intro a
      have hgL : (g : G) ∈ L := hXL hg
      have hx₀L : x₀ ^ j ∈ L := L.pow_mem (hXL hx₀) j
      have h1 := hj (θ a) ⟨a, rfl⟩
      rw [hzdef, piG_mul (L.inv_mem hx₀L) hgL, piG_inv hx₀L, piG_pow (hXL hx₀)]
      have h2 : piG L g * θ a * (piG L g)⁻¹ = piG L x₀ ^ j * θ a * (piG L x₀ ^ j)⁻¹ := h1
      calc (piG L x₀ ^ j)⁻¹ * piG L g * θ a = (piG L x₀ ^ j)⁻¹ * (piG L g * θ a * (piG L g)⁻¹) *
            piG L g := by group
        _ = θ a * ((piG L x₀ ^ j)⁻¹ * piG L g) := by rw [h2]; group
    have hg_eq : (g : G) = x₀ ^ j * z := by rw [hzdef]; group
    have hconv : convI hV g = c₀ ^ j := by
      have hzN : z ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hzc
      have h1 : g = (⟨x₀, hXN hx₀⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ j * ⟨z, hzN⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_pow]; exact hg_eq)
      have hz1 : convI hV ⟨z, hzN⟩ = 1 := (convI_eq_one_iff hV ⟨z, hzN⟩).2 hzc
      rw [h1, map_mul, map_pow, hz1, mul_one]
    rw [hconv]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c₀) j
  refine ⟨?_, ?_⟩
  · rw [hz]
    infer_instance
  · rw [hz, Nat.card_zpowers, hord']

end Key


section Decomp

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

theorem decomp_of_fixed {U X : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hXU : X ≤ Subgroup.centralizer (U : Set G))
    (hodd : Odd (Nat.card (autI hV X)))
    (hfix : ∀ v ∈ V, (∀ x ∈ X, x * v = v * x) → v ∈ U) :
    U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hdec1 := Asc81c.fixV_inf_commSub_eq_bot' hW hodd
  have hdec2 := Asc81c.fixV_sup_commSub_eq_top' hW hodd
  have hcomm := map_valHom_commSub_eq hV hXN
  have hfixU : ∀ w ∈ fixV (autI hV X), E3.valHom hV w ∈ U := by
    intro w hw
    have h1 := (mem_fixV_autI hV hXN w).1 hw
    exact hfix w.val w.val_mem fun x hx => Subgroup.mem_centralizer_iff.1 h1 x hx
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgU, hgc⟩
    rw [← hcomm] at hgc
    obtain ⟨c, hc, rfl⟩ := hgc
    have hcF : c ∈ fixV (autI hV X) ⊓ commSub ⊤ (autI hV X) := by
      refine ⟨(mem_fixV_autI hV hXN c).2 ?_, hc⟩
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have := Subgroup.mem_centralizer_iff.1 (hXU hx) _ hgU
      rw [E3.valHom_apply] at this
      exact this.symm
    rw [hdec1, Subgroup.mem_bot] at hcF
    rw [hcF, map_one]
    exact Subgroup.one_mem _
  · refine le_antisymm (sup_le hUV ?_) fun v hv => ?_
    · rw [← hcomm]
      exact E3.map_valHom_le hV _
    · have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (autI hV X) ⊔ commSub ⊤ (autI hV X) := by
        rw [hdec2]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hw
      have hv' : v = E3.valHom hV a * E3.valHom hV b := by
        rw [← map_mul, hab]
        rfl
      rw [hv']
      refine Subgroup.mul_mem_sup (hfixU a ha) ?_
      rw [← hcomm]
      exact ⟨b, hb, rfl⟩

end Decomp

section Rank

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G}

theorem mQuot_eq_of_card_range (hV2 : IsPGroup 2 V) (hVN : V ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥V →* Bar.Qbar L) (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))
    (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L) {k : ℕ}
    (hk : Nat.card θ.range = 2 ^ k) : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = k := by
  have h1 := card_range_theta hVN θ hθ hZ0 hperf
  have h2 := E3.relIndex_eq_two_pow hV2 (V ⊓ Subgroup.centralizer (L : Set G))
  rw [hk] at h1
  rw [← h1] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

end Rank

end E68Proof

end E6

end CFSG.Quasithin

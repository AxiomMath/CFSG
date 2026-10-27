module

public import CFSG.RankThree.PartOne.F106.QD32Class

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

variable {X : Type} [Group X]

theorem eq_of_card_le_two {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (h : Nat.card H ≤ 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  by_contra hne
  have hinj : Function.Injective
      (![(⟨1, H.one_mem⟩ : H), ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → H) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem qd32Z_mem_of_normal {N : Subgroup QD32} [N.Normal] (hN : N ≠ ⊥) : qd32Z ∈ N := by
  by_contra hz
  have hc := qd32_card_le_two_of_not_mem hz
  obtain ⟨⟨t, htN⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcent : t ∈ Subgroup.center QD32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : g * t * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance t htN g
    have h2 : g * t * g⁻¹ ≠ 1 := by
      intro h
      apply ht1'
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have := eq_of_card_le_two hc h1 htN h2 ht1'
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [this]
  rw [quaternion_dihedral_extraspecial_involution_generation.2.2.2.2.2.2.2.1,
    mem_zpowers_qd32Z] at hcent
  rcases hcent with h | h
  · exact ht1' h
  · exact hz (h ▸ htN)

theorem qd32_dichotomy {G : Type*} [Group G] (ψ : G →* QD32) (hψ : Function.Surjective ψ)
    (K₁ K₂ : Subgroup G) [K₁.Normal] [K₂.Normal] (h1 : ψ.ker ≤ K₁)
    (h12 : K₁ ⊓ K₂ ≤ ψ.ker) : K₁ ≤ ψ.ker ∨ K₂ ≤ ψ.ker := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hK1, hK2⟩ := hcon
  have key : ∀ (K : Subgroup G) [K.Normal], ¬ K ≤ ψ.ker → ∃ s ∈ K, ψ s = qd32Z := by
    intro K _ hK
    obtain ⟨k, hkK, hkψ⟩ := Set.not_subset.mp hK
    have hn : (K.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hne : K.map ψ ≠ ⊥ := by
      intro hbot
      apply hkψ
      have : ψ k ∈ K.map ψ := Subgroup.mem_map_of_mem ψ hkK
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    obtain ⟨s, hsK, hs⟩ := Subgroup.mem_map.mp (qd32Z_mem_of_normal hne)
    exact ⟨s, hsK, hs⟩
  obtain ⟨s₁, hs₁, hψ₁⟩ := key K₁ hK1
  obtain ⟨s₂, hs₂, hψ₂⟩ := key K₂ hK2
  have hker : s₁⁻¹ * s₂ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ₁, hψ₂, inv_mul_cancel]
  have hs₂K₁ : s₂ ∈ K₁ := by
    have := K₁.mul_mem hs₁ (h1 hker)
    simpa using this
  have h3 := h12 ⟨hs₂K₁, hs₂⟩
  rw [MonoidHom.mem_ker, hψ₂] at h3
  have h4 := orderOf_qd32Z
  rw [h3, orderOf_one] at h4
  omega

theorem mem_centralizer_of_trivial_on_center {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Y R : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ q = 1) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ normalizer (Y : Set X)) {r : X} (hr : r ∈ R)
    (hZ : ∀ z ∈ Y, z ∈ centralizer (Y : Set X) → r * z * r⁻¹ = z)
    (hV : ∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) :
    r ∈ centralizer (Y : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨ν, hν⟩ : ∃ ν : X, ν = r * y * r⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hνY : ν ∈ Y := hν ▸ Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRN hr) y).mp hy)
    (Y.inv_mem hy)
  have hνC : ν ∈ centralizer (Y : Set X) := hν ▸ hV y hy
  have hrν : r * ν * r⁻¹ = ν := hZ ν hνY hνC
  have hry : r * y * r⁻¹ = ν * y := by rw [hν]; group
  have hpow : ∀ k : ℕ, r ^ k * y * (r ^ k)⁻¹ = ν ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : r ^ (k + 1) * y * (r ^ (k + 1))⁻¹ = r * (r ^ k * y * (r ^ k)⁻¹) * r⁻¹ := by
        rw [pow_succ']
        group
      have e2 : r * (ν ^ k * y) * r⁻¹ = (r * ν ^ k * r⁻¹) * (r * y * r⁻¹) := by group
      have e3 : r * ν ^ k * r⁻¹ = ν ^ k := by rw [← conj_pow, hrν]
      rw [e1, ih, e2, e3, hry, pow_succ]
      group
  obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
  have hrm : r ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hν2 : ν ^ (2 ^ m) = 1 := by
    have h1 := hpow (2 ^ m)
    rw [hrm, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_right.mp h1.symm)
  have hνq : ν ^ q = 1 := by
    have : ν ∈ Y := hνY
    exact hYexp ν hνY
  have hcop : Nat.Coprime (2 ^ m) q :=
    Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  have hν1 : ν = 1 := by
    have h3 : orderOf ν ∣ Nat.gcd (2 ^ m) q :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν2) (orderOf_dvd_of_pow_eq_one hνq)
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [hν1, one_mul] at hry
  exact (mul_inv_eq_iff_eq_mul.mp hry).symm

@[expose] noncomputable def inducedAutCenter (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun e := QuotientGroup.congr _ _ e (Subgroup.characteristic_iff_map_eq.mp inferInstance e)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' e f := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem inducedAutCenter_mk {G : Type*} [Group G] (e : MulAut G) (g : G) :
    inducedAutCenter G e (QuotientGroup.mk g) = QuotientGroup.mk (e g) := rfl

abbrev centerOf (Y : Subgroup X) : Subgroup X := Y ⊓ Subgroup.centralizer (Y : Set X)

theorem conj_mem_centerOf {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) {r : X}
    (hr : r ∈ R) {z : X} (hz : z ∈ centerOf Y) : r * z * r⁻¹ ∈ centerOf Y := by
  have hz1 := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hRN hr) z).mp hz1.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : r⁻¹ * y * r ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (hRN (R.inv_mem hr)) y).mp hy
    simpa using this
  have h := (Subgroup.mem_centralizer_iff.mp hz1.2) _ hy'
  calc y * (r * z * r⁻¹) = r * ((r⁻¹ * y * r) * z) * r⁻¹ := by group
    _ = r * (z * (r⁻¹ * y * r)) * r⁻¹ := by rw [h]
    _ = (r * z * r⁻¹) * y := by group

theorem le_normalizer_centerOf {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) :
    R ≤ normalizer (centerOf Y : Set X) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_centerOf hRN hr hz, fun hz => ?_⟩
  have := conj_mem_centerOf hRN (R.inv_mem hr) hz
  simpa [mul_assoc] using this

@[expose] noncomputable def actY {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) :
    ↥R →* MulAut ↥Y :=
  Y.normalizerMonoidHom.comp (Subgroup.inclusion hRN)

theorem actY_apply_coe {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) (r : ↥R)
    (y : ↥Y) : (((actY hRN r) y : ↥Y) : X) = (r : X) * (y : X) * (r : X)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Y (Subgroup.inclusion hRN r) y

@[expose] noncomputable def actZ {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) :
    ↥R →* MulAut ↥(centerOf Y) :=
  (centerOf Y).normalizerMonoidHom.comp (Subgroup.inclusion (le_normalizer_centerOf hRN))

theorem mem_ker_actZ {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) (r : ↥R) :
    r ∈ (actZ hRN).ker ↔ (r : X) ∈ centralizer (centerOf Y : Set X) := by
  rw [MonoidHom.mem_ker, actZ, MonoidHom.comp_apply]
  change Subgroup.inclusion (le_normalizer_centerOf hRN) r ∈
    (centerOf Y).normalizerMonoidHom.ker ↔ _
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  rfl

@[expose] noncomputable def actV {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) :
    ↥R →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  (inducedAutCenter ↥Y).comp (actY hRN)

theorem center_form_iff {Y : Subgroup X} {a y : X} (hy : y ∈ Y) :
    a⁻¹ * y ∈ centralizer (Y : Set X) ↔ a * y⁻¹ ∈ centralizer (Y : Set X) := by
  constructor
  · intro hc
    have h1 : y * (a⁻¹ * y) = (a⁻¹ * y) * y := Subgroup.mem_centralizer_iff.mp hc y hy
    have h2 : y * a⁻¹ = a⁻¹ * y := by
      have := h1
      rw [← mul_assoc] at this
      exact mul_right_cancel this
    have h3 : a * y⁻¹ = (a⁻¹ * y)⁻¹ := by
      rw [← h2]
      group
    rw [h3]
    exact Subgroup.inv_mem _ hc
  · intro hc
    have h1 : y * (a * y⁻¹) = (a * y⁻¹) * y := Subgroup.mem_centralizer_iff.mp hc y hy
    have h2 : y * a = a * y := by
      have h1' : y * a * y⁻¹ = a :=
        calc y * a * y⁻¹ = y * (a * y⁻¹) := by group
          _ = (a * y⁻¹) * y := h1
          _ = a := by group
      exact (mul_inv_eq_iff_eq_mul.mp h1')
    have h3 : a⁻¹ * y = (a * y⁻¹)⁻¹ :=
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [h2]
        _ = y * a⁻¹ := by group
        _ = (a * y⁻¹)⁻¹ := by group
    rw [h3]
    exact Subgroup.inv_mem _ hc

theorem mem_ker_actV {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) (r : ↥R) :
    r ∈ (actV hRN).ker ↔
      ∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X) := by
  rw [MonoidHom.mem_ker]
  have key : ∀ y : ↥Y, (QuotientGroup.mk (actY hRN r y) : ↥Y ⧸ Subgroup.center ↥Y) =
      QuotientGroup.mk y ↔
      (((r : X) * (y : X) * (r : X)⁻¹)⁻¹ * (y : X)) ∈ centralizer (Y : Set X) := by
    intro y
    rw [QuotientGroup.eq, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      have := congrArg (fun x : ↥Y => (x : X)) (h ⟨w, hw⟩)
      simpa [actY_apply_coe] using this
    · intro h w
      have := h w w.2
      exact Subtype.ext (by simpa [actY_apply_coe] using this)
  constructor
  · intro h y hy
    have h1' := DFunLike.congr_fun h (QuotientGroup.mk (⟨y, hy⟩ : ↥Y))
    have h1 : (QuotientGroup.mk (actY hRN r ⟨y, hy⟩) : ↥Y ⧸ Subgroup.center ↥Y) =
        QuotientGroup.mk ⟨y, hy⟩ := by
      simpa [actV, inducedAutCenter_mk] using h1'
    have h2 := (key ⟨y, hy⟩).mp h1
    have ha : (r : X) * y * (r : X)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hRN r.2) y).mp hy
    have := (center_form_iff hy).mp h2
    simpa [mul_assoc] using this
  · intro h
    refine MulEquiv.ext fun v => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
    have ha : (r : X) * g * (r : X)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hRN r.2) g).mp g.2
    have hg := h g g.2
    have := (key g).mpr ((center_form_iff g.2).mpr (by simpa [mul_assoc] using hg))
    exact this

theorem qd32_center_dichotomy {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y R : Subgroup X}
    (hYexp : ∀ y ∈ Y, y ^ q = 1) (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X)) :
    (∀ r : ↥R, (r : X) ∈ centralizer (centerOf Y : Set X) → (r : X) ∈ centralizer (Y : Set X)) ∨
    (∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X)) := by
  have h1 : ψ.ker ≤ (actZ hRN).ker := by
    intro r hr
    rw [mem_ker_actZ]
    have : (r : X) ∈ centralizer (Y : Set X) := (hψc r).mp hr
    exact Subgroup.centralizer_le inf_le_left this
  have h12 : (actZ hRN).ker ⊓ (actV hRN).ker ≤ ψ.ker := by
    intro r hr
    obtain ⟨hrZ, hrV⟩ := Subgroup.mem_inf.mp hr
    rw [mem_ker_actZ] at hrZ
    rw [mem_ker_actV] at hrV
    rw [MonoidHom.mem_ker, hψc]
    refine mem_centralizer_of_trivial_on_center hq hq2 hYexp hR2 hRN r.2 (fun z hzY hzC => ?_) hrV
    have := Subgroup.mem_centralizer_iff.mp hrZ z (Subgroup.mem_inf.mpr ⟨hzY, hzC⟩)
    rw [← this]
    group
  rcases qd32_dichotomy ψ hψs (actZ hRN).ker (actV hRN).ker h1 h12 with h | h
  · left
    intro r hr
    exact (hψc r).mp (MonoidHom.mem_ker.mp (h ((mem_ker_actZ hRN r).mpr hr)))
  · right
    intro r hr
    exact (hψc r).mp (MonoidHom.mem_ker.mp (h ((mem_ker_actV hRN r).mpr hr)))

theorem inducesQD32_centerOf {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X))
    (hA : ∀ r : ↥R, (r : X) ∈ centralizer (centerOf Y : Set X) →
      (r : X) ∈ centralizer (Y : Set X)) : InducesQD32 (centerOf Y) R :=
  ⟨le_normalizer_centerOf hRN, ψ, hψs, fun r =>
    ⟨fun h => Subgroup.centralizer_le inf_le_left ((hψc r).mp h), fun h => (hψc r).mpr (hA r h)⟩⟩

theorem isElementaryAbelian_centerOf {q : ℕ} {Y : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ q = 1) :
    IsElementaryAbelian q (centerOf Y) :=
  { is_comm := ⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp a.2).2 b
        (Subgroup.mem_inf.mp b.2).1).symm⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
      Subtype.ext (by simpa using hYexp y (Subgroup.mem_inf.mp y.2).1) }

theorem card_ge_pow_four_of_faithful_quotient [Finite X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Y R : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ q = 1)
    (hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) (hRN : R ≤ normalizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X))
    (hB : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X)) : q ^ 4 ≤ Nat.card Y := by
  have hker : ψ.ker ≤ (actV hRN).ker := fun r hr => (mem_ker_actV hRN r).mpr (fun y hy => by
    have h0 : (r : X) ∈ centralizer (Y : Set X) := (hψc r).mp hr
    have h1 := Subgroup.mem_centralizer_iff.mp h0 y hy
    have h2 : (r : X) * y * (r : X)⁻¹ * y⁻¹ = 1 := by
      rw [← h1]
      group
    rw [h2]
    exact Subgroup.one_mem _)
  let f : QD32 →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
    ψ.liftOfRightInverse (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
      ⟨actV hRN, hker⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨r, rfl⟩ := hψs x
    have hr : r ∈ (actV hRN).ker := by
      rw [MonoidHom.mem_ker]
      simpa [f] using hx
    exact (hψc r).mpr (hB r ((mem_ker_actV hRN r).mp hr))
  have hcomm : ∀ u v : ↥Y ⧸ Subgroup.center ↥Y, u * v = v * u := by
    intro u v
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_center_iff]
    intro g
    have h := hYcl (b : X)⁻¹ (Y.inv_mem b.2) (a : X)⁻¹ (Y.inv_mem a.2) g g.2
    have h' := commutatorElement_eq_one_iff_mul_comm.mp h
    have e : ((a : X) * b)⁻¹ * ((b : X) * a) = ⁅(b : X)⁻¹, (a : X)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact h'.symm
  have hexp : ∀ v : ↥Y ⧸ Subgroup.center ↥Y, v ^ q = 1 := by
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow]
    have : y ^ q = 1 := Subtype.ext (by simpa using hYexp y y.2)
    rw [this]
    rfl
  have h4 := card_ge_pow_four_of_qd32 hq hq2 hcomm hexp f hf
  exact h4.trans (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)

end CFSG.RankThree.PartOne.F106

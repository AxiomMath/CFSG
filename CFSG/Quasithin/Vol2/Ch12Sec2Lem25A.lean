module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24
public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology
public import CFSG.Quasithin.Background.BlueprintB2Frattini

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_centralizer_of_conj {U : Subgroup G} {h x : G} {p : ℕ} (hp : p.Prime)
    (hord : orderOf h = p) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hhU : h ∈ Subgroup.normalizer (U : Set G))
    (hUP : U ⊓ Subgroup.centralizer (Subgroup.zpowers h : Set G) = ⊥) (hU1 : U ≠ ⊥)
    (hxU : x ∈ Subgroup.centralizer (U : Set G)) (hxh : x * h * x⁻¹ ∈ U ⊔ Subgroup.zpowers h) :
    ∃ u ∈ U, u⁻¹ * x ∈ Subgroup.centralizer (Subgroup.zpowers h : Set G) := by
  classical
  have hPU : Subgroup.zpowers h ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).mpr hhU
  have hconjU : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ u ∈ U, g * u * g⁻¹ ∈ U :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  obtain ⟨w, hw, t, ht, hwt⟩ := Lem24.exists_mul_of_mem_sup_normal hPU hxh
  have hy : h⁻¹ * t ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hhu : h * u * h⁻¹ ∈ U := hconjU h hhU u hu
    have htu : t * u * t⁻¹ ∈ U := hconjU t (hPU ht) u hu
    have h1 : x * h * x⁻¹ * u * (x * h * x⁻¹)⁻¹ = h * u * h⁻¹ := by
      have hx := Subgroup.mem_centralizer_iff.mp hxU (h * u * h⁻¹) hhu
      calc x * h * x⁻¹ * u * (x * h * x⁻¹)⁻¹
          = x * h * (x⁻¹ * u * x) * h⁻¹ * x⁻¹ := by group
        _ = x * h * u * h⁻¹ * x⁻¹ := by
            rw [show x⁻¹ * u * x = u by
              have := Subgroup.mem_centralizer_iff.mp hxU u hu
              calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
                _ = x⁻¹ * (x * u) := by rw [this]
                _ = u := by group]
        _ = x * (h * u * h⁻¹) * x⁻¹ := by group
        _ = h * u * h⁻¹ * x * x⁻¹ := by rw [← hx]
        _ = h * u * h⁻¹ := by group
    have h2 : w * t * u * (w * t)⁻¹ = t * u * t⁻¹ := by
      calc w * t * u * (w * t)⁻¹ = w * (t * u * t⁻¹) * w⁻¹ := by group
        _ = t * u * t⁻¹ * w * w⁻¹ := by rw [hUab w hw _ htu]
        _ = t * u * t⁻¹ := by group
    rw [hwt] at h2
    rw [h1] at h2
    calc u * (h⁻¹ * t) = h⁻¹ * (h * u * h⁻¹) * t := by group
      _ = h⁻¹ * (t * u * t⁻¹) * t := by rw [h2]
      _ = h⁻¹ * t * u := by group
  have hth : t = h := by
    by_contra hne
    have hy1 : h⁻¹ * t ≠ 1 := fun h1 => hne (by rw [← mul_inv_cancel_left h t, h1, mul_one])
    have hyP : h⁻¹ * t ∈ Subgroup.zpowers h :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers h)) ht
    have hord' : orderOf (h⁻¹ * t) = p := by
      have hdvd : orderOf (h⁻¹ * t) ∣ p := by
        rw [← hord]
        exact orderOf_dvd_of_mem_zpowers hyP
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h1
    have hzz : Subgroup.zpowers (h⁻¹ * t) = Subgroup.zpowers h :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyP)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hord'])
    have hhC : h ∈ Subgroup.centralizer (U : Set G) := by
      have : h ∈ Subgroup.zpowers (h⁻¹ * t) := hzz ▸ Subgroup.mem_zpowers h
      exact (Subgroup.zpowers_le).mpr hy this
    apply hU1
    rw [eq_bot_iff, ← hUP]
    intro u hu
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcomm : Commute h u := (Subgroup.mem_centralizer_iff.mp hhC u hu).symm
    exact (hcomm.zpow_left k).eq
  rw [hth] at hwt
  let φ : ↥U → ↥U := fun u => ⟨u * h * (u : G)⁻¹ * h⁻¹, by
    rw [show (u : G) * h * (u : G)⁻¹ * h⁻¹ = u * (h * (u : G)⁻¹ * h⁻¹) by group]
    exact U.mul_mem u.2 (hconjU h hhU _ (U.inv_mem u.2))⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : (a : G) * h * (a : G)⁻¹ * h⁻¹ = b * h * (b : G)⁻¹ * h⁻¹ := congrArg Subtype.val hab
    have h2 : (b : G)⁻¹ * a ∈ U ⊓ Subgroup.centralizer (Subgroup.zpowers h : Set G) := by
      refine ⟨U.mul_mem (U.inv_mem b.2) a.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hc : Commute h ((b : G)⁻¹ * a) := by
        show h * ((b : G)⁻¹ * a) = (b : G)⁻¹ * a * h
        have : (a : G) * h * (a : G)⁻¹ = b * h * (b : G)⁻¹ := by
          have := congrArg (· * h) h1
          simpa using this
        calc h * ((b : G)⁻¹ * a) = (b : G)⁻¹ * (b * h * (b : G)⁻¹) * a := by group
          _ = (b : G)⁻¹ * ((a : G) * h * (a : G)⁻¹) * a := by rw [this]
          _ = (b : G)⁻¹ * a * h := by group
      exact (hc.zpow_left k).eq
    rw [hUP, Subgroup.mem_bot] at h2
    apply Subtype.ext
    have := congrArg ((b : G) * ·) h2
    simpa using this
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨w, hw⟩
  have hu' : (u : G) * h * (u : G)⁻¹ * h⁻¹ = w := congrArg Subtype.val hu
  refine ⟨u, u.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hc : Commute h ((u : G)⁻¹ * x) := by
    show h * ((u : G)⁻¹ * x) = (u : G)⁻¹ * x * h
    have e : x * h * x⁻¹ = (u : G) * h * (u : G)⁻¹ := by
      rw [← hwt, ← hu']
      group
    calc h * ((u : G)⁻¹ * x) = (u : G)⁻¹ * ((u : G) * h * (u : G)⁻¹) * x := by group
      _ = (u : G)⁻¹ * (x * h * x⁻¹) * x := by rw [e]
      _ = (u : G)⁻¹ * x * h := by group
  exact (hc.zpow_left k).eq

theorem exists_mul_mem_centralizer_of_cocycle {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ v : ↥V, v * v = 1) {n : ℕ}
    (hn : 4 ≤ n) (hVn : Nat.card ↥V = 2 ^ n) (htop : autOn L V = ⊤) {q : G}
    (hqL : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ V)
    (hqC : ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) → q * l * q⁻¹ * l⁻¹ = 1) :
    ∃ v ∈ V, v * q ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let _ := MulAutTwo.zmod2Module hV2
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive ↥V) = n :=
    Nat.pow_right_injective le_rfl (MulAutTwo.card_eq_pow_finrank.symm.trans hVn)
  set ρ : ↥L →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    MulAutTwo.linEquiv.toMonoidHom.comp (A4.actionOn V L hLV) with hρ
  have hρ1 : ∀ (l : ↥L) (v : ↥V), ρ l (Additive.ofMul v) =
      Additive.ofMul (A4.actionOn V L hLV l v) := fun _ _ => rfl
  have hρt : ∀ (f : Module.Dual (ZMod 2) (Additive ↥V)) (d : Additive ↥V) (h : f d = 0),
      ∃ l, ρ l = LinearEquiv.transvection h := by
    intro f d h
    set σ : MulAut ↥V := MulAutTwo.linEquiv.symm (LinearEquiv.transvection h)
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
    refine ⟨l, ?_⟩
    show MulAutTwo.linEquiv (A4.actionOn V L hLV l) = _
    rw [hl]
    exact MulEquiv.apply_symm_apply _ _
  set δ : ↥L → Additive ↥V := fun l => Additive.ofMul ⟨q * l * q⁻¹ * (l : G)⁻¹, hqL l l.2⟩
    with hδdef
  have hδ : ∀ g h, δ (g * h) = δ g + ρ g (δ h) := by
    intro g h
    rw [hδdef, hρ1]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_add, toMul_ofMul, Subgroup.coe_mul, A4.actionOn_apply_coe]
    group
  have hker : ∀ g, ρ g = 1 → δ g = 0 := by
    intro g hg
    have h1 : A4.actionOn V L hLV g = 1 := MulAutTwo.linEquiv.injective (by
      rw [map_one]
      exact hg)
    rw [A4.actionOn_eq_one_iff] at h1
    rw [hδdef]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, toMul_zero, OneMemClass.coe_one]
    exact hqC g g.2 h1
  obtain ⟨w, hw⟩ :=
    CFSG.GroupTheory.GLnTwoSplitting.exists_eq_of_isCocycle (hfin ▸ hn) ρ hρt δ hδ hker
  set v : ↥V := Additive.toMul w with hv
  have hwv : w = Additive.ofMul v := rfl
  refine ⟨v, v.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have e := hw ⟨l, hl⟩
  rw [hwv, hρ1, hδdef] at e
  have e' := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) e
  simp only [toMul_add, toMul_ofMul, Subgroup.coe_mul, A4.actionOn_apply_coe] at e'
  have hlv : l * (v : G) * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp v.2
  have hcomm : l * (v : G) * l⁻¹ * v = v * (l * (v : G) * l⁻¹) := by
    have := congrArg Subtype.val (mul_comm (⟨l * (v : G) * l⁻¹, hlv⟩ : ↥V) v)
    simpa using this
  have hvv : (v : G) * v = 1 := congrArg Subtype.val (hV2 v)
  have hav : (v : G) * (l * (v : G) * l⁻¹) * v = l * (v : G) * l⁻¹ := by
    calc (v : G) * (l * (v : G) * l⁻¹) * v = (l * (v : G) * l⁻¹) * ((v : G) * v) := by
          rw [← hcomm]; group
      _ = l * (v : G) * l⁻¹ := by rw [hvv, mul_one]
  calc l * ((v : G) * q) = (v : G) * (l * (v : G) * l⁻¹) * v * l * q := by rw [hav]; group
    _ = (v : G) * ((l * (v : G) * l⁻¹ * v) * l * q) := by group
    _ = (v : G) * ((q * l * q⁻¹ * l⁻¹) * l * q) := by rw [e']
    _ = (v : G) * q * l := by group

omit [Finite G] in
theorem comm_eq_one_of_mem_pCoreOf {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hbU : blockU L = V) (hCV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {q : G}
    (hqV : ∀ v ∈ V, q * v = v * q) (hqL : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ V) {l : G}
    (hl : l ∈ pCoreOf 2 L) (hlV : l ∈ Subgroup.centralizer (V : Set G)) :
    q * l * q⁻¹ * l⁻¹ = 1 := by
  have hlL : l ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hl
  set d := q * l * q⁻¹ * l⁻¹ with hd
  have hdV : d ∈ V := hqL l hlL
  have hdC : d ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    have hv₀ : l⁻¹ * l' * l * l'⁻¹ ∈ V := by
      rw [← hbU]
      have := Subgroup.commutator_mem_commutator (H₁ := blockQ L) (H₂ := L)
        (Subgroup.inv_mem _ hl) hl'
      rw [commutatorElement_def, inv_inv] at this
      exact this
    set a := q * l' * q⁻¹ * l'⁻¹ with ha
    have haV : a ∈ V := hqL l' hl'
    have h1 : q * (l' * l * l'⁻¹) * q⁻¹ * (l' * l * l'⁻¹)⁻¹ = d := by
      have hq0 := hqV _ hv₀
      calc q * (l' * l * l'⁻¹) * q⁻¹ * (l' * l * l'⁻¹)⁻¹
          = q * l * (q⁻¹ * (q * (l⁻¹ * l' * l * l'⁻¹))) * q⁻¹ * (l⁻¹ * l' * l * l'⁻¹)⁻¹ * l⁻¹ := by
            group
        _ = q * l * q⁻¹ * ((l⁻¹ * l' * l * l'⁻¹) * q) * q⁻¹ *
              (l⁻¹ * l' * l * l'⁻¹)⁻¹ * l⁻¹ := by rw [hq0]; group
        _ = d := by rw [hd]; group
    have hla : l * (l'⁻¹ * a⁻¹ * l') * l⁻¹ = l'⁻¹ * a⁻¹ * l' := by
      have hm : l'⁻¹ * a⁻¹ * l' ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hl')) a⁻¹).mp (V.inv_mem haV)
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hlV _ hm
      calc l * (l'⁻¹ * a⁻¹ * l') * l⁻¹ = (l'⁻¹ * a⁻¹ * l') * l * l⁻¹ := by rw [← hc]
        _ = l'⁻¹ * a⁻¹ * l' := by group
    have hdl : l' * d * l'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl') d).mp hdV
    have h2 : q * (l' * l * l'⁻¹) * q⁻¹ * (l' * l * l'⁻¹)⁻¹ = l' * d * l'⁻¹ := by
      calc q * (l' * l * l'⁻¹) * q⁻¹ * (l' * l * l'⁻¹)⁻¹
          = a * l' * d * (l * (l'⁻¹ * a⁻¹ * l') * l⁻¹) * l'⁻¹ := by rw [ha, hd]; group
        _ = a * (l' * d * l'⁻¹) * a⁻¹ := by rw [hla]; group
        _ = l' * d * l'⁻¹ * a * a⁻¹ := by rw [hVab a haV _ hdl]
        _ = l' * d * l'⁻¹ := by group
    rw [h1] at h2
    calc l' * d = l' * d * l'⁻¹ * l' := by group
      _ = d * l' := by rw [← h2]
  have : d ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hdV, hdC⟩
  rw [hCV, Subgroup.mem_bot] at this
  exact this

omit [Finite G] in
theorem mem_normalizer_of_TI' {V : Subgroup G}
    (hTI : ∀ g : G, CFSG.conjugate V g = V ∨ V ⊓ CFSG.conjugate V g = ⊥) {g x : G}
    (hx : x ∈ V) (hgx : g * x * g⁻¹ ∈ V) (hx1 : x ≠ 1) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  rcases hTI g with h | h
  · refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [← BlueprintB2.mem_conjugate_iff, h]
  · exfalso
    have : x ∈ V ⊓ CFSG.conjugate V g := ⟨hx, BlueprintB2.mem_conjugate_iff.mpr hgx⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this

omit [Finite G] in
theorem isTISetIn_conjugate {V : Subgroup G}
    (hTI : ∀ g : G, CFSG.conjugate V g = V ∨ V ⊓ CFSG.conjugate V g = ⊥) (k : G) :
    IsTISetIn (CFSG.conjugate V k) ⊤ := by
  refine ⟨le_top, fun g _ hg => eq_bot_iff.mpr fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hne
  have hx1' := BlueprintB2.mem_conjugate_iff.mp hx1
  have hx2' := BlueprintB2.mem_conjugate_iff.mp (mem_conjSubgroup_iff.mp hx2)
  apply hg
  have hN : k * g * k⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    refine mem_normalizer_of_TI' hTI hx1' ?_ ?_
    · rw [show k * g * k⁻¹ * (k * x * k⁻¹) * (k * g * k⁻¹)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ by group]
      exact hx2'
    · intro h1
      apply hne
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  rw [BlueprintB2.mem_conjugate_iff, BlueprintB2.mem_conjugate_iff,
    Subgroup.mem_normalizer_iff.mp hN]
  rw [show k * g * k⁻¹ * (k * z * k⁻¹) * (k * g * k⁻¹)⁻¹ = k * (g * z * g⁻¹) * k⁻¹ by group]

omit [Finite G] in
theorem conjugate_one (V : Subgroup G) : CFSG.conjugate V 1 = V := by
  ext x
  rw [BlueprintB2.mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem center_mulAut_eq_bot {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (h2 : 2 ≤ Nat.card V) : Subgroup.center (MulAut V) = ⊥ := by
  classical
  let _ := MulAutTwo.zmod2Module hV
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  set m := Module.finrank (ZMod 2) (Additive V) with hm
  have hm1 : 1 ≤ m := by
    by_contra h0
    have h00 : m = 0 := by omega
    have := MulAutTwo.card_eq_pow_finrank (V := V)
    rw [← hm, h00, pow_zero] at this
    omega
  let e : MulAut V ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
    (MulAutTwo.linEquiv.trans MulAutTwo.glEquiv).trans (MulAutTwo.slEquivGL m).symm
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    have := hx (e.symm y)
    have h' := congrArg e this
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  rw [MulAutTwo.center_SL_eq_bot hm1, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hex, map_one])

omit [Finite G] in
theorem isElemAbelian_conjugate' {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    IsElemAbelian 2 (CFSG.conjugate V g) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hx := BlueprintB2.mem_conjugate_iff.mp x.2
    have hy := BlueprintB2.mem_conjugate_iff.mp y.2
    have h := congrArg Subtype.val (hV.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    calc (x : G) * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · have h := hV.2 _ (BlueprintB2.mem_conjugate_iff.mp hx)
    rw [conj_pow, conj_eq_one_iff] at h
    exact h

theorem eq_of_fixed_of_odd_index {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ X.index) {x y : V} (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx : ∀ σ ∈ X, σ x = x) (hy : ∀ σ ∈ X, σ y = y) : x = y := by
  classical
  by_contra hxy
  let _ := MulAutTwo.zmod2Module hV
  have hz2 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hadd : ∀ a : Additive V, a + a = 0 := fun a => hV (Additive.toMul a)
  have key : ∀ (W : Submodule (ZMod 2) (Additive V)) (a b : Additive V),
      a ∉ W ⊔ Submodule.span (ZMod 2) {a + b} →
      ∃ σ : MulAut V, (∀ w ∈ W, σ (Additive.toMul w) = Additive.toMul w) ∧
        σ (Additive.toMul a) = Additive.toMul b := by
    intro W a b hab
    obtain ⟨f, hfa, hle⟩ := Submodule.exists_le_ker_of_notMem hab
    have hfd : f (a + b) = 0 :=
      hle (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    refine ⟨MulAutTwo.linEquiv.symm (LinearEquiv.transvection hfd), fun w hw => ?_, ?_⟩
    · show Additive.toMul (LinearEquiv.transvection hfd w) = _
      rw [LinearEquiv.transvection.apply, show f w = 0 from hle (Submodule.mem_sup_left hw),
        zero_smul, add_zero]
    · show Additive.toMul (LinearEquiv.transvection hfd a) = _
      rw [LinearEquiv.transvection.apply, hz2 _ hfa, one_smul, ← add_assoc, hadd, zero_add]
  have hmem2 : ∀ (c d z : Additive V), z ∈ Submodule.span (ZMod 2) {c} ⊔
      Submodule.span (ZMod 2) {d} → z = 0 ∨ z = c ∨ z = d ∨ z = c + d := by
    intro c d z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a with rfl | rfl <;>
      rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) b with rfl | rfl <;> simp
  set Sx := MulAction.stabilizer (MulAut V) x with hSx
  set Sy := MulAction.stabilizer (MulAut V) y with hSy
  have horb1 : MulAction.orbit (MulAut V) x = {v | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨σ, rfl⟩
      exact fun h => hx1 (σ.injective (by rw [map_one]; exact h))
    · intro hv
      by_cases hvx : v = x
      · exact ⟨1, by rw [hvx]; rfl⟩
      obtain ⟨σ, -, hσ⟩ := key ⊥ (Additive.ofMul x) (Additive.ofMul v) (by
        rw [bot_sup_eq]
        intro h
        rcases hmem2 0 (Additive.ofMul x + Additive.ofMul v) (Additive.ofMul x) (by
          rw [Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]; exact h) with h1 | h1 | h1 | h1
        · exact hx1 (Additive.ofMul.injective h1)
        · exact hx1 (Additive.ofMul.injective (by simpa using h1))
        · have h2 : Additive.ofMul v = 0 := by simpa using h1
          exact hv (Additive.ofMul.injective h2)
        · have h2 : Additive.ofMul v = 0 := by simpa using h1
          exact hv (Additive.ofMul.injective h2))
      exact ⟨σ, hσ⟩
  have horb2 : MulAction.orbit ↥Sx y = {v | v ≠ 1 ∧ v ≠ x} := by
    ext v
    constructor
    · rintro ⟨σ, rfl⟩
      have hσx : (σ : MulAut V) x = x := σ.2
      refine ⟨fun h => hy1 ((σ : MulAut V).injective (by rw [map_one]; exact h)), fun h => hxy ?_⟩
      exact (σ : MulAut V).injective (by rw [hσx]; exact h.symm)
    · rintro ⟨hv1, hvx⟩
      by_cases hvy : v = y
      · exact ⟨1, by rw [hvy]; rfl⟩
      obtain ⟨σ, hσW, hσ⟩ := key (Submodule.span (ZMod 2) {Additive.ofMul x}) (Additive.ofMul y)
        (Additive.ofMul v) (by
          intro h
          rcases hmem2 _ _ _ h with h1 | h1 | h1 | h1
          · exact hy1 (Additive.ofMul.injective h1)
          · exact hxy (Additive.ofMul.injective h1).symm
          · have h2 : Additive.ofMul v = 0 := by simpa using h1
            exact hv1 (Additive.ofMul.injective h2)
          · have h3 : Additive.ofMul x + Additive.ofMul v = 0 := by
              rw [add_left_comm] at h1
              simpa using h1
            apply hvx
            apply Additive.ofMul.injective
            calc Additive.ofMul v = Additive.ofMul v + (Additive.ofMul x + Additive.ofMul x) := by
                  rw [hadd, add_zero]
              _ = (Additive.ofMul x + Additive.ofMul v) + Additive.ofMul x := by abel
              _ = Additive.ofMul x := by rw [h3, zero_add])
      exact ⟨⟨σ, hσW _ (Submodule.mem_span_singleton_self _)⟩, hσ⟩
  have hc1 : ({1}ᶜ : Set V) = {v | v ≠ 1} := rfl
  have hidx1 : Sx.index = Nat.card V - 1 := by
    rw [hSx, MulAction.index_stabilizer, horb1, ← hc1]
    have := Set.ncard_add_ncard_compl ({1} : Set V)
    rw [Set.ncard_singleton] at this
    omega
  have hstab : MulAction.stabilizer ↥Sx y = Sy.subgroupOf Sx := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hSy, MulAction.mem_stabilizer_iff]
    rfl
  have hidx2 : (Sy.subgroupOf Sx).index = Nat.card V - 2 := by
    rw [← hstab, MulAction.index_stabilizer, horb2]
    have hc2 : ({1, x}ᶜ : Set V) = {v | v ≠ 1 ∧ v ≠ x} := by
      ext v
      simp
    rw [← hc2]
    have := Set.ncard_add_ncard_compl ({1, x} : Set V)
    rw [Set.ncard_pair (Ne.symm hx1)] at this
    omega
  have hVeven : 2 ∣ Nat.card V - 2 := by
    have hcard := MulAutTwo.card_eq_pow_finrank (V := V)
    have h1 : 1 < Nat.card V := Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨x, 1, hx1⟩⟩
    rw [hcard] at h1 ⊢
    have hm : Module.finrank (ZMod 2) (Additive V) ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h1
      exact lt_irrefl _ h1
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [hm', pow_succ]
    exact Nat.dvd_sub (dvd_mul_left 2 _) (dvd_refl 2)
  have hXle : X ≤ Sx ⊓ Sy := fun σ hσ => ⟨hx σ hσ, hy σ hσ⟩
  apply hX
  have h1 := Subgroup.relIndex_mul_index hXle
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : Sx ⊓ Sy ≤ Sx)
  rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, hidx2, inf_comm] at h2
  rw [← h1, ← h2]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hVeven _) _

end Lem25

end CFSG.Quasithin.H13

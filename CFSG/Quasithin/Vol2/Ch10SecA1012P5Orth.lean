module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecAFactsTorus
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Vec

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_injective_of_case_four
    (hFO : FactOrthTorus) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I)
    {n : ℕ} (h4 : Ch10.Case10_1_1Four T L I n) (hC0 : fsuCVM T L I = ⊥) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) :
    ∃ f : ↥(D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →*
      Multiplicative (ZMod (2 ^ n + 1) × ZMod (2 ^ n + 1)), Function.Injective f := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨-, -, hUab, hO⟩ := h4
  have hloc := hyp.fsu.maximal.1
  have htM := le_fsuM T L ht
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I) (fsuL0_le_normalizer hloc)
  obtain ⟨v, hvU, hvC, hvS⟩ := exists_mem_centralizer_of_fsuCVM_eq_bot hyp hC0
  obtain ⟨w₁, hw₁U, hw₁C, hw₁S, w₂, hw₂U, hw₂C, hw₂S, hx⟩ :=
    exists_vectors h37 h38 h322 hyp ht htn hD hvU hvC hvS
  rw [hC0] at hw₁C hw₂C hx
  set Y := D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hYdef
  have hYX : ∀ x ∈ Y, x ∈ fsuL0 T L ⊓ Subgroup.normalizer (T0 T L : Set G) :=
    fun x hx => oTwoUpper_le _ (hD.1 hx.1)
  have hYU : Y ≤ Subgroup.normalizer (fsuUL T L I : Set G) := fun x hx => hL0U (hYX x hx).1
  have hcY : ∀ x ∈ Y, t * x * t⁻¹ ∈ fsuL0 T L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp htM x).mp (hYX x hx).1
  let ψ₁ : ↥Y →* MulAut ↥(fsuUL T L I) := (conjAct (fsuUL T L I)).comp (Subgroup.inclusion hYU)
  let c : ↥Y →* ↥(Subgroup.normalizer (fsuUL T L I : Set G)) :=
    { toFun := fun x => ⟨t * (x : G) * t⁻¹, hL0U (hcY x x.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let ψ₂ : ↥Y →* MulAut ↥(fsuUL T L I) := (conjAct (fsuUL T L I)).comp c
  have hψ₁v : ∀ x : ↥Y, ψ₁ x = conjAct (fsuUL T L I) ⟨x, hYU x.2⟩ := fun x => rfl
  have hψ₂v : ∀ x : ↥Y,
      ψ₂ x = conjAct (fsuUL T L I) ⟨t * (x : G) * t⁻¹, hL0U (hcY x x.2)⟩ := fun x => rfl
  have hsyl := isSylowTwoOf_autOn_inf hyp
  have hYodd : Odd (Nat.card ↥Y) := Odd.of_dvd_nat hD.2.1 (Subgroup.card_dvd_of_le inf_le_left)
  have hA₁H : ψ₁.range ≤ autOn L (fsuUL T L I) := by
    rintro _ ⟨x, rfl⟩
    exact conjAct_mem_autOn_of_mem_fsuL0 h37 h38 hyp (hYX x x.2).1 (hYU x.2)
  have hA₁N : ψ₁.range ≤
      Subgroup.normalizer (autOn (T ⊓ L) (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) := by
    rintro _ ⟨x, rfl⟩
    exact conjAct_mem_normalizer_autOn (hYU x.2) (mem_normalizer_inf_of_mem (le_fsuL0 T L)
      (fsuL0_le_normalizer hloc) (hYX x x.2).1 (hYX x x.2).2)
  have hw₁P : ∀ p ∈ autOn (T ⊓ L) (fsuUL T L I), p ⟨w₁, hw₁U⟩ = ⟨w₁, hw₁U⟩ := by
    intro p hp
    obtain ⟨g, hgK, rfl⟩ := mem_autOn_iff'.mp hp
    apply Subtype.ext
    rw [coe_conjAct_apply', Subgroup.mem_centralizer_iff.mp hw₁S g hgK, mul_inv_cancel_right]
  have hw₁A : ∀ a ∈ ψ₁.range, a ⟨w₁, hw₁U⟩ = ⟨w₁, hw₁U⟩ := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    rw [hψ₁v, coe_conjAct_apply']
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hx x x.2).1)
  obtain ⟨f₁, hf₁⟩ := hFO ↥(fsuUL T L I) (autOn L (fsuUL T L I)) n hO _ hsyl ψ₁.range hA₁H
    hA₁N (Odd.of_dvd_nat hYodd (Subgroup.card_range_dvd ψ₁)) ⟨w₁, hw₁U⟩
    (fun h => hw₁C (Subgroup.mem_bot.mpr (congrArg Subtype.val h))) hw₁P hw₁A
  have hv₂U : t * w₂ * t⁻¹ ∈ fsuUL T L I := mem_conjugate_iff.mp hw₂U
  have hA₂H : ψ₂.range ≤ autOn L (fsuUL T L I) := by
    rintro _ ⟨x, rfl⟩
    exact conjAct_mem_autOn_of_mem_fsuL0 h37 h38 hyp (hcY x x.2) (hL0U (hcY x x.2))
  have hA₂N : ψ₂.range ≤
      Subgroup.normalizer (autOn (T ⊓ L) (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) := by
    rintro _ ⟨x, rfl⟩
    have hxLt := mem_normalizer_inf_of_mem (conjugate_le_fsuL0 ht)
      (fsuL0_le_normalizer_conjugate hloc htM) (hYX x x.2).1 (hYX x x.2).2
    exact conjAct_mem_normalizer_autOn (hL0U (hcY x x.2)) (conj_mem_normalizer_inf ht hxLt)
  have hw₂P : ∀ p ∈ autOn (T ⊓ L) (fsuUL T L I),
      p ⟨t * w₂ * t⁻¹, hv₂U⟩ = ⟨t * w₂ * t⁻¹, hv₂U⟩ := by
    intro p hp
    obtain ⟨g, hgK, rfl⟩ := mem_autOn_iff'.mp hp
    apply Subtype.ext
    rw [coe_conjAct_apply']
    have h1 := Subgroup.mem_centralizer_iff.mp hw₂S _ ((mem_inf_iff_conj ht _).mp hgK)
    calc (g : G) * (t * w₂ * t⁻¹) * (g : G)⁻¹ =
        t * (t⁻¹ * g * t * w₂) * (t⁻¹ * g * t)⁻¹ * t⁻¹ := by group
      _ = t * (w₂ * (t⁻¹ * g * t)) * (t⁻¹ * g * t)⁻¹ * t⁻¹ := by rw [h1]
      _ = t * w₂ * t⁻¹ := by group
  have hw₂A : ∀ a ∈ ψ₂.range, a ⟨t * w₂ * t⁻¹, hv₂U⟩ = ⟨t * w₂ * t⁻¹, hv₂U⟩ := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    rw [hψ₂v, coe_conjAct_apply']
    have h1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hx x x.2).2)
    calc t * (x : G) * t⁻¹ * (t * w₂ * t⁻¹) * (t * (x : G) * t⁻¹)⁻¹ =
        t * ((x : G) * w₂ * (x : G)⁻¹) * t⁻¹ := by group
      _ = t * w₂ * t⁻¹ := by rw [h1]
  obtain ⟨f₂, hf₂⟩ := hFO ↥(fsuUL T L I) (autOn L (fsuUL T L I)) n hO _ hsyl ψ₂.range hA₂H
    hA₂N (Odd.of_dvd_nat hYodd (Subgroup.card_range_dvd ψ₂)) ⟨t * w₂ * t⁻¹, hv₂U⟩
    (fun h => hw₂C (Subgroup.mem_bot.mpr (conj_eq_one_iff.mp (congrArg Subtype.val h))))
    hw₂P hw₂A
  refine ⟨(@MulEquiv.prodMultiplicative (ZMod (2 ^ n + 1)) (ZMod (2 ^ n + 1)) _
    _).symm.toMonoidHom.comp
    ((f₁.comp ψ₁.rangeRestrict).prod (f₂.comp ψ₂.rangeRestrict)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx'
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    MonoidHom.prod_apply, Prod.mk_eq_one] at hx'
  obtain ⟨h1, h2⟩ := hx'
  rw [MonoidHom.comp_apply, ← map_one f₁] at h1
  rw [MonoidHom.comp_apply, ← map_one f₂] at h2
  have e1 : ψ₁ x = 1 := by simpa using congrArg Subtype.val (hf₁ h1)
  have e2 : ψ₂ x = 1 := by simpa using congrArg Subtype.val (hf₂ h2)
  have hU : ∀ u ∈ fsuUL T L I, (x : G) * u * (x : G)⁻¹ = u := by
    intro u hu
    have h5 := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu⟩ : ↥(fsuUL T L I)) : G)) e1
    simp only [hψ₁v, coe_conjAct_apply', MulAut.one_apply] at h5
    exact h5
  have hU' : ∀ u ∈ fsuUL T L I, t * (x : G) * t⁻¹ * u * (t * (x : G) * t⁻¹)⁻¹ = u := by
    intro u hu
    have h5 := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu⟩ : ↥(fsuUL T L I)) : G)) e2
    simp only [hψ₂v, coe_conjAct_apply', MulAut.one_apply] at h5
    exact h5
  have hxodd : Odd (orderOf (x : G)) :=
    Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard _ x.2.1)
  exact Subtype.ext (eq_one_of_forall_conj_eq h37 h38 hyp ht htn (hYX x x.2).1 hxodd hU
    (forall_conj_eq_of_conj hU'))

end CFSG.Quasithin.Vol2.Ch10.SecA

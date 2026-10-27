module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcAdj
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof3
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.StandardType.RecipeExcLang


private theorem q2cExcF_inndiagConj {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {u : MulAut (TableBExc.RecipeGroup τ K)} (hu : u ∈ TableBExc.RecipeID τ K) :
    ∃ h ∈ inndiagGroup τ K, ∀ c : adjointGroup τ K,
      (MulAut.congr (TableBExc.recipeEquiv τ K) u c : ModGL τ K) = h * c * h⁻¹ := by
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨w, hw⟩ := (E6ThreeModel.recipeID_iff_hatAut u).mp hu
    refine ⟨(w : ModGL .E6 K), E6IDB.mem_hatGroup_iff_mem_inndiagGroup.1 w.2, ?_⟩
    intro c
    rw [← hw]
    exact TableBExc.E6Three.coe_hatAut_apply w c
  · obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_E7 K hu
    refine ⟨((TableBExc.recipeEquiv .E7 K r : adjointGroup .E7 K) : ModGL .E7 K),
      adjointGroup_le_inndiagGroup (TableBExc.recipeEquiv .E7 K r).2, ?_⟩
    intro c
    rw [← hr]
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_E8 K hu
    refine ⟨((TableBExc.recipeEquiv .E8 K r : adjointGroup .E8 K) : ModGL .E8 K),
      adjointGroup_le_inndiagGroup (TableBExc.recipeEquiv .E8 K r).2, ?_⟩
    intro c
    rw [← hr]
    simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem q2cExcF_m_eq {m n s : ℕ} {K F₀ : Type} [Field K] [Finite K]
    [Field F₀] [Finite F₀] (hK : Nat.card K = 2 ^ n) (hF : Nat.card F₀ = 2 ^ m)
    (hfield : Nat.card F₀ = Nat.card K ^ s) : m = n * s := by
  have h2 : 2 ^ m = 2 ^ (n * s) := by rw [← hF, hfield, hK, pow_mul]
  exact Nat.pow_right_injective (le_refl 2) h2

private theorem q2cExcF_transport {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK2 : ringChar K = 2)
    {u : MulAut (TableBExc.RecipeGroup τ K)} (hu : u ∈ TableBExc.RecipeID τ K)
    (huo : orderOf u = p)
    {J : Subgroup (TableBExc.RecipeGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    ∃ s : ℕ, 1 ≤ s ∧ Nat.card F₀ = Nat.card K ^ s ∧ s * (d - 1) ≤ τ.rank ∧
      (τ = .E6 → d ≤ 6) := by
  classical
  let e : TableBExc.RecipeGroup τ K ≃* adjointGroup τ K := TableBExc.recipeEquiv τ K
  let β : MulAut (adjointGroup τ K) := MulAut.congr e u
  have hβ : ∃ h ∈ inndiagGroup τ K, ∀ c : adjointGroup τ K,
      (β c : ModGL τ K) = h * c * h⁻¹ := q2cExcF_inndiagConj hτ hK2 hu
  have hβp : β ^ p = 1 := by
    have hu_p : u ^ p = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
    change (MulAut.congr e u) ^ p = 1
    rw [← map_pow, hu_p, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    have hu1 : u = 1 := by
      apply (MulAut.congr e).injective
      change (MulAut.congr e) u = (MulAut.congr e) 1
      rw [map_one]
      exact h
    have hp1 : p = 1 := by rw [← huo, hu1, orderOf_one]
    exact hp.ne_one hp1
  let J' : Subgroup (adjointGroup τ K) := J.map e.toMonoidHom
  have hfix : (ggAutFixedSubgroup u).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
    rw [show β = MulAut.congr e u from rfl,
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e u]
    have hsame : ggAutFixedSubgroup u =
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup u := by
      ext x
      rw [mem_ggAutFixedSubgroup, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    rw [hsame]
    rfl
  have hJ' : CFSG.Open.IsComponentOf J'
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
    have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e hJ
    rw [hfix] at h
    exact h
  let eJ : ↥J ≃* ↥J' := J.equivMapOfInjective e.toMonoidHom e.injective
  have hc : (Subgroup.center ↥J).map eJ = Subgroup.center ↥J' :=
    Subgroup.map_center_eq eJ
  let θ' : ↥J' ⧸ Subgroup.center ↥J' ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) :=
    (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') eJ hc).symm.trans θ
  exact q2c_exc_comp_typeA hτ hp hp2 hK2 β hβ hβp hβ1 J' hJ' hd hm hF₀ θ'

theorem q2c_exc_field_E7 {p d m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E7)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ => 5 ≤ d →
      ∀ u ∈ I, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
        ∃ s : ℕ, 1 ≤ s ∧ m = lab.n * s ∧ s * (d - 1) ≤ 7) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro hd5 u hu huo J hJ K' _ _ hK'card hθ
  obtain ⟨θ⟩ := hθ
  obtain ⟨s, hs1, hfield, hrank, -⟩ :=
    q2cExcF_transport (τ := .E7) (Or.inr (Or.inl rfl)) hp hp2 (ringChar.eq K 2)
      hu huo hJ hd5 hm hK'card θ
  exact ⟨s, hs1, q2cExcF_m_eq hKcard hK'card hfield, by simpa [Tag.rank] using hrank⟩

theorem q2c_exc_field_E8 {p d m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ => 5 ≤ d →
      ∀ u ∈ I, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
        ∃ s : ℕ, 1 ≤ s ∧ m = lab.n * s ∧ s * (d - 1) ≤ 8) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro hd5 u hu huo J hJ K' _ _ hK'card hθ
  obtain ⟨θ⟩ := hθ
  obtain ⟨s, hs1, hfield, hrank, -⟩ :=
    q2cExcF_transport (τ := .E8) (Or.inr (Or.inr rfl)) hp hp2 (ringChar.eq K 2)
      hu huo hJ hd5 hm hK'card θ
  exact ⟨s, hs1, q2cExcF_m_eq hKcard hK'card hfield, by simpa [Tag.rank] using hrank⟩

theorem q2c_exc_field_E6 {p d m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E6)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ => 5 ≤ d →
      ∀ u ∈ I, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
        ∃ s : ℕ, 1 ≤ s ∧ m = lab.n * s ∧ s * (d - 1) ≤ 6 ∧ d ≤ 6) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro hd5 u hu huo J hJ K' _ _ hK'card hθ
  obtain ⟨θ⟩ := hθ
  obtain ⟨s, hs1, hfield, hrank, hE6⟩ :=
    q2cExcF_transport (τ := .E6) (Or.inl rfl) hp hp2 (ringChar.eq K 2)
      hu huo hJ hd5 hm hK'card θ
  exact ⟨s, hs1, q2cExcF_m_eq hKcard hK'card hfield, by simpa [Tag.rank] using hrank,
    by simpa using hE6 rfl⟩

end CFSG.StandardType

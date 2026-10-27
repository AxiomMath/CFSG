module

public import CFSG.RankThree.PartOne.KE6.E6LData
public import CFSG.RankThree.PartOne.KE.E8A2NativeModule

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE

class M27Ok (τ : Tag) : Prop where
  isE7E8 : τ = .E7 ∨ τ = .E8

instance : M27Ok .E7 := ⟨Or.inl rfl⟩

instance : M27Ok .E8 := ⟨Or.inr rfl⟩

@[expose] def m27Label {τ : Tag} [M27Ok τ] (a : Fin e6Data.d) : Label τ :=
  Sum.inr ⟨m27Root τ a, m27_isRoot M27Ok.isE7E8 a⟩

theorem m27Label_injective {τ : Tag} [M27Ok τ] :
    Function.Injective (m27Label (τ := τ)) := fun _ _ h =>
  m27Root_injective M27Ok.isE7E8 (congrArg Subtype.val (Sum.inr_injective h))

@[expose] def m27Emb (τ : Tag) [M27Ok τ] (K : Type) [Field K] :
    (Fin e6Data.d →₀ K) →ₗ[K] RootModule τ K :=
  Finsupp.lmapDomain K K (m27Label (τ := τ))

theorem m27Emb_single {τ : Tag} [M27Ok τ] {K : Type} [Field K] (a : Fin e6Data.d) (c : K) :
    m27Emb τ K (Finsupp.single a c) = Finsupp.single (m27Label a) c :=
  Finsupp.mapDomain_single

theorem m27Emb_injective {τ : Tag} [M27Ok τ] {K : Type} [Field K] :
    Function.Injective (m27Emb τ K) :=
  Finsupp.mapDomain_injective m27Label_injective

theorem m27Emb_basis {τ : Tag} [M27Ok τ] {K : Type} [Field K] (a : Fin e6Data.d) :
    m27Emb τ K (Finsupp.single a 1) = rootVec τ K (m27Root τ a) := by
  rw [m27Emb_single, rootVec_eq_single_of_isRoot (m27_isRoot M27Ok.isE7E8 a)]
  rfl

theorem xOp_rootVec_E78 {τ : Tag} [M27Ok τ] {K : Type} [Field K] (i : Fin τ.rank) (c : K)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ K i c (rootVec τ K α) = rootVec τ K α + c • rootVec τ K (α + Pi.single i 1) := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact xOp_rootVec_E7 i c hα h₁ h₂
  · exact xOp_rootVec_E8 i c hα h₁ h₂

theorem yOp_rootVec_E78 {τ : Tag} [M27Ok τ] {K : Type} [Field K] (i : Fin τ.rank) (c : K)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ K i c (rootVec τ K α) = rootVec τ K α + c • rootVec τ K (α - Pi.single i 1) := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact yOp_rootVec_E7 i c hα h₁ h₂
  · exact yOp_rootVec_E8 i c hα h₁ h₂

theorem rootVec_eq_zero_of_not_isRoot_E78 {τ : Tag} {K : Type} [Field K]
    {β : Fin τ.rank → ℤ} (hβ : ¬ IsRoot τ β) : rootVec τ K β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem m27_add_single {τ : Tag} [M27Ok τ] [E6Sub τ] (a : Fin e6Data.d) (j : Fin Tag.E6.rank)
    (h : e6wt a j.val = -1) :
    m27Root τ ⟨e6Data.weyl a j, e6Data_weyl_lt a j⟩ = m27Root τ a + Pi.single (e6Idx j) 1 := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact m27_add_single_E7 a j h
  · exact m27_add_single_E8 a j h

theorem m27_sub_single {τ : Tag} [M27Ok τ] [E6Sub τ] (a : Fin e6Data.d) (j : Fin Tag.E6.rank)
    (h : e6wt a j.val = 1) :
    m27Root τ ⟨e6Data.weyl a j, e6Data_weyl_lt a j⟩ = m27Root τ a - Pi.single (e6Idx j) 1 := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact m27_sub_single_E7 a j h
  · exact m27_sub_single_E8 a j h

theorem xOp_comp_m27Emb {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K]
    (j : Fin Tag.E6.rank) (c : K) :
    xOp τ K (e6Idx j) c ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (1 + c • e6Data.rootOp K (Pi.single j 1)) := by
  refine Finsupp.lhom_ext' fun a => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, m27Emb_basis, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [e6Data_valid.rootOp_single_apply, xOp_rootVec_E78 _ c (m27_isRoot M27Ok.isE7E8 a)
    (m27_ne_single M27Ok.isE7E8 a j).1 (m27_ne_single M27Ok.isE7E8 a j).2]
  by_cases hw : e6wt a j.val = -1
  · have hw' : e6Data.wt a j = -1 := hw
    have hs : (⟨e6Data.weyl a j, e6Data_weyl_lt a j⟩ : Fin e6Data.d) = e6Data_valid.sRefl j a :=
      Fin.ext (e6Data_valid.sRefl_val j a).symm
    simp only [hw', ↓reduceIte]
    rw [m27Emb_basis, ← hs, ← m27_add_single a j hw]
  · have hw' : ¬ e6Data.wt a j = -1 := hw
    simp only [hw', ↓reduceIte, map_zero, smul_zero, add_zero]
    rw [rootVec_eq_zero_of_not_isRoot_E78 (m27_not_add M27Ok.isE7E8 a j hw), smul_zero, add_zero]

theorem yOp_comp_m27Emb {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K]
    (j : Fin Tag.E6.rank) (c : K) :
    yOp τ K (e6Idx j) c ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (1 + c • e6Data.rootOp K (-Pi.single j 1)) := by
  refine Finsupp.lhom_ext' fun a => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, m27Emb_basis, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [e6Data_valid.rootOp_neg_single_apply, yOp_rootVec_E78 _ c (m27_isRoot M27Ok.isE7E8 a)
    (m27_ne_single M27Ok.isE7E8 a j).1 (m27_ne_single M27Ok.isE7E8 a j).2]
  by_cases hw : e6wt a j.val = 1
  · have hw' : e6Data.wt a j = 1 := hw
    have hs : (⟨e6Data.weyl a j, e6Data_weyl_lt a j⟩ : Fin e6Data.d) = e6Data_valid.sRefl j a :=
      Fin.ext (e6Data_valid.sRefl_val j a).symm
    simp only [hw', ↓reduceIte]
    rw [m27Emb_basis, ← hs, ← m27_sub_single a j hw]
  · have hw' : ¬ e6Data.wt a j = 1 := hw
    simp only [hw', ↓reduceIte, map_zero, smul_zero, add_zero]
    rw [rootVec_eq_zero_of_not_isRoot_E78 (m27_not_sub M27Ok.isE7E8 a j hw), smul_zero, add_zero]

end CFSG.RankThree.PartOne.KE6

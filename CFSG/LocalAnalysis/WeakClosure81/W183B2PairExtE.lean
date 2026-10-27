module

public import CFSG.LocalAnalysis.WeakClosure81.W19ModE
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic

variable {G : Type} [Group G] [Finite G]

theorem w183b2_pair_psi {H E : Subgroup G} (M : ModDataE H E) {A B : Subgroup G}
    (hA : A ≤ H) (hB : B ≤ H)
    (hKsol : IsSolvable ↥(H ⊓ Subgroup.centralizer (E : Set G))) :
    ∃ ψ : ↥(A ⊔ B) →* ↥(M.img H), IsSolvable ψ.ker ∧
      Nonempty (↥ψ.range ≃* ↥(M.img A ⊔ M.img B)) := by
  have hAB : A ⊔ B ≤ H := sup_le hA hB
  let ψ₀ : ↥(A ⊔ B) →* LGL 2 M.W := M.ρ.comp (Subgroup.inclusion hAB)
  have hmem : ∀ y : ↥(A ⊔ B), ψ₀ y ∈ M.img H := fun y =>
    M.mem_img.2 ⟨⟨y, hAB y.2⟩, hAB y.2, rfl⟩
  let ψ : ↥(A ⊔ B) →* ↥(M.img H) := ψ₀.codRestrict (M.img H) hmem
  refine ⟨ψ, ?_, ?_⟩
  · let j : ↥ψ.ker →* G := (A ⊔ B).subtype.comp ψ.ker.subtype
    have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
    have hjmem : ∀ y : ↥ψ.ker, j y ∈ H ⊓ Subgroup.centralizer (E : Set G) := by
      intro y
      have h1 : ψ y.1 = 1 := MonoidHom.mem_ker.1 y.2
      have h2 : M.ρ ⟨((y.1 : ↥(A ⊔ B)) : G), hAB y.1.2⟩ = 1 := congrArg Subtype.val h1
      exact ⟨hAB y.1.2, (M.ρ_eq_one_iff _).1 h2⟩
    let f := j.codRestrict (H ⊓ Subgroup.centralizer (E : Set G)) hjmem
    have hfinj : Function.Injective f := by
      intro a b hab
      apply hjinj
      have h1 := congrArg Subtype.val hab
      exact h1
    haveI : Group.IsSolvable ↥(H ⊓ Subgroup.centralizer (E : Set G)) := hKsol
    exact Group.isSolvable_of_isSolvable_injective hfinj
  · have h1 : ψ.range.map (M.img H).subtype = ψ₀.range := by
      have h0 : ψ₀ = (M.img H).subtype.comp ψ := MonoidHom.ext fun y => rfl
      rw [h0, MonoidHom.range_comp]
    have hrange : ψ.range.map (M.img H).subtype = M.img A ⊔ M.img B := by
      rw [h1]
      change (M.ρ.comp (Subgroup.inclusion hAB)).range = _
      rw [MonoidHom.range_comp, Subgroup.inclusion_range, Subgroup.subgroupOf_sup hA hB,
        Subgroup.map_sup]
      rfl
    exact ⟨(Subgroup.equivMapOfInjective ψ.range (M.img H).subtype
      (M.img H).subtype_injective).trans (MulEquiv.subgroupCongr hrange)⟩

theorem w183b2_subgroupOf_sup_eq_top (A B : Subgroup G) :
    A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

end CFSG.LocalAnalysis.WeakClosure81

end

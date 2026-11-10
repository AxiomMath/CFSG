module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Timmesfeld
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

noncomputable abbrev RetH
    (τ : Tag) (β : Fin 6 → Fin τ.rank → ℤ) : Subgroup (ModGL τ GGL) :=
  rootSpan τ GGL (rootsOfFam β Set.univ)

theorem rckRet_rootSpan_induction
    {τ : Tag} {R : Type} [Field R] {S : Set (Fin τ.rank → ℤ)}
    {P : ∀ y : ModGL τ R, y ∈ rootSpan τ R S → Prop}
    (hgen : ∀ α ∈ S, ∀ (c : R) (hm : pinnedX τ R α c ∈ rootSpan τ R S),
      P (pinnedX τ R α c) hm)
    (hone : P 1 (one_mem _))
    (hmul : ∀ (y z : ModGL τ R) (hy : y ∈ rootSpan τ R S) (hz : z ∈ rootSpan τ R S),
      P y hy → P z hz → P (y * z) (mul_mem hy hz))
    {x : ModGL τ R} (hx : x ∈ rootSpan τ R S) : P x hx := by
  classical
  refine Subgroup.iSup_induction' (C := fun y hy => P y hy)
    (fun α : Fin τ.rank → ℤ => ⨆ (_ : α ∈ S), rootSubgroup τ R α) ?_ hone
    (fun y z hy hz => hmul y z hy hz) hx
  intro α y hy
  refine Subgroup.iSup_induction' (C := fun y' hy' => P y' (Subgroup.mem_iSup_of_mem α hy'))
    (fun _ : α ∈ S => rootSubgroup τ R α) ?_ hone (fun y' z' hy' hz' => hmul y' z' _ _) hy
  intro hα y' hy'
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy'
  exact hgen α hα c _

@[expose] def RetCompSpec
    {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ)
    (ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL) : Prop :=
  (∀ γ ∈ rootsOfFam β Set.univ, ∀ c : GGL, ∀ hm : pinnedX τ GGL γ c ∈ RetH τ β,
      θ ⟨pinnedX τ GGL γ c, hm⟩ = pinnedX Tag.E6 GGL (ι γ) c) ∧
  θ.range = adjointGroup Tag.E6 GGL ∧
  (∀ x : ↥(RetH τ β), θ x = 1 → x ∈ Subgroup.center ↥(RetH τ β)) ∧
  ∀ K' : Subfield GGL, Finite ↥K' →
    (((rootSpan τ ↥K' (rootsOfFam β Set.univ)).map (baseChangeGL K'.subtype)).subgroupOf
      (RetH τ β)).map θ = (adjointGroup Tag.E6 ↥K').map (baseChangeGL K'.subtype)

end CFSG.StandardType.RCKRP

end

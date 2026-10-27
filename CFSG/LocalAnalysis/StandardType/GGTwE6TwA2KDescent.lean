module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Cover

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly

private theorem ggFixSub_eq_ggFix {X : Type*} [Group X] (a : MulAut X) :
    ggFixSub a = ggFix a :=
  rfl

private theorem subgroupMap_ker_le_center {L' R : Type*} [Group L'] [Group R]
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (J : Subgroup L') :
    (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx1 : ψ (x : L') = 1 := by
    have h := congrArg Subtype.val hx
    simpa using h
  have hxcen : (x : L') ∈ Subgroup.center L' :=
    hker (by rwa [MonoidHom.mem_ker])
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hxcen (y : L')

theorem lift_of_modelRLab {lab : LargeEvenLabel} {P : Prop} {K : Type} [Field K] {m : ℕ}
    (hR : ModelRLab lab P K m) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K m),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 →
          (∃ φ ∈ TwE6Delta.RecipeI K m, ∀ l : L', φ (ψ l) = ψ (e l)) →
            ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) →
                P ∧ ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                  (∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K m, ∀ l : L', φ (ψ l) = ψ (a l)) →
                    Nat.card A ≤ 3 ^ 4 := by
  intro L' _ _ ψ hψ hker hperf e he3 hind J hJ hlab
  obtain ⟨φ, hφI, hφ⟩ := hind
  have hφ3 : φ ^ 3 = 1 := by
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [TypeA.induced_pow ψ hφ 3 l, he3]
    rfl
  have hcomp : CFSG.Assembly.IsComponentOf (J.map ψ) (ggFixSub φ) := by
    have hJ' : CFSG.Assembly.IsComponentOf J (ggFix e) := by
      simpa [ggFixSub_eq_ggFix] using hJ
    simpa [ggFixSub_eq_ggFix] using
      CFSG.StandardType.E6ThreeModel.isComponentOf_map_ggFix_of_central hψ hker hφ hJ'
  have hperfJ : commutator ↥J = ⊤ := hJ.2.2.1
  have hkerJ : (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J :=
    subgroupMap_ker_le_center hker J
  obtain ⟨eQ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperfJ (ψ.subgroupMap J) (MonoidHom.subgroupMap_surjective ψ J) hkerJ
  have hlab' : GGHasLabel lab (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    ggHasLabel_of_mulEquiv eQ hlab
  obtain ⟨hP, hbound⟩ := hR φ hφI hφ3 (J.map ψ) hcomp hlab'
  refine ⟨hP, ?_⟩
  intro A hA heA hAI
  let A' : Subgroup (MulAut (TwE6Delta.RecipeR K m)) := TypeA.inducedSub ψ A
  have hA'abel : IsElemAbelian 3 A' := TypeA.isElemAbelian_inducedSub hψ hA
  have hφA' : φ ∈ A' := TypeA.mem_inducedSub.mpr ⟨e, heA, hφ⟩
  have hA'I : ∀ a' ∈ A', a' ∈ TwE6Delta.RecipeI K m := by
    intro a' ha'
    obtain ⟨a, ha, ha'eq⟩ := TypeA.mem_inducedSub.mp ha'
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    rw [← TypeA.induced_unique ψ hψ hφa ha'eq]
    exact hφaI
  have hcard : Nat.card A' = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (A := A)
      (fun a ha => (hAI a ha).imp (fun φ h => h.2))
  have hbound' := hbound A' hA'abel hφA' hA'I
  rwa [hcard] at hbound'

theorem ggTwE6TwA2CompKnown_of_modelR
    (hM : ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → ModelR K n) :
    GGTwE6TwA2CompKnown := by
  unfold GGTwE6TwA2CompKnown
  intro m _
  exact TwE6Delta.labelAll (lab := ⟨.twE6, 0, m⟩) rfl fun K _ _ hK =>
    lift_of_modelRLab (hM m K hK)

end CFSG.StandardType.TwE6TwA2K

end

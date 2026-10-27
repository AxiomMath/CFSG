module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.Blueprint.NativeSporadic
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

@[expose] def K332Meta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ S : Subgroup G, IsSylowOf 3 S ⊤ → CFSG.Open.pRank 3 S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    ∀ (Q : Type) [Group Q], CFSG.IsMetacyclic Q →
    ∀ φ : ↥S →* Q, Disjoint (Z.subgroupOf S) φ.ker →
      CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1

theorem commute_of_pow_three_of_isMetacyclic {R : Type} [Group R] [Finite R]
    (hR : IsPGroup 3 R) (hmeta : CFSG.IsMetacyclic R) {x y : R} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : Commute x y := by
  by_cases hcyc : IsCyclic R
  · letI := hcyc.commGroup
    exact mul_comm x y
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Fact (IsPGroup 3 R) := ⟨hR⟩
    have hel := (CFSG.lemma_4_10 (R := R) (p := 3) (by norm_num) hmeta hcyc).2
    have hxO : x ∈ CFSG.omega₁ (G := R) (p := 3) := Subgroup.subset_closure (by simpa using hx)
    have hyO : y ∈ CFSG.omega₁ (G := R) (p := 3) := Subgroup.subset_closure (by simpa using hy)
    have hc := hel.toIsMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hxO⟩ ⟨y, hyO⟩)

@[expose] def SylowCenterLeOmegaComm (X : Type) [Group X] : Prop :=
  ∀ T : Sylow 3 X, ∀ x ∈ Subgroup.center ↥(T : Subgroup X), x ^ 3 = 1 →
    x ∈ ⁅CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3),
      CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3)⁆

@[expose] def K332ExclusionMeta : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ∀ S : Subgroup G, IsSylowOf 3 S ⊤ →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    ∀ (Q : Type) [Group Q], CFSG.IsMetacyclic Q →
    ∀ φ : ↥S →* Q, Disjoint (Z.subgroupOf S) φ.ker →
      ¬ CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime (Subgroup.normalClosure (Z : Set G)) ∧
        ¬ Nonempty (Subgroup.normalClosure (Z : Set G) ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

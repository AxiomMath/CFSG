module

public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem le_k_of_ker (hKer : Step142PGLKer) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), V ≤ k142 A (lB A) c := by
  intro V hV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  obtain ⟨π, p, f, K, _, hK', hq, hq2, ψ, hAI⟩ := Item148PtRes2.exists_inndiag_model h hPGL hx
  have hVc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hV
  have hV3 : ¬ 3 ∣ Nat.card V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 a a.2)⟩
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A V hA3 hV3 hV.2.2, hK]
  refine sup_le ?_ ((inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian h) hV3).trans
    le_sup_right)
  refine (Item148PtRes2.commutator_le_of_inndiag hKer h hPGL hK' hq hq2 ψ hAI hVc hV3
    hV.2.2).trans ?_
  exact sup_le (le_sup_left.trans le_sup_left)
    ((Item148PtRes2.pPrimeCoreOf_centralizer_le c).trans (le_sup_right.trans le_sup_left))

end CFSG.RankThree.PartTwo.Sec14.L3PGL

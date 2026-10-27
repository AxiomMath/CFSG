module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesLe
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesCent
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofTypesL3
public import CFSG.RankThree.PartTwo.Sec14.Item14Res3ProofPGL
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step142TypesL3PGLPow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
      (¬ ∃ (p : ℕ) (_ : Fact p.Prime),
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1) →
      (¬ ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
        ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

theorem step142TypesL3PGL_of_ker
    (hKer : Step142PGLKer) (hPow : Step142TypesL3PGLPow) :
    Step142TypesL3PGL := by
  intro G _ _ A c L h Q hQ hK hL3 hPGL hQ8 hx
  have hD := h.toSec13Data
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  by_cases hcent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L
  · have d : L3PGL.Base142 A c L := ⟨h, hK, hcent, L3PGL.le_k_of_ker hKer h hK hPGL hx⟩
    obtain ⟨hlist, hC⟩ := L3PGL.list_bar h hPGL hx
    exact d.typesOne_of_list hQ hlist hC
  · refine hPow G A c L h Q hQ hK hL3 hPGL hQ8 hx ?_ hcent
    rintro ⟨p, _, hiso⟩
    exact hcent (L3PGL.cent_of_isoPrime h hPGL hx hiso)

theorem step142TypesL3PGL_of
    (hPow : Step142TypesL3PGLPow) :
    Step142TypesL3PGL :=
  step142TypesL3PGL_of_ker (step142PGLKer_of_res3 KFacts.kpSz) hPow

end CFSG.RankThree.PartTwo.Sec14

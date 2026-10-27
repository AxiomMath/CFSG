module

public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Base
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG.Blueprint.Chevalley CFSG.Open

theorem nonempty_adjointGroup_g2_mulEquiv_quasithinG2_charTwo
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nonempty (adjointGroup .G2 K ≃* quasithinG2 K) := by
  haveI := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  by_cases hf : (f : ℕ) = 1
  · exact CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2
      (by rw [hK, hf, pow_one])
  · obtain ⟨ψ, -, hsurj, hker⟩ :=
      CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hK (by have := f.pos; omega)
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, CFSG.LieType.Chevalley.center_adjointGroup_eq_bot]
    exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).trans
      (MulEquiv.subgroupCongr (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).symm)⟩

@[expose] def QuasithinThreeCentTwoExp : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    ∀ z : quasithinG2 K, z ^ 3 = 1 → z ≠ 1 →
      ∀ y : quasithinG2 K, y * z = z * y → (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 4 = 1

@[expose] def G2ThreeCentTwoExp :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → 3 ∣ Nat.card K + 1 →
    ∀ z : adjointGroup .G2 K, z ^ 3 = 1 → z ≠ 1 →
      ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 4 = 1

theorem g2ThreeCentTwoExp_of_quasithin
    (h7 : QuasithinThreeCentTwoExp) : G2ThreeCentTwoExp := by
  intro K _ _ hK hK3 z hz3 hz1 y hy hy2
  haveI : CharP K 2 := ringChar.of_eq hK
  obtain ⟨e⟩ := nonempty_adjointGroup_g2_mulEquiv_quasithinG2_charTwo K
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have h := h7 K hK3 (e z) (by rw [← map_pow, hz3, map_one])
    (fun h => hz1 (e.injective (h.trans (map_one e).symm))) (e y)
    (by rw [← map_mul, ← map_mul, hyz])
    (by obtain ⟨k, hk⟩ := hy2; exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
  rw [← map_pow] at h
  exact e.injective (h.trans (map_one e).symm)

end CFSG.RankThree.PartTwo.Sec8.Hering88N

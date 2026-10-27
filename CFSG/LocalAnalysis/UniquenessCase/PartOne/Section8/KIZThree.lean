module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutoX
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZDihedral
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SOdd
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

open Subgroup
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
open CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

variable {X : Type} [Group X] [Finite X]

private theorem le_of_not_dvd_index [Fact (Nat.Prime 3)] {K : Subgroup X} [K.Normal]
    (P : Sylow 3 X) (h : ¬ 3 ∣ K.index) : (P : Subgroup X) ≤ K := by
  rw [Subgroup.index_eq_card] at h
  exact CFSG.RankThree.PartOne.CTP.le_of_isPGroup_of_not_dvd_card_quotient
    P.isPGroup' h

private theorem eq_one_of_le_of_elemAbelian [Fact (Nat.Prime 3)] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup ↥K] (hKnab : ∃ a b : ↥K, a * b ≠ b * a) (P : Sylow 3 X)
    (hPK : (P : Subgroup X) ≤ K) (hEA : CFSG.Open.IsElemAbelian 3 (P ⊓ K)) {x : X}
    (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  refine eq_one_of_le_of_commute hKnab P hPK ?_ hxP hx
  intro a ha b hb
  exact congrArg Subtype.val (hEA.1.is_comm.comm
    ⟨a, ⟨ha, hPK ha⟩⟩ ⟨b, ⟨hb, hPK hb⟩⟩)

private theorem not_dvd_index_of_eq_two_pow {K : Subgroup X} {k : ℕ}
    (h : K.index = 2 ^ k) : ¬ 3 ∣ K.index := by
  rw [h]
  intro hd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  exact absurd h32 (by norm_num)

theorem eq_one_of_three_of_gls3
    (hG3 : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeSylowCenterTorus) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) (P : Sylow 3 X) {x : X}
    (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P₀, hP₀syl, hP₀N⟩ := hN.exists_isSylowOf_le
  have hP₀index : ¬ 3 ∣ P₀.index := by
    have := hP₀syl.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let R : Sylow 3 X := hP₀syl.2.1.toSylow hP₀index
  have hRcoe : (R : Subgroup X) = P₀ := IsPGroup.toSylow_coe hP₀syl.2.1 hP₀index
  have hmain : ∀ (P₀ : Sylow 3 X), (P₀ : Subgroup X) ≤ N → ∀ y ∈ (P₀ : Subgroup X),
      (∀ n ∈ normalizer ((P₀ : Subgroup X) : Set X), y * n = n * y) → y = 1 := by
    intro P₀ hP₀N y hyP₀ hy
    let K : Subgroup X := CFSG.generalizedFitting X
    obtain ⟨hKs, hKnab, hKn, hKC⟩ :=
      CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 3) (by norm_num) hO hN
    haveI : K.Normal := hKn
    haveI : IsSimpleGroup ↥K := hKs
    have hrk : 2 ≤ CFSG.Open.pRank 3 (P₀ : Subgroup X) := by
      rw [(CFSG.SectionRank.pRank_sylow P₀).1]
      exact h2
    have hΓ : gammaCore 3 1 ⊤ (P₀ : Subgroup X) < ⊤ := by
      have hle : gammaCore 3 1 ⊤ (P₀ : Subgroup X) ≤ N ⊓ ⊤ :=
        gammaCore_le_inf (glb_of_spe hN) hP₀N ⊤ (P₀ : Subgroup X) le_rfl
      exact lt_of_le_of_lt hle (by simpa using (lt_top_iff_ne_top.mpr hN.1 : N < ⊤))
    have hrows := (hG3 X hX K hKn hKs hKnab hKC P₀ hrk hΓ).2.2
    rcases hrows with
      ⟨_, _, _, hind, _, _, hEA, _⟩ |
      ⟨q, hq, hIso, hind, _, _, _, _, _, _, _, _⟩ |
      ⟨m, hIso, hind, _, _, _, _, _, _⟩ |
      ⟨_, hKi, hQc, hQ9, hΓeq, hD, hP27, hPnab⟩ |
      ⟨_, hind, hEA, _, _, _, _, _, _⟩ |
      ⟨_, ⟨k, hk⟩, _, hEA, _, _, _, _, _, _, _, _⟩ |
      ⟨_, hKtop, hEA, _, _, _, _, _, _, _, _, _⟩
    ·
      exact eq_one_of_le_of_elemAbelian hKnab P₀ (le_of_not_dvd_index P₀ hind) hEA hyP₀ hy
    ·
      have hPK : (P₀ : Subgroup X) ≤ K := le_of_not_dvd_index P₀ hind
      obtain ⟨hv, ⟨e⟩⟩ := hIso
      let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA 2 q, hv⟩
      have hU : CFSG.AGLEmbedding.IsUnitaryIndex 3 d := ⟨q, hq, rfl⟩
      obtain ⟨ψ, hψ, hψr, htor⟩ :=
        CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus ↥K 3 d hU ⟨e⟩ (P₀.subtype hPK)
      have htor' : ∀ μ : (GaloisField 3 d.1.fieldExponent)ˣ,
          ∃ c ∈ normalizer (((P₀.subtype hPK : Sylow 3 ↥K) : Subgroup ↥K) : Set ↥K),
          ∀ a : Multiplicative (GaloisField 3 d.1.fieldExponent),
            c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd
              ((μ : GaloisField 3 d.1.fieldExponent) ^ 1 * Multiplicative.toAdd a)) := by
        intro μ
        simpa using htor μ
      refine eq_one_of_torus (p := 3) (e := 1)
        (F := GaloisField 3 d.1.fieldExponent) P₀ hPK ψ hψ hψr htor' ?_ hyP₀ hy
      refine ⟨-1, ?_⟩
      have hchar : ringChar (GaloisField 3 d.1.fieldExponent) ≠ 2 := by
        rw [ringChar.eq (GaloisField 3 d.1.fieldExponent) 3]
        norm_num
      simpa using Ring.neg_one_ne_one_of_char_ne_two hchar
    ·
      have hPK : (P₀ : Subgroup X) ≤ K := le_of_not_dvd_index P₀ hind
      obtain ⟨hv, ⟨e⟩⟩ := hIso
      let d : TauCeti.ValidLieTypeIndex := ⟨.reeG2 m, hv⟩
      have hd : CFSG.AGLEmbedding.IsReeGTwoIndex 3 d := ⟨rfl, m, rfl⟩
      obtain ⟨ψ, hψ, hψr, htor⟩ := hRee ↥K d hd ⟨e⟩ (P₀.subtype hPK)
      have htor' : ∀ μ : (GaloisField 3 d.1.fieldExponent)ˣ,
          ∃ c ∈ normalizer (((P₀.subtype hPK : Sylow 3 ↥K) : Subgroup ↥K) : Set ↥K),
          ∀ a : Multiplicative (GaloisField 3 d.1.fieldExponent),
            c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd
              ((μ : GaloisField 3 d.1.fieldExponent) ^ 1 * Multiplicative.toAdd a)) := by
        intro μ
        simpa using htor μ
      refine eq_one_of_torus (p := 3) (e := 1)
        (F := GaloisField 3 d.1.fieldExponent) P₀ hPK ψ hψ hψr htor' ?_ hyP₀ hy
      refine ⟨-1, ?_⟩
      have hchar : ringChar (GaloisField 3 d.1.fieldExponent) ≠ 2 := by
        rw [ringChar.eq (GaloisField 3 d.1.fieldExponent) 3]
        norm_num
      simpa using Ring.neg_one_ne_one_of_char_ne_two hchar
    ·
      have hD' : Nonempty (↥(K ⊓ normalizer ((((P₀ : Subgroup X) ⊓ K : Subgroup X)) : Set X)) ≃*
          DihedralGroup 9) := by
        rw [← hΓeq]
        exact hD
      exact eq_one_of_dihedral_eighteen hKi P₀ hQc hQ9 hD' hP27 hPnab hyP₀ hy
    ·
      exact eq_one_of_le_of_elemAbelian hKnab P₀ (le_of_not_dvd_index P₀ hind) hEA hyP₀ hy
    ·
      have hind : ¬ 3 ∣ K.index := not_dvd_index_of_eq_two_pow hk
      exact eq_one_of_le_of_elemAbelian hKnab P₀ (le_of_not_dvd_index P₀ hind) hEA hyP₀ hy
    ·
      have hPK : (P₀ : Subgroup X) ≤ K := by rw [hKtop]; exact le_top
      exact eq_one_of_le_of_elemAbelian hKnab P₀ hPK hEA hyP₀ hy
  exact eq_one_of_forall_sylow_le (N := N) ⟨R, by rw [hRcoe]; exact hP₀N⟩ hmain P hxP hx

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

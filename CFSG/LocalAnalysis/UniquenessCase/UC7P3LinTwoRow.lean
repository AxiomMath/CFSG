module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Basic
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3ConclusionPlus Gls3StronglyThreeEmbeddedPlus)

theorem exists_isoLie_A1_of_gls3ConclusionPlus {X : Type} [Group X] [Finite X]
    {K P : Subgroup X} [K.Normal] (h : Gls3ConclusionPlus X K P) {p : ℕ} (hp3 : p = 3)
    (hP : IsPGroup p P) (hr : 3 ≤ CFSG.Open.pRank p P) (hR : ∀ m : ℕ, ¬ IsoLie ↥K (.reeG2 m))
    (hU : ∀ q : TauCeti.PrimePower, q.p = 3 → IsoLie ↥K (.twistedA 2 q) → q.exponent = 1) :
    ∃ q : TauCeti.PrimePower, q.p = 3 ∧ IsoLie ↥K (.A 1 q) ∧ P ≤ K ∧
      CFSG.Open.IsElemAbelian 3 P ∧ Nat.card ↥P = q.card := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) P
  have hE27 : 27 ≤ Nat.card ↥E := by
    rw [hEcard]
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 P := Nat.pow_le_pow_right (by norm_num) hr
  have h27 : 27 ≤ Nat.card ↥P := hE27.trans (Subgroup.card_le_of_le hEP)
  have hcomm : Nat.card ↥P ≤ 27 → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro hc a ha b hb
    have hEq : E = P := Subgroup.eq_of_le_of_card_ge hEP (by omega)
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, hEq ▸ ha⟩ ⟨b, hEq ▸ hb⟩)
  have hPK : ¬ 3 ∣ K.index → P ≤ K :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1810_le_of_not_dvd_index hP
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨q, hq3, hI, hidx, -, -, hEl, hcard⟩ | ⟨q, hq3, hI, hidx, -, -, hnab, hcard, -⟩ |
      ⟨m, hI, -⟩ | ⟨-, -, -, -, -, -, hP27, hnab⟩ | ⟨-, hidx, -, h9, -⟩ |
      ⟨-, ⟨j, hidx⟩, -, -, h9, -⟩ | ⟨-, hK, -, h9, -⟩
  · rw [inf_of_le_left (hPK hidx)] at hEl hcard
    exact ⟨q, hq3, hI, hPK hidx, hEl, hcard⟩
  · rw [inf_of_le_left (hPK hidx)] at hnab hcard
    rw [q.card_def, hq3, hU q hq3 hI] at hcard
    exact absurd (hcomm (by rw [hcard]; norm_num)) hnab
  · exact absurd hI (hR m)
  · exact absurd (hcomm hP27.le) hnab
  · rw [inf_of_le_left (hPK hidx)] at h9
    omega
  · have h3 : ¬ 3 ∣ K.index := by
      rw [hidx]
      exact fun hd => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
    rw [inf_of_le_left (hPK h3)] at h9
    omega
  · rw [hK, inf_top_eq] at h9
    omega

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem exists_isoLie_A1_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Config k H) (h3 : 3 ≤ CFSG.Open.pRank k.p (H ⊓ k.M))
    (P : Sylow k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
    (hPN : (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :
    ∃ q : TauCeti.PrimePower, q.p = 3 ∧
      IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) (.A 1 q) ∧
      (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
        CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ∧
      CFSG.Open.IsElemAbelian 3 (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      Nat.card ↥(P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) = q.card ∧
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
          CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) =
        CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ⊓
          normalizer ((P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
            Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
        normalizer ((P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
          Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨h, hR, hU⟩ := k.rows3_of_config hG3 hRee hp3 hH P
  obtain ⟨hNK, hNP⟩ := k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P hPN
  obtain ⟨-, -, hKn, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar k.prime
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH)
  haveI := hKn
  have hr : 3 ≤ CFSG.Open.pRank k.p (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1, CFSG.SectionRank.pRank_quotient_eq _
      ((k.prime.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (p := k.p) (G := ↥H))),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact h3.trans (CFSG.SectionRank.pRank_mono k.prime.one_lt inf_le_left)
  obtain ⟨q, hq3, hI, hPK, hEl, hcard⟩ :=
    exists_isoLie_A1_of_gls3ConclusionPlus h hp3 P.isPGroup' hr hR hU
  rw [inf_of_le_left hPK] at hNK hNP
  exact ⟨q, hq3, hI, hPK, hEl, hcard, hNK, hNP⟩

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

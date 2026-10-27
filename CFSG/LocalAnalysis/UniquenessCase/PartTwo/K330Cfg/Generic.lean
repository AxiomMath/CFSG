module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

theorem sup_normalizer_eq_top (h : OneComp J M X P) : J ⊔ normalizer (X : Set K) = ⊤ := by
  haveI := h.normal
  obtain ⟨Q, hQ⟩ := h.sylow
  haveI : Finite (Sylow 3 ↥J) := Sylow.finite_of_finiteIndex Q
  have hfr := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfr
  rwa [sup_comm] at hfr

theorem not_le (h : OneComp J M X P) : ¬ J ≤ M := by
  intro hJM
  apply h.strong.1
  rw [eq_top_iff, ← h.sup_normalizer_eq_top]
  exact sup_le hJM h.normalizer_le

theorem normalizer_le_of_seven (h : OneComp J M X P) {R : Subgroup K} (hR : R ≤ M)
    (h7 : 7 ∣ Nat.card R) : normalizer (R : Set K) ≤ M := by
  intro g hg
  by_contra hgM
  refine h.strong.2.2 g hgM (dvd_trans h7 (Subgroup.card_dvd_of_le ?_))
  refine le_inf hR ?_
  intro x hx
  have hmem := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
    (by simpa [mul_assoc] using hx)
  exact ⟨g⁻¹ * x * g, hR hmem, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem isSylowOf_seven_top (h : OneComp J M X P) : IsSylowOf 7 P ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hPM : P ≤ M := h.sylowSeven.le
  have h7P : 7 ∣ Nat.card P := by
    rw [h.sylowSeven.card_eq]
    exact dvd_pow_self 7 (Nat.Prime.factorization_pos_of_dvd Nat.prime_seven
      Nat.card_pos.ne' h.strong.2.1).ne'
  obtain ⟨S, hPS⟩ := h.sylowSeven.isPGroup.exists_le_sylow
  have hSP : (S : Subgroup K) = P := by
    have hSg : IsPGroup 7 (S : Subgroup K) := S.isPGroup'
    haveI : Group.IsNilpotent ↥(S : Subgroup K) := IsPGroup.isNilpotent hSg
    have hnc : NormalizerCondition ↥(S : Subgroup K) :=
      Group.normalizerCondition_of_isNilpotent
    have hHtop : P.subgroupOf (S : Subgroup K) = ⊤ := by
      apply (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc)
      refine le_antisymm ?_ le_normalizer
      intro s hs
      by_contra hsp
      have hnorm : (s : K) ∈ normalizer (P : Set K) := by
        have hmap := Subgroup.le_normalizer_map (H := P.subgroupOf (S : Subgroup K))
          (S : Subgroup K).subtype
        have hmem : (s : K) ∈ normalizer ((P.subgroupOf (S : Subgroup K)).map
            (S : Subgroup K).subtype) :=
          hmap (Subgroup.mem_map_of_mem (S : Subgroup K).subtype hs)
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPS] at hmem
      have hsM : (s : K) ∈ M := h.normalizer_le_of_seven hPM h7P hnorm
      have hzple : Subgroup.zpowers (s : K) ≤ M := Subgroup.zpowers_le.mpr hsM
      have hzpleS : Subgroup.zpowers (s : K) ≤ (S : Subgroup K) :=
        Subgroup.zpowers_le.mpr s.2
      have hQp : IsPGroup 7 ↥(P ⊔ Subgroup.zpowers (s : K)) :=
        hSg.to_le (sup_le hPS hzpleS)
      have hQeq : P ⊔ Subgroup.zpowers (s : K) = P :=
        IsSylowOf.eq_of_le h.sylowSeven le_sup_left (sup_le hPM hzple) hQp
      have hsP : (s : K) ∈ P := by
        have : (s : K) ∈ P ⊔ Subgroup.zpowers (s : K) :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers (s : K))
        rwa [hQeq] at this
      exact hsp (Subgroup.mem_subgroupOf.mpr hsP)
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp hHtop) hPS
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [Subgroup.card_top, ← hSP]
  simpa using S.card_eq_multiplicity

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

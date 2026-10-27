module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Setup
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2
import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit
import CFSG.GroupTheory.ConjNormalFaithful
import CFSG.GroupTheory.PSubgroupLeOfPrimeNotDvdIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

private theorem absKN_of_mulEquiv_psl {L A : Subgroup X} (e : ↥L ≃* PSL(2, GaloisField 3 3))
    (hAL : A ≤ L) (hA27 : Nat.card A = 27) :
    UC6.AbsKN ↥L 3 (A.subgroupOf L) False := by
  have hA'card : Nat.card ↥(A.subgroupOf L) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA27]
    norm_num
  have hEcard : Nat.card ↥((A.subgroupOf L).map e.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA'card]
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEcard).exists_le_sylow
  obtain ⟨-, hScard⟩ := UC6.isElemAbelian_card_sylow_psl2 (F := GaloisField 3 3) (r := 3) (n := 3)
    (by norm_num) (GaloisField.card 3 3 (by norm_num)) (by norm_num) S
  have hEeq : (A.subgroupOf L).map e.toMonoidHom = (S : Subgroup (PSL(2, GaloisField 3 3))) :=
    Subgroup.eq_of_le_of_card_ge hES (by rw [hScard, hEcard])
  have hEsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((A.subgroupOf L).map e.toMonoidHom) ⊤ := by
    rw [hEeq, CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by simpa using S.not_dvd_index⟩
  exact UC6.AbsKN.of_iso_sylow (E := A.subgroupOf L) e hEsyl hEsyl
    (hEeq ▸ UC6.absKN_psl2 (F := GaloisField 3 3) (r := 3) (n := 3) (by norm_num)
      (GaloisField.card 3 3 (by norm_num)) (by norm_num) S False)

theorem eq_bot_of_mulEquiv_psl {L A W : Subgroup X} (hLn : L.Normal)
    (e : ↥L ≃* PSL(2, GaloisField 3 3)) (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hAL : A ≤ L) (hA27 : Nat.card A = 27) (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) : W = ⊥ := by
  haveI := hLn
  set ψ : X →* MulAut ↥L := MulAut.conjNormal with hψ
  have hinj : Function.Injective ψ := by
    rw [hψ]
    refine Subgroup.conjNormal_injective_of_centralizer_le (by rw [hC]; exact bot_le) ?_
    have h := Subgroup.map_center_eq e
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot] at h
    rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff _).mpr e.injective] at h
    exact le_bot_iff.mp h
  have h1 : ∀ ε ∈ A.subgroupOf L, ∀ x ∈ W.map ψ,
      MulAut.conj ε * x * (MulAut.conj ε)⁻¹ ∈ W.map ψ := by
    intro ε hε x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hc : MulAut.conj ε = ψ (ε : X) := (MulAut.conjNormal_val (h := ε)).symm
    have haw : (ε : X) * w * (ε : X)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hW hε) w).mp hw
    have hconj : MulAut.conj ε * ψ w * (MulAut.conj ε)⁻¹ = ψ ((ε : X) * w * (ε : X)⁻¹) := by
      rw [hc, ← map_inv, ← map_mul, ← map_mul]
    rw [hconj]
    exact Subgroup.mem_map_of_mem ψ haw
  have h2 : ∀ x ∈ W.map ψ, (∃ k : ℕ, orderOf x = 3 ^ k) → x = 1 := by
    intro x hx hord
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := hord
    have hdvd : 3 ^ k ∣ Nat.card W := by
      rw [← hk]
      exact (orderOf_map_dvd ψ w).trans (Subgroup.orderOf_dvd_natCard W hw)
    have h3W : ¬ 3 ∣ Nat.card W :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop.symm
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · exact absurd ((dvd_pow_self 3 (ne_of_gt h)).trans hdvd) h3W
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  obtain ⟨-, hdisj⟩ := absKN_of_mulEquiv_psl e hAL hA27 (W.map ψ) h1 h2
  have hbot : W.map ψ = ⊥ := hdisj.resolve_right fun hf => hf
  rw [Subgroup.map_eq_bot_iff, (MonoidHom.ker_eq_bot_iff ψ).mpr hinj] at hbot
  exact le_bot_iff.mp hbot

theorem nonempty_mulEquiv_psl_of_le_of_not_le (h717 : RankThreeUC.AGL81C.SevenOneSeven)
    {P A L : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hL : CFSG.IsComponent L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hAL : A ≤ L) (hPL : ¬ P ≤ L) :
    Nonempty (↥L ≃* PSL(2, GaloisField 3 3)) := by
  have hLn : L.Normal := CFSG.GH74.Generic.BProg.B3.S1Three.normal_of_centralizer_le (z := 1) hL
    fun w hw => by
      rw [hC] at hw
      exact Or.inl (Subgroup.mem_bot.mp hw)
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 := by
    obtain ⟨-, hPgrp, hPidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hX.sylow
    have hPsyl : CFSG.Open.pRank 3 P = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      (CFSG.SectionRank.pRank_sylow
        (hPgrp.toSylow (by rwa [Subgroup.relIndex_top_right] at hPidx))).1
    obtain ⟨eZ⟩ := hPZ
    rw [← hPsyl, CFSG.SectionRank.pRank_eq_pRank_top_subgroup P]
    exact UC22.InS3.UC326.zwr_pRank (n := 1) (by norm_num) eZ
  have hL3 : CFSG.Open.pRank 3 L = 3 := by
    refine le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans_eq hX3) ?_
    exact CFSG.SectionRank.le_pRank (by norm_num) hAL hX.elem (k := 3) (by rw [hX.card]; norm_num)
  have h3idx : 3 ∣ (L ⊔ Subgroup.centralizer (L : Set X)).index := by
    rw [hC, sup_bot_eq]
    by_contra h
    exact hPL (CFSG.pSubgroup_le_of_not_dvd_index Nat.prime_three hLn h hX.sylow.isPGroup)
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzC : (z : X) ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩)
    rw [hC, Subgroup.mem_bot] at hzC
    exact Subtype.ext hzC
  rcases h717 X hX.kgroup L hL hLn hL3 hX3 with h | h
  · exact absurd h3idx h
  · obtain ⟨φ⟩ := h
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ⟩

theorem eq_bot_of_le_of_not_le (h717 : RankThreeUC.AGL81C.SevenOneSeven)
    {P A L : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hL : CFSG.IsComponent L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hAL : A ≤ L) (hPL : ¬ P ≤ L)
    {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) : W = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_of_le_of_not_le h717 hX hPZ hL hC hAL hPL
  exact eq_bot_of_mulEquiv_psl
    (CFSG.GH74.Generic.BProg.B3.S1Three.normal_of_centralizer_le (z := 1) hL fun w hw => by
      rw [hC] at hw
      exact Or.inl (Subgroup.mem_bot.mp hw)) e hC hAL hX.card hW hcop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.BlocksSL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpCover
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Symplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

private theorem isLeviBlock_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hK4 : 4 ≤ Nat.card K) : IsLeviBlock (StatedSp m K) := by
  refine Or.inr (Or.inr ⟨spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4), ?_, ?_⟩)
  · rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.card_bot]
    exact odd_one
  · obtain ⟨f, hf, hKcard⟩ := spFlag_card_eq_two_pow (K := K)
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hKcard]
    refine Dvd.dvd.mul_right ?_ _
    have h2 : (2 ^ f) ∣ (2 ^ f) ^ (m ^ 2) := by
      have h := pow_dvd_pow (2 ^ f) (one_le_pow₀ hm : 1 ≤ m ^ 2)
      rwa [pow_one] at h
    exact (dvd_pow_self 2 (by omega : f ≠ 0)).trans h2

private theorem spFlagLeviBlock_eq_bot_or_isLeviBlock {r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) (hK4 : 4 ≤ Nat.card K) :
    ∀ j, spFlagLeviBlock (K := K) hI t j = ⊥ ∨
      IsLeviBlock ↥(spFlagLeviBlock (K := K) hI t j) := by
  intro j
  by_cases hj0 : (j : ℕ) = 0
  · have h0 := spFlagLeviBlock_of_eq_zero (K := K) (t := t) hI hj0
    rcases Nat.eq_zero_or_pos (r - t) with hm | hm
    · left
      rw [h0]
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have hcomm : commutator (StatedSp (r - t) K) = ⊥ := by
        rw [hm]
        refine le_bot_iff.mp ?_
        intro x _
        exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
      rw [Nat.card_congr (MulEquiv.subgroupCongr h0).symm.toEquiv,
        Nat.card_congr (spFlagLeviBlockZeroEquiv (K := K) hI t hj0).toEquiv,
        hcomm, Subgroup.card_bot]
    · right
      rw [h0]
      have hcomm_top : commutator (StatedSp (r - t) K) = ⊤ :=
        (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1
      have e : StatedSp (r - t) K ≃*
          ↥((commutator (StatedSp (r - t) K)).map
            (spFlagResEmb (r := r) (K := K) t)) :=
        ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcomm_top).symm).trans
          ((spFlagLeviBlockZeroEquiv (K := K) hI t hj0).symm.trans
            (MulEquiv.subgroupCongr h0)))
      exact IsLeviBlock.of_mulEquiv e (isLeviBlock_statedSp hm hK4)
  · by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviBlock_of_mem hI hj0 hj]
      rcases range_toGL_eq_bot_or_isLeviBlock (K := K)
        (m := (j : ℕ) - spFlagPrev I (j : ℕ)) with hbot | hblock
      · left
        rw [MonoidHom.range_comp, hbot, Subgroup.map_bot]
      · right
        rw [MonoidHom.range_comp]
        exact IsLeviBlock.of_mulEquiv
          (Subgroup.equivMapOfInjective
            (Matrix.SpecialLinearGroup.toGL.range :
              Subgroup (GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K))
            (spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ) (hI (j : ℕ) hj))
            (spFlagCutEmb_injective _ _ _)) hblock
    · rw [spFlagLeviBlock_of_not_mem hI hj0 hj]
      exact Or.inl rfl

private theorem spFlagLeviBlock_eq_bot_or_isQuasisimple {r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) (hK4 : 4 ≤ Nat.card K) :
    ∀ j, spFlagLeviBlock (K := K) hI t j = ⊥ ∨
      CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) := by
  intro j
  by_cases hj0 : (j : ℕ) = 0
  · rcases Nat.eq_zero_or_pos (r - t) with hm | hm
    · left
      have h0 := spFlagLeviBlock_of_eq_zero (K := K) (t := t) hI hj0
      rw [h0]
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have hcomm : commutator (StatedSp (r - t) K) = ⊥ := by
        rw [hm]
        refine le_bot_iff.mp ?_
        intro x _
        exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
      rw [Nat.card_congr (MulEquiv.subgroupCongr h0).symm.toEquiv,
        Nat.card_congr (spFlagLeviBlockZeroEquiv (K := K) hI t hj0).toEquiv,
        hcomm, Subgroup.card_bot]
    · right
      have hcomm_top : commutator (StatedSp (r - t) K) = ⊤ :=
        (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1
      have e : ↥(spFlagLeviBlock (K := K) hI t j) ≃* StatedSp (r - t) K :=
        (spFlagLeviBlockZeroEquiv (K := K) hI t hj0).trans
          ((MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv)
      exact CFSG.Open.IsQuasisimple.of_mulEquiv e
        (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4))
  · by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviBlock_of_mem hI hj0 hj]
      rcases range_toGL_eq_bot_or_isQuasisimple (K := K) (by omega : Nat.card K ≠ 2)
        (m := (j : ℕ) - spFlagPrev I (j : ℕ)) with hbot | hq
      · left
        rw [MonoidHom.range_comp, hbot, Subgroup.map_bot]
      · right
        rw [MonoidHom.range_comp]
        exact CFSG.Open.IsQuasisimple.of_mulEquiv
          (Subgroup.equivMapOfInjective
            (Matrix.SpecialLinearGroup.toGL.range :
              Subgroup (GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K))
            (spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ) (hI (j : ℕ) hj))
            (spFlagCutEmb_injective _ _ _)).symm hq
    · rw [spFlagLeviBlock_of_not_mem hI hj0 hj]
      exact Or.inl rfl

private theorem two_le_gap_of_ne_bot {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} {j : Fin (r + 1)}
    (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I)
    (hne : spFlagLeviBlock (K := K) hI t j ≠ ⊥) :
    2 ≤ (j : ℕ) - spFlagPrev I (j : ℕ) := by
  have hmem := spFlagLeviBlock_of_mem (K := K) (t := t) hI hj0 hj
  rw [hmem, MonoidHom.range_comp] at hne
  have hinj : Function.Injective
      (spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ) (hI (j : ℕ) hj)) :=
    spFlagCutEmb_injective _ _ _
  have hbot : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K →*
        GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K).range ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mpr h)
  by_contra hgap
  exact hbot ((range_toGL_eq_bot_iff (K := K) _).mpr (not_lt.mp hgap))

private theorem spFlagLeviBlock_eq_of_ne_bot_of_ne_zero {r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) (hr : r ≤ 3)
    {t : ℕ} {j k : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0) (hk0 : (k : ℕ) ≠ 0)
    (hj : spFlagLeviBlock (K := K) hI t j ≠ ⊥)
    (hk : spFlagLeviBlock (K := K) hI t k ≠ ⊥) : j = k := by
  have hjm : (j : ℕ) ∈ I := by
    by_contra h
    exact hj (spFlagLeviBlock_of_not_mem hI hj0 h)
  have hkm : (k : ℕ) ∈ I := by
    by_contra h
    exact hk (spFlagLeviBlock_of_not_mem hI hk0 h)
  have hj2 : 2 ≤ (j : ℕ) - spFlagPrev I (j : ℕ) :=
    two_le_gap_of_ne_bot hI hj0 hjm hj
  have hk2 : 2 ≤ (k : ℕ) - spFlagPrev I (k : ℕ) :=
    two_le_gap_of_ne_bot hI hk0 hkm hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hkp : (j : ℕ) ≤ spFlagPrev I (k : ℕ) :=
      le_spFlagPrev (b := (k : ℕ)) (c := (j : ℕ)) hjm hlt
    have hkgap : (k : ℕ) - spFlagPrev I (k : ℕ) ≤ (k : ℕ) - (j : ℕ) :=
      Nat.sub_le_sub_left hkp _
    have hjgap : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ (j : ℕ) := Nat.sub_le _ _
    have hj1 : 1 ≤ (j : ℕ) := hI1 _ hjm
    have hkr : (k : ℕ) ≤ r := hI _ hkm
    omega
  · have hjp : (k : ℕ) ≤ spFlagPrev I (j : ℕ) :=
      le_spFlagPrev (b := (j : ℕ)) (c := (k : ℕ)) hkm hlt
    have hjgap : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ (j : ℕ) - (k : ℕ) :=
      Nat.sub_le_sub_left hjp _
    have hkgap : (k : ℕ) - spFlagPrev I (k : ℕ) ≤ (k : ℕ) := Nat.sub_le _ _
    have hk1 : 1 ≤ (k : ℕ) := hI1 _ hkm
    have hjr : (j : ℕ) ≤ r := hI _ hjm
    omega

private theorem card_nontrivial_spFlagLeviBlock_le_two {r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) (hr : r ≤ 3)
    (t : ℕ) :
    Nat.card {j : Fin (r + 1) // spFlagLeviBlock (K := K) hI t j ≠ ⊥} ≤ 2 := by
  let f : {j : Fin (r + 1) // spFlagLeviBlock (K := K) hI t j ≠ ⊥} → Fin 2 :=
    fun x => if (x.1 : ℕ) = 0 then 0 else 1
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx0 : (x.1 : ℕ) = 0
    · by_cases hy0 : (y.1 : ℕ) = 0
      · exact Subtype.ext (Fin.ext (by rw [hx0, hy0]))
      · have hxval : (f x : ℕ) = 0 := by
          dsimp only [f]
          rw [if_pos hx0]
          rfl
        have hyval : (f y : ℕ) = 1 := by
          dsimp only [f]
          rw [if_neg hy0]
          rfl
        have := congrArg Fin.val hxy
        omega
    · by_cases hy0 : (y.1 : ℕ) = 0
      · have hxval : (f x : ℕ) = 1 := by
          dsimp only [f]
          rw [if_neg hx0]
          rfl
        have hyval : (f y : ℕ) = 0 := by
          dsimp only [f]
          rw [if_pos hy0]
          rfl
        have := congrArg Fin.val hxy
        omega
      · exact Subtype.ext
          (spFlagLeviBlock_eq_of_ne_bot_of_ne_zero hI hI1 hr hx0 hy0 x.2 y.2)
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)

private theorem censusAlt_spFlagLeviBlock {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) (t : ℕ)
    (hK4 : 4 ≤ Nat.card K) (hr : r ≤ 3) :
    CensusAlt (spFlagLeviBlock (K := K) hI t) :=
  Or.inl ⟨card_nontrivial_spFlagLeviBlock_le_two hI hI1 hr t,
    spFlagLeviBlock_eq_bot_or_isQuasisimple hI t hK4⟩

private theorem range_spFlagLeviHom_le_pi_topBlocks {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) :
    (spFlagLeviHom (K := K) hI htI).range ≤
      Subgroup.pi Set.univ (spFlagLeviTopBlocks (K := K) hI t) := by
  intro x hx
  rw [Subgroup.mem_pi]
  intro j _
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [spFlagLeviHom, MonoidHom.pi_apply]
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviTopBlocks_zero hI t hj0, spFlagLeviCoord_of_eq_zero hI htI hj0,
      MonoidHom.comp_apply]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviTopBlocks_mem hI t hj0 hj, spFlagLeviCoord_of_mem hI htI hj0 hj,
        MonoidHom.comp_apply]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · rw [spFlagLeviTopBlocks_not_mem hI t hj0 hj, spFlagLeviCoord_of_not_mem hI htI hj0 hj]
      exact one_mem _

private theorem not_two_dvd_relIndex_range_spFlagLeviHom {r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) (hK4 : 4 ≤ Nat.card K) :
    ¬ 2 ∣ (Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI t)).relIndex
      (spFlagLeviHom (K := K) hI htI).range := by
  have hcomm_top : commutator (StatedSp (r - t) K) = ⊤ := by
    rcases Nat.eq_zero_or_pos (r - t) with hm | hm
    · have : Subsingleton (StatedSp (r - t) K) := by rw [hm]; infer_instance
      refine eq_top_iff.mpr ?_
      intro x _
      rw [Subsingleton.elim x 1]
      exact one_mem _
    · exact (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1
  refine not_two_dvd_relIndex_pi (T := spFlagLeviTopBlocks (K := K) hI t) ?_
    (pi_le_range_spFlagLeviHom hI htI hmax) (range_spFlagLeviHom_le_pi_topBlocks hI htI) ?_
  · intro j
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviBlock_of_eq_zero hI hj0, spFlagLeviTopBlocks_zero hI t hj0]
      exact Subgroup.map_le_range _ _
    · by_cases hj : (j : ℕ) ∈ I
      · rw [spFlagLeviBlock_of_mem hI hj0 hj, spFlagLeviTopBlocks_mem hI t hj0 hj,
          MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
      · rw [spFlagLeviBlock_of_not_mem hI hj0 hj, spFlagLeviTopBlocks_not_mem hI t hj0 hj]
  · intro j
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviBlock_of_eq_zero hI hj0, spFlagLeviTopBlocks_zero hI t hj0]
      have hEq : (commutator (StatedSp (r - t) K)).map
          (spFlagResEmb (r := r) (K := K) t) = (spFlagResEmb (r := r) (K := K) t).range := by
        rw [hcomm_top, Subgroup.map_top]
      rw [hEq, Subgroup.relIndex_self]
      norm_num
    · by_cases hj : (j : ℕ) ∈ I
      · rw [spFlagLeviBlock_of_mem hI hj0 hj, spFlagLeviTopBlocks_mem hI t hj0 hj,
          MonoidHom.range_comp,
          ← Subgroup.map_top (spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ)
            (hI (j : ℕ) hj)),
          Subgroup.relIndex_map_map_of_injective _ _ (spFlagCutEmb_injective _ _ _),
          Subgroup.relIndex_top_right]
        exact not_two_dvd_index_range_toGL _
      · rw [spFlagLeviBlock_of_not_mem hI hj0 hj, spFlagLeviTopBlocks_not_mem hI t hj0 hj,
          Subgroup.relIndex_self]
        norm_num

private theorem ne_bot_of_isQuasisimple {X : Type} [Group X] {L : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥L) : L ≠ ⊥ := by
  have : Nontrivial (↥L ⧸ center ↥L) := hq.2.1
  have : Nontrivial ↥L := (QuotientGroup.mk'_surjective (N := center ↥L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

private theorem three_dvd_card_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) : 3 ∣ Nat.card (StatedSp m K) := by
  obtain ⟨f, -, hKcard⟩ := spFlag_card_eq_two_pow (K := K)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hKcard]
  have hmem : 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have h3 : 3 ∣ (2 ^ f) ^ (2 * 1) - 1 := by
    have h4 : 3 ∣ 4 ^ f - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
    have hpow : (2 ^ f) ^ (2 * 1) = 4 ^ f := by
      rw [mul_one, ← pow_mul]
      rw [show f * 2 = 2 * f by omega, pow_mul]
      norm_num
    rwa [hpow]
  have hdiv : (2 ^ f) ^ (2 * 1) - 1 ∣
      ∏ j ∈ Finset.Icc 1 m, ((2 ^ f) ^ (2 * j) - 1) :=
    Finset.dvd_prod_of_mem (fun j => (2 ^ f) ^ (2 * j) - 1) hmem
  exact dvd_mul_of_dvd_right (h3.trans hdiv) ((2 ^ f) ^ m ^ 2)

private theorem blockFacts_spFlagLeviBlock {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) (t : ℕ)
    (hK4 : 4 ≤ Nat.card K) (hr : r ≤ 3) :
    BlockFacts False False (spFlagLeviBlock (K := K) hI t) := by
  refine ⟨?_, ?_, Or.inl (card_nontrivial_spFlagLeviBlock_le_two hI hI1 hr t)⟩
  · intro j hq
    by_cases hj0 : (j : ℕ) = 0
    · have hne : spFlagLeviBlock (K := K) hI t j ≠ ⊥ := ne_bot_of_isQuasisimple hq
      have hm : 1 ≤ r - t := by
        rcases Nat.eq_zero_or_pos (r - t) with h0 | h0
        · exfalso
          apply hne
          rw [spFlagLeviBlock_of_eq_zero (K := K) (t := t) hI hj0]
          have : Subsingleton (StatedSp (r - t) K) := by
            rw [h0]
            infer_instance
          have hcomm : commutator (StatedSp (r - t) K) = ⊥ :=
            Subgroup.eq_bot_of_subsingleton _
          rw [hcomm, Subgroup.map_bot]
        · exact h0
      have hcomm_top : commutator (StatedSp (r - t) K) = ⊤ :=
        (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1
      let e : ↥(spFlagLeviBlock (K := K) hI t j) ≃* StatedSp (r - t) K :=
        (spFlagLeviBlockZeroEquiv (K := K) hI t hj0).trans
          ((MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv)
      have hZ : Subgroup.center (StatedSp (r - t) K) = ⊥ := by
        rw [CFSG.LieType.Universal.Symplectic.center_eq,
          CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
      have hcard : Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
          center ↥(spFlagLeviBlock (K := K) hI t j)) = Nat.card (StatedSp (r - t) K) :=
        (spFlag_card_center_congr e).trans (by
          rw [hZ]
          exact Nat.card_congr QuotientGroup.quotientBot.toEquiv)
      rw [hcard]
      exact three_dvd_card_statedSp hm
    · by_cases hj : (j : ℕ) ∈ I
      · have hne : spFlagLeviBlock (K := K) hI t j ≠ ⊥ := ne_bot_of_isQuasisimple hq
        have hgap : 2 ≤ (j : ℕ) - spFlagPrev I (j : ℕ) :=
          two_le_gap_of_ne_bot hI hj0 hj hne
        rw [spFlagLeviBlock_of_mem (K := K) (t := t) hI hj0 hj]
        let S : Subgroup (GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K) :=
          (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K →*
              GL (Fin ((j : ℕ) - spFlagPrev I (j : ℕ))) K).range
        have e : ↥S ≃* ↥(((spFlagCutEmb (K := K) (spFlagPrev I (j : ℕ)) (j : ℕ)
            (hI (j : ℕ) hj)).comp Matrix.SpecialLinearGroup.toGL).range) := by
          rw [MonoidHom.range_comp]
          exact Subgroup.equivMapOfInjective S _ (spFlagCutEmb_injective _ _ _)
        rw [spFlag_card_center_congr e.symm]
        exact three_dvd_card_quotient_center_range_toGL (K := K) hgap
      · exfalso
        exact (ne_bot_of_isQuasisimple hq)
          (spFlagLeviBlock_of_not_mem (K := K) (t := t) hI hj0 hj)
  · intro j h3
    exact not_nonempty_mulEquiv_perm_three
      (spFlagLeviBlock_eq_bot_or_isQuasisimple hI t hK4 j) h3

theorem hasLeviDataX_of_psp {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : CFSG.Blueprint.LieModel S .PSp n 2 f) (hn : n ≤ 3) (hf : 2 ≤ f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX False False ↥J := by
  have hn2 : 2 ≤ n := by
    have hadm := h.admissible
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    exact hadm.2.2.1
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eS⟩⟩ := h.statedClassicalModel_of_ne_zero hn0
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let φ : ↥(⊤ : Subgroup S) ≃* StatedSp n K :=
    Subgroup.topEquiv.trans (eS.trans (spFlagProjEquiv n K))
  obtain ⟨ρ, I, t, hI, htI, hmax, hcomap⟩ :=
    exists_flagStabilizer_of_isParabolicTwo (r := n) (K := K)
      (isParabolicTwo_top_of_isNontrivialParabolic hJ) hJ.2.1 φ
  have hI' : ∀ i ∈ I, i ≤ n := fun i hi => (hI i hi).2
  have hI1 : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  classical
  let Sblk : Fin (n + 1) → Subgroup (StatedSp n K) := spFlagLeviBlock (K := K) hI' t
  let β : ↥((J.subgroupOf ⊤).comap ρ.toMonoidHom) →* (Fin (n + 1) → StatedSp n K) :=
    (spFlagLeviHom (K := K) hI' htI).comp (MulEquiv.subgroupCongr hcomap).toMonoidHom
  have hrange : β.range = (spFlagLeviHom (K := K) hI' htI).range := by
    dsimp only [β]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hcomap).surjective, Subgroup.map_top]
  have hβ : IsPGroup 2 β.ker := by
    have hker_eq : β.ker = Subgroup.comap (MulEquiv.subgroupCongr hcomap).toMonoidHom
        (spFlagLeviHom (K := K) hI' htI).ker := rfl
    rw [hker_eq]
    exact IsPGroup.comap_of_injective (p := 2)
      (isPGroup_ker_spFlagLeviHom hI' htI hI1)
      (MulEquiv.subgroupCongr hcomap).toMonoidHom (MulEquiv.injective _)
  have hle : Subgroup.pi Set.univ Sblk ≤ β.range := by
    rw [hrange]
    exact pi_le_range_spFlagLeviHom hI' htI hmax
  have hn' : β.range ≤ normalizer (Subgroup.pi Set.univ Sblk :
      Set (Fin (n + 1) → StatedSp n K)) := by
    refine le_normalizer_of_commutator_le hle ?_
    rw [hrange]
    exact commutator_range_spFlagLeviHom_le hI' htI
  have hi : ¬ 2 ∣ (Subgroup.pi Set.univ Sblk).relIndex β.range := by
    rw [hrange]
    exact not_two_dvd_relIndex_range_spFlagLeviHom hI' htI hmax hK4
  have hblock : ∀ j, Sblk j = ⊥ ∨ IsLeviBlock ↥(Sblk j) :=
    spFlagLeviBlock_eq_bot_or_isLeviBlock hI' t hK4
  have halt : CensusAlt Sblk := censusAlt_spFlagLeviBlock hI' hI1 t hK4 hn
  have hB : BlockFacts False False Sblk := blockFacts_spFlagLeviBlock hI' hI1 t hK4 hn
  exact hasLeviDataX_of_mulEquiv le_top ρ (β := β) hβ hle hn' hi hblock halt hB

theorem hasLeviData_of_psp {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : CFSG.Blueprint.LieModel S .PSp n 2 f) (hn : n ≤ 3) (hf : 2 ≤ f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_psp h hn hf hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

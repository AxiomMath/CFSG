module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S123
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Proved
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90T7Quasi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90T7KnEq
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90T7CalC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Rank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

theorem r890_eM_le_of_isTwoLocal {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hN : IsTwoLocal N) : PartTwo.S17.eM N ≤ evenRank G := by
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  exact CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 N hN

theorem r890_le_of_mem_calC {G : Type} [Group G] [Finite G] {D : Data G}
    (h847 : UC22.R847ThinNe3 D) (h61 : UC6.R6_1 D) (h5 : (5 : ℕ) ∈ D.sig)
    {J K H : Subgroup G} (hJ : J ∈ calC D.M) {n m : ℕ} (hSzJ : IsSz (Bar2 J) n)
    (hKJ : K ≤ J) (hSzK : IsSz (Bar2 K) m) (hKH : K ∈ calC H) : H ≤ D.M := by
  classical
  have hNK : normalizer (K : Set G) ≤ D.M :=
    r890_normalizer_le_of_le_sz h847 h5 (by norm_num) hJ hSzJ hKJ hSzK
  have hKM : K ≤ D.M := hKJ.trans hJ.1.le
  intro h hh
  by_contra hhM
  have hKh : K.map (MulAut.conj h).toMonoidHom ∈ calC H :=
    PartTwo.Inputs1719.FourteenEight.map_conj_mem_calC hKH hh
  have hne : K.map (MulAut.conj h).toMonoidHom ≠ K := by
    intro heq
    exact hhM (hNK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq))
  have hKhM : K.map (MulAut.conj h).toMonoidHom ≤ D.M :=
    (PartTwo.calC_le_normalizer_of_ne hKH hKh hne.symm).trans hNK
  have hKhMh : K.map (MulAut.conj h).toMonoidHom ≤ D.M.map (MulAut.conj h).toMonoidHom :=
    Subgroup.map_mono hKM
  have hKhi : K.map (MulAut.conj h⁻¹).toMonoidHom ∈ calC H :=
    PartTwo.Inputs1719.FourteenEight.map_conj_mem_calC hKH (inv_mem hh)
  have hnei : K.map (MulAut.conj h⁻¹).toMonoidHom ≠ K := by
    intro heq
    exact hhM (by
      have := hNK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
      simpa using inv_mem this)
  have hKhiM : K.map (MulAut.conj h⁻¹).toMonoidHom ≤ D.M :=
    (PartTwo.calC_le_normalizer_of_ne hKH hKhi hnei.symm).trans hNK
  have hKMh : K ≤ D.M.map (MulAut.conj h).toMonoidHom := by
    intro k hk
    refine ⟨h⁻¹ * k * h, hKhiM ⟨k, hk, by simp⟩, by simp [mul_assoc]⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrank : 2 ≤ CFSG.Open.pRank 5 (K ⊔ K.map (MulAut.conj h).toMonoidHom) :=
    PartTwo.Inputs1719.FourteenEight.two_le_pRank_sup_of_conj hKH hKh hne rfl (by norm_num)
      (by norm_num) (PartTwo.Inputs1719.FourteenEight.center_eq_bot_of_isSz hSzK)
      (PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz hSzK)
  obtain ⟨E, hE, hEp, hEcyc⟩ :=
    PartTwo.Inputs1719.FourteenEight.exists_noncyclic_le_of_two_le_pRank (by norm_num) hrank
  have hEM : E ≤ D.M := hE.trans (sup_le hKM hKhM)
  have hEMh : E ≤ D.M.map (MulAut.conj h).toMonoidHom := hE.trans (sup_le hKMh hKhMh)
  have huniq := h61 5 h5 E hEM hEp hEcyc
  have hmem : D.M.map (MulAut.conj h).toMonoidHom ∈ calMOf E :=
    ⟨CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map D.maxLocal _, hEMh⟩
  rw [huniq] at hmem
  have hMh : D.M.map (MulAut.conj h).toMonoidHom = D.M := by simpa using hmem
  have hN := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMh
  rw [CFSG.LocalAnalysis.AGL81TheoremCD.Section12.normalizer_maxTwoLocal D.maxLocal] at hN
  exact hhM hN

theorem r890_fstar_perfInter_eq_pCoreOf {G : Type} [Group G] [Finite G] {J C N : Subgroup G}
    {n : ℕ} (hKX : perfInter890 J C ≤ perfInter890 J N)
    (hJ : perfInter890 J C ⊔ pCoreOf 2 J = J)
    (hF : Fstar (perfInter890 J C) = pCoreOf 2 (perfInter890 J C))
    (hSz : IsSz (Bar2 (perfInter890 J N)) n) :
    Fstar (perfInter890 J N) = pCoreOf 2 (perfInter890 J N) := by
  by_contra hne
  exact r890_false_of_isQuasisimple_perfInter hKX hJ hF hSz
    (r890_isQuasisimple_of_fstar_ne_pCoreOf (r890_perfInter_perfect J N) hSz hne)

theorem r890_theorem5d7_of_uc410 (hPS : PairStep_890) (h31 : Lemma3_1_890)
    (h32 : Lemma3_2a_890) (h410 : PartTwo.Inputs1719.UC1_4_10) : Theorem5d7_890 := by
  intro G _ _ D L P J Y n cfg h847 h61 h869 hK318 hSch hCat hSLB h885 h887 h888 h889 hF hSz
  by_contra hne
  obtain ⟨N, hNmem, hNM, hnorm, hSzN, R, hR, hRM⟩ :=
    hPS G D L P J Y n cfg h847 h61 h869 hK318 h885 h887 h888 h889 hF hSz hne
  have h885' := h885 L P cfg.set880
  have h5 : (5 : ℕ) ∈ D.sig := by
    rw [h885'.2.1]
    exact Set.mem_singleton 5
  have hev : evenRank G ≤ 3 := h885'.2.2.le
  have : IsSimpleGroup G := D.standing.simple
  have hL31 := h31 G D L P J Y n cfg h885
  obtain ⟨hcov, -, -, -, -⟩ := h32 G D L P J Y n cfg h889 hL31
  have hKN : perfInter890 J (centralizer (Y : Set G)) ≤ N := hNmem.2
  have hKX : perfInter890 J (centralizer (Y : Set G)) ≤ perfInter890 J N :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _
      (Subgroup.isPerfect_iff.mpr (r890_perfInter_perfect J (centralizer (Y : Set G))))
      (le_inf (r890_perfInter_le_left J _) hKN)
  have hKNF := r890_fstar_perfInter_eq_pCoreOf hKX hcov hF hSzN
  have hJM : J ≤ D.M := cfg.memJ.1.le
  have hKNJ : perfInter890 J N ≤ J := r890_perfInter_le_left J N
  have hKNcalC : perfInter890 J N ∈ calC (N ⊓ D.M) := r890_perfInter_mem_calC hJM hnorm hSzN
  have hNtop : N ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab N hNmem.1.1
  have hNK : CFSG.Open.IsKGroup ↥N := D.standing.kProper.isKGroup N hNtop
  have heM : PartTwo.S17.eM N ≤ 3 := (r890_eM_le_of_isTwoLocal hNmem.1.1).trans hev
  have hNorm : ∀ A : Subgroup G, A ≤ perfInter890 J N → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set G) ≤ D.M := fun A h1 h2 h3 =>
    UC22.normalizer_le_of_isSz_of_r847ThinNe3 h847 h5 (by norm_num) cfg.memJ cfg.szJ
      (h1.trans hKNJ) h2 h3
  have hC : perfInter890 J N ∈ calC N :=
    h410 G N (N ⊓ D.M) (perfInter890 J N) R n hNK heM inf_le_left hKNcalC hKNF hSzN hR
      (le_inf inf_le_left (inf_le_right.trans hRM))
      (fun A h1 h2 h3 => le_inf inf_le_left (inf_le_right.trans (hNorm A h1 h2 h3)))
  have hle : N ≤ D.M := r890_le_of_mem_calC h847 h61 h5 cfg.memJ cfg.szJ hKNJ hSzN hC
  exact hNM (hNmem.1.2 D.M D.maxLocal.1 hle).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

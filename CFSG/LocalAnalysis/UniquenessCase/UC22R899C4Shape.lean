module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Asm
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Three
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3SzT
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BGam
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c4_sp_L2 {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p % 3 ≠ 1) (hpn : p ∣ 2 ^ n + 1) :
    IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hLm : L ∈ conjSetOf D.M L := ⟨1, D.M.one_mem, by ext x; simp⟩
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hfour p hp)
  by_cases hmv : p = 3 ∧ ¬ A₀ ≤ normalizer (L : Set G)
  · obtain ⟨rfl, hmv⟩ := hmv
    obtain ⟨w, hw, hwL⟩ := SetLike.not_le_iff_exists.1 hmv
    exact uc22r899c3_sp_of_moves hSg h614 h76 hL hc3 hL2 hs hsn hr hrs hp hA₀M hA₀ hA₀c hw hwL
  have hA₀N : ∀ K ∈ conjSetOf D.M L, A₀ ≤ normalizer (K : Set G) := fun K hK g hg =>
    uc22r899_mem_normalizer_of_fix hc3 (hA₀M hg) hpp hp2 (k := 1)
      (by rw [pow_one]; exact hA₀.2 g hg)
      (fun h3 => ⟨L, hLm, (not_not.1 fun h => hmv ⟨h3, h⟩) hg⟩) K hK
  have hX : ∀ K ∈ conjSetOf D.M L, IsL2 (barImage D.M K) n := by
    intro K hK
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e (uc22s21r899_isL2_of_mem hK hL2)
  refine uc22r899c4_sp_of_facts hSg h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs hp hp3 hA₀M hA₀
    hA₀c hA₀N (fun K hK S hS => ?_)
    (fun K hK S hS => uc22r8100b_not_dvd_normalizer_of_le (hX K hK) hpp hp2 hpn hr hrn hS)
    (fun K hK B hB => uc22r8100b_card_inf_le hpp hp2 (hX K hK) hB) (fun K hK => ?_)
  ·
    haveI := P22y.isCyclic_of_isPGroup_of_isL2Ev (P22fin.isL2Ev_of_isL2 (hX K hK)).1 hr hr2
      (S.subgroupOf (barImage D.M K))
      (hS.isPGroup.comap_of_injective (barImage D.M K).subtype (barImage D.M K).subtype_injective)
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS.le) (MulEquiv.surjective _)
  ·
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
    have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have h := Nat.sq_sub_sq (2 ^ n) 1
      rwa [one_pow] at h
    rw [← Nat.card_congr e.toEquiv, uc22p22r_L2_card (uc22s21r899_isL2_of_mem hK hL2), h1]
    exact (hpn.mul_right _).mul_left _

theorem uc22r899c4_sp_Sz {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p % 3 ≠ 1)
    (hpn : p ∣ 2 ^ (2 * n) + 1) : IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hp3' : p ≠ 3 := by
    rintro rfl
    have h1 := Nat.mod_eq_zero_of_dvd hpn
    rw [pow_mul, Nat.add_mod, Nat.pow_mod] at h1
    norm_num at h1
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hfour p hp)
  have hA₀N : ∀ K ∈ conjSetOf D.M L, A₀ ≤ normalizer (K : Set G) := fun K hK g hg =>
    uc22r899_mem_normalizer_of_fix hc3 (hA₀M hg) hpp hp2 (k := 1)
      (by rw [pow_one]; exact hA₀.2 g hg) (fun h => absurd h hp3') K hK
  have hY : ∀ K ∈ conjSetOf D.M L, IsSz (Bar2 K) n := by
    rintro K ⟨g, -, rfl⟩
    obtain ⟨e⟩ := uc22p20d_bar2_conj g L
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  have hX : ∀ K ∈ conjSetOf D.M L, IsSz (barImage D.M K) n := by
    intro K hK
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e (hY K hK)
  refine uc22r899c4_sp_of_facts hSg h614 h76 hL hc3 (Or.inr hSz) hs hsn hr hrs hp hp3 hA₀M hA₀
    hA₀c hA₀N (fun K hK S hS => ?_)
    (fun K hK S hS => uc22r899c3_not_dvd_normalizer_Sz (hX K hK) hpp hp2 hpn hr hr2 hrn hS)
    (fun K hK B hB => uc22r899c3_card_inf_le_Sz hpp hp2 (hX K hK) hB) (fun K hK => ?_)
  ·
    obtain ⟨Q, rfl⟩ := hS
    obtain ⟨a, F, _, _, e, -, -, -, hQT, -⟩ := uc22r899c3_suzuki_torus_frame (hX K hK) hr2 hrn Q
    haveI := CFSG.ShultStronglyClosedTI.SuzukiModel.isCyclic_suzukiT (a := a) (K := F)
    haveI : IsCyclic ((Q : Subgroup (barImage D.M K)).map e.toMonoidHom) :=
      Subgroup.isCyclic_of_le hQT
    haveI : IsCyclic (Q : Subgroup (barImage D.M K)) := isCyclic_of_injective
      ((Q : Subgroup (barImage D.M K)).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
      (MulEquiv.injective _)
    exact isCyclic_of_surjective ((Q : Subgroup (barImage D.M K)).equivMapOfInjective _
      (barImage D.M K).subtype_injective) (MulEquiv.surjective _)
  ·
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
    obtain ⟨a, ha, hna, ⟨e'⟩⟩ :=
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 (hY K hK)
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr
      (e'.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
      CFSG.SectionRank.card_suzukiMatrixGroup a ha, ← hna]
    have h5 : p ∣ (2 ^ n) ^ 2 + 1 := by
      rw [← pow_mul, mul_comm]
      exact hpn
    exact (h5.mul_right _).mul_right _

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Quasithin.H13.U4ParModel
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.U4FF (disp u4RankDichotomySix_holds)

theorem even_card_of_isU4 {X : Type} [Group X] [Finite X] {e : ℕ} (hS : IsU4 X e) :
    Even (Nat.card X) := by
  obtain ⟨K, _, h, ⟨φ⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hS
  obtain ⟨hcard, -⟩ := CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h (r := 2)
    (ε := 0) (by norm_num) (by norm_num)
  have hdvd : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h 2 0) ∣ Nat.card X := by
    rw [← Nat.card_congr φ.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd
  have he := h.one_le
  exact even_iff_two_dvd.2 (dvd_trans (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) hdvd)

theorem k14_5SmallFor_u4 :
    K14_5SmallFor fun L _ e => IsU4 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have : Fact (∀ s : I, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hI s⟩
  have hne := nParam_eq_of_isU4_parabolic hq hS hPL hpar hinf hN
  have he2 : 2 ≤ e := by omega
  have hU4 : CFSG.LocalAnalysis.RankThreeUC.IsU4Group e L := by
    have hC := CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide)
    obtain ⟨q, hv, hp, hqe, ⟨φ⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.exists_twistedA_of_statedClassicalModel_PSU
        (m := 3) hC
    exact ⟨⟨_, hv⟩, ⟨q, hp, hqe, rfl⟩, ⟨φ⟩⟩
  have hirrL : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L := fun J hJ =>
    hirr.2.2.2 J hJ bot_le le_top
  have hevL : Even (Nat.card ↥L) := even_card_of_isU4 hS
  have hev : Even (Nat.card ↥X) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hevL).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hdt : disp t ≤ n + 1 := by
    rw [← rkIdx_fixV_zpowers_eq_disp, htm]
    exact hm
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  rcases u4RankDichotomySix_holds I e L (by omega) hU4 hirrL with hnat | hbig
  · rcases hnat with hSU | hO6
    ·
      have hn2 : n = 2 * e := by
        rcases hne with h1 | h2
        · exfalso
          have := two_mul_le_disp_of_naturalSU4 hirr hSU htt ht1 (hXN htX)
          omega
        · exact h2
      exact Or.inl ⟨2 * e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, rfl, isSUn_natSUn_of_naturalSU4 hSU⟩))))), Or.inl hn2⟩
    ·
      exact Or.inl ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (isOmegaMinus_natOmegaMinus_of_naturalOmega6 hO6))))))), hne⟩
  ·
    exfalso
    have htc : ∃ x ∈ L, t * x ≠ x * t := by
      by_contra hcon
      push Not at hcon
      exact ht1 (eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact htt) hcon)
    have hsimpL : IsSimpleGroup ↥L :=
      uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hS
    have hLodd : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N = ⊥ :=
      fun N hN hodd => eq_bot_of_odd_of_isSimpleGroup hevL N hN hodd
    obtain ⟨l, hl, k, hyL, hy1, hy2⟩ := exists_involution_pow_mul_conj hLodd (hXN htX) htt htc
    have hy : 6 * e ≤ disp ((t * (l⁻¹ * t * l)) ^ k) := hbig _ hyL hy1 hy2
    have : Module.Finite (ZMod 2) (Additive I) := Module.Finite.of_finite
    have hrky : disp ((t * (l⁻¹ * t * l)) ^ k) ≤ 2 * disp t :=
      finrank_range_pow_mul_conj_le
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp binaryLin) t l k
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

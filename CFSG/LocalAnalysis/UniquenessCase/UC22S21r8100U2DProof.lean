module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DInv
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2C
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DExcl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UIrr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Matrix
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem uc22r8u2d_normalizer_le {D : Data G}
    (hSg : UC6S846.SigmaStd D) {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {R E : Subgroup G} {b : Fin 2 → G} (hb : U2DBasis D.M L K r R E b)
    (hNb : normalizer (zpowers (b 0) : Set G) ≤ D.M)
    (hdvd : ¬ p ∣ Nat.card (centralizer (E : Set G))) :
    normalizer (E : Set G) ≤ D.M := by
  by_contra hNM
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCM : centralizer (E : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (hb.frame.mem 0))).trans
      ((CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _).trans hNb)
  obtain ⟨y, hyNM, hyo⟩ := uc22r8u2d_exists_pElement hSg hL hK hne hset hLS hp hr hb.sylow
    hb.le_R hb.le_sup hb.frame.elem hb.omega
  have hY : IsStronglyPEmbedded p
      ((normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G))) := by
    refine hsp.subgroupOf hNM ?_
    have h := orderOf_dvd_natCard (⟨y, hyNM⟩ : ↥(normalizer (E : Set G) ⊓ D.M))
    rwa [Subgroup.orderOf_mk, hyo] at h
  have hkY : hb.frame.rho.ker ≤
      (normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G)) := by
    rw [hb.frame.ker_rho]
    exact fun m hm => Subgroup.mem_subgroupOf.2 ⟨m.2, hCM (Subgroup.mem_subgroupOf.1 hm)⟩
  have hpk : ¬ p ∣ Nat.card hb.frame.rho.ker := by
    rwa [hb.frame.ker_rho, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
  have hemb := u81_isStronglyPEmbedded_subgroupOf_range hY hb.frame.rho hkY hpk
  have hrH : ¬ r ∣ Nat.card
      (((normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G))).map
        hb.frame.rho) := by
    rw [← Subgroup.relIndex_ker]
    intro h
    obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1
      (hb.sylow.of_le (le_inf (hb.le_centralizer.trans hCN) hb.sylow.le) inf_le_right)
    refine hidx ?_
    rw [← Subgroup.relIndex_subgroupOf
      (inf_le_left : normalizer (E : Set G) ⊓ D.M ≤ normalizer (E : Set G))]
    refine h.trans (Subgroup.relIndex_dvd_of_le_left _ ?_)
    rw [hb.frame.ker_rho]
    exact fun m hm =>
      Subgroup.mem_subgroupOf.2 (hb.le_centralizer (Subgroup.mem_subgroupOf.1 hm))
  have hmemY : ∀ {m : G} (h : m ∈ normalizer (E : Set G) ⊓ D.M),
      hb.frame.rho ⟨m, h.1⟩ ∈
        ((normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G))).map
          hb.frame.rho :=
    fun h => ⟨⟨_, h.1⟩, Subgroup.mem_subgroupOf.2 h, rfl⟩
  have hstab : ∀ g ∈ hb.frame.rho.range,
      (g : Matrix (Fin 2) (Fin 2) (ZMod r)) *ᵥ Pi.single 0 1 ∈
        Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 2 → ZMod r)} →
      g ∈ ((normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G))).map
        hb.frame.rho := by
    rintro _ ⟨m, rfl⟩ hm
    have h1 := hb.frame.conj_mem_zpowers_of_mulVec m 0 hm
    have hmN : (m : G) ∈ normalizer (zpowers (b 0) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
        rw [← conj_zpow]
        exact zpow_mem h1 k
    exact hmemY ⟨m.2, hNb hmN⟩
  obtain ⟨t, ht, htb⟩ := hb.exists_inv hL hK hne hset hLS hr hr2
  have hd : (hb.frame.rho ⟨t, ht.1⟩ : Matrix (Fin 2) (Fin 2) (ZMod r)) =
      Matrix.diagonal ![-1, 1] := by
    rw [hb.frame.rho_eq_diagonal ⟨t, ht.1⟩ htb]
    congr 1
    funext i
    fin_cases i
    exacts [(Int.cast_neg 1).trans (congrArg Neg.neg Int.cast_one), Int.cast_one]
  obtain ⟨s, hs, hs₀, hs₁⟩ := hb.exists_swap hne hset hr hr2
  obtain ⟨hs0, hs1⟩ := hb.frame.rho_antidiag ⟨s, hs.1⟩ hs₀ hs₁
  obtain ⟨α, hα⟩ := hb.frame.exists_rho_eq_diagonal ⟨y, hyNM.1⟩ fun i =>
    hb.conj_mem_zpowers hne hset hyNM.2 hyNM.1 (by rw [hyo]; exact hpP.odd_of_ne_two hp2) i
  have hyp : hb.frame.rho ⟨y, hyNM.1⟩ ^ p = 1 := by
    have h1 : (⟨y, hyNM.1⟩ : ↥(normalizer (E : Set G))) ^ p = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := pow_orderOf_eq_one y
      rwa [hyo] at h
    rw [← map_pow, h1, map_one]
  have hρy1 : hb.frame.rho ⟨y, hyNM.1⟩ ≠ 1 := by
    intro h1
    have h := orderOf_dvd_natCard
      (⟨y, (hb.frame.rho_eq_one_iff ⟨y, hyNM.1⟩).1 h1⟩ : ↥(centralizer (E : Set G)))
    rw [Subgroup.orderOf_mk, hyo] at h
    exact hdvd h
  exact gl2Excl r p hr2 hp2 hb.frame.rho.range
    (((normalizer (E : Set G) ⊓ D.M).subgroupOf (normalizer (E : Set G))).map hb.frame.rho)
    (Subgroup.map_le_range _ _) hemb hrH hstab _ (hmemY ht) hd _ (hmemY hs) hs0 hs1 _
    (hmemY hyNM) hyp hρy1 α hα

theorem r8100U2_of_normalizer_le {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D)
    (hN : ∀ (L : Subgroup G) (n r p : ℕ), L ∈ calC D.M → (conjSetOf D.M L).ncard = 2 →
      (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) → r.Prime → r ≠ 2 → p ∈ D.sig →
        ∀ A : Subgroup G, A ≤ L → Nat.card A = r → normalizer (A : Set G) ≤ D.M) :
    R8100U2 D := by
  intro he L n s r p hL hc2 hcong hs _ hr hrs hp A hAL hAr
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have : Fact r.Prime := ⟨hr⟩
  by_cases hspr : IsStronglyPEmbedded r D.M
  · refine uc22p22r_mem_uniqueSet_of_sp D hr hspr (hAL.trans hL.1.le)
      (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])) ?_
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hspr (UC6S846.sp_of_mem_sig hSg hns h)
  have hr7 : 7 ≤ r := PartTwo.s13_seven_le_of_dvd hs hr hrs
  have hr2 : r ≠ 2 := by omega
  have h2 := uc22r8u2_pRank_le_two hSg h13 he hp hr hr7 hrσ
  have hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hcong.imp And.left And.left
  have hNA := hN L n r p hL hc2 hLS hr hr2 hp A hAL hAr
  obtain ⟨R, E, b, hb, rfl⟩ := uc22r8u2d_exists_basis hL hK hne hset hLS hr hr2 h2 hAL hAr
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  by_cases hdvd : p ∣ Nat.card (centralizer (E : Set G))
  · exact u81_mem_uniqueSet_of_dvd (UC6S846.sp_of_mem_sig hSg hns hp) hb.sylow hb.le_R
      hb.frame.elem hb.omega (zpowers_le.2 (hb.frame.mem 0)) hNA hdvd
  · exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega
      hb.sylow hb.le_R hb.frame.elem hb.omega
      (uc22r8u2d_normalizer_le hSg hL hK hne hset hLS hp hr hr2 hb hNA hdvd)
      (zpowers_le.2 (hb.frame.mem 0)) hNA

theorem r8100U2_dataOfSetup_of_normalizer_le (hS : Standing G)
    (hUC : rankThreeUC G) (S : Setup G)
    (hN : ∀ (L : Subgroup G) (n r p : ℕ), L ∈ calC (dataOfSetup hS S).M →
      (conjSetOf (dataOfSetup hS S).M L).ncard = 2 →
      (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) → r.Prime → r ≠ 2 → p ∈ (dataOfSetup hS S).sig →
        ∀ A : Subgroup G, A ≤ L → Nat.card A = r →
          normalizer (A : Set G) ≤ (dataOfSetup hS S).M) :
    R8100U2 (dataOfSetup hS S) :=
  r8100U2_of_normalizer_le (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) hN

end CFSG.LocalAnalysis.UniquenessCase.UC22

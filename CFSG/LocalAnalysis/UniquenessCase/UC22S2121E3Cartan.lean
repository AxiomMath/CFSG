module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Z
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xh
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender (cartan)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_exists_cartan_lift {M L T B : Subgroup G}
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hBM : B ≤ M) (hB : Odd (Nat.card B)) (hBT : Permutes B T) {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    ∃ c ∈ L, c ∈ centralizer (B : Set G) ∧ 2 ^ n - 1 ∣ orderOf c ∧
      (IsU3 (Bar2 L) n → 2 ^ (2 * n) - 1 ∣ orderOf c) := by
  have hBN : B ≤ normalizer (L : Set G) :=
    hBM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  obtain ⟨Q, t, -, -, hcyc, h2, h3, -, hfix⟩ := uc22s13xf_fix_cartan hLM hLn hT hBN hB hBT hn hX
  haveI := hcyc
  obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(cartan (Q : Subgroup (Bar2 L)) t))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (d : Bar2 L)
  obtain ⟨c, hcB, hcl⟩ := uc22s13xh_exists_lift hBN hB l fun b hb => hl ▸ hfix b hb d d.2
  have hD : Nat.card (cartan (Q : Subgroup (Bar2 L)) t) ∣ orderOf (c : G) := by
    rw [← hd, ← Subgroup.orderOf_coe, ← hl, ← hcl, Subgroup.orderOf_coe]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) c
  have hsq : 2 ^ n - 1 ∣ 2 ^ (2 * n) - 1 := by
    rw [two_mul, pow_add, mul_self_tsub_one]
    exact dvd_mul_left _ _
  refine ⟨c, c.2, hcB, ?_, fun hU => h3 hU ▸ hD⟩
  rcases hX with hL2 | hU
  · exact h2 hL2 ▸ hD
  · exact hsq.trans (h3 hU ▸ hD)

theorem uc22s2121e3_exists_elem_Sp (hThin : PartTwo.ThinList13) {D : Data G}
    (hS : PartTwo.Setting13 D) {p : ℕ} (hpp : p.Prime) {B : Subgroup G} (hB : F13.Case136b D p B)
    (h1 : 1 ≤ CFSG.Open.pRank p (F13.Sp D.M p)) :
    ∃ y : ↥D.M, (y : G) ∈ normalizer (B : Set G) ∧ orderOf (y : G) = p ∧
      ∀ J ∈ PartTwo.s13_compsP (Bar2 D.M) p,
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y ∈ centralizer (J : Set (Bar2 D.M)) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨P, hP, hPN⟩ := hB.2.2.2.2.2
  obtain ⟨E, hE, -, hcE⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (F13.Sp D.M p)
  have hpS : p ∣ Nat.card (F13.Sp D.M p) := by
    have hEc := Subgroup.card_dvd_of_le hE
    rw [hcE] at hEc
    exact (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp h1)).trans hEc
  have hpP : p ∣ Nat.card P := by
    rw [hP.card_eq]
    exact dvd_pow_self p (Nat.one_le_iff_ne_zero.mp ((hpp.dvd_iff_one_le_factorization
      (Nat.card_pos (α := ↥(F13.Sp D.M p))).ne').mp hpS))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hpP
  have hyS : (y : G) ∈ F13.Sp D.M p := hP.le y.2
  refine ⟨⟨y, PartTwo.s13_Sp_le D.M p hyS⟩, hPN y.2, (Subgroup.orderOf_coe y).trans hy,
    fun J hJ => ?_⟩
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, PartTwo.s13_Sp_le D.M p hyS⟩ ∈
      barImage D.M (F13.Sp D.M p) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyS)
  rw [PartTwo.s13_barImage_Sp D.M hpp] at hmem
  refine Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_)
    (PartTwo.s13_Thirteen2_pElementSubgroup_le p _ hmem)
  rw [PartTwo.s13_pElementSubgroup_layer_eq (PartTwo.s13_normalSimple hThin D hS) hpp]
  exact le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 D.M) p) => J) J hJ

theorem uc22s2121e3_false_of_cartan_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B) {L : Subgroup G}
    (hL : L ∈ calC S.M) {n : ℕ} (hn : IsPowTwo n) (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n)
    (hpn : p ∣ 2 ^ n - 1 ∨ (IsU3 (Bar2 L) n ∧ p ∣ 2 ^ n + 1)) {y : G} (hyM : y ∈ S.M)
    (hyN : y ∈ normalizer (B : Set G)) (hy : orderOf y = p)
    (hyc : QuotientGroup.mk' (CFSG.pCore 2 ↥S.M) ⟨y, hyM⟩ ∈
      centralizer (barImage S.M L : Set (Bar2 S.M))) : False := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  obtain ⟨hB1, hBM, hBo, hBT, hN, -⟩ := hB
  have hLM := PartTwo.s13_le_of_mem_calC hL
  obtain ⟨c, hcL, hcB, hc1, hc2⟩ := uc22s2121e3_exists_cartan_lift hLM
    (hS13.hyp131.normal L hL) (PartTwo.Three.dataOfSetup hS S).sylowM hBM hBo hBT hn hX
  have h3 : 3 ∣ 2 ^ n - 1 := uc22s13xo_three_dvd_sub_one (uc22s13xg_even_center_outer hn hX).1
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [two_mul, pow_add, mul_self_tsub_one]
  have hpc : p ∣ orderOf c := by
    rcases hpn with h | ⟨hU, h⟩
    · exact h.trans hc1
    · have hc := hc2 hU
      rw [hsq] at hc
      exact (h.mul_right _).trans hc
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  have hx : orderOf (c ^ (orderOf c / p)) = p := orderOf_pow_orderOf_div hc0 hpc
  have hz : orderOf (c ^ (orderOf c / 3)) = 3 := orderOf_pow_orderOf_div hc0 (h3.trans hc1)
  have hmem : ∀ k : ℕ, c ^ k ∈ normalizer (B : Set G) ⊓ S.M := fun k =>
    Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ (pow_mem hcB k),
      hLM (pow_mem hcL k)⟩
  have hns : PartTwo.s13_NormalSimple (Bar2 S.M) := PartTwo.s13_normalSimple hThin _ hS13
  have hJ := PartTwo.s13_Layer13_inf_centralizer_eq_bot hns (PartTwo.s13_barImage_isComponent hL)
  have hr := uc22s13xm_succ_le_pRank (M := S.M) (K := normalizer (B : Set G) ⊓ S.M) hpp hp2
    inf_le_right hJ (zpowers_le.mpr hyc)
    (zpowers_le.mpr (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyN, hyM⟩))))
    (hmem _) hx (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (pow_mem hcL _)))
  have hr1 := uc22s13xm_one_le_pRank_zpowers hpp (uc22s13xm_orderOf_bar hpp hp2 hyM hy)
  have hcase : F08.Thin8 L ∨ ∃ m : ℕ, IsSU3 (Bar2 L) m ∧ 3 ∣ 2 ^ m - 1 := by
    rcases hX with hL2 | hU
    · exact Or.inl fun q hq hq2 => pRank_bar2_eq_of_odd (Y := L) hq hq2 ▸
        pRank_le_one_of_isL2_or_isSz (Or.inl hL2) hq hq2
    · exact Or.inr ⟨n, uc22p22d_isSU3_of_isU3 hL.2.2 hU, h3⟩
  have hrank : 2 ≤ CFSG.Open.pRank p (S.M ⊓ normalizer (B : Set G)) := by
    rw [inf_comm]
    omega
  exact uc22s2121e3_false_of_routeZ_r847E3 hSE hS S h847T h847S hp hp5
    (hSig.sig1_sp p (hS13.sig_eq ▸ hp)) hB1 hBM hN hrank (hmem _) (hmem _) hx
    (Commute.pow_pow_self c _ _).eq hL (hS13.hyp131.normal L hL) (pow_mem hcL _) Nat.prime_three
    (by norm_num) (by omega) hz hcase

theorem uc22s2121e3_false_of_two_cartan_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B) {L K : Subgroup G}
    (hL : L ∈ calC S.M) (hK : K ∈ calC S.M) (hne : barImage S.M L ≠ barImage S.M K) {n m : ℕ}
    (hn : IsPowTwo n) (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n)
    (hpn : p ∣ 2 ^ n - 1 ∨ (IsU3 (Bar2 L) n ∧ p ∣ 2 ^ n + 1)) (hm : IsPowTwo m)
    (hY : IsL2 (Bar2 K) m ∨ IsU3 (Bar2 K) m)
    (hpm : p ∣ 2 ^ m - 1 ∨ (IsU3 (Bar2 K) m ∧ p ∣ 2 ^ m + 1)) : False := by
  have hB' := hB
  obtain ⟨-, hBM, hBo, hBT, -, -⟩ := hB'
  have hKM := PartTwo.s13_le_of_mem_calC hK
  obtain ⟨y, hyK, hyB, hy⟩ := uc22s13xm_exists_elem hKM (hS13.hyp131.normal K hK)
    (PartTwo.Three.dataOfSetup hS S).sylowM hBM hBo hBT hm hY
    ((PartTwo.Three.dataOfSetup hS S).sig_prime p hp).1 hpm
  have hns : PartTwo.s13_NormalSimple (Bar2 S.M) := PartTwo.s13_normalSimple hThin _ hS13
  exact uc22s2121e3_false_of_cartan_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5 hB hL hn
    hX hpn (hKM hyK) (Subgroup.centralizer_le_normalizer _ hyB) hy
    (PartTwo.s13_components_commute hns (PartTwo.s13_barImage_isComponent hK)
      (PartTwo.s13_barImage_isComponent hL) hne.symm
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyK)))

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R847E4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xh
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xn
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_exists_cartan_lift {M L T B : Subgroup G}
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hBM : B ≤ M) (hB : Odd (Nat.card B)) (hBT : Permutes B T) {n : ℕ} (hn : IsPowTwo n)
    (hU : IsU3 (Bar2 L) n) :
    ∃ c ∈ L, c ∈ centralizer (B : Set G) ∧ 2 ^ (2 * n) - 1 ∣ orderOf c := by
  have hBN : B ≤ normalizer (L : Set G) :=
    hBM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  obtain ⟨Q, t, -, -, hcyc, -, h3, -, hfix⟩ :=
    uc22s13xf_fix_cartan hLM hLn hT hBN hB hBT hn (Or.inr hU)
  haveI := hcyc
  obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(cartan (Q : Subgroup (Bar2 L)) t))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (d : Bar2 L)
  obtain ⟨c, hcB, hcl⟩ := uc22s13xh_exists_lift hBN hB l fun b hb => by
    rw [hl]
    exact hfix b hb d d.2
  have hcd : orderOf (QuotientGroup.mk c : Bar2 L) = 2 ^ (2 * n) - 1 := by
    rw [hcl, hl, Subgroup.orderOf_coe, hd, h3 hU]
  refine ⟨c, c.2, hcB, ?_⟩
  rw [Subgroup.orderOf_coe, ← hcd]
  exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) c

theorem uc22ine229_s13xn_false_setup4 (hSE : StronglyEmbeddedFive)
    (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13) (hS4 : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hS : PartTwo.Setting13 (UC6.dataOfSetup4 hS4 hU S))
    (hSig : UC6S846.SigmaStd (UC6.dataOfSetup4 hS4 hU S))
    (h847 : R847E4 (UC6.dataOfSetup4 hS4 hU S)) {p : ℕ}
    (hp : p ∈ (UC6.dataOfSetup4 hS4 hU S).sig) {B : Subgroup G}
    (hB : F13.Case136b (UC6.dataOfSetup4 hS4 hU S) p B) {L : Subgroup G}
    (hL : L ∈ calC (UC6.dataOfSetup4 hS4 hU S).M) {n : ℕ} (hn : IsPowTwo n)
    (hU3 : IsU3 (Bar2 L) n) (hpn : p ∣ 2 ^ n + 1) {y : G}
    (hyM : y ∈ (UC6.dataOfSetup4 hS4 hU S).M) (hyN : y ∈ normalizer (B : Set G))
    (hy : orderOf y = p)
    (hyc : (QuotientGroup.mk' (CFSG.pCore 2 ↥(UC6.dataOfSetup4 hS4 hU S).M) ⟨y, hyM⟩ :
        Bar2 (UC6.dataOfSetup4 hS4 hU S).M) ∈
      centralizer (barImage (UC6.dataOfSetup4 hS4 hU S).M L :
        Set (Bar2 (UC6.dataOfSetup4 hS4 hU S).M))) : False := by
  obtain ⟨hpp, hp2⟩ := (UC6.dataOfSetup4 hS4 hU S).sig_prime p hp
  obtain ⟨hB1, hBM, hBo, hBT, hN, -⟩ := hB
  have hsp := hSig.sig1_sp p (hS.sig_eq ▸ hp)
  have hLM := PartTwo.s13_le_of_mem_calC hL
  have hn2 := PartTwo.s13_two_le_of_isU3 hU3
  have hp5 : 5 ≤ p := hpp.five_le_of_ne_two_of_ne_three hp2
    (by have := uc22s13xn_three_lt hn hn2 hpp hpn; omega)
  have h4 : 4 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn2
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    omega
  have hℓp : ℓ ≠ p := by
    rintro rfl
    have h2 : ℓ ∣ 2 := by
      rw [show 2 ^ n + 1 = 2 ^ n - 1 + 2 by omega] at hpn
      exact (Nat.dvd_add_right hℓd).mp hpn
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hsq : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [two_mul, pow_add, mul_self_tsub_one]
  have hpD : p ∣ 2 ^ (2 * n) - 1 := by
    rw [hsq]
    exact Dvd.dvd.mul_right hpn _
  have hℓD : ℓ ∣ 2 ^ (2 * n) - 1 := by
    rw [hsq]
    exact Dvd.dvd.mul_left hℓd _
  have hmod : 2 ^ (2 * n) ≡ 1 [MOD ℓ] := ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hℓD).symm
  obtain ⟨c, hcL, hcB, hcd⟩ := uc22ine229_exists_cartan_lift hLM (hS.hyp131.normal L hL)
    (UC6.dataOfSetup4 hS4 hU S).sylowM hBM hBo hBT hn hU3
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  set x := c ^ (orderOf c / p) with hxdef
  set z := c ^ (orderOf c / ℓ) with hzdef
  have hx : orderOf x = p := orderOf_pow_orderOf_div hc0 (hpD.trans hcd)
  have hz : orderOf z = ℓ := orderOf_pow_orderOf_div hc0 (hℓD.trans hcd)
  have hxz : x * z = z * x := (Commute.pow_pow_self c _ _).eq
  have hxL : x ∈ L := pow_mem hcL _
  have hzL : z ∈ L := pow_mem hcL _
  have hxHM : x ∈ normalizer (B : Set G) ⊓ (UC6.dataOfSetup4 hS4 hU S).M :=
    Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ (pow_mem hcB _), hLM hxL⟩
  have hzHM : z ∈ normalizer (B : Set G) ⊓ (UC6.dataOfSetup4 hS4 hU S).M :=
    Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ (pow_mem hcB _), hLM hzL⟩
  have hyHM : y ∈ normalizer (B : Set G) ⊓ (UC6.dataOfSetup4 hS4 hU S).M :=
    Subgroup.mem_inf.mpr ⟨hyN, hyM⟩
  have hJ := PartTwo.s13_Layer13_inf_centralizer_eq_bot
    (PartTwo.s13_normalSimple hThin (UC6.dataOfSetup4 hS4 hU S) hS)
    (PartTwo.s13_barImage_isComponent hL)
  have hr : 1 < CFSG.Open.pRank p (normalizer (B : Set G) ⊓ (UC6.dataOfSetup4 hS4 hU S).M) := by
    have h1 := uc22s13xm_succ_le_pRank (M := (UC6.dataOfSetup4 hS4 hU S).M)
      (K := normalizer (B : Set G) ⊓ (UC6.dataOfSetup4 hS4 hU S).M) hpp hp2 inf_le_right hJ
      (zpowers_le.mpr hyc)
      (zpowers_le.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyHM))) hxHM hx
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL))
    have h2 := uc22s13xm_one_le_pRank_zpowers hpp (uc22s13xm_orderOf_bar hpp hp2 hyM hy)
    omega
  let k : Sec7Core4 G := .ofUnique hS4 hU S.M S.maxLocal p hp hsp
  have hno : Sec7Core4.KIDExcluded k := uc22ine229_kIDExcluded_setup4 hB3 hS4 hU S hσ hp hp5 hsp
  have hH : Sec7Core4.Config k (normalizer (B : Set G)) :=
    k.config_normalizer hB1 hBM (by rw [inf_comm]; exact hr) hN
  have hxp : IsPGroup k.p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]; rfl)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hpp.one_lt.ne hx
  obtain ⟨j, hjM, hjz⟩ := k.exists_not_mem_commute_of_prime (k.step75 hp5 hSE) k.step72L
    (k.step76C_of_kIDExcluded hp5 hno hSE) hH hxHM hzHM hxp hx1 (by rw [hz]; exact hℓ)
    (by rw [hz]; exact hℓ2) (by rw [hz]; exact hℓp) hxz
  have hNz := h847 L hL (zpowers z) (zpowers_le.mpr hzL) ℓ hℓ hℓ2
    (by rw [Nat.card_zpowers, hz]) p hp (Or.inr ⟨n, uc22p22d_isSU3_of_isU3 hL.2.2 hU3, hmod⟩)
  have hjC : j ∈ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    exact ((Commute.zpow_right (show Commute j z from hjz) i).eq).symm
  exact hjM (hNz (Subgroup.centralizer_le_normalizer _ hjC))

end CFSG.LocalAnalysis.UniquenessCase.UC22

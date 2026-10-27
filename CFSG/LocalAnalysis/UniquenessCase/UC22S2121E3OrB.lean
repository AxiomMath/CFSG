module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Z
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarX108
import CFSG.LocalAnalysis.UniquenessCase.UC1S5Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xh
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_rhoL_eq_one {D : Data G} {p : ℕ}
    {B L : Subgroup G} (hB : F13.Case136b D p B) (hLM : L ≤ D.M)
    (hLn : (L.subgroupOf D.M).Normal) {n : ℕ} (hn : IsPowTwo n) (hL2 : IsL2 (Bar2 L) n) {r : ℕ}
    (hr : r.Prime) (hr1 : ¬ r ∣ 2 ^ n - 1) (b : ↥(normalizer (L : Set G)))
    (hb : (b : G) ∈ CFSG.Open.pCoreOf r B) : UC6S846.rhoL L b = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hBM, hBodd, hBT, -, -⟩ := hB
  have hBN : B ≤ normalizer (L : Set G) :=
    hBM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  obtain ⟨Q, t, -, -, -, h2, -, hmap⟩ :=
    uc22s13xf_cartan hLM hLn D.sylowM hBN hBodd hBT hn (Or.inl hL2)
  obtain ⟨d, hdC, hd⟩ := hmap b (CFSG.LieType.BorelTits.pCoreOf_le r B hb)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup r B ⟨b, hb⟩
  have h1 : orderOf (UC6S846.rhoL L b) ∣ r ^ k := by
    refine (orderOf_map_dvd _ _).trans (orderOf_dvd_of_pow_eq_one (Subtype.ext ?_))
    simpa using congrArg Subtype.val hk
  have h2' : orderOf (UC6S846.rhoL L b) ∣ 2 ^ n - 1 := by
    rw [← hd, ← h2 hL2]
    exact (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard _ hdC)
  have hcop : Nat.Coprime (r ^ k) (2 ^ n - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).mpr hr1)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2')

theorem uc22s2121e3_exists_elem_of_rhoL {L X : Subgroup G} (hXN : X ≤ normalizer (L : Set G))
    (hX : Odd (Nat.card X))
    (hρ : ∀ b : ↥(normalizer (L : Set G)), (b : G) ∈ X → UC6S846.rhoL L b = 1) {q : ℕ}
    (hq : q.Prime) (hqL : q ∣ Nat.card (Bar2 L)) :
    ∃ x ∈ L, x ∈ centralizer (X : Set G) ∧ orderOf x = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' q hqL
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective d
  obtain ⟨c, hcX, hcl⟩ := uc22s13xh_exists_lift hXN hX l fun b hb => by
    rw [hρ b hb]
    rfl
  have hcd : orderOf (QuotientGroup.mk c : Bar2 L) = q := by rw [hcl, hl, hd]
  have hqc : q ∣ orderOf (c : G) := by
    rw [Subgroup.orderOf_coe, ← hcd]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) c
  exact ⟨(c : G) ^ (orderOf (c : G) / q), Subgroup.pow_mem _ c.2 _, Subgroup.pow_mem _ hcX _,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hqc⟩

theorem uc22s2121e3_routeZ_of_not_dvd
    (hThin : PartTwo.ThinList13) {D : Data G} (hS : PartTwo.Setting13 D) {p : ℕ}
    (hp : p ∈ D.sig) {B : Subgroup G} (hB : F13.Case136b D p B) (hBab : IsMulCommutative B)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : barImage D.M L ≠ barImage D.M K) {n : ℕ} (hn : IsPowTwo n)
    (hLs : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) (hKs : IsL2 (Bar2 K) n) (hpn : p ∣ 2 ^ n + 1)
    {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card B) (hr1 : ¬ r ∣ 2 ^ n - 1) :
    ∃ (R : Subgroup G) (x z : G) (Y : Subgroup G) (ℓ : ℕ),
      R ≠ ⊥ ∧ R ≤ D.M ∧ ¬ normalizer (R : Set G) ≤ D.M ∧
      2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (R : Set G)) ∧
      x ∈ normalizer (R : Set G) ⊓ D.M ∧ z ∈ normalizer (R : Set G) ⊓ D.M ∧
      orderOf x = p ∧ x * z = z * x ∧
      Y ∈ calC D.M ∧ z ∈ Y ∧ ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ p ∧ orderOf z = ℓ ∧ F08.Thin8 Y := by
  classical
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : 3 < p := uc22s13xn_three_lt hn (PartTwo.s13_two_le_of_isL2 hKs) hpp hpn
  have hns := PartTwo.s13_normalSimple hThin D hS
  obtain ⟨-, hBM, hBodd, hBT, hBN, -⟩ := id hB
  have hLM := PartTwo.s13_le_of_mem_calC hL
  have hKM := PartTwo.s13_le_of_mem_calC hK
  have hLn := hS.hyp131.normal L hL
  have hKn := hS.hyp131.normal K hK
  have hMK : D.M ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by rw [sq, mul_self_tsub_one]
  have hpL2 : ∀ {X : Subgroup G}, IsL2 (Bar2 X) n → p ∣ Nat.card (Bar2 X) := fun hX => by
    rw [uc22p22r_L2_card hX, hsq]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpn _) _
  set R := CFSG.Open.pCoreOf r B
  have hRB : R ≤ B := CFSG.LieType.BorelTits.pCoreOf_le r B
  have hRM : R ≤ D.M := hRB.trans hBM
  have hRodd : Odd (Nat.card R) := hBodd.of_dvd_nat (Subgroup.card_dvd_of_le hRB)
  have hNR : centralizer (R : Set G) ≤ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨x, hxL, hxR, hxo⟩ : ∃ x ∈ L, x ∈ centralizer (R : Set G) ∧ orderOf x = p := by
    rcases hLs with hL2 | hU
    · exact uc22s2121e3_exists_elem_of_rhoL
        (hRM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)) hRodd
        (uc22s2121e3_rhoL_eq_one hB hLM hLn hn hL2 hr hr1) hpp (hpL2 hL2)
    · obtain ⟨x, hxL, hxB, hxo⟩ := uc22s13xm_exists_elem hLM hLn D.sylowM hBM hBodd hBT hn
        (Or.inr hU) hpp (Or.inr ⟨hU, hpn⟩)
      exact ⟨x, hxL, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRB) hxB, hxo⟩
  have hρK := uc22s2121e3_rhoL_eq_one hB hKM hKn hn hKs hr hr1
  obtain ⟨y, hyK, hyR, hyo⟩ :=
    uc22s2121e3_exists_elem_of_rhoL (hRM.trans hMK) hRodd hρK hpp (hpL2 hKs)
  have hxM : x ∈ D.M := hLM hxL
  have hCL := PartTwo.s13_barImage_isComponent hL
  have hCK := PartTwo.s13_barImage_isComponent hK
  have hJ := PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hCL
  have hy' : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hKM hyK⟩ : Bar2 D.M) ∈ barImage D.M K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyK)
  have hyN : y ∈ D.M ⊓ normalizer (R : Set G) := ⟨hKM hyK, hNR hyR⟩
  have hrk := uc22s13xm_succ_le_pRank hpp hp2 (inf_le_left : D.M ⊓ normalizer (R : Set G) ≤ D.M)
    hJ (zpowers_le.mpr (PartTwo.s13_components_commute hns hCK hCL (Ne.symm hne) hy'))
    (zpowers_le.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyN)))
    (⟨hxM, hNR hxR⟩ : x ∈ D.M ⊓ normalizer (R : Set G)) hxo
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL))
  have h1 := uc22s13xm_one_le_pRank_zpowers hpp (uc22s13xm_orderOf_bar hpp hp2 (hKM hyK) hyo)
  have hρx : UC6S846.rhoL K ⟨x, hMK hxM⟩ = 1 :=
    (PartOne.Section8.mem_ker_rhoL_iff_mem_centralizer_barImage hK le_rfl hMK ⟨x, hxM⟩).mpr
      (PartTwo.s13_components_commute hns hCL hCK hne
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)))
  have hXN : R ⊔ zpowers x ≤ normalizer (K : Set G) :=
    sup_le (hRM.trans hMK) (zpowers_le.mpr (hMK hxM))
  have hρX : ∀ b : ↥(normalizer (K : Set G)), (b : G) ∈ R ⊔ zpowers x →
      UC6S846.rhoL K b = 1 := by
    have hle : R ⊔ zpowers x ≤ (UC6S846.rhoL K).ker.map (normalizer (K : Set G)).subtype :=
      sup_le (fun b hb => ⟨⟨b, hMK (hRM hb)⟩, MonoidHom.mem_ker.mpr (hρK _ hb), rfl⟩)
        (zpowers_le.mpr ⟨⟨x, hMK hxM⟩, MonoidHom.mem_ker.mpr hρx, rfl⟩)
    intro b hb
    obtain ⟨b', hb', hbb⟩ := hle hb
    obtain rfl : b' = b := Subtype.ext hbb
    exact MonoidHom.mem_ker.mp hb'
  have hXodd : Odd (Nat.card ↥(R ⊔ zpowers x)) := by
    have hc : ∀ (a : ↥R) (b : ↥(zpowers x)), Commute (R.subtype a) ((zpowers x).subtype b) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (show Commute a x from Subgroup.mem_centralizer_iff.mp hxR a ha).zpow_right k
    have hrange : (MonoidHom.noncommCoprod R.subtype (zpowers x).subtype hc).range =
        R ⊔ zpowers x := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    rw [← hrange]
    refine Odd.of_dvd_nat ?_ (Subgroup.card_range_dvd _)
    rw [Nat.card_prod, Nat.card_zpowers, hxo]
    exact hRodd.mul (hpp.odd_of_ne_two hp2)
  have h3K : 3 ∣ Nat.card (Bar2 K) := by
    have h3 : 3 ∣ 4 ^ n - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := n)
    rw [uc22p22r_L2_card hKs, show (2 ^ n) ^ 2 = 4 ^ n by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    exact h3.mul_left _
  obtain ⟨z, hzK, hzX, hzo⟩ :=
    uc22s2121e3_exists_elem_of_rhoL hXN hXodd hρX Nat.prime_three h3K
  have hzR : z ∈ centralizer (R : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hzX
  refine ⟨R, x, z, K, 3, F05.pCoreOf_ne_bot_of_dvd hBab hr hrB, hRM,
    fun h => hBN ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf r B).trans h),
    by omega, ⟨hNR hxR, hxM⟩, ⟨hNR hzR, hKM hzK⟩, hxo, ?_, hK, hzK, Nat.prime_three,
    by norm_num, by omega, hzo, uc22s13a_thin8_of_isL2_or_isSz (Or.inl hKs)⟩
  exact Subgroup.mem_centralizer_iff.mp hzX x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem uc22s2121e3_false_of_not_dvd_r847E3
    (hSE : StronglyEmbeddedFive) (hS : Standing G) (S : Setup G)
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S))
    (hThin : PartTwo.ThinList13) (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    {p : ℕ} (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hsp : IsStronglyPEmbedded p S.M)
    {B : Subgroup G} (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B)
    (hBab : IsMulCommutative B) {L K : Subgroup G} (hL : L ∈ calC S.M) (hK : K ∈ calC S.M)
    (hne : barImage S.M L ≠ barImage S.M K) {n : ℕ} (hn : IsPowTwo n)
    (hLs : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) (hKs : IsL2 (Bar2 K) n) (hpn : p ∣ 2 ^ n + 1)
    {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card B) (hr1 : ¬ r ∣ 2 ^ n - 1) : False := by
  obtain ⟨hpp, -⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hp3 := uc22s13xn_three_lt hn (PartTwo.s13_two_le_of_isL2 hKs) hpp hpn
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hpp
  obtain ⟨R, x, z, Y, ℓ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    uc22s2121e3_routeZ_of_not_dvd hThin hS13 hp hB hBab hL hK hne hn hLs hKs hpn hr hrB hr1
  exact uc22s2121e3_false_of_routeZ_r847E3 hSE hS S h847T h847S hp (by omega) hsp h1 h2 h3 h4 h5
    h6 h7 h8 h9 (hS13.hyp131.normal _ h9) h10 h11 h12 h13 h14 (Or.inl h15)

end CFSG.LocalAnalysis.UniquenessCase.UC22

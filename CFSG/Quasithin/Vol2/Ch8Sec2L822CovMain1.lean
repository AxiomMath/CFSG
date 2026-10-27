module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3LzSyl
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem cov_exists_z {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (h711n : Stmt7_1_1_normal) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58) (h317 : AS317Sylow)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    ∃ z : G, z ≠ 1 ∧ z ^ 2 = 1 ∧ z ∈ fsuV T I ∧
      H ≤ Subgroup.centralizer ({z} : Set G) ∧ T ≤ Subgroup.centralizer ({z} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hne := fsuV_inf_omegaOneCenter_ne_bot hyp.fsu hV hN
  obtain ⟨z, hzX, hz1⟩ : ∃ z ∈ fsuV T I ⊓ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have hzV : z ∈ fsuV T I := hzX.1
  have hzΩ : z ∈ quasithinOmegaOneCenter T := hzX.2
  have hz2 : z ^ 2 = 1 := hV.2 z hzV
  have hzc : z ∈ centerOf H := omegaOneCenter_le_center hC58 h317 h37 h38 h39 h3228 hyp hTL hH hzΩ
  have hHz : H ≤ Subgroup.centralizer ({z} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp hzc.2 h hh).symm
  have hTc : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.2
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp (hTc hzΩ) t ht).symm
  exact ⟨z, hz1, hz2, hzV, hHz, hTz⟩

theorem cov_pCoreL_le_H {G : Type} [Group G] [Finite G] {T L H : Subgroup G}
    (hsyl : quasithinIsSylowTwo T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTH : T ≤ H) :
    pCoreOf 2 L ≤ H := by
  have hidx : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index := by
    have h1 : (T.subgroupOf (L ⊔ T)).index ∣ T.index :=
      ⟨(L ⊔ T).index, (Subgroup.relIndex_mul_index le_sup_right).symm⟩
    exact fun h => hsyl.2 (h.trans h1)
  have hO2LT : pCoreOf 2 (L ⊔ T) ≤ T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right hsyl.1 hidx
  have hnorm : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hO2LT' : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hnorm
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact hO2LT'.trans (hO2LT.trans hTH)

theorem cov_P_le_H {G : Type} [Group G] [Finite G] {L H : Subgroup G}
    (hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3) (hO2H : pCoreOf 2 L ≤ H)
    {x0 : G} (hx0L : x0 ∈ L) (hx0H : x0 ∈ H) (hx0P : x0 ∈ res822P L) (hx03 : orderOf x0 = 3) :
    res822P L ≤ H := by
  intro p hp
  obtain ⟨j, hjH, o, hoO, rfl⟩ := res822_decomp hcenter3 hx0L hx0H hx0P hx03 p hp
  exact H.mul_mem hjH (hO2H hoO)

theorem cov_P9 {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3) :
    ¬ 9 ∣ Nat.card (res822P L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomap : Nat.card ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker *
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    card_comap_kz3 _ (QuotientGroup.mk'_surjective _) _
  have hP : Nat.card (res822P L) = Nat.card ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
    Subgroup.card_map_of_injective L.subtype_injective
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hP, hcomap, QuotientGroup.ker_mk', hk, hcenter3]
  intro h9
  have h3 : 3 ∣ 2 ^ k := by
    have : 3 * 3 ∣ 3 * 2 ^ k := by
      have e : 2 ^ k * 3 = 3 * 2 ^ k := by ring
      rw [← e]
      exact h9
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem cov_inf_pCoreOf_le {G : Type} [Group G] [Finite G] {Lz L : Subgroup G} (hLzL : Lz ≤ L) :
    Lz ⊓ pCoreOf 2 L ≤ pCoreOf 2 Lz := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnY, hnO⟩ := hn
    refine ⟨Lz.mul_mem (Lz.mul_mem g.2 hnY) (Lz.inv_mem g.2), ?_⟩
    have hgN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hLzL g.2)
    have key := (Subgroup.mem_normalizer_iff.mp hgN (n : G)).mp hnO
    simpa using key
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right

theorem cov_comm_pCoreOf {G : Type} [Group G] [Finite G] {Lz L : Subgroup G} {y : G}
    (hLzL : Lz ≤ L) (hyP : y ∈ res822P L) (hyLz : y ∈ Lz) :
    ∀ l ∈ Lz, y⁻¹ * l⁻¹ * y * l ∈ pCoreOf 2 Lz := by
  intro l hl
  have hyL : y ∈ L := hLzL hyLz
  have h1 := (res822_mk_mem_center_iff_G L hyL).mp ((res822_mem_P_iff L y).mp hyP).2 l (hLzL hl)
  have h2 : y⁻¹ * l⁻¹ * y * l ∈ Lz :=
    Lz.mul_mem (Lz.mul_mem (Lz.mul_mem (Lz.inv_mem hyLz) (Lz.inv_mem hl)) hyLz) hl
  exact cov_inf_pCoreOf_le hLzL ⟨h2, h1⟩

end CFSG.Quasithin.H13

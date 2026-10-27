module

public import CFSG.Quasithin.Vol2.Ch12Sec7L23d
public import CFSG.Quasithin.Vol2.Ch9Sec2KStar
public import CFSG.Quasithin.Vol2.Ch9FactsOdd
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem exists_hall_three (h1222 : Stmt12_2_2)
    (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8) (h331 : Stmt3_3_1) (hE : E2.E22StatementC)
    (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) (h22 : Lemma12_7_22)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ C : Subgroup G,
      QuasithinUnique.Lin2.IsHallTwoPrimeOf C (H ⊓ Subgroup.normalizer (L : Set G)) ∧
        Nat.card C = 3 := by
  have hy := hS.hyp.hyp
  have hn2 := nParam_eq_two h1222 h1211 h10 h11 h22 hS hHs hHz
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hmin := minParabolic_H h331 hS hHs
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hy.qtke hy.simple hy.nonabelian hHs.1.2
  obtain ⟨m, -, -, hB⟩ :=
    E2.e22BorelLift hE (E2.e22TorusCover_of_facts e22TorusFacts_holds) hmin hSQ hn1
  obtain ⟨-, R, -, -, -, ⟨C, hCM, hCodd, hCidx⟩, -⟩ := hB
  have hC3 := (nParam_le_two h1222 h1211 hS hHs hHz).2 hn2 C hCM hCodd hCidx
  have hCle : Nat.card C ≤ 3 :=
    card_le_three h1222 h2 h128 hS hC3.2 (hCM.trans (inf_le_inf_right _ hHz) |>.trans
      (by rw [inf_comm]))
  refine ⟨C, ⟨hCM, hCodd, hCidx⟩, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC3.2
  have h1 : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot _).2 hC3.1
  rw [hn] at h1 hCle ⊢
  rcases n with _ | _ | n
  · norm_num at h1
  · norm_num
  · have : 3 ^ 2 ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_comp_H
    (h1222 : Stmt12_2_2) (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8) (h331 : Stmt3_3_1)
    (hE : E2.E22StatementC) (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h22 : Lemma12_7_22) {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z)
    {H : Subgroup G} (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ K : Subgroup G, H = K ⊔ T ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      IsPGroup 2 (kerIn (H ⊓ Subgroup.normalizer (L : Set G)) H) ∧
      (IsPSL 2 2 2 ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) ∨
        IsPSL 3 2 2 ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)) := by
  have hy := hS.hyp.hyp
  have hn2 := nParam_eq_two h1222 h1211 h10 h11 h22 hS hHs hHz
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hmin := minParabolic_H h331 hS hHs
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hy.qtke hy.simple hy.nonabelian hHs.1.2
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd (E1.solvable_nParam_le_one hs) (not_le.mpr hn1)
  have hTX : T ≤ H ⊓ Subgroup.normalizer (L : Set G) := le_inf hHs.1.1 hy.normalizes
  have hTXs : QuasithinUnique.IsSylowTwoOf T (H ⊓ Subgroup.normalizer (L : Set G)) :=
    ⟨hTX, hy.sylow.1, fun h => hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTX))⟩
  obtain ⟨C, hC, hC3⟩ := exists_hall_three h1222 h1211 h128 h331 hE h2 h10 h11 h22 hS hHs hHz
  obtain ⟨K, -, hHK, hTK, hJ, -, htype⟩ := Ch9.KStar.exists_comp (n := 2) hE
    Ch9.FactsOdd.factBorelOddLarge_holds hmin hSQ hns inf_le_left hTX hTXs hn1 le_rfl
    (by rw [hn2]; norm_num) hC (by rw [hC3]; norm_num)
  refine ⟨K, hHK, hTK, hJ, ?_⟩
  rcases htype with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact absurd h Vol2.Ch10.SecB.C11AmS.not_isSz_two
  · exact Or.inr h

omit [Finite G] in
theorem kerIn_eq_pCoreOf {H X : Subgroup G} (hXH : X ≤ H) (hJ : IsPGroup 2 (kerIn X H))
    (hO : pCoreOf 2 H ≤ X) : kerIn X H = pCoreOf 2 H := by
  refine le_antisymm
    (le_pCoreOf_of_le_normalizer 2 (kerIn_le.trans hXH) (le_normalizer_kerIn X H) hJ) ?_
  intro x hx b hb
  exact hO ((Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hb) x).1 hx)

omit [Finite G] in
theorem pCoreOf_subgroupOf (H : Subgroup G) : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H :=
  CFSG.openPCoreOf_subgroupOf 2 H

theorem isPSL_map_of_eq {Y : Type} [Group Y] {N₁ N₂ : Subgroup Y} [N₁.Normal] [N₂.Normal]
    (h : N₁ = N₂) (A : Subgroup Y) {n p e : ℕ}
    (hA : IsPSL n p e ↥(A.map (QuotientGroup.mk' N₁))) :
    IsPSL n p e ↥(A.map (QuotientGroup.mk' N₂)) := by
  subst h
  exact hA

theorem eq_oTwoUpper_of_isSimpleGroup {Y : Type} [Group Y] {A : Subgroup Y}
    (hs : IsSimpleGroup ↥A) {a : Y} (ha : a ∈ A) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) :
    A = oTwoUpper A := by
  have hN : ((oTwoUpper A).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le A)).2 (le_normalizer_oTwoUpper A)
  have := hs
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oTwoUpper A).subgroupOf A) with h | h
  · exfalso
    have hmem : (⟨a, ha⟩ : ↥A) ∈ (oTwoUpper A).subgroupOf A :=
      Subgroup.mem_subgroupOf.2 (mem_oTwoUpper_of_odd ha hao)
    rw [h, Subgroup.mem_bot] at hmem
    exact ha1 (congrArg Subtype.val hmem)
  · refine le_antisymm (fun x hx => ?_) (oTwoUpper_le A)
    have hmem : (⟨x, hx⟩ : ↥A) ∈ (oTwoUpper A).subgroupOf A := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

theorem oTwoUpper_eq_map {H K T : Subgroup G} (hHK : H = K ⊔ T) (hT2 : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))))
    (h3 : 3 ∣ Nat.card ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) :
    oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) =
      (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨a, ha⟩, ha3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  rw [Subgroup.orderOf_mk] at ha3
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha3
    norm_num at ha3
  have hKo := eq_oTwoUpper_of_isSimpleGroup hs ha ha1 (by rw [ha3]; decide)
  refine (eq_oTwoUpper_of_pow_mem le_top (fun x _ => ?_) hKo).symm
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have hh : (h : G) ∈ K ⊔ T := by
    rw [← hHK]
    exact h.2
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hT2 hTK hh
  refine ⟨k, h ^ 2 ^ k, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hk
  · rw [map_pow]
    rfl

theorem lemma12_7_23_two
    (h1222 : Stmt12_2_2) (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8) (h331 : Stmt3_3_1)
    (hE : E2.E22StatementC) (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h22 : Lemma12_7_22) {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z)
    {H : Subgroup G} (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) ∨
      IsPSL 3 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) := by
  have hy := hS.hyp.hyp
  obtain ⟨K, hHK, hTK, hJ, htype⟩ :=
    exists_comp_H h1222 h1211 h128 h331 hE h2 h10 h11 h22 hS hHs hHz
  have hTX : T ≤ H ⊓ Subgroup.normalizer (L : Set G) := le_inf hHs.1.1 hy.normalizes
  have hO : pCoreOf 2 H ≤ H ⊓ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_H hS hHs)).trans hTX
  have hJ' : (kerIn (H ⊓ Subgroup.normalizer (L : Set G)) H).subgroupOf H = CFSG.pCore 2 ↥H := by
    rw [kerIn_eq_pCoreOf inf_le_left hJ hO, pCoreOf_subgroupOf]
  have htype' : IsPSL 2 2 2 ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ∨
      IsPSL 3 2 2 ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :=
    htype.imp (isPSL_map_of_eq hJ' (K.subgroupOf H)) (isPSL_map_of_eq hJ' (K.subgroupOf H))
  have hs : IsSimpleGroup ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
    rcases htype' with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2
  have h3 : 3 ∣ Nat.card ↥((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
    rcases htype' with h | h
    · rw [card_of_statedPSL (by norm_num) h]
      decide
    · rw [card_of_statedPSL (by norm_num) h]
      decide
  rw [oTwoUpper_eq_map hHK hy.sylow.1 hTK hs h3]
  exact htype'

end S127

open S127 in
theorem lemma12_7_23_of
    (h1222 : Stmt12_2_2) (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8) (h331 : Stmt3_3_1)
    (hE : E2.E22StatementC) (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h22 : Lemma12_7_22) : Lemma12_7_23 := by
  intro G _ _ T L V t z hS H hHs hHz
  exact ⟨nParam_eq_two h1222 h1211 h10 h11 h22 hS hHs hHz,
    lemma12_7_23_two h1222 h1211 h128 h331 hE h2 h10 h11 h22 hS hHs hHz,
    lemma12_7_23_three h1222 h1211 h128 h331 hE h2 h10 h11 h22 hS hHs hHz⟩

end CFSG.Quasithin.H13

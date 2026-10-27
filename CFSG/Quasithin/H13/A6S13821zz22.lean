module

public import CFSG.RankThree.PartOne.D4RC.RxOrder
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.A3Structure318Star
public import CFSG.Quasithin.H13.A6S13816b
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank

namespace A6S20

theorem pow_eight_le_sl3 {q : ℕ} (hq : 1 ≤ q) :
    (q - 1) ^ 8 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h1 : q - 1 ≤ q := Nat.sub_le q 1
  have h2 : (q - 1) ^ 2 ≤ q ^ 2 - 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    omega
  have h3 : (q - 1) ^ 3 ≤ q ^ 3 - 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : r ^ 3 + 1 ≤ (r + 1) ^ 3 := by nlinarith [sq_nonneg r]
    omega
  calc (q - 1) ^ 8 = (q - 1) ^ 3 * ((q - 1) ^ 2 * (q - 1) ^ 3) := by ring
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left h1 3) (Nat.mul_le_mul h2 h3)

theorem pow_eight_le_su3 {q : ℕ} (hq : 1 ≤ q) :
    (q - 1) ^ 8 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h := pow_eight_le_sl3 hq
  calc (q - 1) ^ 8 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := h
    _ ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)

theorem exists_slPi_of_case2List {Q : Type} [Group Q] [Finite Q]
    (hL : A36Case2List Q) (hZ : Nat.card (Subgroup.center Q) = 3)
    (hc : Nat.card (Q ⧸ Subgroup.center Q) = 20160 ∨
      Nat.card (Q ⧸ Subgroup.center Q) = 5515776) :
    ∃ (π : Bool) (f : ℕ) (F : Type) (_ : Field F), PiField π 2 f F ∧ ModThree π (2 ^ f) ∧
      2 < 2 ^ f ∧ ((π = true ∧ f = 2) ∨ (π = false ∧ f = 3)) ∧
      Nonempty (Q ≃* slPi π 3 (2 ^ f) F) := by
  have hQc : Nat.card Q = Nat.card (Q ⧸ Subgroup.center Q) * 3 := by
    rw [← hZ]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hQ : Nat.card Q = 60480 ∨ Nat.card Q = 16547328 := by
    rcases hc with h | h <;> [left; right] <;> rw [hQc, h]
  rcases hL with ⟨s, p, e, hp, he, hpe, hSL⟩ | ⟨-, -, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩
  · obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ e := ⟨_, rfl⟩
    have hq1 : 2 ≤ q := hqdef ▸ (Nat.le_self_pow (by omega) p).trans' hp.two_le
    have hp2 : ∀ {k : ℕ}, q = 2 ^ k → 1 ≤ k → p = 2 := by
      intro k hk hk1
      have h2 : p ∣ 2 ^ k := by
        rw [← hk, hqdef]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    cases s
    ·
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hSL
      have : Fact p.Prime := ⟨hp⟩
      have : CharP K p := by
        have := Fintype.ofFinite K
        refine charP_of_card_eq_prime_pow (f := 2 * e) ?_
        rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
      have hcU := CFSG.RankThree.PartOne.D4RC.rcl_card_statedSU_three (f := e) hK
      rw [← Nat.card_congr φ.toEquiv, ← hqdef] at hcU
      have hlow := pow_eight_le_su3 (q := q) (by omega)
      have hq8 : q ≤ 8 := by
        by_contra h
        push Not at h
        have h9 : 8 ^ 8 ≤ (q - 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
        rw [← hcU] at hlow
        rcases hQ with h' | h' <;> rw [h'] at hlow <;> omega
      have key : q = 8 := by
        interval_cases q <;> rcases hQ with h' | h' <;> rw [h'] at hcU <;>
          first | rfl | (norm_num at hcU)
      have hp' : p = 2 := hp2 (k := 3) (by rw [key]; norm_num) (by norm_num)
      subst hp'
      have he3 : e = 3 := by
        have : (2 : ℕ) ^ e = 2 ^ 3 := by rw [← hqdef, key]; norm_num
        exact Nat.pow_right_injective le_rfl this
      subst he3
      refine ⟨false, 3, K, inferInstance, ⟨Nat.prime_two, by norm_num, ?_⟩,
        (by show 2 ^ 3 % 3 = 2; norm_num), by norm_num, Or.inr ⟨rfl, rfl⟩, ⟨φ⟩⟩
      rw [hK]
      rfl
    ·
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hSL
      have hcL : Nat.card Q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        rw [Nat.card_congr φ.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
          CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num),
          show 3 * (3 - 1) / 2 = 3 by rfl, show Finset.Icc 2 3 = {2, 3} by decide,
          Finset.prod_pair (by norm_num), hK, hqdef]
      have hlow := pow_eight_le_sl3 (q := q) (by omega)
      have hq8 : q ≤ 8 := by
        by_contra h
        push Not at h
        have h9 : 8 ^ 8 ≤ (q - 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
        rw [← hcL] at hlow
        rcases hQ with h' | h' <;> rw [h'] at hlow <;> omega
      have key : q = 4 := by
        interval_cases q <;> rcases hQ with h' | h' <;> rw [h'] at hcL <;>
          first | rfl | (norm_num at hcL)
      have hp' : p = 2 := hp2 (k := 2) (by rw [key]; norm_num) (by norm_num)
      subst hp'
      have he2 : e = 2 := by
        have : (2 : ℕ) ^ e = 2 ^ 2 := by rw [← hqdef, key]; norm_num
        exact Nat.pow_right_injective le_rfl this
      subst he2
      refine ⟨true, 2, K, inferInstance, ⟨Nat.prime_two, by norm_num, ?_⟩,
        (by show 2 ^ 2 % 3 = 1; norm_num), by norm_num, Or.inl ⟨rfl, rfl⟩, ⟨φ⟩⟩
      rw [hK]
      rfl
  ·
    exfalso
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hc
    rcases hc with h | h <;> revert h <;> decide
  ·
    exfalso
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hc
    rcases hc with h | h <;> revert h <;> decide
  ·
    exfalso
    have hM : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr φ.toEquiv, hM] at hc
    omega

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_slPi_13820 (h36 : A36ForSQTK) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKN : H ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3)
    (hc : Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 20160 ∨
      Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 5515776) :
    ∃ (π : Bool) (f : ℕ) (F : Type) (_ : Field F), PiField π 2 f F ∧ ModThree π (2 ^ f) ∧
      2 < 2 ^ f ∧ ((π = true ∧ f = 2) ∨ (π = false ∧ f = 3)) ∧
      Nonempty (↥(S.KSt H K) ≃* slPi π 3 (2 ^ f) F) := by
  have hSQ : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hA := h36 _ (SQTKHyp.of_sqtkGroup ↥H hSQ)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  obtain ⟨e₁⟩ := Vol2.Ch11.SecA.quotPCore_subgroupOf_equiv (L := K) hKH
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm hq
  obtain ⟨-, hcases⟩ := A318.lBar_structure hA (subgroupOf_mem_cComp hK) hq'
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hZc : Nat.card (Subgroup.center ↥(modO2Image H K)) = 3 := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective, hZ]
  have hlist : A36Case2List ↥(modO2Image H K) := by
    rcases hcases with ⟨hb, -⟩ | ⟨-, h⟩
    · exfalso
      have hb' : Subgroup.center ↥(modO2Image H K) = ⊥ := hb
      rw [hb', Subgroup.card_bot] at hZc
      omega
    · exact h
  have hcc : Nat.card (↥(modO2Image H K) ⧸ Subgroup.center ↥(modO2Image H K)) =
      Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Nat.card_congr (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).toEquiv
  obtain ⟨π, f, F, _, hF, hq3, hq2, hπf, ⟨φ⟩⟩ :=
    A6S20.exists_slPi_of_case2List hlist hZc (by rw [hcc]; exact hc)
  obtain ⟨e₂⟩ := S.kst_equiv hS hH hK
  exact ⟨π, f, F, inferInstance, hF, hq3, hq2, hπf, ⟨(e₂.symm.trans e).trans φ⟩⟩

end Setting4

end CFSG.Quasithin.H13.A6

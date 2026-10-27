module

public import CFSG.Walter.ReeOrder.WardLocal.P1c

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {k : ℕ} (hq : q = 3 ^ (2 * k + 1))
  (hK : Fintype.card K = q) (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))

@[expose] noncomputable def CC (S : WardSetup G PSL(2, K) q (-1)) (hq : q = 3 ^ (2 * k + 1))
    (hK : Fintype.card K = q) (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
    (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) : Subgroup G where
  carrier := {x | x ∈ PP1 S ∧ S.J * x * S.J⁻¹ = x⁻¹}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    calc S.J * (a * b) * S.J⁻¹ = (S.J * a * S.J⁻¹) * (S.J * b * S.J⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, PP1_comm hq hK hcT hG (Subgroup.inv_mem _ ha)
          (Subgroup.inv_mem _ hb)]
  one_mem' := ⟨Subgroup.one_mem _, by group⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    calc S.J * a⁻¹ * S.J⁻¹ = (S.J * a * S.J⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [ha']

theorem mem_CC {x : G} : x ∈ CC S hq hK hcT hG ↔ x ∈ PP1 S ∧ S.J * x * S.J⁻¹ = x⁻¹ :=
  Iff.rfl

variable (hA : (AA S).card = q - 1)

include hA in
theorem AA_subset_CC {x : G} (hx : x ∈ AA S) : x ∈ CC S hq hK hcT hG :=
  ⟨(mem_AA.mp hx).1, J_inv_AA hq hK hcT hG hA hx⟩

theorem CC_inf_FF {x : G} (hx : x ∈ CC S hq hK hcT hG) (hxF : x ∈ FF S) : x = 1 := by
  obtain ⟨hxP, hxJ⟩ := (mem_CC hq hK hcT hG).mp hx
  have hJx : S.J * x * S.J⁻¹ = x := by
    rw [← FF_comm_J hxF, mul_assoc, mul_inv_cancel, mul_one]
  rw [hJx] at hxJ
  have h3 := PP1_pow_three hq hK hcT hG hxP
  have h2 : x ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hxJ]; exact mul_inv_cancel x
  have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
  rw [this, h3, h2, inv_one, one_mul]

theorem card_CC_mul_FF_le :
    Nat.card (CC S hq hK hcT hG) * Nat.card (FF S) ≤ Nat.card (PP1 S) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ ((mem_CC hq hK hcT hG).mp p.1.2).1
      (FF_le_PP1 hq hcT p.2.2)⟩) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  simp only [Subtype.mk.injEq] at h
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hc : a'⁻¹ * a ∈ CC S hq hK hcT hG := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha
  have hf : a'⁻¹ * a ∈ FF S := h1 ▸ Subgroup.mul_mem _ hb' (Subgroup.inv_mem _ hb)
  have he := CC_inf_FF hq hK hcT hG hc hf
  have haa : a = a' := by
    have := congrArg (fun t => a' * t) he
    simp only [mul_one, mul_inv_cancel_left] at this
    exact this
  subst haa
  have hbb : b = b' := by
    have := h
    exact mul_left_cancel this
  subst hbb
  rfl

include hA in
theorem card_CC : Nat.card (CC S hq hK hcT hG) = q := by
  have hle := card_CC_mul_FF_le hq hK hcT hG
  rw [card_FF, hK, card_PP1 hq hK hcT hG] at hle
  have hq0 : 0 < q := by rw [hq]; positivity
  have hle' : Nat.card (CC S hq hK hcT hG) ≤ q := by nlinarith
  have hge : q ≤ Nat.card (CC S hq hK hcT hG) := by
    have hsub : insert 1 (AA S) ⊆ (CC S hq hK hcT hG : Set G).toFinset := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rw [Set.mem_toFinset]
      rcases hx with rfl | hx
      · exact Subgroup.one_mem _
      · exact AA_subset_CC hq hK hcT hG hA hx
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (fun h => (mem_AA.mp h).2.1 rfl), hA,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] at this
    have hq1 : 1 ≤ q := by omega
    rw [Nat.sub_add_cancel hq1] at this
    simpa using this
  omega

include hA in
theorem mem_AA_of_mem_CC {x : G} (hx : x ∈ CC S hq hK hcT hG) (hx1 : x ≠ 1) : x ∈ AA S := by
  by_contra hxA
  have hsub : insert x (insert 1 (AA S)) ⊆ (CC S hq hK hcT hG : Set G).toFinset := by
    intro y hy
    simp only [Finset.mem_insert] at hy
    rw [Set.mem_toFinset]
    rcases hy with rfl | rfl | hy
    · exact hx
    · exact Subgroup.one_mem _
    · exact AA_subset_CC hq hK hcT hG hA hy
  have := Finset.card_le_card hsub
  have hcc : Nat.card ((CC S hq hK hcT hG : Set G)) = q := card_CC hq hK hcT hG hA
  rw [Finset.card_insert_of_notMem (by simp [hx1, hxA]),
    Finset.card_insert_of_notMem (fun h => (mem_AA.mp h).2.1 rfl), hA, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, hcc] at this
  have hq0 : 0 < q := by rw [hq]; positivity
  omega

variable (hC1 : ∀ x : G, Odd (orderOf x) → 3 ∣ orderOf x →
  Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 3)

include hC1 in
omit [Fintype K] [DecidableEq K] [CharP K 3] in
theorem card_centralizer_dvd_q3 {x : G} (hx3 : orderOf x = 3)
    (hinv : ∀ t : G, orderOf t = 2 → x * t ≠ t * x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ q ^ 3 := by
  have hcdvd := hC1 x (by rw [hx3]; decide) (by rw [hx3])
  have hcodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G))
      2 h2
    apply hinv t (by rw [Subgroup.orderOf_coe]; exact ht)
    exact (Subgroup.mem_centralizer_singleton_iff.mp t.2).symm
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hcodd)) hcdvd

include hq hK hcT hG hA hC1 in
theorem centralizer_AA {x : G} (hx : x ∈ AA S) :
    IsPGroup 3 (Subgroup.centralizer ({x} : Set G)) ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = q ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := (isPGroup_PP1 (S := S)).exists_le_sylow
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hPc : 1 < Nat.card P := by
    rw [card_sylow3 hq hG P]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨z, hz, hz1⟩ := exists_zcen_ne_one P hPc
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mem_zcen.mp hz).2 p hp).symm
  have hzP1 : z ∈ PP1 S := zcen_le_PP1 hq hcT hP (FF_le_PP1 hq hcT) hz
  have hzinv : ∀ t : G, orderOf t = 2 → z * t ≠ t * z :=
    fun t ht h => zcen_no_involution hq hK hcT hG hz hz1 ht h
  have hz3 : orderOf z = 3 := orderOf_eq_prime (PP1_pow_three hq hK hcT hG hzP1) hz1
  have hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) ≤ q ^ 3 :=
    Nat.le_of_dvd (by positivity) (card_centralizer_dvd_q3 hC1 hz3 hzinv)
  have hPeq : (P : Subgroup G) = Subgroup.centralizer ({z} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_sylow3 hq hG P]; exact hcz)
  have hzA : z ∈ AA S := mem_AA.mpr ⟨hzP1, hz1, hzinv, by
    rw [← hPeq, card_sylow3 hq hG P]
    exact Nat.pow_lt_pow_right (by omega) (by norm_num)⟩
  obtain ⟨w, -, hw⟩ := AA_transitive hq hK hcT hG hA hzA hx
  have hconj : IsConj x z := isConj_iff.mpr ⟨w⁻¹, by rw [← hw]; group⟩
  have hcx : Nat.card (Subgroup.centralizer ({x} : Set G)) = q ^ 3 := by
    rw [card_centralizer_of_isConj hconj, ← hPeq, card_sylow3 hq hG P]
  refine ⟨IsPGroup.of_card (n := 3 * (2 * k + 1)) ?_, hcx⟩
  rw [hcx, hq, ← pow_mul, mul_comm]

include hA in
theorem conj_mem_CC {n x : G} (hn : n ∈ Subgroup.normalizer (PP1 S : Set G))
    (hx : x ∈ CC S hq hK hcT hG) : n * x * n⁻¹ ∈ CC S hq hK hcT hG := by
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · exact AA_subset_CC hq hK hcT hG hA
      (conj_mem_AA hn (mem_AA_of_mem_CC hq hK hcT hG hA hx hx1))

include hq hK hcT hG hA in
theorem card_N1 {x : G} (hx : x ∈ AA S) :
    Nat.card (Subgroup.normalizer (PP1 S : Set G)) = (q - 1) *
      Nat.card (Subgroup.normalizer (PP1 S : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) := by
  rw [← hA]
  apply card_eq_card_mul_centralizer _ _ (fun n hn y hy => conj_mem_AA hn hy) _ hx
  intro y hy z hz
  obtain ⟨w, hw, hwz⟩ := AA_transitive hq hK hcT hG hA hy hz
  exact ⟨w, WW_le_normalizer_PP1 hq hcT hw, hwz⟩

end CFSG.Walter.WardLocal

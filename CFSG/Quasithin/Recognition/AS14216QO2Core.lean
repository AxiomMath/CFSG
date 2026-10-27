module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.AS14216

variable {G : Type*} [Group G]

theorem mem_centralizer_singleton_iff' {g k : G} :
    g ∈ Subgroup.centralizer {k} ↔ k * g = g * k :=
  Subgroup.mem_centralizer_singleton_iff.trans eq_comm

theorem card_modEq_card_inf_centralizer [Finite G] {W : Subgroup G} {k : G} (hk : k ^ 5 = 1)
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card W ≡ Nat.card ↥(W ⊓ Subgroup.centralizer {k}) [MOD 5] := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fintype ↥W := Fintype.ofFinite _
  have hmem : ∀ w ∈ W, k * w * k⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hkW w).mp hw
  let f : Function.End ↥W := fun w => ⟨k * w * k⁻¹, hmem w w.2⟩
  have hpow : ∀ (n : ℕ) (w : ↥W), ((f ^ n) w : G) = k ^ n * w * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp; rfl
    | succ n ih =>
      intro w
      rw [pow_succ]
      show (((f ^ n) (f w)) : G) = _
      rw [ih]
      simp only [f]
      group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hpow, hk]
    simp
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have he : Nat.card (Function.fixedPoints f) =
      Nat.card ↥(W ⊓ Subgroup.centralizer {k}) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, Subgroup.mem_inf.mpr ⟨w.1.2, ?_⟩⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.mp c.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have hw : f w.1 = w.1 := w.2
      have hw' : k * (w.1 : G) * k⁻¹ = w.1 := congrArg Subtype.val hw
      rw [mem_centralizer_singleton_iff']
      calc k * (w.1 : G) = k * w.1 * k⁻¹ * k := by group
        _ = w.1 * k := by rw [hw']
    · have hc : k * (c.1 : G) = c.1 * k :=
        mem_centralizer_singleton_iff'.mp (Subgroup.mem_inf.mp c.2).2
      show f ⟨c.1, _⟩ = ⟨c.1, _⟩
      apply Subtype.ext
      show k * (c.1 : G) * k⁻¹ = c.1
      rw [hc]
      group
  rw [← he]
  exact h

theorem eq_one_or_eq_of_card_le_two [Finite G] {W : Subgroup G} (hW : Nat.card W ≤ 2) {z c : G}
    (hz : z ∈ W) (hz1 : z ≠ 1) (hc : c ∈ W) : c = 1 ∨ c = z := by
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hcz⟩ := hne
  let f : Fin 3 → ↥W := ![1, ⟨z, hz⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab' ⊢
    all_goals first
      | exact absurd hab'.symm hz1 | exact absurd hab' hz1 | exact absurd hab'.symm hc1
      | exact absurd hab' hc1 | exact absurd hab'.symm hcz | exact absurd hab' hcz
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

theorem exists_card_eq_two_pow [Finite G] {Q W : Subgroup G} (hQ : Nat.card Q = 32) (hWQ : W ≤ Q) :
    ∃ a ≤ 5, Nat.card W = 2 ^ a := by
  have hd : Nat.card W ∣ 2 ^ 5 := by
    rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hQ]
    exact Subgroup.card_dvd_of_le hWQ
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hd

theorem eq_of_orderOf_five [Finite G] {Q W : Subgroup G} {k z : G} (hQ : Nat.card Q = 32)
    (hWQ : W ≤ Q) (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) (hk : orderOf k = 5)
    (hcomm : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W) (hnc : ¬ ∀ q ∈ Q, k * q = q * k)
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hzc : ∀ q ∈ Q, z * q = q * z)
    (hcen : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z)
    (hsq : ∃ q ∈ Q, q * q = z) : W = Q := by
  have hk5 : k ^ 5 = 1 := hk ▸ pow_orderOf_eq_one k
  have hkQ' : ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hkQ q).mp hq
  have hkQi : ∀ q ∈ Q, k⁻¹ * q * k ∈ Q := fun q hq => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkQ) q).mp hq
    simpa using this
  have hkz : k * z * k⁻¹ = z := by
    have hc : ∀ q ∈ Q, k * z * k⁻¹ * q = q * (k * z * k⁻¹) := by
      intro q hq
      have h1 := hzc _ (hkQi q hq)
      calc k * z * k⁻¹ * q = k * (z * (k⁻¹ * q * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * q * k) * z) * k⁻¹ := by rw [h1]
        _ = q * (k * z * k⁻¹) := by group
    rcases hcen _ (hkQ' z hzQ) hc with h | h
    · exfalso
      apply hz1
      calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hzC' : z ∈ Subgroup.centralizer {k} := by
    rw [mem_centralizer_singleton_iff']
    calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [hkz]
  have hzC : z ∈ Q ⊓ Subgroup.centralizer {k} := Subgroup.mem_inf.mpr ⟨hzQ, hzC'⟩
  have hcentQ : (∀ q ∈ Q, k * q = q * k) ↔ Q ⊓ Subgroup.centralizer {k} = Q := by
    constructor
    · intro h
      exact le_antisymm inf_le_left fun q hq =>
        Subgroup.mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff'.mpr (h q hq)⟩
    · intro h q hq
      rw [← h] at hq
      exact mem_centralizer_singleton_iff'.mp (Subgroup.mem_inf.mp hq).2
  have hCQ : Nat.card ↥(Q ⊓ Subgroup.centralizer {k}) = 2 := by
    have hmod := card_modEq_card_inf_centralizer hk5 hkQ
    obtain ⟨b, hb, hcb⟩ := exists_card_eq_two_pow hQ (inf_le_left : Q ⊓ _ ≤ Q)
    rw [hQ, hcb] at hmod
    interval_cases b
    all_goals first
      | (exfalso; revert hmod; decide)
      | exact hcb
      | (exfalso
         apply hnc
         refine hcentQ.mpr (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)
         rw [hQ, hcb]; norm_num)
  have hC12 : ∀ c ∈ Q ⊓ Subgroup.centralizer {k}, c = 1 ∨ c = z := fun c hc =>
    eq_one_or_eq_of_card_le_two hCQ.le hzC hz1 hc
  have hW1 : W ≠ ⊥ := by
    intro hb
    apply hnc
    intro q hq
    have := hcomm q hq
    rw [hb, Subgroup.mem_bot] at this
    calc k * q = k * q * k⁻¹ * q⁻¹ * (q * k) := by group
      _ = q * k := by rw [this, one_mul]
  have hmodW := card_modEq_card_inf_centralizer hk5 hkW
  obtain ⟨a, ha, hca⟩ := exists_card_eq_two_pow hQ hWQ
  by_cases hzW : z ∈ W
  · have hWC : Nat.card ↥(W ⊓ Subgroup.centralizer {k}) = 2 := by
      apply le_antisymm
      · rw [← hCQ]
        exact Subgroup.card_le_of_le (inf_le_inf_right _ hWQ)
      · have hne : W ⊓ Subgroup.centralizer {k} ≠ ⊥ := fun h => by
          have : z ∈ W ⊓ Subgroup.centralizer {k} := Subgroup.mem_inf.mpr ⟨hzW, hzC'⟩
          rw [h, Subgroup.mem_bot] at this
          exact hz1 this
        exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    rw [hca, hWC] at hmodW
    interval_cases a
    all_goals first
      | (exfalso; revert hmodW; decide)
      | skip
    swap
    · exact Subgroup.eq_of_le_of_card_ge hWQ (by rw [hQ, hca]; norm_num)
    exfalso
    have hW12 : ∀ c ∈ W, c = 1 ∨ c = z := fun c hc =>
      eq_one_or_eq_of_card_le_two (by rw [hca]; norm_num) hzW hz1 hc
    apply hnc
    intro q hq
    rcases hW12 _ (hcomm q hq) with h | h
    · calc k * q = k * q * k⁻¹ * q⁻¹ * (q * k) := by group
        _ = q * k := by rw [h, one_mul]
    · exfalso
      have h1 : k * q * k⁻¹ = z * q := by
        calc k * q * k⁻¹ = k * q * k⁻¹ * q⁻¹ * q := by group
          _ = z * q := by rw [h]
      have hzz : z * z = 1 := by
        have hc : ∀ q ∈ Q, z * z * q = q * (z * z) := fun q hq => by
          rw [mul_assoc, hzc q hq, ← mul_assoc, hzc q hq, mul_assoc]
        rcases hcen _ (Q.mul_mem hzQ hzQ) hc with h' | h'
        · exact h'
        · exact absurd (mul_eq_left.mp h') hz1
      have h2 : k ^ 2 * q * (k ^ 2)⁻¹ = q := by
        calc k ^ 2 * q * (k ^ 2)⁻¹ = k * (k * q * k⁻¹) * k⁻¹ := by
              simp only [pow_two, mul_inv_rev]; group
          _ = k * (z * q) * k⁻¹ := by rw [h1]
          _ = k * z * k⁻¹ * (k * q * k⁻¹) := by group
          _ = z * (z * q) := by rw [hkz, h1]
          _ = q := by rw [← mul_assoc, hzz, one_mul]
      have h3 : k = (k ^ 2) ^ 3 := by
        rw [← pow_mul]
        calc k = k ^ 5 * k := by rw [hk5, one_mul]
          _ = k ^ (2 * 3) := by rw [← pow_succ]
      have h4 : k * q * k⁻¹ = q := by
        rw [h3]
        calc (k ^ 2) ^ 3 * q * ((k ^ 2) ^ 3)⁻¹
            = k ^ 2 * (k ^ 2 * (k ^ 2 * q * (k ^ 2)⁻¹) * (k ^ 2)⁻¹) * (k ^ 2)⁻¹ := by group
          _ = q := by rw [h2, h2, h2]
      rw [h4] at h1
      exact hz1 (mul_eq_right.mp h1.symm)
  · have hWC : Nat.card ↥(W ⊓ Subgroup.centralizer {k}) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro c hc
      obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
      rcases hC12 c (Subgroup.mem_inf.mpr ⟨hWQ hc1, hc2⟩) with h | h
      · exact (Subgroup.mem_bot).mpr h
      · exact absurd (h ▸ hc1) hzW
    rw [hca, hWC] at hmodW
    interval_cases a
    all_goals first
      | (exfalso; revert hmodW; decide)
      | skip
    ·
      exact absurd (Subgroup.card_eq_one.mp hca) hW1
    ·
      exfalso
      obtain ⟨q, hq, hqq⟩ := hsq
      have hidx : (W.subgroupOf Q).index = 2 := by
        have h := (W.subgroupOf Q).card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv, hca, hQ] at h
        omega
      have := Subgroup.sq_mem_of_index_two hidx ⟨q, hq⟩
      rw [Subgroup.mem_subgroupOf, pow_two] at this
      exact hzW (hqq ▸ this)

end CFSG.Quasithin.AS14216

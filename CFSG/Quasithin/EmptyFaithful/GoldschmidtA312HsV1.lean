module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesExtra

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin
open scoped Pointwise

theorem hsV1Mul_lt : ∀ i < 64, ∀ k < 64, hsV1Mul i k < 64 := by
  decide +kernel

@[expose] def hsV1M (i k : Fin 64) : Fin 64 := ⟨hsV1Mul i k % 64, Nat.mod_lt _ (by norm_num)⟩

theorem hsV1M_val : ∀ i k : Fin 64, (hsV1M i k).1 = hsV1Mul i k := by
  decide +kernel

theorem hsV1M_facts :
    hsV1M 0 0 = 0 ∧ (∀ k, hsV1M 16 k = hsV1M k 16) ∧ hsV1M 16 16 = 32 ∧ hsV1M 32 32 = 0 ∧
    (∀ i k : Fin 64, i.1 / 16 % 2 = 0 → k.1 / 16 % 2 = 0 → (hsV1M i k).1 / 16 % 2 = 0) ∧
    (∀ i : Fin 64, i.1 / 16 % 2 = 0 → hsV1M i i = 0 ∨ hsV1M i i = 32) ∧
    (∀ i k : Fin 64, i.1 / 16 % 2 = 0 → k.1 / 16 % 2 = 0 →
      hsV1M i k = hsV1M k i ∨ hsV1M i k = hsV1M 32 (hsV1M k i)) ∧
    (∀ i : Fin 64, i.1 / 16 % 2 = 0 → (∀ k : Fin 64, k.1 / 16 % 2 = 0 → hsV1M i k = hsV1M k i) →
      i = 0 ∨ i = 32) ∧
    (Finset.univ.filter fun i : Fin 64 => i.1 / 16 % 2 = 0).card = 32 := by
  decide +kernel

theorem isZ4StarExtra2_of_idx {G : Type} [Group G] (idx : Fin 64 ≃ G)
    (hm : ∀ (i k : Fin 64) (hik : hsV1Mul i k < 64), idx ⟨hsV1Mul i k, hik⟩ = idx i * idx k) :
    IsZ4StarExtra2 G := by
  classical
  have : Finite G := Finite.of_equiv (Fin 64) idx
  obtain ⟨T0, T1, T2, T3, T4, T5, T6, T7, T8⟩ := hsV1M_facts
  have hmm : ∀ i k, idx (hsV1M i k) = idx i * idx k := fun i k => by
    have := hm i k (hsV1Mul_lt i i.2 k k.2)
    rw [← this]
    exact congrArg idx (Fin.ext (hsV1M_val i k))
  have h00 : idx 0 = 1 := by
    have := hmm 0 0
    rw [T0] at this
    exact mul_eq_left.mp this.symm
  have hcc : ∀ g : G, g * idx 16 = idx 16 * g := by
    intro g
    obtain ⟨k, rfl⟩ := idx.surjective g
    rw [← hmm, ← hmm, T1 k]
  have hc2 : idx 16 ^ 2 = idx 32 := by rw [pow_two, ← hmm, T2]
  have hc4 : idx 16 ^ 4 = 1 := by
    have : idx 16 ^ 4 = idx 32 * idx 32 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc2, pow_two]
    rw [this, ← hmm, T3, h00]
  have h32 : idx 32 ≠ 1 := by
    intro h
    rw [← h00] at h
    exact absurd (Fin.ext_iff.mp (idx.injective h)) (by decide)
  have hord : orderOf (idx 16) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := idx 16)
      (by rw [pow_one, hc2]; exact h32) (by simpa using hc4)
    simpa using h
  let S : Set G := {g | ∃ i : Fin 64, i.1 / 16 % 2 = 0 ∧ idx i = g}
  have hS2 : S * S = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ⟨i, hi, rfl⟩, b, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨hsV1M i k, T4 i k hi hk, hmm i k⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨idx i, ⟨i, hi, rfl⟩, idx 0, ⟨0, by decide, rfl⟩, by simp [h00]⟩
  let E : Subgroup G := subgroupOfIdempotent S ⟨idx 0, 0, by decide, rfl⟩ hS2
  have hE : ∀ g, g ∈ E ↔ ∃ i : Fin 64, i.1 / 16 % 2 = 0 ∧ idx i = g := fun g => Iff.rfl
  have hEi : ∀ i : Fin 64, idx i ∈ E ↔ i.1 / 16 % 2 = 0 := fun i => by
    rw [hE]
    constructor
    · rintro ⟨j, hj, hji⟩
      rw [← idx.injective hji]
      exact hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  have hcardE : Nat.card E = 32 := by
    have e : {i : Fin 64 // i.1 / 16 % 2 = 0} ≃ ↥E :=
      idx.subtypeEquiv (fun i => (hEi i).symm)
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact T8
  have hcE : idx 16 ∉ E := by
    rw [hEi]
    decide
  have hz0E : idx 32 ∈ E := (hEi 32).mpr (by decide)
  let Z : Subgroup G := Subgroup.zpowers (idx 16)
  have hcardZ : Nat.card Z = 4 := by rw [Nat.card_zpowers, hord]
  have hZc : Z ≤ Subgroup.center G := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact fun g => hcc g
  have hcardG : Nat.card G = 64 := by
    rw [← Nat.card_congr idx, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hZE : Nat.card ↥(Z ⊓ E) = 2 := by
    have hd4 : Nat.card ↥(Z ⊓ E) ∣ 4 := hcardZ ▸ Subgroup.card_dvd_of_le inf_le_left
    have hz0Z : idx 32 ∈ Z := by
      rw [← hc2]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    have hzo : orderOf (idx 32) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two, ← hmm, T3, h00]) h32
    have hd2 : 2 ∣ Nat.card ↥(Z ⊓ E) := by
      have hle : Subgroup.zpowers (idx 32) ≤ Z ⊓ E :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hz0Z, hz0E⟩)
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hzo] at this
    have hne : Nat.card ↥(Z ⊓ E) ≠ 4 := by
      intro h4
      have heq : Z ⊓ E = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hcardZ])
      have hcmem : idx 16 ∈ Z ⊓ E := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact hcE (Subgroup.mem_inf.mp hcmem).2
    have hpos : 0 < Nat.card ↥(Z ⊓ E) := Nat.card_pos
    have hle4 : Nat.card ↥(Z ⊓ E) ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    interval_cases h : Nat.card ↥(Z ⊓ E) <;> omega
  have hZEtop : Z ⊔ E = ⊤ := by
    have hd : Nat.card ↥(Z ⊔ E) ∣ 64 := hcardG ▸ Subgroup.card_subgroup_dvd_card (Z ⊔ E)
    have hd32 : 32 ∣ Nat.card ↥(Z ⊔ E) := hcardE ▸ Subgroup.card_dvd_of_le le_sup_right
    have hne : Nat.card ↥(Z ⊔ E) ≠ 32 := by
      intro h32'
      have heq : Z ⊔ E = E := (Subgroup.eq_of_le_of_card_ge le_sup_right
        (by rw [h32', hcardE])).symm
      exact hcE (heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers (idx 16)))
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hcardG]
    have hmem : Nat.card ↥(Z ⊔ E) ∈ Nat.divisors 64 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have h2 : Nat.divisors 64 = {1, 2, 4, 8, 16, 32, 64} := by decide
    rw [h2] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h <;> omega
  have hext : IsExtraspecial2 2 ↥E := by
    let z : ↥E := ⟨idx 32, hz0E⟩
    have hzcent : ∀ g : G, g * idx 32 = idx 32 * g := fun g => by
      rw [← hc2, pow_two, ← mul_assoc, hcc g, mul_assoc, hcc g, mul_assoc]
    have hel : ∀ x : ↥E, ∃ i : Fin 64, i.1 / 16 % 2 = 0 ∧ idx i = x.1 := fun x => (hE _).mp x.2
    refine A312ExtShapes.isExtraspecial2_of_central_involution z ?_ ?_ ?_ ?_ ?_
      (hcardE.trans (by norm_num)) (by norm_num)
    · intro h
      exact h32 (congrArg Subtype.val h)
    · intro y
      exact Subtype.ext (hzcent y.1)
    · intro x
      obtain ⟨i, hi, hx⟩ := hel x
      have hxx : x.1 * x.1 = idx (hsV1M i i) := by rw [hmm, hx]
      rcases T5 i hi with h | h
      · left
        exact Subtype.ext (by rw [Subgroup.coe_mul, hxx, h, h00]; rfl)
      · right
        exact Subtype.ext (by rw [Subgroup.coe_mul, hxx, h])
    · intro x y
      obtain ⟨i, hi, hx⟩ := hel x
      obtain ⟨k, hk, hy⟩ := hel y
      have h1 : x.1 * y.1 = idx (hsV1M i k) := by rw [hmm, hx, hy]
      have h2 : y.1 * x.1 = idx (hsV1M k i) := by rw [hmm, hx, hy]
      have h3 : idx 32 * idx (hsV1M k i) = idx (hsV1M 32 (hsV1M k i)) := (hmm _ _).symm
      rcases T6 i k hi hk with h | h
      · left
        exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, h2, h])
      · right
        exact Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, h1, h2]
          show idx (hsV1M i k) = idx 32 * idx (hsV1M k i)
          rw [h3, h])
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hel x
      have hcomm : ∀ k : Fin 64, k.1 / 16 % 2 = 0 → hsV1M i k = hsV1M k i := fun k hk => by
        have := hx ⟨idx k, (hEi k).mpr hk⟩
        have h2 := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h2
        rw [← hxi, ← hmm, ← hmm] at h2
        exact idx.injective h2
      rcases T7 i hi hcomm with h | h
      · left
        exact Subtype.ext (by rw [← hxi, h, h00]; rfl)
      · right
        exact Subtype.ext (by rw [← hxi, h])
  exact ⟨Z, E, hcardZ, inferInstance, hext, hZc, hZEtop, hZE⟩

end CFSG.Quasithin.A312Hs

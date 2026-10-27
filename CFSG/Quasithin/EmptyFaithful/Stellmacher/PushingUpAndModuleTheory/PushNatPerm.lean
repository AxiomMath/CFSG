module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreConj
public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Quasithin.F53Mod Equiv

theorem fixW_anti {n : ℕ} (M : Model n) {B₁ B₂ : Subgroup (Perm (Fin n))} (h : B₁ ≤ B₂) :
    fixW M B₂ ≤ fixW M B₁ := fun _ hw b hb => hw b (h hb)

theorem index_fixW_le {n : ℕ} (M : Model n) {B₁ B₂ : Subgroup (Perm (Fin n))} (h : B₁ ≤ B₂) :
    (fixW M B₁).index ≤ (fixW M B₂).index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le (fixW_anti M h))

theorem four_le_index_fixW {B : Subgroup (Perm (Fin 5))} {σ : Perm (Fin 5)} (hσB : σ ∈ B)
    (hσ : σ ≠ 1) : 4 ≤ (fixW nat B).index :=
  ((transvections σ hσ).1).trans
    (index_fixW_le nat ((Subgroup.zpowers_le).mpr hσB))

theorem card_le_four {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5Syl) (hsq : ∀ b ∈ B, b * b = 1) :
    Nat.card B ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card B ∣ 8 := card_S5Syl ▸ Subgroup.card_dvd_of_le hB
  have hmem : Nat.card B ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h8 : Nat.card B = 8 := by
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hBS : B = S5Syl := Subgroup.eq_of_le_of_card_ge hB (by rw [card_S5Syl, h8])
  have hg : S5g ∈ B := by
    rw [hBS]
    exact Subgroup.subset_closure (Or.inl rfl)
  exact (show S5g * S5g ≠ 1 by decide +kernel) (hsq _ hg)

private theorem key_dec : ∀ b ∈ S5SylF, ∀ c ∈ S5SylF, b ∉ S5TF → b * b = 1 → c * c = 1 →
    (b * c) * (b * c) = 1 → c ≠ 1 → c ≠ b →
    (swap (0 : Fin 5) 2 = b ∨ swap 0 2 = c ∨ swap 0 2 = b * c) ∧
    (swap (1 : Fin 5) 3 = b ∨ swap 1 3 = c ∨ swap 1 3 = b * c) := by decide +kernel

theorem index_fixW_S5That : (fixW nat S5That).index = 8 := by
  have h1 : Nat.card (fixW nat S5That) = 2 := congrArg (fun p => p.2.1) profile_nat.2.2.1
  have h2 := Subgroup.card_mul_index (fixW nat S5That)
  rw [h1, card_nat] at h2
  omega

theorem le_S5T_of_idx {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5Syl) (hsq : ∀ b ∈ B, b * b = 1)
    (hc : Nat.card B = 4) (hidx : (fixW nat B).index ≤ 4) : B ≤ S5T := by
  intro b hb
  by_contra hbT
  have hbS : b ∈ S5Syl := hB hb
  obtain ⟨c, hcB, hc1, hcb⟩ : ∃ c ∈ B, c ≠ 1 ∧ c ≠ b := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ Subgroup.zpowers b := by
      intro c hc'
      by_cases h1 : c = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hcon c hc' h1]; exact Subgroup.mem_zpowers b
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers b) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq b hb))
    omega
  have hbc : b * c ∈ B := B.mul_mem hb hcB
  have hdec := key_dec b ((mem_S5Syl_iff b).mp hbS) c ((mem_S5Syl_iff c).mp (hB hcB))
    (fun h => hbT ((mem_S5T_iff b).mpr h)) (hsq b hb) (hsq c hcB) (hsq _ hbc) hc1 hcb
  have hmem : ∀ τ : Perm (Fin 5), (τ = b ∨ τ = c ∨ τ = b * c) → τ ∈ B := by
    rintro τ (rfl | rfl | rfl)
    · exact hb
    · exact hcB
    · exact hbc
  have hThat : S5That ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro τ (rfl | rfl)
    · exact hmem _ hdec.1
    · exact hmem _ hdec.2
  have := index_fixW_le nat hThat
  rw [index_fixW_S5That] at this
  omega

@[expose] def S5c : Perm (Fin 5) := swap 0 1 * swap 1 4

theorem S5c_pow_three : S5c ^ 3 = 1 := by unfold S5c; decide +kernel

theorem sign_S5c : Perm.sign S5c = 1 := by unfold S5c; decide +kernel

@[expose] def S5x1 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def S5x2 : Perm (Fin 5) := swap 0 3 * swap 1 2

theorem S5x1_mem : S5x1 ∈ S5T := (mem_S5T_iff _).mpr (by unfold S5x1; decide +kernel)

theorem S5x2_mem : S5x2 ∈ S5T := (mem_S5T_iff _).mpr (by unfold S5x2; decide +kernel)

@[expose] def S5gens (g : Perm (Fin 5)) : List (Perm (Fin 5)) :=
  [S5x1, S5x2, g * S5x1 * g⁻¹, g * S5x2 * g⁻¹]

private theorem alt_le_sup_cj_of (g : Perm (Fin 5))
    (h : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → τ ∈ Subgroup.closure {x | x ∈ S5gens g}) :
    ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → τ ∈ S5T ⊔ cj g S5T := by
  intro τ hτ
  refine (Subgroup.closure_le (S5T ⊔ cj g S5T)).mpr ?_ (h τ hτ)
  intro y hy
  simp only [S5gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hy
  have hc : ∀ x ∈ S5T, g * x * g⁻¹ ∈ cj g S5T := fun x hx => by
    rw [mem_cj]; simpa [mul_assoc] using hx
  rcases hy with rfl | rfl | rfl | rfl
  · exact Subgroup.mem_sup_left S5x1_mem
  · exact Subgroup.mem_sup_left S5x2_mem
  · exact Subgroup.mem_sup_right (hc _ S5x1_mem)
  · exact Subgroup.mem_sup_right (hc _ S5x2_mem)

set_option maxRecDepth 100000 in
private theorem alt_closure_one : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 →
    τ ∈ Subgroup.closure {x | x ∈ S5gens S5c} := by
  intro τ hτ
  refine wordSet_subset_closure (S5gens S5c) 5 τ ?_
  revert τ
  unfold S5gens S5x1 S5x2 S5c; decide +kernel

set_option maxRecDepth 100000 in
private theorem alt_closure_two : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 →
    τ ∈ Subgroup.closure {x | x ∈ S5gens (S5c * S5c)} := by
  intro τ hτ
  refine wordSet_subset_closure (S5gens (S5c * S5c)) 5 τ ?_
  revert τ
  unfold S5gens S5x1 S5x2 S5c; decide +kernel

theorem alt_le_sup_cj {g : Perm (Fin 5)} (hg : g = S5c ∨ g = S5c * S5c) :
    ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → τ ∈ S5T ⊔ cj g S5T := by
  rcases hg with rfl | rfl
  · exact alt_le_sup_cj_of S5c alt_closure_one
  · exact alt_le_sup_cj_of (S5c * S5c) alt_closure_two

theorem S5c_pow_two_pow (k : ℕ) : S5c ^ 2 ^ k = S5c ∨ S5c ^ 2 ^ k = S5c * S5c := by
  induction k with
  | zero => exact Or.inl (pow_one _)
  | succ k ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · rw [h]; exact Or.inr (pow_two _)
    · rw [h]
      left
      have h3 := S5c_pow_three
      calc (S5c * S5c) ^ 2 = S5c ^ 4 := by rw [← pow_two, ← pow_mul]
        _ = S5c := by rw [show 4 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]

theorem exists_le_conj_S5Syl {P : Subgroup (Perm (Fin 5))} (hP : IsPGroup 2 P) :
    ∃ g : Perm (Fin 5), P ≤ S5Syl.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨D, hD⟩ := hP.exists_le_sylow
  have hG : Nat.card (Perm (Fin 5)) = 2 ^ 3 * 15 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have h0 : Nat.card S5Syl = 2 ^ 3 := by rw [card_S5Syl]; norm_num
  have idx : ¬ 2 ∣ S5Syl.index := by
    have h1 := Subgroup.card_mul_index S5Syl
    rw [h0, hG] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1]
    norm_num
  let P0 : Sylow 2 (Perm (Fin 5)) := (IsPGroup.of_card h0).toSylow idx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) P0 D
  have h1 : (D : Subgroup (Perm (Fin 5))) = S5Syl.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun R : Sylow 2 (Perm (Fin 5)) => (R : Subgroup (Perm (Fin 5)))) hg).symm
  exact ⟨g, h1 ▸ hD⟩

end CFSG.Quasithin.F53Push

module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA8Cyc

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm Item434AltPerm

@[expose] def sw8 : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5

@[expose] def sw8' : Perm (Fin 8) := swap 0 3 * swap 1 5 * swap 2 4

@[expose] def t67 : Perm (Fin 8) := swap 6 7

@[expose] def centA (s : Perm (Fin 8)) (p : Fin 3 × Fin 3 × Fin 2 × Fin 2) : Perm (Fin 8) :=
  c1 8 ^ (p.1 : ℕ) * c2 8 ^ (p.2.1 : ℕ) * s ^ (p.2.2.1 : ℕ) * t67 ^ (p.2.2.2 : ℕ)

theorem centA_comm_one : ∀ (i j : Fin 3) (k l : Fin 2),
    centA sw8 (i, j, k, l) * (c1 8 * c2 8) = (c1 8 * c2 8) * centA sw8 (i, j, k, l) := by
  decide +kernel

theorem centA_comm_two : ∀ (i j : Fin 3) (k l : Fin 2),
    centA sw8' (i, j, k, l) * (c1 8 * c2 8 ^ 2) = (c1 8 * c2 8 ^ 2) * centA sw8' (i, j, k, l) := by
  decide +kernel

theorem centA_inj_one : ∀ (i j : Fin 3) (k l : Fin 2) (i' j' : Fin 3) (k' l' : Fin 2),
    centA sw8 (i, j, k, l) = centA sw8 (i', j', k', l') → i = i' ∧ j = j' ∧ k = k' ∧ l = l' := by
  decide +kernel

theorem centA_inj_two : ∀ (i j : Fin 3) (k l : Fin 2) (i' j' : Fin 3) (k' l' : Fin 2),
    centA sw8' (i, j, k, l) = centA sw8' (i', j', k', l') → i = i' ∧ j = j' ∧ k = k' ∧ l = l' := by
  decide +kernel

theorem centA_injective {s : Perm (Fin 8)} (hs : s = sw8 ∨ s = sw8') :
    Function.Injective (centA s) := by
  rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
  rcases hs with rfl | rfl
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := centA_inj_one i j k l i' j' k' l' h
    rfl
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := centA_inj_two i j k l i' j' k' l' h
    rfl

theorem isThreeCycle_c2_eight_sq : (c2 8 ^ 2).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

theorem disjoint_c1_c2_eight : (c1 8).Disjoint (c2 8) ∧ (c1 8).Disjoint (c2 8 ^ 2) := by
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> revert x <;> decide

theorem card_centralizer_pair {b : Perm (Fin 8)} (hb : b = c1 8 * c2 8 ∨ b = c1 8 * c2 8 ^ 2) :
    Nat.card (Subgroup.centralizer ({b} : Set (Perm (Fin 8)))) = 36 := by
  have hct : b.cycleType = {3, 3} := by
    rcases hb with rfl | rfl
    · rw [disjoint_c1_c2_eight.1.cycleType_mul, isThreeCycle_c1_eight.cycleType,
        isThreeCycle_c2_eight.cycleType]
      rfl
    · rw [disjoint_c1_c2_eight.2.cycleType_mul, isThreeCycle_c1_eight.cycleType,
        isThreeCycle_c2_eight_sq.cycleType]
      rfl
  rw [nat_card_centralizer, hct]
  decide

theorem mem_range_centA {b s : Perm (Fin 8)}
    (hbs : (b = c1 8 * c2 8 ∧ s = sw8) ∨ (b = c1 8 * c2 8 ^ 2 ∧ s = sw8')) {y : Perm (Fin 8)}
    (hy : y * b = b * y) : ∃ p, y = centA s p := by
  have hcomm : ∀ p, centA s p * b = b * centA s p := by
    rintro ⟨i, j, k, l⟩
    rcases hbs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact centA_comm_one i j k l
    · exact centA_comm_two i j k l
  have hinj : Function.Injective (centA s) :=
    centA_injective (hbs.imp And.right And.right)
  set C := Subgroup.centralizer ({b} : Set (Perm (Fin 8))) with hC
  have hSC : Set.range (centA s) ⊆ (C : Set (Perm (Fin 8))) := by
    rintro _ ⟨p, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm p)
  have hS : (Set.range (centA s)).ncard = 36 := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
    rfl
  have hCc : (C : Set (Perm (Fin 8))).ncard = 36 := by
    rw [← Nat.card_coe_set_eq]
    exact card_centralizer_pair (hbs.imp And.left And.left)
  have heq : Set.range (centA s) = (C : Set (Perm (Fin 8))) :=
    Set.eq_of_subset_of_ncard_le hSC (by rw [hS, hCc]) (Set.toFinite _)
  have hyC : y ∈ (C : Set (Perm (Fin 8))) := Subgroup.mem_centralizer_singleton_iff.mpr hy
  rw [← heq] at hyC
  obtain ⟨p, hp⟩ := hyC
  exact ⟨p, hp.symm⟩

theorem check_centA_one : ∀ (i j : Fin 3) (k l : Fin 2), centA sw8 (i, j, k, l) ^ 6 = 1 ∧
    (k = l → centA sw8 (i, j, k, l) ≠ 1 → centA sw8 (i, j, k, l) ^ 2 ≠ 1 ∨
      ((centA sw8 (i, j, k, l) * (c1 8 * centA sw8 (i, j, k, l) * (c1 8)⁻¹)) ^ 3 = 1 ∧
        centA sw8 (i, j, k, l) * (c1 8 * centA sw8 (i, j, k, l) * (c1 8)⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_centA_two : ∀ (i j : Fin 3) (k l : Fin 2), centA sw8' (i, j, k, l) ^ 6 = 1 ∧
    (k = l → centA sw8' (i, j, k, l) ≠ 1 → centA sw8' (i, j, k, l) ^ 2 ≠ 1 ∨
      ((centA sw8' (i, j, k, l) * (c1 8 * centA sw8' (i, j, k, l) * (c1 8)⁻¹)) ^ 3 = 1 ∧
        centA sw8' (i, j, k, l) * (c1 8 * centA sw8' (i, j, k, l) * (c1 8)⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_centA {s : Perm (Fin 8)} (hs : s = sw8 ∨ s = sw8')
    (p : Fin 3 × Fin 3 × Fin 2 × Fin 2) : centA s p ^ 6 = 1 ∧
    (p.2.2.1 = p.2.2.2 → centA s p ≠ 1 → centA s p ^ 2 ≠ 1 ∨
      ((centA s p * (c1 8 * centA s p * (c1 8)⁻¹)) ^ 3 = 1 ∧
        centA s p * (c1 8 * centA s p * (c1 8)⁻¹) ≠ 1)) := by
  obtain ⟨i, j, k, l⟩ := p
  rcases hs with rfl | rfl
  · exact check_centA_one i j k l
  · exact check_centA_two i j k l

theorem signs_eight : sign (c1 8) = 1 ∧ sign (c2 8) = 1 ∧ sign sw8 = -1 ∧ sign sw8' = -1 ∧
    sign t67 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [c1, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  · rw [c2, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  · rw [sw8, Perm.sign_mul, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide),
      sign_swap (by decide)]
    decide
  · rw [sw8', Perm.sign_mul, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide),
      sign_swap (by decide)]
    decide
  · rw [t67, sign_swap (by decide)]

theorem eq_of_sign_centA {s : Perm (Fin 8)} (hs : sign s = -1) {p : Fin 3 × Fin 3 × Fin 2 × Fin 2}
    (h : sign (centA s p) = 1) : p.2.2.1 = p.2.2.2 := by
  obtain ⟨h1, h2, -, -, h5⟩ := signs_eight
  rw [centA, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul, map_pow, map_pow, map_pow, map_pow, h1,
    h2, hs, h5, one_pow, one_pow, one_mul, one_mul] at h
  revert h
  generalize p.2.2.1 = k
  generalize p.2.2.2 = l
  revert k l
  decide

theorem eq_bot_of_thetaLike_pair {b : Perm (Fin 8)} (hb : b = c1 8 * c2 8 ∨ b = c1 8 * c2 8 ^ 2)
    {P : Subgroup (Perm (Fin 8))} (hP : ThetaLike b P) : P = ⊥ := by
  obtain ⟨hs1, -, hs3, hs4, -⟩ := signs_eight
  obtain ⟨s, hbs, hsm, hss⟩ : ∃ s, ((b = c1 8 * c2 8 ∧ s = sw8) ∨
      (b = c1 8 * c2 8 ^ 2 ∧ s = sw8')) ∧ (s = sw8 ∨ s = sw8') ∧ sign s = -1 := by
    rcases hb with rfl | rfl
    · exact ⟨sw8, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hs3⟩
    · exact ⟨sw8', Or.inr ⟨rfl, rfl⟩, Or.inr rfl, hs4⟩
  have hc1b : c1 8 * b = b * c1 8 := by
    rcases hb with rfl | rfl <;> decide
  have hc1A : c1 8 ∈ alternatingGroup (Fin 8) := hs1
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨p, rfl⟩ := mem_range_centA hbs (hP.comm _ hy)
  have hkl := eq_of_sign_centA hss (hP.even hy)
  obtain ⟨h6, hcheck⟩ := check_centA hsm p
  have hy2 : centA s p ^ 2 = 1 := by
    have hd : orderOf (centA s p) ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6
    exact orderOf_dvd_iff_pow_eq_one.mp ((hP.coprime _ hy).dvd_of_dvd_mul_right hd)
  by_contra hne
  rcases hcheck hkl hne with h2 | ⟨h3, h1⟩
  · exact h2 hy2
  · exact hP.false_of_mem (mul_mem hy (hP.conj _ hy _ hc1A hc1b)) h3 h1

end Res423Two

end CFSG.RankThree.PartTwo.Sec4

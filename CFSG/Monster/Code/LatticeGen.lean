module

public import CFSG.Monster.Code.LatticeBasic

public section

namespace CFSG.Monster.Code

open CFSG.Monster

@[expose] def lam0 : Fin 24 → ℤ := fun i => 1 - 4 * eℤ 0 i

@[expose] def latticeGens : Set (Fin 24 → ℤ) :=
  {u | ∃ i j : Fin 24, i < j ∧ (u = (4 : ℤ) • (eℤ i - eℤ j) ∨ u = (4 : ℤ) • (eℤ i + eℤ j))} ∪
    Set.range (fun j : Fin 12 => (2 : ℤ) • liftℤ (B j)) ∪ {lam0}

private theorem sum_eℤ (i : Fin 24) : ∑ k, eℤ i k = 1 := by
  simp [eℤ]

private theorem sum_mul_eℤ (k : Fin 24 → ℤ) (c : Fin 24) : ∑ i, k i * eℤ i c = k c := by
  simp [eℤ, Pi.single_apply]

private theorem sum_lam0 : ∑ i, lam0 i = 20 := by decide +kernel

private theorem normSq_pm : ∀ i j : Fin 24, i ≠ j →
    normSq ((4 : ℤ) • (eℤ i - eℤ j)) = 32 ∧ normSq ((4 : ℤ) • (eℤ i + eℤ j)) = 32 := by
  decide +kernel

private theorem normSq_B : ∀ j : Fin 12, normSq ((2 : ℤ) • liftℤ (B j)) = 32 := by
  intro j
  rw [B_eq_bvec]
  revert j
  decide +kernel

private theorem normSq_lam0 : normSq lam0 = 32 := by decide +kernel

theorem latticeGens_mem {u : Fin 24 → ℤ} (hu : u ∈ latticeGens) :
    u ∈ codeLattice C ∧ normSq u = 32 := by
  rcases hu with (⟨i, j, hij, rfl | rfl⟩ | ⟨j, rfl⟩) | rfl
  · refine ⟨⟨0, .inl rfl, 0, C.zero_mem, fun k => ?_, ?_⟩, (normSq_pm i j (ne_of_lt hij)).1⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero,
        Nat.cast_zero, mul_zero, add_zero]
      exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, ← Finset.mul_sum,
        Finset.sum_sub_distrib, sum_eℤ, sub_self, mul_zero]
      rfl
  · refine ⟨⟨0, .inl rfl, 0, C.zero_mem, fun k => ?_, ?_⟩, (normSq_pm i j (ne_of_lt hij)).2⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero,
        Nat.cast_zero, mul_zero, add_zero]
      exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, ← Finset.mul_sum,
        Finset.sum_add_distrib, sum_eℤ]
      decide
  · refine ⟨⟨0, .inl rfl, B j, B_mem_C j, fun k => ?_, ?_⟩, normSq_B j⟩
    · simp only [Pi.smul_apply, smul_eq_mul, liftℤ, zero_add]
      rfl
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_liftℤ, wt_B, mul_zero]
      decide
  · refine ⟨⟨1, .inr rfl, 0, C.zero_mem, fun k => ?_, ?_⟩, normSq_lam0⟩
    · simp only [lam0, Pi.zero_apply, bitLift, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
      unfold Int.ModEq
      omega
    · rw [sum_lam0]
      decide

theorem four_smul_mem_closure (k : Fin 24 → ℤ) (hk : Even (∑ i, k i)) :
    (4 : ℤ) • k ∈ AddSubgroup.closure latticeGens := by
  set S := AddSubgroup.closure latticeGens
  have hdiff : ∀ i, (4 : ℤ) • (eℤ i - eℤ 0) ∈ S := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [sub_self, smul_zero]
      exact S.zero_mem
    · have h := S.neg_mem (AddSubgroup.subset_closure
        (Or.inl (Or.inl ⟨0, i, Fin.pos_iff_ne_zero.2 hi, Or.inl rfl⟩)))
      rwa [← smul_neg, neg_sub] at h
  have h8 : (8 : ℤ) • eℤ 0 ∈ S := by
    have h1 : (4 : ℤ) • (eℤ 0 + eℤ 1) ∈ S :=
      AddSubgroup.subset_closure (Or.inl (Or.inl ⟨0, 1, by decide, Or.inr rfl⟩))
    have h2 : (4 : ℤ) • (eℤ 0 - eℤ 1) ∈ S :=
      AddSubgroup.subset_closure (Or.inl (Or.inl ⟨0, 1, by decide, Or.inl rfl⟩))
    have : (8 : ℤ) • eℤ 0 = (4 : ℤ) • (eℤ 0 + eℤ 1) + (4 : ℤ) • (eℤ 0 - eℤ 1) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℤ (eℤ 0), smul_smul]
      norm_num
    rw [this]
    exact S.add_mem h1 h2
  obtain ⟨t, ht⟩ := hk
  have key : (4 : ℤ) • k = ∑ i, k i • ((4 : ℤ) • (eℤ i - eℤ 0)) + t • ((8 : ℤ) • eℤ 0) := by
    funext c
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    have h : ∑ i, k i * (4 * (eℤ i c - eℤ 0 c)) =
        4 * ∑ i, k i * eℤ i c - 4 * (∑ i, k i) * eℤ 0 c := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, sum_mul_eℤ, ht]
    ring
  rw [key]
  exact S.add_mem (S.sum_mem fun i _ => S.zsmul_mem (hdiff i) _) (S.zsmul_mem h8 _)

private theorem bitLift_modEq_sum (d : Fin 24 → ZMod 2) (c : Fin 12 → ZMod 2)
    (hd : d = ∑ j, c j • B j) (i : Fin 24) :
    bitLift (d i) ≡ ∑ j, ((c j).val : ℤ) * bitLift (B j i) [ZMOD 2] := by
  have h : ((bitLift (d i) : ℤ) : ZMod 2) = ((∑ j, ((c j).val : ℤ) * bitLift (B j i) : ℤ) : ZMod 2) := by
    push_cast
    simp only [bitLift_cast, ZMod.natCast_val, ZMod.cast_id', id]
    rw [hd, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  exact (ZMod.intCast_eq_intCast_iff _ _ 2).1 h

theorem mem_closure_of_even (u : Fin 24 → ℤ) {d : Fin 24 → ZMod 2} (hd : d ∈ C)
    (hud : ∀ i, u i ≡ 2 * bitLift (d i) [ZMOD 4]) (hus : ∑ i, u i ≡ 0 [ZMOD 8]) :
    u ∈ AddSubgroup.closure latticeGens := by
  set S := AddSubgroup.closure latticeGens
  set c := ψ d
  set v : Fin 24 → ℤ := ∑ j, ((c j).val : ℤ) • ((2 : ℤ) • liftℤ (B j)) with hvdef
  have hv : v ∈ S := S.sum_mem fun j _ =>
    S.zsmul_mem (AddSubgroup.subset_closure (Or.inl (Or.inr ⟨j, rfl⟩))) _
  have hvi : ∀ i, v i = 2 * ∑ j, ((c j).val : ℤ) * bitLift (B j i) := by
    intro i
    simp only [hvdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, liftℤ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumv : ∑ i, v i = 16 * ∑ j, ((c j).val : ℤ) := by
    simp only [hvi, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    have : ∀ j : Fin 12, ∑ i, bitLift (B j i) = 8 := fun j => by
      have := sum_liftℤ (B j)
      rw [wt_B] at this
      exact_mod_cast this
    simp only [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmod : ∀ i, (u i - v i) % 4 = 0 := by
    intro i
    have h1 := hud i
    have h2 := bitLift_modEq_sum d c (eq_comb_of_mem_C hd) i
    rw [hvi]
    unfold Int.ModEq at h1 h2
    omega
  set k : Fin 24 → ℤ := fun i => (u i - v i) / 4
  have huv : u = v + (4 : ℤ) • k := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, k]
    have := hmod i
    omega
  have hk : Even (∑ i, k i) := by
    have hs : ∑ i, u i = ∑ i, v i + 4 * ∑ i, k i := by
      conv_lhs => rw [huv]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    rw [hs, hsumv] at hus
    unfold Int.ModEq at hus
    rw [Int.even_iff]
    omega
  rw [huv]
  exact S.add_mem hv (four_smul_mem_closure k hk)

theorem mem_closure_of_mem_codeLattice {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    u ∈ AddSubgroup.closure latticeGens := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  rcases hm with rfl | rfl
  · exact mem_closure_of_even u hd (fun i => by simpa using hud i) (by simpa using hus)
  · have h := mem_closure_of_even (u - lam0) hd (fun i => by
        have h1 := hud i
        simp only [Pi.sub_apply, lam0]
        unfold Int.ModEq at h1 ⊢
        have : eℤ 0 i = 0 ∨ eℤ 0 i = 1 := by
          simp only [eℤ, Pi.single_apply]; split_ifs <;> simp
        omega) (by
        have hs : ∑ i, (u - lam0) i = ∑ i, u i - 20 := by
          rw [← sum_lam0, ← Finset.sum_sub_distrib]; rfl
        rw [hs]
        unfold Int.ModEq at hus ⊢
        omega)
    have : u = (u - lam0) + lam0 := by abel
    rw [this]
    exact (AddSubgroup.closure latticeGens).add_mem h (AddSubgroup.subset_closure (Or.inr rfl))

theorem closure_latticeGens :
    AddSubgroup.closure latticeGens = codeLatticeSubgroup allOnes_mem_C := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 fun u hu => (latticeGens_mem hu).1)
    fun u hu => mem_closure_of_mem_codeLattice hu

theorem mog_lattice_short_generation :
    (∀ j, hammingNorm (B j) = 8) ∧
    (∀ u ∈ latticeGens, u ∈ codeLattice C ∧ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4) ∧
    AddSubgroup.closure latticeGens = codeLatticeSubgroup allOnes_mem_C ∧
    AddSubgroup.closure {u : Fin 24 → ℤ | u ∈ codeLattice C ∧
      codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4} = codeLatticeSubgroup allOnes_mem_C := by
  have hgen : ∀ u ∈ latticeGens, u ∈ codeLattice C ∧
      codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4 := fun u hu =>
    ⟨(latticeGens_mem hu).1, (codeForm_self_eq_four_iff u).2 (latticeGens_mem hu).2⟩
  refine ⟨wt_B, hgen, closure_latticeGens, le_antisymm ?_ ?_⟩
  · exact (AddSubgroup.closure_le _).2 fun u hu => hu.1
  · rw [← closure_latticeGens]
    exact AddSubgroup.closure_mono fun u hu => hgen u hu

end CFSG.Monster.Code

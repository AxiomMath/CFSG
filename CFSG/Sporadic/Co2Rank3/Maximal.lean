module

public import CFSG.Sporadic.Co2Rank3.Extension

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Rank3.Native MulAction

section Overgroups

variable {x : Fin 2300} {K : Subgroup (Equiv.Perm (Fin 2300))}
  (h1 : co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x ≤ K) (h2 : K ≤ co2P0)
include h1 h2

theorem inf_stabilizer_eq_of_le :
    K ⊓ stabilizer (Equiv.Perm (Fin 2300)) x = co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x :=
  le_antisymm (inf_le_inf_right _ h2) (le_inf h1 inf_le_right)

theorem card_eq_orbit_mul :
    Nat.card K = (orbit K x).ncard *
      Nat.card (co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x : Subgroup _) := by
  rw [← inf_stabilizer_eq_of_le h1 h2, ← card_inf_stabilizer_eq, ← index_stabilizer,
    Subgroup.index_mul_card]

omit h1 h2 in
theorem card_co2P0_eq_orbit_mul (x : Fin 2300) :
    Nat.card co2P0 = (orbit co2P0 x).ncard *
      Nat.card (co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x : Subgroup _) := by
  rw [← card_inf_stabilizer_eq, ← index_stabilizer, Subgroup.index_mul_card]

theorem ncard_orbit_dvd : (orbit K x).ncard ∣ (orbit co2P0 x).ncard := by
  have hd := Subgroup.card_dvd_of_le h2
  rw [card_eq_orbit_mul h1 h2, card_co2P0_eq_orbit_mul x] at hd
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hd

theorem eq_or_eq_of_orbit
    (h : (orbit K x).ncard = 1 ∨ (orbit K x).ncard = (orbit co2P0 x).ncard) :
    K = co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) x ∨ K = co2P0 := by
  rcases h with h | h
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    have hxa : x = a := by
      have := mem_orbit_self (M := K) x
      rw [ha] at this
      exact this
    refine le_antisymm (le_inf h2 fun k hk => ?_) h1
    have : k • x ∈ orbit K x := mem_orbit_subgroup_iff.2 ⟨k, hk, rfl⟩
    rw [ha, ← hxa] at this
    exact mem_stabilizer_iff.2 this
  · right
    refine Subgroup.eq_of_le_of_card_ge h2 ?_
    rw [card_eq_orbit_mul h1 h2, card_co2P0_eq_orbit_mul x, h]

end Overgroups

theorem orbit_co2N_ne
    {y z : Fin 2300} (hy : stabRec.1[(y : ℕ)]! = y)
    (hz : stabRec.1[(z : ℕ)]! = z) (hyz : y ≠ z) : orbit co2N y ≠ orbit co2N z := by
  intro he
  have : z ∈ orbit co2N y := he ▸ mem_orbit_self z
  rw [co2N_rec.1, hy, hz] at this
  exact hyz (Fin.ext this).symm

theorem orbit_co2P01_ne
    {y z : Fin 2300} (hy : p01Rec.1[(y : ℕ)]! = y)
    (hz : p01Rec.1[(z : ℕ)]! = z) (hyz : y ≠ z) : orbit co2P01 y ≠ orbit co2P01 z := by
  intro he
  have : z ∈ orbit co2P01 y := he ▸ mem_orbit_self z
  rw [co2P01_rec.1, hy, hz] at this
  exact hyz (Fin.ext this).symm

theorem orbit_invariant_of_le {N K : Subgroup (Equiv.Perm (Fin 2300))} (hNK : N ≤ K)
    (x : Fin 2300) : ∀ n ∈ N, ∀ y : Fin 2300, n • y ∈ orbit K x ↔ y ∈ orbit K x := by
  intro n hn y
  constructor
  · intro h
    have := smul_mem_orbit_subgroup (K.inv_mem (hNK hn)) h
    rwa [inv_smul_smul] at this
  · exact smul_mem_orbit_subgroup (hNK hn)

theorem disjoint_co2Delta_co2Gamma :
    Disjoint (orbit co2P0 (3 : Fin 2300)) (orbit co2P0 (1 : Fin 2300)) :=
  disjoint_orbit_of_ncard_ne (by rw [ncard_co2Delta, ncard_co2Gamma]; norm_num)

theorem co2P03_maximal
    {K : Subgroup (Equiv.Perm (Fin 2300))}
    (h1 : co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (3 : Fin 2300) ≤ K) (h2 : K ≤ co2P0) :
    K = co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (3 : Fin 2300) ∨ K = co2P0 := by
  refine eq_or_eq_of_orbit h1 h2 ?_
  have hdvd := ncard_orbit_dvd h1 h2
  rw [ncard_co2Delta] at hdvd ⊢
  have hinv := orbit_invariant_of_le (le_trans co2N_le h1) (3 : Fin 2300)
  have hsub : orbit K (3 : Fin 2300) ⊆ orbit co2P0 (3 : Fin 2300) := orbit_subgroup_mono h2 _
  have hΓ : ∀ d ∈ orbit co2P0 (1 : Fin 2300),
      (orbit K (3 : Fin 2300) ∩ orbit co2N d).ncard = 0 := by
    intro d hd
    rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyd⟩
    have hyΓ : y ∈ orbit co2P0 (1 : Fin 2300) :=
      (orbit_eq_of_mem hd) ▸ orbit_subgroup_mono co2N_le_P0 d hyd
    exact Set.disjoint_left.1 disjoint_co2Delta_co2Gamma (hsub hy) hyΓ
  let r : Fin 7 → Fin 2300 := ![0, 3, 36, 4, 5, 2, 1]
  have hroot : ∀ i, stabRec.1[((r i : Fin 2300) : ℕ)]! = ((r i : Fin 2300) : ℕ) := by
    intro i
    fin_cases i
    · exact co2N_rec.2.2.1 (0, 1) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (3, 1) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (36, 42) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (4, 336) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (5, 512) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (2, 512) (by simp [stabRoots])
    · exact co2N_rec.2.2.1 (1, 896) (by simp [stabRoots])
  have hne : ∀ i j, i ≠ j → orbit co2N (r i) ≠ orbit co2N (r j) := fun i j hij =>
    orbit_co2N_ne (hroot i) (hroot j) (by fin_cases i <;> fin_cases j <;> simp_all [r])
  have hcovr : ∀ y, ∃ i, y ∈ orbit co2N (r i) := by
    intro y
    rcases co2N_cover y with rfl | rfl | h | h | h | h | h
    · exact ⟨0, mem_orbit_self _⟩
    · exact ⟨1, mem_orbit_self _⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
  have hcount := ncard_eq_sum_ncard_orbits hne hcovr (orbit K (3 : Fin 2300))
  rw [Fin.sum_univ_seven] at hcount
  have h0 : orbit co2N (0 : Fin 2300) = {0} :=
    orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 (co2N_le hk).1.2
  have h3 : orbit co2N (3 : Fin 2300) = {3} :=
    orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 (co2N_le hk).2
  have h0K : (0 : Fin 2300) ∉ orbit K (3 : Fin 2300) := fun h =>
    (suborbit_facts (H := co2P) ncard_co2Delta ncard_co2Gamma).1 (hsub h)
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h0, h3,
    Set.inter_singleton_eq_empty.2 h0K, Set.inter_singleton_of_mem (mem_orbit_self _),
    Set.ncard_empty, Set.ncard_singleton, hΓ _ (mem_co2Gamma_of_lab (x := 2) co2Rank3Facts.loc2),
    hΓ _ (mem_orbit_self _)] at hcount
  have c₁ := ncard_inter_orbit hinv (36 : Fin 2300)
  have c₂ := ncard_inter_orbit hinv (4 : Fin 2300)
  have c₃ := ncard_inter_orbit hinv (5 : Fin 2300)
  rw [ncard_co2N_36] at c₁
  rw [ncard_co2N_4] at c₂
  rw [ncard_co2N_5] at c₃
  rcases c₁ with ⟨-, c₁⟩ | ⟨-, c₁⟩ <;> rcases c₂ with ⟨-, c₂⟩ | ⟨-, c₂⟩ <;>
    rcases c₃ with ⟨-, c₃⟩ | ⟨-, c₃⟩ <;> rw [c₁, c₂, c₃] at hcount <;> rw [hcount] at hdvd ⊢ <;>
    omega

theorem co2P01_maximal
    {K : Subgroup (Equiv.Perm (Fin 2300))} (h1 : co2P01 ≤ K)
    (h2 : K ≤ co2P0) : K = co2P01 ∨ K = co2P0 := by
  refine eq_or_eq_of_orbit (x := (1 : Fin 2300)) h1 h2 ?_
  have hdvd := ncard_orbit_dvd (x := (1 : Fin 2300)) h1 h2
  rw [ncard_co2Gamma] at hdvd ⊢
  have hinv := orbit_invariant_of_le h1 (1 : Fin 2300)
  have hsub : orbit K (1 : Fin 2300) ⊆ orbit co2P0 (1 : Fin 2300) := orbit_subgroup_mono h2 _
  have hΔ : ∀ d ∈ orbit co2P0 (3 : Fin 2300),
      (orbit K (1 : Fin 2300) ∩ orbit co2P01 d).ncard = 0 := by
    intro d hd
    rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyd⟩
    have hyΔ : y ∈ orbit co2P0 (3 : Fin 2300) :=
      (orbit_eq_of_mem hd) ▸ orbit_subgroup_mono (inf_le_left : co2P01 ≤ co2P0) d hyd
    exact Set.disjoint_left.1 disjoint_co2Delta_co2Gamma hyΔ (hsub hy)
  let r : Fin 6 → Fin 2300 := ![0, 1, 4, 3, 2, 8]
  have hroot : ∀ i, p01Rec.1[((r i : Fin 2300) : ℕ)]! = ((r i : Fin 2300) : ℕ) := by
    intro i
    fin_cases i
    · exact co2P01_rec.2.2.1 (0, 1) (by simp [p01Roots])
    · exact co2P01_rec.2.2.1 (1, 1) (by simp [p01Roots])
    · exact co2P01_rec.2.2.1 (4, 324) (by simp [p01Roots])
    · exact co2P01_rec.2.2.1 (3, 567) (by simp [p01Roots])
    · exact co2P01_rec.2.2.1 (2, 567) (by simp [p01Roots])
    · exact co2P01_rec.2.2.1 (8, 840) (by simp [p01Roots])
  have hne : ∀ i j, i ≠ j → orbit co2P01 (r i) ≠ orbit co2P01 (r j) := fun i j hij =>
    orbit_co2P01_ne (hroot i) (hroot j) (by fin_cases i <;> fin_cases j <;> simp_all [r])
  have hcovr : ∀ y, ∃ i, y ∈ orbit co2P01 (r i) := by
    intro y
    rcases co2P01_cover y with rfl | rfl | h | h | h | h
    · exact ⟨0, mem_orbit_self _⟩
    · exact ⟨1, mem_orbit_self _⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
  have hcount := ncard_eq_sum_ncard_orbits hne hcovr (orbit K (1 : Fin 2300))
  rw [Fin.sum_univ_six] at hcount
  have h0 : orbit co2P01 (0 : Fin 2300) = {0} :=
    orbit_subgroup_eq_singleton (K := co2P01) fun _ hk => mem_stabilizer_iff.1 hk.1.2
  have h1' : orbit co2P01 (1 : Fin 2300) = {1} :=
    orbit_subgroup_eq_singleton (K := co2P01) fun _ hk => mem_stabilizer_iff.1 hk.2
  have h0K : (0 : Fin 2300) ∉ orbit K (1 : Fin 2300) := fun h =>
    (suborbit_facts (H := co2P) ncard_co2Delta ncard_co2Gamma).2.1 (hsub h)
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h0, h1',
    Set.inter_singleton_eq_empty.2 h0K, Set.inter_singleton_of_mem (mem_orbit_self _),
    Set.ncard_empty, Set.ncard_singleton, hΔ _ (mem_co2Delta_of_lab (x := 4) co2Rank3Facts.loc4),
    hΔ _ (mem_orbit_self _)] at hcount
  have c₁ := ncard_inter_orbit hinv (2 : Fin 2300)
  have c₂ := ncard_inter_orbit hinv (8 : Fin 2300)
  rw [ncard_co2P01_2] at c₁
  rw [ncard_co2P01_8] at c₂
  rcases c₁ with ⟨-, c₁⟩ | ⟨-, c₁⟩ <;> rcases c₂ with ⟨-, c₂⟩ | ⟨-, c₂⟩ <;>
    rw [c₁, c₂] at hcount <;> rw [hcount] at hdvd ⊢ <;> omega

end CFSG.Sporadic.Co2Rank3

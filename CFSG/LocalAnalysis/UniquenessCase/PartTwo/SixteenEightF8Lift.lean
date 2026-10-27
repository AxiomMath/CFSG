module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.RankThree.GF2n.Stroth80

variable {K : Type} [Field K] [Finite K]

private theorem s16g_not_dvd_eight {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 8 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by norm_num; exact h)))

private theorem s16g_not_dvd_sixty_three {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    ¬ p ∣ 63 := fun h => by
  have h63 : p ∣ 3 ^ 2 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h63 with h3 | h7
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)

private theorem s16g_fixNc_statedSL_of_elem {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (Fin n → K)))} (hEN : E ≤ s16gNorm (StatedSL n K))
    (hE : IsElemAbelian p E) (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedSL n K) p := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hEL : E ≤ s16gLin (Fin n) K := s16g_le_lin_of_coprime (addCommutantScalar_statedSL hn) hp
    (by
      rw [s16g_card_ringAut_eight hK]
      exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)) hEN hE.isPGroup
  obtain ⟨F, hFN, hF, hFcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hE
  have hFS : F ≤ StatedSL n K := by
    intro x hx
    rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]
    exact DFunLike.congr_fun (s16g_hom_eq_one_of_coprime hp hF.isPGroup
      (by
        rw [Nat.card_units, hK]
        exact fun h => hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
      ((Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp F.subtype)) ⟨x, hx⟩
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedSL hn hp (by rw [hK]; exact s16g_not_dvd_eight hp hp2) hFS hF.2
    hFc (hFcard ▸ hcard)

private theorem s16g_fixNc_statedSp_of_elem {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (Fin m ⊕ Fin m → K)))}
    (hEN : E ≤ s16gNorm (StatedSp m K)) (hE : IsElemAbelian p E) (hcard : p ^ 3 ≤ Nat.card E) :
    FixNc (StatedSp m K) p := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (K := K) hm
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16g_exists_iso_elem_generic
    (addCommutantScalar_statedSp (m := m) (K := K)) hK μ hp hp3 hp7 hEN hE
  have hFS : F ≤ StatedSp m K := fun x hx => (hμ ⟨x, hFN hx⟩).1 (hμF ⟨x, hFN hx⟩ hx)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedSp hp (by rw [hK]; exact s16g_not_dvd_eight hp hp2) hFS hF.2
    hFc (hFcard ▸ hcard)

private theorem s16g_fixNc_statedOmegaPlus_of_elem {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (Fin m ⊕ Fin m → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadPlus m K))) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedOmega (StatedQuadPlus m K)) p := by
  haveI := s16g_charP_two hK
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaPlus (K := K) hm
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16g_exists_iso_elem_generic
    (addCommutantScalar_statedOmegaPlus hm) hK μ hp hp3 hp7 hEN hE
  have hFΩ : F ≤ StatedOmega (StatedQuadPlus m K) := s16g_le_statedOmegaPlus_of_odd hm hp hp2 hF.2
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedOmegaPlus hm hp hp2
    (by rw [hK]; exact s16g_not_dvd_sixty_three hp hp3 hp7) hFΩ hF.2
    hFc (hFcard ▸ hcard)

private theorem s16g_fixNc_statedOmegaMinus_of_elem {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hK : Nat.card K = 8) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedOmega (StatedQuadMinus m K b c)) p := by
  haveI := s16g_charP_two hK
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := m) (by omega) hirr
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16g_exists_iso_elem_generic
    (addCommutantScalar_statedOmegaMinus (by omega) hirr) hK μ hp hp3 hp7 hEN hE
  have hFΩ : F ≤ StatedOmega (StatedQuadMinus m K b c) :=
    s16g_le_statedOmegaMinus_of_odd (by omega) hirr hp hp2 hF.2
      (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedOmegaMinus hm hirr hp hp2
    (by rw [hK]; exact s16g_not_dvd_sixty_three hp hp3 hp7) hFΩ hF.2
    hFc (hFcard ▸ hcard)

theorem s16g_fixNc_statedSL_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) (ρ : ↥A →* MulAut (Multiplicative (Fin n → K))) (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSL n K)) (hrk : 3 ≤ CFSG.Open.pRank p A) :
    FixNc (StatedSL n K) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16g_fixNc_statedSL_of_elem hn hK hp hp2 hp3 hp7 (hEr.trans (s16g_range_le_norm hρN)) hE
    hcard

theorem s16g_fixNc_statedSp_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K)))
    (hρ : Function.Injective ρ) (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSp m K))
    (hrk : 3 ≤ CFSG.Open.pRank p A) : FixNc (StatedSp m K) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16g_fixNc_statedSp_of_elem hm hK hp hp2 hp3 hp7 (hEr.trans (s16g_range_le_norm hρN)) hE
    hcard

theorem s16g_fixNc_statedOmegaPlus_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp7 : p ≠ 7) (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadPlus m K)))
    (hrk : 3 ≤ CFSG.Open.pRank p A) : FixNc (StatedOmega (StatedQuadPlus m K)) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16g_fixNc_statedOmegaPlus_of_elem hm hK hp hp2 hp3 hp7
    (hEr.trans (s16g_range_le_norm hρN)) hE hcard

theorem s16g_fixNc_statedOmegaMinus_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hK : Nat.card K = 8)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c)))
    (hrk : 3 ≤ CFSG.Open.pRank p A) : FixNc (StatedOmega (StatedQuadMinus m K b c)) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16g_fixNc_statedOmegaMinus_of_elem hm hK hirr hp hp2 hp3 hp7
    (hEr.trans (s16g_range_le_norm hρN)) hE hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

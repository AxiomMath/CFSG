module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.RankThree.GF2n.Stroth80

variable {K : Type} [Field K] [Finite K]

theorem s16k_charP_two_of_card {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ a) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := a) (by rw [← Nat.card_eq_fintype_card, hK])

theorem s16k_card_ringAut_of_card {a : ℕ} (hK : Nat.card K = 2 ^ a) :
    Nat.card (RingAut K) = a :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1

theorem s16k_card_units_of_card {a : ℕ} (hK : Nat.card K = 2 ^ a) :
    Nat.card Kˣ = 2 ^ a - 1 := by
  rw [Nat.card_units, hK]

theorem s16k_exists_iso_elem_generic {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Γ : Subgroup (GL ι K)} (hΓ : AddCommutantScalar Γ)
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ) {p : ℕ} (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hE : IsElemAbelian p E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian p F ∧ Nat.card F = Nat.card E ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 := by
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN
    (s16g_le_lin_of_coprime hΓ hp hA hEN hE.isPGroup) hE
  exact ⟨F, hFN, hF, hcard, s16g_mu_eq_one_of_coprime μ hFN hp hF.isPGroup hU⟩

private theorem s16k_fixNc_statedSL_of_elem {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    {E : Subgroup (MulAut (Multiplicative (Fin n → K)))} (hEN : E ≤ s16gNorm (StatedSL n K))
    (hE : IsElemAbelian p E) (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedSL n K) p := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨F, hFN, hF, hFcard⟩ := s16g_exists_matrix_elem_of_lin hEN
    (s16g_le_lin_of_coprime (addCommutantScalar_statedSL hn) hp hA hEN hE.isPGroup) hE
  have hFS : F ≤ StatedSL n K := by
    intro x hx
    rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]
    exact DFunLike.congr_fun (s16g_hom_eq_one_of_coprime hp hF.isPGroup hU
      ((Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp F.subtype)) ⟨x, hx⟩
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedSL hn hp hpK hFS hF.2 hFc (hFcard ▸ hcard)

private theorem s16k_fixNc_statedSp_of_elem {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    {E : Subgroup (MulAut (Multiplicative (Fin m ⊕ Fin m → K)))}
    (hEN : E ≤ s16gNorm (StatedSp m K)) (hE : IsElemAbelian p E) (hcard : p ^ 3 ≤ Nat.card E) :
    FixNc (StatedSp m K) p := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (K := K) hm
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16k_exists_iso_elem_generic
    (addCommutantScalar_statedSp (m := m) (K := K)) μ hp hA hU hEN hE
  have hFS : F ≤ StatedSp m K := fun x hx => (hμ ⟨x, hFN hx⟩).1 (hμF ⟨x, hFN hx⟩ hx)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedSp hp hpK hFS hF.2 hFc (hFcard ▸ hcard)

private theorem s16k_fixNc_statedOmegaPlus_of_elem [CharP K 2] {m : ℕ} (hm : 3 ≤ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    {E : Subgroup (MulAut (Multiplicative (Fin m ⊕ Fin m → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadPlus m K))) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedOmega (StatedQuadPlus m K)) p := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaPlus (K := K) hm
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16k_exists_iso_elem_generic
    (addCommutantScalar_statedOmegaPlus hm) μ hp hA hU hEN hE
  have hFΩ : F ≤ StatedOmega (StatedQuadPlus m K) := s16g_le_statedOmegaPlus_of_odd hm hp hp2 hF.2
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedOmegaPlus hm hp hp2 hpq hFΩ hF.2 hFc (hFcard ▸ hcard)

private theorem s16k_fixNc_statedOmegaMinus_of_elem [CharP K 2] {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hA : ¬ p ∣ Nat.card (RingAut K))
    (hU : ¬ p ∣ Nat.card Kˣ)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedOmega (StatedQuadMinus m K b c)) p := by
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := m) (by omega) hirr
  obtain ⟨F, hFN, hF, hFcard, hμF⟩ := s16k_exists_iso_elem_generic
    (addCommutantScalar_statedOmegaMinus (by omega) hirr) μ hp hA hU hEN hE
  have hFΩ : F ≤ StatedOmega (StatedQuadMinus m K b c) :=
    s16g_le_statedOmegaMinus_of_odd (by omega) hirr hp hp2 hF.2
      (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  exact s16g_fixNc_statedOmegaMinus hm hirr hp hp2 hpq hFΩ hF.2 hFc (hFcard ▸ hcard)

theorem s16k_fixNc_statedSL_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    (ρ : ↥A →* MulAut (Multiplicative (Fin n → K))) (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSL n K)) (hrk : 3 ≤ CFSG.Open.pRank p A) :
    FixNc (StatedSL n K) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16k_fixNc_statedSL_of_elem hn hp hpK hA hU (hEr.trans (s16g_range_le_norm hρN)) hE hcard

theorem s16k_fixNc_statedSp_of_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K))) (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSp m K)) (hrk : 3 ≤ CFSG.Open.pRank p A) :
    FixNc (StatedSp m K) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16k_fixNc_statedSp_of_elem hm hp hpK hA hU (hEr.trans (s16g_range_le_norm hρN)) hE hcard

theorem s16k_fixNc_statedOmegaPlus_of_pRank [CharP K 2] {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {m : ℕ} (hm : 3 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (hA : ¬ p ∣ Nat.card (RingAut K))
    (hU : ¬ p ∣ Nat.card Kˣ) (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadPlus m K)))
    (hrk : 3 ≤ CFSG.Open.pRank p A) : FixNc (StatedOmega (StatedQuadPlus m K)) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16k_fixNc_statedOmegaPlus_of_elem hm hp hp2 hpq hA hU
    (hEr.trans (s16g_range_le_norm hρN)) hE hcard

theorem s16k_fixNc_statedOmegaMinus_of_pRank [CharP K 2] {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {m : ℕ} (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hA : ¬ p ∣ Nat.card (RingAut K)) (hU : ¬ p ∣ Nat.card Kˣ)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c)))
    (hrk : 3 ≤ CFSG.Open.pRank p A) :
    FixNc (StatedOmega (StatedQuadMinus m K b c)) p := by
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  exact s16k_fixNc_statedOmegaMinus_of_elem hm hirr hp hp2 hpq hA hU
    (hEr.trans (s16g_range_le_norm hρN)) hE hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

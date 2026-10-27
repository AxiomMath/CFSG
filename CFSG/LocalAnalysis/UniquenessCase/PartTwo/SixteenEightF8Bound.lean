module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Rank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus
  nondegenerate_polarBilin_quadMinus_of_finite)

variable {K : Type} [Field K] [Finite K]

private theorem s16g_card_le_norm_sl_three {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 8)
    {E : Subgroup (MulAut (Multiplicative (Fin n → K)))} (hEN : E ≤ s16gNorm (StatedSL n K))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ (n / 2 + 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h1 := s16g_card_le_of_norm (addCommutantScalar_statedSL hn) hEN
  rw [s16g_card_ringAut_eight hK] at h1
  obtain ⟨F, -, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin (E := E ⊓ s16gLin (Fin n) K)
    (inf_le_left.trans hEN) inf_le_right (hE.mono inf_le_left)
  have h2 := s16g_card_le_gl_three hK hF
  rw [Fintype.card_fin] at h2
  calc Nat.card E ≤ 3 * Nat.card ↥(E ⊓ s16gLin (Fin n) K) := h1
    _ = 3 * Nat.card F := by rw [hcard]
    _ ≤ 3 * 3 ^ (n / 2) := Nat.mul_le_mul_left _ h2
    _ = 3 ^ (n / 2 + 1) := by ring

private theorem s16g_card_le_norm_sl_seven {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 8)
    {E : Subgroup (MulAut (Multiplicative (Fin n → K)))} (hEN : E ≤ s16gNorm (StatedSL n K))
    (hE : IsElemAbelian 7 E) : Nat.card E ≤ 7 ^ n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hEL : E ≤ s16gLin (Fin n) K := s16g_le_lin_of_coprime (addCommutantScalar_statedSL hn)
    (by norm_num) (by rw [s16g_card_ringAut_eight hK]; norm_num) hEN hE.isPGroup
  obtain ⟨F, -, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hE
  have h2 := s16g_card_le_gl_seven hK hF
  rwa [Fintype.card_fin, hcard] at h2

private theorem s16g_card_le_norm_sp {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 8) {p : ℕ}
    (hp : p = 3 ∨ p = 7) {E : Subgroup (MulAut (Multiplicative (Fin m ⊕ Fin m → K)))}
    (hEN : E ≤ s16gNorm (StatedSp m K)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (m + 1) := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  have hΓ := addCommutantScalar_statedSp (m := m) (K := K)
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (K := K) hm
  rcases hp with rfl | rfl
  · obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_three hΓ hK μ hEN hE
    have hFS : F ≤ StatedSp m K := fun x hx => (hμ ⟨x, hFN hx⟩).1 (hμF ⟨x, hFN hx⟩ hx)
    calc Nat.card E ≤ 3 * Nat.card F := hcard
      _ ≤ 3 * 3 ^ m := Nat.mul_le_mul_left _ (s16g_card_le_sp hK (Or.inl rfl) hFS hF)
      _ = 3 ^ (m + 1) := by ring
  · obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_seven hΓ hK μ hEN hE
    have hFS : F ≤ StatedSp m K := fun x hx => (hμ ⟨x, hFN hx⟩).1 (hμF ⟨x, hFN hx⟩ hx)
    calc Nat.card E ≤ 7 * Nat.card F := hcard
      _ ≤ 7 * 7 ^ m := Nat.mul_le_mul_left _ (s16g_card_le_sp hK (Or.inr rfl) hFS hF)
      _ = 7 ^ (m + 1) := by ring

private theorem s16g_card_le_norm_omegaMinus_two {b c : K} (hK : Nat.card K = 8)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 2) {p : ℕ} (hp : p = 3 ∨ p = 7)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  subst hm
  haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  haveI := s16g_charP_two hK
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 2) (K := K) (by norm_num) hirr
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 2) (by norm_num) hirr
  rcases hp with rfl | rfl
  · obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_three hΓ hK μ hEN hE
    have hF' := s16g_card_le_orthMinus_two hK hirr rfl (Or.inl rfl) hF
      (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
    calc Nat.card E ≤ 3 * Nat.card F := hcard
      _ ≤ 3 * 3 := Nat.mul_le_mul_left _ hF'
      _ = 3 ^ 2 := by norm_num
  · obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_seven hΓ hK μ hEN hE
    have hF' := s16g_card_le_orthMinus_two hK hirr rfl (Or.inr rfl) hF
      (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
    calc Nat.card E ≤ 7 * Nat.card F := hcard
      _ ≤ 7 * 7 := Nat.mul_le_mul_left _ hF'
      _ = 7 ^ 2 := by norm_num

private theorem s16g_card_le_norm_omegaMinus_three_seven {b c : K} (hK : Nat.card K = 8)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) (hE : IsElemAbelian 7 E) :
    Nat.card E ≤ 7 ^ 3 := by
  subst hm
  haveI : Nonempty (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  haveI := s16g_charP_two hK
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 3) (K := K) (by norm_num) hirr
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 3) (by norm_num) hirr
  obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_seven hΓ hK μ hEN hE
  have hF' := s16g_card_le_orthMinus_three_seven hK hirr rfl hF
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  calc Nat.card E ≤ 7 * Nat.card F := hcard
    _ ≤ 7 * 7 ^ 2 := Nat.mul_le_mul_left _ hF'
    _ = 7 ^ 3 := by norm_num

private theorem s16g_card_le_norm_omegaMinus_three_three {b c : K} (hK : Nat.card K = 8)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c)))
    (hEL : E ≤ s16gLin (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 3 := by
  subst hm
  haveI := s16g_charP_two hK
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 3) (by norm_num) hirr
  obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_of_lin hK μ Nat.prime_three
    (by norm_num) hEN hEL hE
  rw [← hcard]
  exact s16g_card_le_orthMinus_three_three hK hirr rfl hF
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)

private theorem s16g_not_sq_dvd_orth {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) : ¬ p ^ 2 ∣ 524160 := by
  intro h
  have hc : ∀ q : ℕ, q.Prime → p ≠ q → Nat.Coprime p q := fun q hq hne =>
    (Nat.coprime_primes hp hq).2 hne
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 7 * 3 ^ 2 * 7) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right 7 (hc 2 Nat.prime_two hp2))
      (Nat.Coprime.pow_right 2 (hc 3 Nat.prime_three hp3))) (hc 7 (by norm_num) hp7))
  have h' : p ^ 2 ∣ (2 ^ 7 * 3 ^ 2 * 7) * 65 := by
    rwa [show (2 ^ 7 * 3 ^ 2 * 7) * 65 = 524160 by norm_num]
  have h65 : p ^ 2 ∣ 65 := hcop.dvd_of_dvd_mul_left h'
  have hle : p ^ 2 ≤ 65 := Nat.le_of_dvd (by norm_num) h65
  have hp8 : p ≤ 8 := by nlinarith
  interval_cases p <;> first | omega | (norm_num at hp) | (norm_num at h65)

private theorem s16g_card_dvd_orthogonal {m : ℕ} {b c : K}
    {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)) := by
  have hQ : ⇑(quadMinus m K b c) = StatedQuadMinus m K b c := coe_quadMinus m K b c
  have hle : F.map (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c) := by
    rintro _ ⟨x, hx, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]
    exact hFQ x hx v
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).injective] at h

private theorem s16g_card_le_norm_omegaMinus_two_generic {b c : K} (hK : Nat.card K = 8)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))}
    (hEN : E ≤ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p := by
  subst hm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  haveI := s16g_charP_two hK
  have hΓ := addCommutantScalar_statedOmegaMinus (m := 2) (K := K) (by norm_num) hirr
  obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (m := 2) (by norm_num) hirr
  obtain ⟨F, hFN, hF, hcard, hμF⟩ := s16g_exists_iso_elem_generic hΓ hK μ hp hp3 hp7 hEN hE
  have hdvd := s16g_card_dvd_orthogonal (m := 2) (b := b) (c := c) (F := F)
    (fun x hx v => hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v)
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) = 524160 := by
    have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) * ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
      GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
    have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
        524160 := by
      rw [h, hK]
      norm_num [Finset.Icc_self]
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
  rw [← hcard, hk]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  · rw [hk, hO] at hdvd
    exact absurd ((pow_dvd_pow p hk2).trans hdvd) (s16g_not_sq_dvd_orth hp hp2 hp3 hp7)

theorem s16g_pRank_le_statedSL_three {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 8) (ρ : ↥A →* MulAut (Multiplicative (Fin n → K)))
    (hρ : Function.Injective ρ) (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSL n K)) :
    CFSG.Open.pRank 3 A ≤ n / 2 + 1 :=
  s16g_pRank_le_of_embedding ρ hρ Nat.prime_three fun E hE hEel =>
    s16g_card_le_norm_sl_three hn hK (hE.trans (s16g_range_le_norm hρN)) hEel

theorem s16g_pRank_le_statedSL_seven {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 8) (ρ : ↥A →* MulAut (Multiplicative (Fin n → K)))
    (hρ : Function.Injective ρ) (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSL n K)) :
    CFSG.Open.pRank 7 A ≤ n :=
  s16g_pRank_le_of_embedding ρ hρ (by norm_num) fun E hE hEel =>
    s16g_card_le_norm_sl_seven hn hK (hE.trans (s16g_range_le_norm hρN)) hEel

theorem s16g_pRank_le_statedSp {G : Type*} [Group G] [Finite G] {A : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 8) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (ρ : ↥A →* MulAut (Multiplicative (Fin m ⊕ Fin m → K))) (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSp m K)) : CFSG.Open.pRank p A ≤ m + 1 := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  exact s16g_pRank_le_of_embedding ρ hρ hpp fun E hE hEel =>
    s16g_card_le_norm_sp hm hK hp (hE.trans (s16g_range_le_norm hρN)) hEel

theorem s16g_pRank_le_statedOmegaMinus_two {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {b c : K} (hK : Nat.card K = 8) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hm : m = 2) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank p A ≤ 2 := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  exact s16g_pRank_le_of_embedding ρ hρ hpp fun E hE hEel =>
    s16g_card_le_norm_omegaMinus_two hK hirr hm hp (hE.trans (s16g_range_le_norm hρN)) hEel

theorem s16g_pRank_le_statedOmegaMinus_three_seven {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {b c : K} (hK : Nat.card K = 8) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 3)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank 7 A ≤ 3 :=
  s16g_pRank_le_of_embedding ρ hρ (by norm_num) fun E hE hEel =>
    s16g_card_le_norm_omegaMinus_three_seven hK hirr hm (hE.trans (s16g_range_le_norm hρN)) hEel

theorem s16g_pRank_le_statedOmegaMinus_three_three {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {b c : K} (hK : Nat.card K = 8) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 3)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c)))
    (hρL : ρ.range ≤ s16gLin (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
    CFSG.Open.pRank 3 A ≤ 3 :=
  s16g_pRank_le_of_embedding ρ hρ Nat.prime_three fun E hE hEel =>
    s16g_card_le_norm_omegaMinus_three_three hK hirr hm (hE.trans (s16g_range_le_norm hρN))
      (hE.trans hρL) hEel

theorem s16g_pRank_le_statedOmegaMinus_two_generic {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {b c : K} (hK : Nat.card K = 8) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    (ρ : ↥A →* MulAut (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)))
    (hρ : Function.Injective ρ)
    (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.pRank p A ≤ 1 :=
  s16g_pRank_le_of_embedding ρ hρ hp fun E hE hEel => by
    rw [pow_one]
    exact s16g_card_le_norm_omegaMinus_two_generic hK hirr hm hp hp2 hp3 hp7
      (hE.trans (s16g_range_le_norm hρN)) hEel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

namespace CorFourTwoOpen

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggInnerDiagOnLab_bstar_of_pow {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : GGInnerDiagOnLab S p B L) : GGInnerDiagOnLab S p Bs L := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hBsN := hC.bstar_le_normalizer hnc
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := fun b hb => hC.2.1.2.1.2 b hb
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, -, -⟩, hpow⟩
  refine ⟨hs, hna, θ, hSl, hsplit, hBsN, fun b hb => ⟨_, hpow _ ?_,
    largeEvenInduces_ggLAut_inv L θ (hBsN (Bs.inv_mem hb))⟩⟩
  have h1 : (⟨b⁻¹, hBsN (Bs.inv_mem hb)⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hexp b hb, inv_one]; rfl)
  rw [← map_pow, h1, map_one]

end Config

theorem ggBstarInnerDiagLInputOn_of_pow {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  exact ggInnerDiagOnLab_bstar_of_pow h hC (ha₀ G p B x L hC.1) hM

theorem mem_conjImage_of_pow_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : ¬(d = 3 ∧ 2 ^ n = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hcard : Nat.card (K ≃+* K) = 2 * n := by
    obtain ⟨-, -, -, -, hc, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two
      (by omega : 1 ≤ 2 * n) (by rw [hK, ← pow_mul, mul_comm])
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσp : (InndiagSU.fieldFactorU h hd hdq φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  have hσn : (InndiagSU.fieldFactorU h hd hdq φ) ^ (2 * n) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime p (2 * n) := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
  have h1 : orderOf (InndiagSU.fieldFactorU h hd hdq φ) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hσp)
      (orderOf_dvd_of_pow_eq_one hσn)
  have hker : φ ∈ (InndiagSU.fieldFactorU h hd hdq).ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    exact h1
  rw [InndiagSU.ker_fieldFactorU] at hker
  exact InndiagSU.mem_conjImage_of_mem_inndiagU h hker

theorem recipeUnitary_pow_mem {d n p : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n)
    (hdq : ¬(d = 3 ∧ 2 ^ n = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun φ hφ =>
    mem_conjImage_of_pow_unitary hK hn hd hdq hp hp2 hpn hφ⟩

theorem recipeOmegaMinus_pow_mem {m n p : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, fun φ hφ =>
    OrthRest.mem_range_conj_minus hm hbc hK hp hp2 hpn hφ⟩

theorem recipeOmegaPlus_pow_mem_two {m : ℕ} (hm : 5 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m (2 ^ 1) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ 1) fun R _ I F =>
      Q R I F ∧ ∀ φ : MulAut R, φ ^ 3 = 1 → φ ∈ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun φ hφ =>
    OrthRest.mem_range_conj_plus_two hm hK2 hφ⟩

end CorFourTwoOpen

open CorFourTwoOpen

@[expose] def GGCorFourTwoOpenVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ≠ 2 ∧ ((lab.tag = .twD ∧ 4 ≤ lab.rank ∧ ¬ p ∣ lab.n) ∨
    (lab.tag = .D ∧ 5 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨
    ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ ¬ p ∣ lab.n))

theorem largeEvenLabelAll_pow_mem_vac {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoOpenVacLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp2, h⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨htag, hl, hpn⟩ | ⟨htag, hl, hn1, rfl⟩ | ⟨htag, hpn⟩
  · dsimp only at htag hl hpn
    subst htag
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_pow_mem (by omega) hp hp2 hpn hQ
  · dsimp only at htag hl hn1
    subst htag hn1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_pow_mem_two hl hQ
  · dsimp only at htag hpn
    rcases htag with rfl | ⟨rfl, h3⟩
    · have hl : 2 ≤ l := hlab.2.1
      have hl2 : l = 2 → 2 ≤ n := hlab.2.2
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      refine recipeUnitary_pow_mem (by omega) hn ?_ hp hp2 hpn hQ
      rintro ⟨hd, hq⟩
      have h2n : 2 ≤ n := hl2 (by omega)
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
      omega
    · subst h3
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hQ ⊢
      exact recipeUnitary_pow_mem (by norm_num) hn (by omega) hp hp2 hpn hQ

theorem ggBstarInnerDiagLInputOn_vac (ha₀ : GGLNoncyclicInput) (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGCorFourTwoOpenVacLabel p lab :=
  ggBstarInnerDiagLInputOn_of_pow ha₀ fun _ _ hp hlab h => largeEvenLabelAll_pow_mem_vac hp hlab h.2

end CFSG.StandardType

end

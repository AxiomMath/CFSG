module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1M4
import CFSG.CGT.Stroth77.L4Sylow.SylowSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.CGT.Stroth77.L4Sylow CFSG.LocalAnalysis.Mason73 CFSG.GH74.GLS.Stage1.Thm3.Sec8
open Equiv

private theorem uc22s2112r34q35_prime_not_dvd_480 {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ 480 := by
  intro hd
  have hfac : 480 = 2 ^ 5 * 3 * 5 := by norm_num
  rw [hfac] at hd
  rcases (Nat.Prime.dvd_mul hs).mp hd with h | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h3
    · have : s = 2 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
      omega
    · have : s = 3 := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h3
      omega
  · have : s = 5 :=
      (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 5)).mp h5
    omega

private theorem uc22s2112r34q35_prime_not_dvd_5760 {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ 5760 := by
  intro hd
  have hfac : 5760 = 2 ^ 7 * 3 ^ 2 * 5 := by norm_num
  rw [hfac] at hd
  rcases (Nat.Prime.dvd_mul hs).mp hd with h | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h3
    · have : s = 2 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
      omega
    · have : s = 3 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h3)
      omega
  · have : s = 5 :=
      (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 5)).mp h5
    omega

theorem uc22s2112r34q35_alpha_psl4_five {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 4 5 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  let H := StatedSL 4 K
  let Z := (StatedScalars (Fin 4) K).subgroupOf H
  have hZ : IsPGroup 2 Z := by
    have hZcard : Nat.card Z ∣ Nat.card K - 1 := by
      let f : Z →* StatedScalars (Fin 4) K :=
        { toFun := fun g => ⟨((g : H) : GL (Fin 4) K), g.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun g g' h => by
        have := congrArg (fun z : StatedScalars (Fin 4) K =>
          ((z : GL (Fin 4) K))) h
        exact Subtype.ext (Subtype.ext this)
      have h1 : Nat.card Z ∣ Nat.card (StatedScalars (Fin 4) K) :=
        Subgroup.card_dvd_of_injective f hf
      have h2 : Nat.card (StatedScalars (Fin 4) K) ∣ Nat.card Kˣ :=
        Subgroup.card_range_dvd _
      rw [Nat.card_units] at h2
      exact h1.trans h2
    have h4 : Nat.card K - 1 = 4 := by rw [hK]; norm_num
    exact IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [h4] at hZcard
      simpa using hZcard)
  have hq : Nat.card K % 4 = 1 := by rw [hK]; norm_num
  obtain ⟨D⟩ : Nonempty (L4Data K 2) :=
    exists_l4Data_of_dvd (n := 2) (by rw [hK]; norm_num)
  let φ : L4P 2 →* H := D.toSL (by norm_num)
  have hφinj : Function.Injective φ := D.toSL_injective (by norm_num)
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 * 1 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 1), add_zero]
  have hHcard : (Nat.card H).factorization 2 = 9 := by
    dsimp [H]
    rw [factorization_card_statedSL_four K hq, hK]
    norm_num [h4]
  have hcard : Nat.card φ.range = 2 ^ (Nat.card H).factorization 2 := by
    have h1 : Nat.card φ.range = Nat.card (L4P 2) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, card_L4P, hHcard]
  let S : Sylow 2 H := Sylow.ofCard φ.range hcard
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hS : (S : Subgroup H) = φ.range := Sylow.coe_ofCard _ _
  have hN : ∀ a ∈ (L4P 2 : Subgroup (L4Hat 2)), ∃ a' ∈ (L4P 2 : Subgroup (L4Hat 2)),
      (h : GL (Fin 4) K) * D.embed a * (h : GL (Fin 4) K)⁻¹ = D.embed a' := by
    intro a ha
    have hφmem : φ ⟨a, ha⟩ ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hmem : h * φ ⟨a, ha⟩ * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN (φ ⟨a, ha⟩)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(b : L4Hat 2), b.2, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 4) K))) hb
    simpa [φ, D.coe_toSL] using hb'.symm
  have hN' : ∀ a ∈ (L4P 2 : Subgroup (L4Hat 2)), ∃ a' ∈ (L4P 2 : Subgroup (L4Hat 2)),
      (h : GL (Fin 4) K)⁻¹ * D.embed a * (h : GL (Fin 4) K) = D.embed a' := by
    intro a ha
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hφmem : φ ⟨a, ha⟩ ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hmem : h⁻¹ * φ ⟨a, ha⟩ * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' (φ ⟨a, ha⟩)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(b : L4Hat 2), b.2, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 4) K))) hb
    simpa [φ, D.coe_toSL] using hb'.symm
  have hhGL : (h : GL (Fin 4) K) ^ s = 1 := by
    have := congrArg (fun z : H => ((z : GL (Fin 4) K))) hhs
    simpa using this
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) := by
    let := Fintype.ofFinite K
    have hq5 : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    have hcardGL : Nat.card (GL (Fin 2) K) = 480 := by
      rw [Matrix.card_GL_field, hq5, Fin.prod_univ_two]
      norm_num
    rw [hcardGL]
    exact uc22s2112r34q35_prime_not_dvd_480 hs hs7
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) -
        (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2))) ∨
      ¬ IsConst (pv (π : Perm (Fin 4)) (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) -
        (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2))) := by
    unfold IsConst pv
    decide
  have he₁ : hat (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have he₂ : hat (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  let y₀₁ : L4Hat 2 := hat ![2, 0, 0, 0] uc22s2112r34q35_r01
  let y₂₃ : L4Hat 2 := hat ![2, 0, 0, 0] uc22s2112r34q35_r23
  let y₀₂ : L4Hat 2 := hat 0 uc22s2112r34q35_r02
  have hy₀₁ : y₀₁ ∈ L4P 2 := by
    dsimp [y₀₁]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hy₂₃ : y₂₃ ∈ L4P 2 := by
    dsimp [y₂₃]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hy₀₂ : y₀₂ ∈ L4P 2 := by
    dsimp [y₀₂]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hz : hat (uc22s2112r34q35_zvec 2) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hgl : (h : GL (Fin 4) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_embed (n := 2) (by norm_num) D (L4P 2) hsep
      he₁ he₂ hy₀₁ hy₂₃ hy₀₂ (by rfl) (by rfl) (by rfl) hz hs (by omega) hhGL hGL hN hN'
  exact hh1 (Subtype.ext hgl)

theorem uc22s2112r34q35_alpha_psu4_three {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSU 4 3 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  let H := StatedSU 4 (3 ^ 1) K
  let Z := (StatedScalars (Fin 4) K).subgroupOf H
  have hZ : IsPGroup 2 Z := by
    have hZcard : Nat.card Z ∣ Nat.card K - 1 := by
      let f : Z →* StatedScalars (Fin 4) K :=
        { toFun := fun g => ⟨((g : H) : GL (Fin 4) K), g.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun g g' h => by
        have := congrArg (fun z : StatedScalars (Fin 4) K =>
          ((z : GL (Fin 4) K))) h
        exact Subtype.ext (Subtype.ext this)
      have h1 : Nat.card Z ∣ Nat.card (StatedScalars (Fin 4) K) :=
        Subgroup.card_dvd_of_injective f hf
      have h2 : Nat.card (StatedScalars (Fin 4) K) ∣ Nat.card Kˣ :=
        Subgroup.card_range_dvd _
      rw [Nat.card_units] at h2
      exact h1.trans h2
    have h8 : Nat.card K - 1 = 8 := by rw [hK]; norm_num
    exact IsPGroup.of_card_dvd_pow (n := 3) (by
      rw [h8] at hZcard
      simpa using hZcard)
  obtain ⟨D⟩ : Nonempty (L4Data K 2) :=
    exists_l4Data_of_card_eq_sq (n := 2) (q := 3) hK (by norm_num)
  let φ : L4P 2 →* H := D.toSU (by norm_num) (by norm_num)
  have hφinj : Function.Injective φ := D.toSU_injective (by norm_num) (by norm_num)
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 * 1 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 1), add_zero]
  have hHcard : (Nat.card H).factorization 2 = 9 := by
    dsimp [H]
    have h := factorization_card_statedSU_four (K := K) Nat.prime_three (by norm_num) hK
      (by norm_num)
    rw [show (3 : ℕ) ^ 1 = 3 by norm_num] at h
    norm_num [h4] at h
    rw [Nat.factorization_def _ Nat.prime_two]
    exact h
  have hcard : Nat.card φ.range = 2 ^ (Nat.card H).factorization 2 := by
    have h1 : Nat.card φ.range = Nat.card (L4P 2) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, card_L4P, hHcard]
  let S : Sylow 2 H := Sylow.ofCard φ.range hcard
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hS : (S : Subgroup H) = φ.range := Sylow.coe_ofCard _ _
  have hN : ∀ a ∈ (L4P 2 : Subgroup (L4Hat 2)), ∃ a' ∈ (L4P 2 : Subgroup (L4Hat 2)),
      (h : GL (Fin 4) K) * D.embed a * (h : GL (Fin 4) K)⁻¹ = D.embed a' := by
    intro a ha
    have hφmem : φ ⟨a, ha⟩ ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hmem : h * φ ⟨a, ha⟩ * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN (φ ⟨a, ha⟩)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(b : L4Hat 2), b.2, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 4) K))) hb
    simpa [φ, D.coe_toSU] using hb'.symm
  have hN' : ∀ a ∈ (L4P 2 : Subgroup (L4Hat 2)), ∃ a' ∈ (L4P 2 : Subgroup (L4Hat 2)),
      (h : GL (Fin 4) K)⁻¹ * D.embed a * (h : GL (Fin 4) K) = D.embed a' := by
    intro a ha
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hφmem : φ ⟨a, ha⟩ ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hmem : h⁻¹ * φ ⟨a, ha⟩ * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' (φ ⟨a, ha⟩)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(b : L4Hat 2), b.2, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 4) K))) hb
    simpa [φ, D.coe_toSU] using hb'.symm
  have hhGL : (h : GL (Fin 4) K) ^ s = 1 := by
    have := congrArg (fun z : H => ((z : GL (Fin 4) K))) hhs
    simpa using this
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) := by
    let := Fintype.ofFinite K
    have hq9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    have hcardGL : Nat.card (GL (Fin 2) K) = 5760 := by
      rw [Matrix.card_GL_field, hq9, Fin.prod_univ_two]
      norm_num
    rw [hcardGL]
    exact uc22s2112r34q35_prime_not_dvd_5760 hs hs7
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) -
        (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2))) ∨
      ¬ IsConst (pv (π : Perm (Fin 4)) (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) -
        (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2))) := by
    unfold IsConst pv
    decide
  have he₁ : hat (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have he₂ : hat (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  let y₀₁ : L4Hat 2 := hat ![2, 0, 0, 0] uc22s2112r34q35_r01
  let y₂₃ : L4Hat 2 := hat ![2, 0, 0, 0] uc22s2112r34q35_r23
  let y₀₂ : L4Hat 2 := hat 0 uc22s2112r34q35_r02
  have hy₀₁ : y₀₁ ∈ L4P 2 := by
    dsimp [y₀₁]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hy₂₃ : y₂₃ ∈ L4P 2 := by
    dsimp [y₂₃]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hy₀₂ : y₀₂ ∈ L4P 2 := by
    dsimp [y₀₂]
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hz : hat (uc22s2112r34q35_zvec 2) 1 ∈ L4P 2 := by
    rw [hat_mem_L4P]
    unfold detSum sgnH
    decide
  have hgl : (h : GL (Fin 4) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_embed (n := 2) (by norm_num) D (L4P 2) hsep
      he₁ he₂ hy₀₁ hy₂₃ hy₀₂ (by rfl) (by rfl) (by rfl) hz hs (by omega) hhGL hGL hN hN'
  exact hh1 (Subtype.ext hgl)

end CFSG.LocalAnalysis.UniquenessCase.UC22

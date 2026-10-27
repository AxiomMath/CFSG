module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.C24Eight.A5Sylow

open Equiv Perm

abbrev A5 : Type := alternatingGroup (Fin 5)

theorem pow_four_imp_pow_two :
    ∀ σ : Perm (Fin 5), sign σ = 1 → σ ^ 4 = 1 → σ ^ 2 = 1 := by
  decide +kernel

theorem card_square_one_le :
    ∀ ω : Fin 5, (Finset.univ.filter (fun σ : Perm (Fin 5) =>
      sign σ = 1 ∧ σ ω = ω ∧ σ ^ 2 = 1)).card ≤ 4 := by
  decide +kernel

theorem exists_order_three_fixing :
    ∀ ω : Fin 5, ∃ σ : Perm (Fin 5), sign σ = 1 ∧ σ ω = ω ∧ σ ^ 3 = 1 ∧ σ ≠ 1 := by
  decide +kernel

theorem exists_fixed_point (P : Subgroup A5) (hP : IsPGroup 2 P) :
    ∃ ω : Fin 5, ∀ p : P, ((p : A5) : Perm (Fin 5)) ω = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.card_modEq_card_fixedPoints (Fin 5)
  have h5 : Nat.card (Fin 5) = 5 := by simp
  rw [h5] at h
  have hne : Nat.card (MulAction.fixedPoints P (Fin 5)) ≠ 0 := by
    intro h0
    rw [h0] at h
    have := (Nat.modEq_iff_dvd' (by omega)).mp h.symm
    omega
  have : Nonempty (MulAction.fixedPoints P (Fin 5)) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hne (by simp)
  obtain ⟨⟨ω, hω⟩⟩ := this
  exact ⟨ω, fun p => hω p⟩

theorem natCard_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num
  decide

theorem card_eq_four (P : Subgroup A5) (hP : IsPGroup 2 P) (hi : ¬ 2 ∣ P.index) :
    Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h60 : Nat.card A5 = 60 := natCard_A5
  have hmul := P.card_mul_index
  rw [hk, h60] at hmul
  have hpos : 0 < P.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hk6 : k < 6 := by
    by_contra hk6
    have h64 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk6)
    nlinarith
  rw [hk]
  interval_cases k <;> simp at hmul ⊢
  all_goals omega

theorem exists_normalizer_order_three (P : Subgroup A5) (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.index) :
    ∃ y ∈ Subgroup.normalizer (P : Set A5), y ^ 3 = 1 ∧ y ≠ 1 := by
  have hcard := card_eq_four P hP hi
  obtain ⟨ω, hω⟩ := exists_fixed_point P hP
  have : Fintype P := Fintype.ofFinite P
  set E : Finset (Perm (Fin 5)) := Finset.univ.filter
    (fun σ : Perm (Fin 5) => sign σ = 1 ∧ σ ω = ω ∧ σ ^ 2 = 1) with hE
  set s : Finset (Perm (Fin 5)) :=
    (Finset.univ : Finset P).image (fun p : P => ((p : A5) : Perm (Fin 5))) with hs
  have hsE : s ⊆ E := by
    intro σ hσ
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hσ
    have hp4 : p ^ 4 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hp4' : ((p : A5) : Perm (Fin 5)) ^ 4 = 1 := by
      simpa using congrArg (fun q : P => ((q : A5) : Perm (Fin 5))) hp4
    have hsgn : sign ((p : A5) : Perm (Fin 5)) = 1 := (p : A5).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsgn, hω p,
      pow_four_imp_pow_two _ hsgn hp4'⟩
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_image_of_injective _ (fun p q h => Subtype.ext (Subtype.ext h)),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hEcard : E.card ≤ 4 := card_square_one_le ω
  have hsEeq : s = E := Finset.eq_of_subset_of_card_le hsE (by omega)
  have key : ∀ g : A5, ((g : A5) : Perm (Fin 5)) ω = ω → ∀ h ∈ P, g * h * g⁻¹ ∈ P := by
    intro g hg h hh
    have hmemE : ((g * h * g⁻¹ : A5) : Perm (Fin 5)) ∈ E := by
      have hh' : ((h : A5) : Perm (Fin 5)) ∈ E := hsE (Finset.mem_image.mpr ⟨⟨h, hh⟩, by simp, rfl⟩)
      obtain ⟨-, hsg, hfix, hsq⟩ := Finset.mem_filter.mp hh'
      have hginv : ((g⁻¹ : A5) : Perm (Fin 5)) ω = ω := by
        simp only [Subgroup.coe_inv]
        rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
        exact hg.symm
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (g * h * g⁻¹ : A5).2, ?_, ?_⟩
      · show (g : Perm (Fin 5)) (((h : A5) : Perm (Fin 5)) (((g⁻¹ : A5) : Perm (Fin 5)) ω)) = ω
        rw [hginv, hfix, hg]
      · have : ((g * h * g⁻¹ : A5) : Perm (Fin 5)) ^ 2 =
            (g : Perm (Fin 5)) * ((h : A5) : Perm (Fin 5)) ^ 2 * (g : Perm (Fin 5))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact conj_pow ..
        rw [this, hsq]
        simp
    rw [← hsEeq] at hmemE
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmemE
    have : (p : A5) = g * h * g⁻¹ := Subtype.ext hp
    rw [← this]
    exact p.2
  obtain ⟨σ, hsg, hfix, h3, h1⟩ := exists_order_three_fixing ω
  refine ⟨⟨σ, hsg⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key _ hfix h hh, fun hh => ?_⟩
    have hinv : ((⟨σ, hsg⟩ : A5)⁻¹ : A5) ∈ (⊤ : Subgroup A5) := trivial
    have hfix' : (((⟨σ, hsg⟩ : A5)⁻¹ : A5) : Perm (Fin 5)) ω = ω := by
      simp only [Subgroup.coe_inv]
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hfix.symm
    have := key _ hfix' _ hh
    simpa [mul_assoc] using this
  · exact Subtype.ext (by simpa using h3)
  · exact fun h => h1 (by simpa using congrArg Subtype.val h)

end CFSG.Quasithin.C24Eight.A5Sylow

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Parity for real virtual characters of odd-order groups
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Section5

universe v
universe u
open Section1 Section2 Section3 Section4


public theorem real_virtual_principal_orthogonal_scalarProduct_even
    {G : Type u} [Group G] [Finite G]
    {Γ Δ : Section1.ClassFunction G}
    (hodd : Odd (Nat.card G))
    (hΓvirt : Theory.Character.IsVirtualCharacter Γ)
    (hΓreal : Γ = Section1.conjugateCharacter Γ)
    (hΓone : Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0)
    (hΔvirt : Theory.Character.IsVirtualCharacter Δ)
    (hΔreal : Δ = Section1.conjugateCharacter Δ) :
    ∃ m : ℤ, Section1.scalarProduct G Γ Δ = ((2 * m : ℤ) : ℂ) := by
  classical
  have ofConjClassFunction_injective
      {φ ψ : Theory.Character.ConjClassFunction G}
      (h : Section1.ofConjClassFunction φ = Section1.ofConjClassFunction ψ) :
      φ = ψ := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun h g
  have virtualCharacter_isClassFunction
      {φ : Section1.ClassFunction G}
      (hφ : Theory.Character.IsVirtualCharacter φ) :
      Section1.IsClassFunction φ := by
    rcases hφ with ⟨r, m, n, ρ, rfl⟩
    intro x g
    unfold Theory.Character.virtualCharacterOfRepresentations
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hchar :
        Section1.IsCharacter ((ρ i).character : Section1.ClassFunction G) :=
      ⟨ULift.{u} (Fin (n i) → ℂ), inferInstance, inferInstance, inferInstance,
        Section1.uliftRepresentation (G := G) (V := Fin (n i) → ℂ) (ρ i), by
          ext g
          exact (Section1.uliftRepresentation_character
            (G := G) (V := Fin (n i) → ℂ) (rho := ρ i) g).symm⟩
    rw [Section1.isCharacter_isClassFunction ((ρ i).character) hchar x g]
  have scalarProduct_virtual_character_int
      {φ ψ : Section1.ClassFunction G}
      (hφ : Theory.Character.IsVirtualCharacter φ)
      (hψ : Section1.IsCharacter ψ) :
      ∃ z : ℤ, Section1.scalarProduct G φ ψ = (z : ℂ) := by
    rcases hφ with ⟨r, m, n, ρ, rfl⟩
    have hterm : ∀ i : Fin r,
        ∃ z : ℤ, Section1.scalarProduct G (ρ i).character ψ = (z : ℂ) := by
      intro i
      have hρchar :
          Section1.IsCharacter ((ρ i).character : Section1.ClassFunction G) :=
        ⟨ULift.{u} (Fin (n i) → ℂ), inferInstance, inferInstance, inferInstance,
          Section1.uliftRepresentation (G := G) (V := Fin (n i) → ℂ) (ρ i), by
            ext g
            exact (Section1.uliftRepresentation_character
              (G := G) (V := Fin (n i) → ℂ) (rho := ρ i) g).symm⟩
      rcases Section1.scalarProduct_character_character_eq_nat
          ((ρ i).character : Section1.ClassFunction G) ψ hρchar hψ with
        ⟨k, hk⟩
      exact ⟨(k : ℤ), by simpa using hk⟩
    refine ⟨∑ i : Fin r, m i * Classical.choose (hterm i), ?_⟩
    change Section1.scalarProduct G
        (fun g : G => ∑ i : Fin r,
          (((m i : ℂ) • ((ρ i).character : Section1.ClassFunction G)) g)) ψ =
        ((∑ i : Fin r, m i * Classical.choose (hterm i) : ℤ) : ℂ)
    rw [Section1.scalarProduct_fintype_sum_left]
    simp_rw [Section1.scalarProduct_smul_left]
    calc
      ∑ i : Fin r, (m i : ℂ) *
          Section1.scalarProduct G ((ρ i).character : Section1.ClassFunction G) ψ =
          ∑ i : Fin r, ((m i * Classical.choose (hterm i) : ℤ) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            let zi : ℤ := Classical.choose (hterm i)
            have hzi :
                Section1.scalarProduct G
                  ((ρ i).character : Section1.ClassFunction G) ψ = (zi : ℂ) :=
              Classical.choose_spec (hterm i)
            calc
              (m i : ℂ) * Section1.scalarProduct G
                    ((ρ i).character : Section1.ClassFunction G) ψ =
                  (m i : ℂ) * (zi : ℂ) := by rw [hzi]
              _ = ((m i * zi : ℤ) : ℂ) := by norm_num
              _ = ((m i * Classical.choose (hterm i) : ℤ) : ℂ) := by rfl
      _ = ((∑ i : Fin r, m i * Classical.choose (hterm i) : ℤ) : ℂ) := by simp
  have scalarProduct_conjugate_left
      (φ ψ : Section1.ClassFunction G) :
      Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
        star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
    simp [Section1.scalarProduct, Section1.conjugateCharacter]
  have scalarProduct_real_conjugate_right_eq
      {φ ψ : Section1.ClassFunction G}
      (hφreal : φ = Section1.conjugateCharacter φ)
      (hint : ∃ z : ℤ, Section1.scalarProduct G φ ψ = (z : ℂ)) :
      Section1.scalarProduct G φ (Section1.conjugateCharacter ψ) =
        Section1.scalarProduct G φ ψ := by
    rcases hint with ⟨z, hz⟩
    calc
      Section1.scalarProduct G φ (Section1.conjugateCharacter ψ) =
          star (Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ) := by
            simpa using
              (congrArg star (scalarProduct_conjugate_left φ ψ)).symm
      _ = star (Section1.scalarProduct G φ ψ) := by rw [← hφreal]
      _ = Section1.scalarProduct G φ ψ := by rw [hz]; simp
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  have conjugate_pairing :
      ∃ i0 : ι, ∃ pair : ι → ι,
        Section1.ofConjClassFunction (χ i0) = Section1.principalCharacter G ∧
          (∀ i,
            Section1.ofConjClassFunction (χ (pair i)) =
              Section1.conjugateCharacter (Section1.ofConjClassFunction (χ i))) ∧
          (∀ i, pair (pair i) = i) ∧
          (∀ i, i ≠ i0 → pair i ≠ i) ∧
          (∀ i, i ≠ i0 → pair i ≠ i0) := by
    rcases Section3.exists_principal_index_of_completeFamily (G := G)
        (χ := χ) hχ with ⟨i0, hi0⟩
    let μ : ι → Section1.ClassFunction G :=
      fun i => Section1.ofConjClassFunction (χ i)
    have hμ_irred : ∀ i, Section1.IsIrreducibleCharacterOnGroup (μ i) := by
      intro i
      exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
    have hconj_exists : ∀ i : ι,
        ∃ j : ι, μ j = Section1.conjugateCharacter (μ i) := by
      intro i
      rcases Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
          (hμ_irred i) with ⟨n, ρ, hρirr, hρchar⟩
      let ψ : Theory.Character.ConjClassFunction G := Theory.Character.characterClassFunction ρ
      have hψirr : Theory.Character.IsIrreducibleConjCharacter ψ := by
        refine ⟨⟨n, ρ, rfl⟩, ?_⟩
        exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
      rcases hχ.2.1 ψ hψirr with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      calc
        μ j = Section1.ofConjClassFunction ψ := by dsimp [μ]; rw [hj]
        _ = ρ.character := Section1.ofConjClassFunction_characterClassFunction ρ
        _ = Section1.conjugateCharacter (μ i) := hρchar.symm
    let pair : ι → ι := fun i => Classical.choose (hconj_exists i)
    have hpair_spec : ∀ i,
        μ (pair i) = Section1.conjugateCharacter (μ i) := by
      intro i
      exact Classical.choose_spec (hconj_exists i)
    have hconj_involutive : ∀ φ : Section1.ClassFunction G,
        Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
      intro φ
      ext g
      simp [Section1.conjugateCharacter]
    have hpair_pair : ∀ i, pair (pair i) = i := by
      intro i
      apply hχ.2.2
      apply ofConjClassFunction_injective
      dsimp [μ] at hpair_spec
      calc
        Section1.ofConjClassFunction (χ (pair (pair i))) =
            Section1.conjugateCharacter
              (Section1.ofConjClassFunction (χ (pair i))) := hpair_spec (pair i)
        _ = Section1.conjugateCharacter
              (Section1.conjugateCharacter
                (Section1.ofConjClassFunction (χ i))) := by rw [hpair_spec i]
        _ = Section1.ofConjClassFunction (χ i) := hconj_involutive _
    have hnonprincipal : ∀ i, i ≠ i0 →
        μ i ≠ Section1.principalCharacter G := by
      intro i hi hμi
      apply hi
      apply hχ.2.2
      apply ofConjClassFunction_injective
      dsimp [μ] at hμi hi0
      rw [hμi, hi0]
    have hpair_ne : ∀ i, i ≠ i0 → pair i ≠ i := by
      intro i hi hfix
      rcases hμ_irred i with ⟨n, ρ, hρirr, hρchar⟩
      have hne_principal : ρ.character ≠ Section1.principalCharacter G := by
        intro hρprincipal
        exact hnonprincipal i hi (by rw [hρchar, hρprincipal])
      have hfixed : ρ.character = Section1.conjugateCharacter ρ.character := by
        rw [← hρchar]
        have hs := hpair_spec i
        dsimp [μ] at hs
        rw [hfix] at hs
        exact hs
      exact (Section1.proposition_1_1 hodd ρ hρirr hne_principal) hfixed
    have hpair_ne_i0 : ∀ i, i ≠ i0 → pair i ≠ i0 := by
      intro i hi hpair_i0
      apply hnonprincipal i hi
      have hconj_i :
          Section1.conjugateCharacter (μ i) = Section1.principalCharacter G := by
        dsimp [μ] at hpair_spec hi0
        rw [← hpair_spec i, hpair_i0, hi0]
      calc
        μ i = Section1.conjugateCharacter (Section1.conjugateCharacter (μ i)) := by
          rw [hconj_involutive]
        _ = Section1.conjugateCharacter (Section1.principalCharacter G) := by
          rw [hconj_i]
        _ = Section1.principalCharacter G :=
          Section1.conjugateCharacter_principalCharacter
    exact ⟨i0, pair, hi0, hpair_spec, hpair_pair, hpair_ne, hpair_ne_i0⟩
  rcases conjugate_pairing with
    ⟨i0, pair, hi0, hpair_spec, hpair_pair, hpair_ne, hpair_ne_i0⟩
  let μ : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (χ i)
  have hΓclass : Section1.IsClassFunction Γ := virtualCharacter_isClassFunction hΓvirt
  have hΔclass : Section1.IsClassFunction Δ := virtualCharacter_isClassFunction hΔvirt
  have hΓint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G Γ (μ i) = (z : ℂ) := by
    intro i
    exact scalarProduct_virtual_character_int hΓvirt
      (by
        simpa [μ] using
          (Section1.isBookIrreducibleCharacter_of_representation_irreducible
            (χ i) (hχ.1 i)).1)
  have hΔint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G Δ (μ i) = (z : ℂ) := by
    intro i
    exact scalarProduct_virtual_character_int hΔvirt
      (by
        simpa [μ] using
          (Section1.isBookIrreducibleCharacter_of_representation_irreducible
            (χ i) (hχ.1 i)).1)
  let a : Section1.CoeffVector ι := Section3.irreducibleBasisCoeff Γ hΓint
  let d : Section1.CoeffVector ι := Section3.irreducibleBasisCoeff Δ hΔint
  have hΓeval : Section1.evalCoeff μ a = Γ :=
    Section3.irreducibleBasis_evalCoeff_coeff hχ b hb Γ hΓclass hΓint
  have hΔeval : Section1.evalCoeff μ d = Δ :=
    Section3.irreducibleBasis_evalCoeff_coeff hχ b hb Δ hΔclass hΔint
  have hΓcoeff_pair : ∀ i : ι, a (pair i) = a i := by
    intro i
    have hcoeffC : (a (pair i) : ℂ) = (a i : ℂ) := by
      calc
        (a (pair i) : ℂ) = Section1.scalarProduct G Γ (μ (pair i)) :=
          (Section3.irreducibleBasisCoeff_spec Γ hΓint (pair i)).symm
        _ = Section1.scalarProduct G Γ (Section1.conjugateCharacter (μ i)) := by
          simpa [μ] using congrArg (fun θ => Section1.scalarProduct G Γ θ) (hpair_spec i)
        _ = Section1.scalarProduct G Γ (μ i) :=
          scalarProduct_real_conjugate_right_eq hΓreal (hΓint i)
        _ = (a i : ℂ) := Section3.irreducibleBasisCoeff_spec Γ hΓint i
    exact_mod_cast hcoeffC
  have hΔcoeff_pair : ∀ i : ι, d (pair i) = d i := by
    intro i
    have hcoeffC : (d (pair i) : ℂ) = (d i : ℂ) := by
      calc
        (d (pair i) : ℂ) = Section1.scalarProduct G Δ (μ (pair i)) :=
          (Section3.irreducibleBasisCoeff_spec Δ hΔint (pair i)).symm
        _ = Section1.scalarProduct G Δ (Section1.conjugateCharacter (μ i)) := by
          simpa [μ] using congrArg (fun θ => Section1.scalarProduct G Δ θ) (hpair_spec i)
        _ = Section1.scalarProduct G Δ (μ i) :=
          scalarProduct_real_conjugate_right_eq hΔreal (hΔint i)
        _ = (d i : ℂ) := Section3.irreducibleBasisCoeff_spec Δ hΔint i
    exact_mod_cast hcoeffC
  have hΓprincipal_coeff : a i0 = 0 := by
    have hcoeffC : (a i0 : ℂ) = 0 := by
      calc
        (a i0 : ℂ) = Section1.scalarProduct G Γ (μ i0) :=
          (Section3.irreducibleBasisCoeff_spec Γ hΓint i0).symm
        _ = Section1.scalarProduct G Γ (Section1.principalCharacter G) := by
          simpa [μ] using congrArg (fun θ => Section1.scalarProduct G Γ θ) hi0
        _ = 0 := hΓone
    exact_mod_cast hcoeffC
  let s : Finset ι := Finset.univ.erase i0
  have hpair_mem_s : ∀ i, i ∈ s → pair i ∈ s := by
    intro i hi
    have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_erase.mpr ⟨hpair_ne_i0 i hi_ne, Finset.mem_univ _⟩
  have hprod_pair : ∀ i, i ∈ s → a (pair i) * d (pair i) = a i * d i := by
    intro i _hi
    rw [hΓcoeff_pair i, hΔcoeff_pair i]
  have even_sum_of_pairing :
      ∃ m : ℤ, (∑ i ∈ s, a i * d i) = 2 * m := by
    let P : ℕ → Prop := fun k =>
      ∀ t : Finset ι, t.card = k →
        (∀ i, i ∈ t → pair i ∈ t) →
        (∀ i, i ∈ t → pair (pair i) = i) →
        (∀ i, i ∈ t → pair i ≠ i) →
        (∀ i, i ∈ t → a (pair i) * d (pair i) = a i * d i) →
        ∃ m : ℤ, (∑ i ∈ t, a i * d i) = 2 * m
    have hmain : ∀ k, P k := by
      intro k
      refine Nat.strong_induction_on k ?_
      intro k ih t hcard hmem hinv hne hn
      by_cases htempty : t = ∅
      · subst htempty
        exact ⟨0, by simp⟩
      · rcases Finset.nonempty_iff_ne_empty.mpr htempty with ⟨x, hx⟩
        let y := pair x
        have hy : y ∈ t := hmem x hx
        have hyx : y ≠ x := hne x hx
        let rest : Finset ι := (t.erase x).erase y
        have hytx : y ∈ t.erase x := by simp [y, hy, hyx]
        have hrest_card_lt : rest.card < t.card := by
          have hsub : rest ⊆ t.erase x := by
            intro z hz
            exact (Finset.mem_erase.mp hz).2
          exact lt_of_le_of_lt (Finset.card_le_card hsub)
            (Finset.card_erase_lt_of_mem hx)
        have hmem_rest : ∀ i, i ∈ rest → pair i ∈ rest := by
          intro i hi
          have hi_t : i ∈ t :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
          have hpi_t : pair i ∈ t := hmem i hi_t
          have hpi_ne_x : pair i ≠ x := by
            intro hfix
            have hiy : i = y := by
              calc
                i = pair (pair i) := (hinv i hi_t).symm
                _ = pair x := by rw [hfix]
                _ = y := rfl
            exact (Finset.mem_erase.mp hi).1 hiy
          have hpi_ne_y : pair i ≠ y := by
            intro hfix
            have hpair_y : pair y = x := by simpa [y] using hinv x hx
            have hix : i = x := by
              calc
                i = pair (pair i) := (hinv i hi_t).symm
                _ = pair y := by rw [hfix]
                _ = x := hpair_y
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 hix
          simp [rest, hpi_t, hpi_ne_x, hpi_ne_y]
        have hinv_rest : ∀ i, i ∈ rest → pair (pair i) = i := by
          intro i hi
          exact hinv i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
        have hne_rest : ∀ i, i ∈ rest → pair i ≠ i := by
          intro i hi
          exact hne i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
        have hn_rest : ∀ i, i ∈ rest →
            a (pair i) * d (pair i) = a i * d i := by
          intro i hi
          exact hn i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
        rcases ih rest.card (by simpa [hcard] using hrest_card_lt)
            rest rfl hmem_rest hinv_rest hne_rest hn_rest with ⟨m, hm⟩
        have hsum :
            (∑ i ∈ t, a i * d i) =
              a x * d x + a y * d y + ∑ i ∈ rest, a i * d i := by
          calc
            (∑ i ∈ t, a i * d i) =
                ∑ i ∈ insert x (t.erase x), a i * d i := by
                  rw [Finset.insert_erase hx]
            _ = a x * d x + ∑ i ∈ t.erase x, a i * d i := by
                  rw [Finset.sum_insert (show x ∉ t.erase x by simp)]
            _ = a x * d x +
                (a y * d y + ∑ i ∈ rest, a i * d i) := by
                  rw [show (∑ i ∈ t.erase x, a i * d i) =
                      ∑ i ∈ insert y rest, a i * d i by
                    rw [Finset.insert_erase hytx]]
                  rw [Finset.sum_insert (show y ∉ rest by simp [rest])]
            _ = a x * d x + a y * d y + ∑ i ∈ rest, a i * d i := by ring
        have hyval : a y * d y = a x * d x := by
          simpa [y] using hn x hx
        refine ⟨a x * d x + m, ?_⟩
        rw [hsum, hyval, hm]
        ring
    exact hmain s.card s rfl hpair_mem_s
      (fun i _hi => hpair_pair i)
      (fun i hi => hpair_ne i (Finset.mem_erase.mp hi).1) hprod_pair
  rcases even_sum_of_pairing with ⟨m, hm⟩
  have hdot_s : Section1.coeffDot a d = ∑ i ∈ s, a i * d i := by
    unfold Section1.coeffDot
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => a i * d i) (Finset.mem_univ i0)
    calc
      (∑ i : ι, a i * d i) =
          (Finset.univ.erase i0).sum (fun i => a i * d i) + a i0 * d i0 :=
        hsplit.symm
      _ = (Finset.univ.erase i0).sum (fun i => a i * d i) := by
        rw [hΓprincipal_coeff]
        ring
      _ = ∑ i ∈ s, a i * d i := by simp [s]
  have hscalar :
      Section1.scalarProduct G Γ Δ = (Section1.coeffDot a d : ℂ) := by
    rw [← hΓeval, ← hΔeval]
    exact Section3.irreducibleBasis_scalarProduct_evalCoeff hχ a d
  exact ⟨m, by rw [hscalar, hdot_s, hm]⟩

end CFSG.Section5

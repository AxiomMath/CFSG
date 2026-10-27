module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Upper
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE8Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7E8Five
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Toral

theorem not_dvd_card_of_charP_two_of_odd {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  intro h
  rw [Nat.card_eq_fintype_card, hn] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem utoralAt_of_nonTorsion
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) {n : ℕ}
    (hn : 0 < n) :
    UToralAt τ p n := by
  intro K _ _ _ A hA hel hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Finite A := by
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn.ne')
  exact LieCore.isToralSubgroup_of_nonTorsion hp hp2 h3 h5 (L := AlgebraicClosure K) (ℓ := 2)
    (Ne.symm hp2)
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2)
    hA this hel

theorem utoralAt_of_bigBar
    {τ : Tag}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hbar : ExcFramesHalf.BigElemAbelianToralBar τ p) {n : ℕ} (hn : p ^ (τ.rank - 1) ≤ n) :
    UToralAt τ p n := by
  intro K _ _ _ A hA hel hcard
  exact hbar K (not_dvd_card_of_charP_two_of_odd hp hp2) A hA (fun x hx y hy => hel.comm hx hy)
    hel.2 (hcard ▸ hn)

end Toral

section Leaves

theorem uFieldInput_of_SL
    (hR : LangFamilyCompFieldSL) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    UFieldInput τ := by
  intro L _ _ _ p₀ p S hp hp2 ι a haT hap K hK
  obtain ⟨i, hspan, hfield⟩ := hR τ L p₀ p S hτ hp hp2 ι a haT hap K hK
  exact ⟨i, hspan, hfield.toAt⟩

theorem upper_E7_of_inputs
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E7 n f).K →* X} (h : GGTCHyp .E7 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E7 f) (htor : p = 3 → p ^ 6 ≤ Nat.card B) :
    Nat.card B ≤ p ^ 5 := by
  have hp := h.prime
  have hp2 := h.ne_two
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E7 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E7 p (Nat.card B) := by
    by_cases hp3 : p = 3
    · subst hp3
      refine utoralAt_of_bigBar (τ := .E7) hp hp2
        ExcFramesHalf.bigElemAbelianToralBar_E7_three ?_
      have h6 := htor rfl
      have h7 : Tag.rank .E7 - 1 = 6 := rfl
      rw [h7]
      exact h6
    · exact utoralAt_of_nonTorsion hp hp2 (fun _ => hp3) (fun h => by cases h) hBpos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, -, -, -, -, hcard, h2r⟩ := uframe_main
    (uFieldInput_of_SL hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hmod
    h.b_norm h.inner_E7 h.b_faithful h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hlt, hm⟩ hTor
  have hr : Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ 3 := by
    have : (Tag.E7).rank = 7 := rfl
    omega
  exact hcard.trans (Nat.pow_le_pow_right hp.pos (by omega))

theorem upper_E8_of_inputs
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E8 f) (htor : p = 3 ∨ p = 5 → p ^ 7 ≤ Nat.card B) :
    Nat.card B ≤ p ^ 6 := by
  have hp := h.prime
  have hp2 := h.ne_two
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have h7 : Tag.rank .E8 - 1 = 7 := rfl
  have hTor : UToralAt .E8 p (Nat.card B) := by
    by_cases hp3 : p = 3
    · subst hp3
      refine utoralAt_of_bigBar (τ := .E8) hp hp2
        ExcFramesHalf.bigElemAbelianToralBar_E8_three ?_
      rw [h7]
      exact htor (Or.inl rfl)
    · by_cases hp5 : p = 5
      · subst hp5
        refine utoralAt_of_bigBar (τ := .E8) hp hp2
          ExcFramesHalf.bigElemAbelianToralBar_E8_five ?_
        rw [h7]
        exact htor (Or.inr rfl)
      · exact utoralAt_of_nonTorsion hp hp2 (fun _ => hp3) (fun _ => hp5) hBpos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, -, -, -, -, hcard, h2r⟩ := uframe_main
    (uFieldInput_of_SL hR (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr rfl))) hp hp2 hmod
    h.b_norm h.inner_E8 h.b_faithful h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hlt, hm⟩ hTor
  have hr : Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ 4 := by
    have : (Tag.E8).rank = 8 := rfl
    omega
  exact hcard.trans (Nat.pow_le_pow_right hp.pos (by omega))

end Leaves

end CFSG.StandardType.TableCRes

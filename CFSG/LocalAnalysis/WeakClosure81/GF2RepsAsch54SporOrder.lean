module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2

import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Class
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.GLTheoremA.List93 (lie2Tags mem_lie2Tags)

@[expose] def lieAdmTwo : StatedLieTag → ℕ → ℕ → Bool
  | .PSL, n, f => decide (2 ≤ n ∧ 1 ≤ f ∧ ¬ (n = 2 ∧ f = 1))
  | .PSU, n, f => decide (3 ≤ n ∧ 1 ≤ f ∧ ¬ (n = 3 ∧ f = 1))
  | .PSp, n, f => decide (2 ≤ n ∧ 1 ≤ f ∧ ¬ (n = 2 ∧ f = 1))
  | .POmegaOdd, _, _ => false
  | .POmegaPlus, n, f => decide (4 ≤ n ∧ 1 ≤ f)
  | .POmegaMinus, n, f => decide (4 ≤ n ∧ 1 ≤ f)
  | .G2, n, f => decide (n = 0 ∧ 2 ≤ f)
  | .F4, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .E6, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .E7, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .E8, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .twistedE6, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .trialityD4, n, f => decide (n = 0 ∧ 1 ≤ f)
  | .twistedB2, n, f => decide (n = 0 ∧ f % 2 = 1 ∧ 3 ≤ f)
  | .twistedG2, _, _ => false
  | .twistedF4, n, f => decide (n = 0 ∧ f % 2 = 1 ∧ 3 ≤ f)
  | .Tits, n, f => decide (n = 0 ∧ f = 1)

@[expose] def calL0Small : StatedLieTag → ℕ → ℕ → Bool
  | .trialityD4, n, f => decide (n = 0 ∧ (f = 1 ∨ f = 2))
  | .PSU, n, f => decide ((n = 4 ∨ n = 5) ∧ f = 2)
  | .POmegaMinus, n, f => decide (n = 4 ∧ f = 2)
  | _, _, _ => false

@[expose] def calL0Orders (k : ℕ) : List ℕ :=
  (if 6 ≤ k then [181440] else []) ++
    lie2Tags.flatMap fun t => (List.range (k + 2)).flatMap fun n =>
      (List.range (k + 1)).filterMap fun f =>
        if lieAdmTwo t n f = true ∧ (2 < f ∨ calL0Small t n f = true) ∧
            lieSylowExponent t n * f ≤ k then
          some (lieOrderNumerator t n (2 ^ f) / lieOrderDivisor t n (2 ^ f))
        else none

theorem lieAdmTwo_of_admissible {t : StatedLieTag} {n f : ℕ} (h : StatedLieAdmissible t n 2 f) :
    lieAdmTwo t n f = true := by
  cases t
  case PSL =>
    obtain ⟨-, hf, hn, h2, -⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf, by rintro ⟨rfl, rfl⟩; exact h2 (by norm_num)⟩
  case PSU =>
    obtain ⟨-, hf, hn, h2⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf, by rintro ⟨rfl, rfl⟩; exact h2 (by norm_num)⟩
  case PSp =>
    obtain ⟨-, hf, hn, h2⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf, by rintro ⟨rfl, rfl⟩; exact h2 (by norm_num)⟩
  case POmegaOdd => exact absurd rfl h.2.2.2
  case POmegaPlus =>
    obtain ⟨-, hf, hn⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf⟩
  case POmegaMinus =>
    obtain ⟨-, hf, hn⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf⟩
  case G2 =>
    obtain ⟨-, -, hn, h3⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    refine ⟨hn, ?_⟩
    by_contra hlt
    have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  case F4 => obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case E6 => obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case E7 => obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case E8 => obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case twistedE6 =>
    obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case trialityD4 =>
    obtain ⟨-, hf, hn⟩ := h; simp only [lieAdmTwo, decide_eq_true_eq]; exact ⟨hn, hf⟩
  case twistedB2 =>
    obtain ⟨-, -, hn, -, hodd, h3⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, Nat.odd_iff.mp hodd, h3⟩
  case twistedG2 => exact absurd h.2.2.2.1 (by norm_num)
  case twistedF4 =>
    obtain ⟨-, -, hn, -, hodd, h3⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, Nat.odd_iff.mp hodd, h3⟩
  case Tits =>
    obtain ⟨-, -, hn, -, hf⟩ := h
    simp only [lieAdmTwo, decide_eq_true_eq]
    exact ⟨hn, hf⟩

theorem natCard_mem_calL0Orders (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : IsCalL0 X) {k : ℕ} (hk : ¬ 2 ^ (k + 1) ∣ Nat.card X) : Nat.card X ∈ calL0Orders k := by
  have key : ∀ {t : StatedLieTag} {n f : ℕ}, LieModel X t n 2 f →
      (2 < f ∨ calL0Small t n f = true) → Nat.card X ∈ calL0Orders k := by
    intro t n f hL hs
    have hadm := hL.admissible
    obtain ⟨hfin, hord, hv⟩ := hO X t n 2 f hadm hL
    have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
    have hle : lieSylowExponent t n * f ≤ k := by
      by_contra hlt
      exact hk ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).2 (by omega))
    obtain ⟨hn, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.HDesc.bounds_of_adm hadm rfl
    have hD : 0 < lieOrderDivisor t n (2 ^ f) := Nat.pos_of_ne_zero fun h0 =>
      CFSG.ComponentClassification.CatLeafProof.not_dvd_lieOrderDivisor hadm (h0 ▸ dvd_zero 2)
    have hcard : lieOrderNumerator t n (2 ^ f) / lieOrderDivisor t n (2 ^ f) = Nat.card X := by
      rw [← hord, Nat.mul_div_cancel _ hD]
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨t, mem_lie2Tags t,
      List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega),
        List.mem_filterMap.2 ⟨f, List.mem_range.2 (by omega), ?_⟩⟩⟩)
    rw [if_pos ⟨lieAdmTwo_of_admissible hadm, hs, hle⟩, hcard]
  rcases hX with ⟨f, hf, t, n, hL⟩ | hL | hL | hL | hL | hL | hA
  · exact key hL (Or.inl hf)
  · exact key (t := .trialityD4) (n := 0) (f := 1) hL (Or.inr (by decide))
  · exact key (t := .trialityD4) (n := 0) (f := 2) hL (Or.inr (by decide))
  · exact key (t := .PSU) (n := 4) (f := 2) hL (Or.inr (by decide))
  · exact key (t := .PSU) (n := 5) (f := 2) hL (Or.inr (by decide))
  · exact key (t := .POmegaMinus) (n := 4) (f := 2) hL (Or.inr (by decide))
  · obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin 9)) := hA
    have hc : Nat.card X = 181440 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hc] at hk ⊢
    have h6 : 6 ≤ k := by
      by_contra hlt
      exact hk (dvd_trans (Nat.pow_dvd_pow 2 (by omega : k + 1 ≤ 6)) (by norm_num))
    exact List.mem_append_left _ (by simp [h6])

@[expose] def calL0FreeCheck (k N : ℕ) : Bool :=
  decide (¬ 2 ^ (k + 1) ∣ N) && (calL0Orders k).all fun c => decide (¬ c ∣ N)

theorem not_isCalL0_of_dvd (hO : LieOrderFormulasInput) {k N : ℕ}
    (h : calL0FreeCheck k N = true) {X : Type} [Group X] (hX : IsCalL0 X) :
    ¬ Nat.card X ∣ N := by
  intro hdvd
  simp only [calL0FreeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2 _ (natCard_mem_calL0Orders hO hX fun h' => h.1 (h'.trans hdvd)) hdvd

theorem not_isCalL0_of_isCompositionFactor_of_dvd (hO : LieOrderFormulasInput) {k N : ℕ}
    (h : calL0FreeCheck k N = true) {X : Type} [Group X] [Finite X] (hX : Nat.card X ∣ N)
    {L : Type} [Group L] (hL : E1.IsCompositionFactor X L) : ¬ IsCalL0 L := fun hcal =>
  not_isCalL0_of_dvd hO h hcal ((isCompositionFactor_natCard_dvd hL).trans hX)

theorem not_hasCompFactor_isCalL0_of_dvd (hO : LieOrderFormulasInput) {k N : ℕ}
    (h : calL0FreeCheck k N = true) {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    (hA : Nat.card A ∣ N) : ¬ HasCompFactor A IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  exact not_isCalL0_of_isCompositionFactor_of_dvd hO h hA hL hcal

@[expose] def calL0OrderCheck (k N : ℕ) : Bool :=
  decide (¬ 2 ^ (k + 1) ∣ N) && (calL0Orders k).all fun c => decide (c ≠ N)

theorem not_isCalL0_of_card (hO : LieOrderFormulasInput) {k N : ℕ}
    (h : calL0OrderCheck k N = true) {X : Type} [Group X] (hX : Nat.card X = N) :
    ¬ IsCalL0 X := by
  intro hcal
  simp only [calL0OrderCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  subst hX
  exact h.2 _ (natCard_mem_calL0Orders hO hcal h.1) rfl

theorem not_isCalL0_of_isCompositionFactor_of_isSimpleGroup (hO : LieOrderFormulasInput) {k : ℕ}
    {X : Type} [Group X] [IsSimpleGroup X] (h : calL0OrderCheck k (Nat.card X) = true)
    {L : Type} [Group L] (hL : E1.IsCompositionFactor X L) : ¬ IsCalL0 L := by
  obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup hL
  exact not_isCalL0_of_card hO h (Nat.card_congr e.toEquiv).symm

end CFSG.LocalAnalysis.WeakClosure81

end

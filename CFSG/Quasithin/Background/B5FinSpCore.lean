module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Quasithin.Background.B5FinPerm

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.PresentationLocal Matrix

namespace B5FinSp

@[expose] def phi (v : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 := fun k => quadForm (omegaVec k) v

@[expose] def chi (x : Fin 6 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![x 0 + x 5, x 2 + x 4, x 2 + x 3, x 0 + x 1]

theorem chi_phi : ∀ v, chi (phi v) = v := by decide

theorem chi_add (x y : Fin 6 → ZMod 2) : chi (x + y) = chi x + chi y := by
  funext i
  fin_cases i <;> simp [chi] <;> ring

theorem chi_const (c : ZMod 2) : chi (fun _ => c) = 0 := by
  revert c
  decide

theorem sum_phi : ∀ v, ∑ i, phi v i = 0 := by decide

theorem exists_phi_of_sum_zero : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    ∃ (v : Fin 4 → ZMod 2) (c : ZMod 2), x = phi v + fun _ => c := by
  decide

theorem chi_eq_zero_iff : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    (chi x = 0 ↔ (x = 0 ∨ x = fun _ => 1)) := by
  decide

theorem phi_perm (h : sympFour) (v : Fin 4 → ZMod 2) (i : Fin 6) :
    phi v ((omegaPerm h)⁻¹ i) =
      phi (((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) i := by
  rw [phi, phi, ← map_inv, quadForm_omegaVec_omegaPerm, inv_inv]

theorem chi_permute (h : sympFour) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    chi (fun i => x ((omegaPerm h)⁻¹ i)) =
      ((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ chi x := by
  obtain ⟨v, c, rfl⟩ := exists_phi_of_sum_zero x hx
  have h1 : (fun i => (phi v + fun _ => c : Fin 6 → ZMod 2) ((omegaPerm h)⁻¹ i)) =
      phi (((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) + fun _ => c := by
    funext i
    simp only [Pi.add_apply, phi_perm]
  rw [h1, chi_add, chi_add, chi_phi, chi_phi, chi_const, add_zero, add_zero]

@[expose] def chiHom : G6.PermMod 6 →* Multiplicative (Fin 4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (chi (Multiplicative.toAdd x))
  map_one' := by
    have : chi (0 : Fin 6 → ZMod 2) = 0 := by decide
    exact congrArg Multiplicative.ofAdd this
  map_mul' x y := by
    exact congrArg Multiplicative.ofAdd (chi_add (Multiplicative.toAdd x) (Multiplicative.toAdd y))

theorem toAdd_chiHom (x : G6.PermMod 6) :
    Multiplicative.toAdd (chiHom x) = chi (Multiplicative.toAdd x) := rfl

theorem chiHom_permAct (h : sympFour) {x : G6.PermMod 6} (hx : x ∈ G6.coreMod 6) :
    chiHom (G6.permAct 6 (omegaPerm h) x) =
      Multiplicative.ofAdd
        (((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (chiHom x)) := by
  have h1 := chi_permute h (Multiplicative.toAdd x) hx
  have e : ∀ i, Multiplicative.toAdd (G6.permAct 6 (omegaPerm h) x) i =
      Multiplicative.toAdd x ((omegaPerm h)⁻¹ i) := fun i => rfl
  show Multiplicative.ofAdd (chi (Multiplicative.toAdd (G6.permAct 6 (omegaPerm h) x))) = _
  have e' : Multiplicative.toAdd (G6.permAct 6 (omegaPerm h) x) =
      fun i => Multiplicative.toAdd x ((omegaPerm h)⁻¹ i) := funext e
  rw [e', h1]
  rfl

theorem exists_core_chiHom_eq (w : Multiplicative (Fin 4 → ZMod 2)) :
    ∃ x ∈ G6.coreMod 6, chiHom x = w := by
  refine ⟨Multiplicative.ofAdd (phi (Multiplicative.toAdd w)), ?_, ?_⟩
  · rw [G6.mem_coreMod]
    exact sum_phi _
  · exact congrArg Multiplicative.ofAdd (chi_phi _)

theorem chiHom_eq_one_iff {x : G6.PermMod 6} (hx : x ∈ G6.coreMod 6) :
    chiHom x = 1 ↔ x ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 := by
  have h := chi_eq_zero_iff (Multiplicative.toAdd x) hx
  rw [Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  constructor
  · intro h1
    have h2 : chi (Multiplicative.toAdd x) = 0 := congrArg Multiplicative.toAdd h1
    rcases h.mp h2 with h3 | h3
    · exact ⟨Or.inl (Multiplicative.toAdd.injective h3), hx⟩
    · exact ⟨Or.inr (Multiplicative.toAdd.injective h3), hx⟩
  · rintro ⟨h1 | h1, -⟩
    · rw [h1]
      exact map_one chiHom
    · have : chi (Multiplicative.toAdd x) = 0 := h.mpr (Or.inr (by rw [h1]; rfl))
      exact congrArg Multiplicative.ofAdd this

end B5FinSp

end CFSG.Quasithin

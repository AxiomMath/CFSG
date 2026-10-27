module

public import CFSG.Quasithin.Background.Harris.R1.J2VertTau
public import CFSG.Quasithin.Recognition.J2RecCzAut

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM Equiv

theorem linePerm_mul (α β : MulAut QM) : linePerm (α * β) = linePerm α * linePerm β :=
  map_mul linePermHom α β

theorem linePerm_inv (α : MulAut QM) : linePerm α⁻¹ = (linePerm α)⁻¹ :=
  map_inv linePermHom α

theorem aut_eq_of_sign {σ : MulAut QM} (hσ : Perm.sign (linePerm σ) = 1) :
    ∃ p : QM, ∃ φ ∈ L0, σ = MulAut.conj p * φ := by
  have hmem : linePerm σ ∈ alternatingGroup (Fin 5) := hσ
  set φ : MulAut QM := ((lineEquiv.symm ⟨linePerm σ, hmem⟩ : ↥L0) : MulAut QM) with hφdef
  have hφ : φ ∈ L0 := (lineEquiv.symm ⟨linePerm σ, hmem⟩).2
  have hφp : linePerm φ = linePerm σ := linePerm_lineEquiv_symm ⟨linePerm σ, hmem⟩
  obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one (α := σ * φ⁻¹) (by
    rw [linePerm_mul, linePerm_inv, hφp, mul_inv_cancel])
  refine ⟨p, φ, hφ, ?_⟩
  rw [← hp, inv_mul_cancel_right]

theorem aut_eq (σ : MulAut QM) :
    ∃ p : QM, ∃ φ ∈ L0, σ = MulAut.conj p * φ ∨ σ = MulAut.conj p * φ * tau := by
  rcases Int.units_eq_one_or (Perm.sign (linePerm σ)) with h | h
  · obtain ⟨p, φ, hφ, hp⟩ := aut_eq_of_sign h
    exact ⟨p, φ, hφ, Or.inl hp⟩
  · have h' : Perm.sign (linePerm (σ * tau⁻¹)) = 1 := by
      rw [linePerm_mul, linePerm_inv, Perm.sign_mul, Perm.sign_inv, h, sign_linePerm_tau]
      rfl
    obtain ⟨p, φ, hφ, hp⟩ := aut_eq_of_sign h'
    refine ⟨p, φ, hφ, Or.inr ?_⟩
    rw [← hp, inv_mul_cancel_right]

theorem phiB_cube : phiB * phiB * phiB = 1 :=
  MulEquiv.ext fun p => phiBHom_three p

theorem phiA_phiB_five : (phiA * phiB) ^ 5 = 1 := by
  refine aut_ext fun j => ?_
  show phiAHom (phiBHom (phiAHom (phiBHom (phiAHom (phiBHom (phiAHom (phiBHom
    (phiAHom (phiBHom (x j.succ)))))))))) = x j.succ
  revert j
  decide +kernel

theorem eq_of_mem_L0 {α β : MulAut QM} (hα : α ∈ L0) (hβ : β ∈ L0)
    (h : linePerm α = linePerm β) : α = β :=
  aut_ext fun j => by rw [hα j.succ, hβ j.succ, h]

theorem closure_phiA_phiB : Subgroup.closure ({phiA, phiB} : Set (MulAut QM)) = L0 := by
  set X := Subgroup.closure ({phiA, phiB} : Set (MulAut QM)) with hX
  have hle : X ≤ L0 := by
    rw [hX, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact phiA_mem
    · exact phiB_mem
  have hA : ∀ σ ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 5))),
      ∃ β ∈ X, linePerm β = σ := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ⟨phiA, Subgroup.subset_closure (Set.mem_insert _ _), linePerm_phiA⟩
      · exact ⟨phiB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), linePerm_phiB⟩
    | one => exact ⟨1, one_mem _, map_one linePermHom⟩
    | mul y w _ _ ihy ihw =>
      obtain ⟨β, hβ, rfl⟩ := ihy
      obtain ⟨γ, hγ, rfl⟩ := ihw
      exact ⟨β * γ, mul_mem hβ hγ, linePerm_mul β γ⟩
    | inv y _ ihy =>
      obtain ⟨β, hβ, rfl⟩ := ihy
      exact ⟨β⁻¹, inv_mem hβ, linePerm_inv β⟩
  refine le_antisymm hle fun α hα => ?_
  have hσ : linePerm α ∈ Subgroup.closure ({pa, pb} : Set (Perm (Fin 5))) := by
    rw [closure_pa_pb]
    exact linePerm_mem_alternatingGroup hα
  obtain ⟨β, hβ, hβα⟩ := hA _ hσ
  rw [← eq_of_mem_L0 (hle hβ) hα hβα]
  exact hβ

theorem card_L0 : Nat.card L0 = 60 := by
  rw [Nat.card_congr lineEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

end CFSG.Quasithin.Background.Harris.R1.J2Vert

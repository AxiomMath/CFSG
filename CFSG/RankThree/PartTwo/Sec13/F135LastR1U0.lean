module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Equiv Equiv.Perm Subgroup

@[expose] noncomputable def u1AltPhi : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by omega) (by omega))

theorem u1AltPhi_apply (σ : Perm (Fin 7)) : u1AltPhi σ = MulAut.conjNormal σ := rfl

@[expose] noncomputable def u1AltEquiv {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    MulAut X ≃* Perm (Fin 7) :=
  (MulAut.congr e).trans u1AltPhi.symm

@[expose] noncomputable def u1Psi {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    X →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom

theorem u1Psi_apply {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) (k : X) :
    u1Psi e k = ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl

theorem u1AltEquiv_spec {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X)
    (k : X) : u1Psi e (y k) = u1AltEquiv e y * u1Psi e k * (u1AltEquiv e y)⁻¹ := by
  have h1 : u1AltPhi (u1AltEquiv e y) = MulAut.congr e y := u1AltPhi.apply_symm_apply _
  rw [u1AltPhi_apply] at h1
  have h2 : e (y k) = MulAut.congr e y (e k) := by simp [MulAut.congr_apply]
  rw [u1Psi_apply, u1Psi_apply, h2, ← h1, MulAut.conjNormal_apply]

theorem u1AltEquiv_unique {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X)
    (τ : Perm (Fin 7)) (h : ∀ k : X, u1Psi e (y k) = τ * u1Psi e k * τ⁻¹) :
    τ = u1AltEquiv e y := by
  apply u1AltPhi.injective
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  obtain ⟨k, rfl⟩ := e.surjective a
  have hl : ((u1AltPhi τ (e k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      τ * (e k : Perm (Fin 7)) * τ⁻¹ := by
    rw [u1AltPhi_apply, MulAut.conjNormal_apply]
  have hr : ((u1AltPhi (u1AltEquiv e y) (e k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      u1AltEquiv e y * (e k : Perm (Fin 7)) * (u1AltEquiv e y)⁻¹ := by
    rw [u1AltPhi_apply, MulAut.conjNormal_apply]
  rw [hl, hr, ← u1Psi_apply, ← u1AltEquiv_spec e y k]
  exact (h k).symm

theorem u1AltEquiv_conj {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) (k : X) :
    u1AltEquiv e (MulAut.conj k) = u1Psi e k := by
  symm
  apply u1AltEquiv_unique
  intro x
  simp [u1Psi, MulAut.conj_apply]

end CFSG.RankThree.PartTwo.Sec13.F135Last

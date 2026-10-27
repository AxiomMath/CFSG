module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNat
public import CFSG.RankThree.GF2n.Stroth80.Omega8SmallTransfer

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.Open
open scoped Matrix

section ToOm8

variable {K : Type} [Field K] {H : Type} [Group H] {φ : H →* GL (Fin 4 ⊕ Fin 4) K}

theorem phi_mem_statedOmega (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (h : H) :
    φ h ∈ StatedOmega (StatedQuadPlus 4 K) :=
  hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩

@[expose] noncomputable def toOm8 (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (h : H) :
    CFSG.StandardType.Triality.Om8 K :=
  reindexOm8 K ⟨φ h, phi_mem_statedOmega hφ h⟩

theorem toOm8_surjective (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) :
    Function.Surjective (toOm8 hφ) := by
  intro g
  have hg : ((((reindexOm8 K).symm g : StatedOmega (StatedQuadPlus 4 K)) :
      GL (Fin 4 ⊕ Fin 4) K)) ∈ φ.range := by
    rw [hφ]
    exact ((reindexOm8 K).symm g).2
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp hg
  refine ⟨h, ?_⟩
  have h1 : (⟨φ h, phi_mem_statedOmega hφ h⟩ : StatedOmega (StatedQuadPlus 4 K)) =
      (reindexOm8 K).symm g := Subtype.ext hh
  rw [toOm8, h1]
  exact (reindexOm8 K).apply_symm_apply g

theorem natRep_toOm8 (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (h : H)
    (v : Fin 4 ⊕ Fin 4 → K) :
    natRep K (toOm8 hφ h) v =
      ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v := by
  rw [natRep_apply, toOm8, MulEquiv.symm_apply_apply]

end ToOm8

section Descent

variable {K : Type} [Field K] {H : Type} [Group H] {φ : H →* GL (Fin 4 ⊕ Fin 4) K}
  {X : Type} [AddCommGroup X] [Module K X]

@[expose] def Descends (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (ρ : H →* (X ≃ₗ[K] X))
    (σ : Representation K (CFSG.StandardType.Triality.Om8 K) X) : Prop :=
  ∀ h : H, σ (toOm8 hφ h) = (ρ h : X →ₗ[K] X)

theorem exists_descends (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    {ρ : H →* (X ≃ₗ[K] X)} (hker : ∀ h : H, φ h = 1 → ρ h = 1) :
    ∃ σ : Representation K (CFSG.StandardType.Triality.Om8 K) X, Descends hφ ρ σ := by
  obtain ⟨ρ', hρ'⟩ := exists_statedOmega_factor hφ hker
  refine ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (ρ'.comp (reindexOm8 K).symm.toMonoidHom), fun h => ?_⟩
  change ((ρ' ((reindexOm8 K).symm (toOm8 hφ h)) : X ≃ₗ[K] X) : X →ₗ[K] X) = _
  rw [toOm8, MulEquiv.symm_apply_apply, hρ' h (phi_mem_statedOmega hφ h)]

variable {hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)} {ρ : H →* (X ≃ₗ[K] X)}
  {σ : Representation K (CFSG.StandardType.Triality.Om8 K) X}

theorem Descends.apply_eq (hd : Descends hφ ρ σ) (h : H) (x : X) :
    σ (toOm8 hφ h) x = ρ h x := by
  rw [hd h]
  rfl

end Descent

section Om8Irr8

variable {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X]

structure Om8Irr8 (σ : Representation K (CFSG.StandardType.Triality.Om8 K) X) : Prop where
  irreducible : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, σ g x ∈ S) → S = ⊥ ∨ S = ⊤
  finrank_eq : Module.finrank K X = 8

theorem Om8Irr8.exists_ne_one {σ : Representation K (CFSG.StandardType.Triality.Om8 K) X}
    (h : Om8Irr8 σ) : ∃ g, σ g ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < Module.finrank K X := by
    rw [h.finrank_eq]
    norm_num
  haveI : Module.Finite K X := Module.finite_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  rcases h.irreducible (Submodule.span K {x}) (fun g y hy => by rwa [hcon g]) with hbot | htop
  · exact hx (Submodule.span_singleton_eq_bot.mp hbot)
  · have h1 := finrank_span_singleton (K := K) hx
    rw [htop, finrank_top, h.finrank_eq] at h1
    omega

variable {H : Type} [Group H] {φ : H →* GL (Fin 4 ⊕ Fin 4) K}
  {hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)} {ρ : H →* (X ≃ₗ[K] X)}
  {σ : Representation K (CFSG.StandardType.Triality.Om8 K) X}

theorem Descends.irr8 (hd : Descends hφ ρ σ)
    (hirr : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hdim : Module.finrank K X = 8) : Om8Irr8 σ where
  irreducible S hS := hirr S fun h x hx => by
    rw [← hd.apply_eq h x]
    exact hS _ x hx
  finrank_eq := hdim

end Om8Irr8

end CFSG.RankThree.GF2n.Stroth80.Tri

end

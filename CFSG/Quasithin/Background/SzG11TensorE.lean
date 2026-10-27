module

public import CFSG.Quasithin.Background.SzG11TensorC
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

namespace Tensor

open Matrix

section Columns

variable (K : Type) [Field K]

@[expose] def colsAddEquiv : Matrix (Fin 2) (Fin 2) K ≃+ (Fin 2 → K) × (Fin 2 → K) where
  toFun X := (colOf 0 X, colOf 1 X)
  invFun p := colEmb 0 p.1 + colEmb 1 p.2
  left_inv X := (eq_colEmb_add X).symm
  right_inv p := by
    refine Prod.ext ?_ ?_
    · ext r
      simp [colOf, colEmb]
    · ext r
      simp [colOf, colEmb]
  map_add' X Y := rfl

variable {K}

end Columns

section Theta

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def thetaEquiv (I J : Submodule (ZMod 2) V) (hIJ : IsCompl I J)
    (ι : ↥I ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)) (φ : ↥I ≃ₗ[ZMod 2] ↥J) :
    Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V :=
  (zmodEquiv (colsAddEquiv (GaloisField 2 2))).trans
    ((ι.symm.prodCongr (ι.symm.trans φ)).trans (Submodule.prodEquivOfIsCompl I J hIJ))

theorem thetaEquiv_apply (I J : Submodule (ZMod 2) V) (hIJ : IsCompl I J)
    (ι : ↥I ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)) (φ : ↥I ≃ₗ[ZMod 2] ↥J)
    (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    thetaEquiv I J hIJ ι φ X =
      ((ι.symm (colOf 0 X) : ↥I) : V) + ((φ (ι.symm (colOf 1 X)) : ↥J) : V) := by
  show ((Submodule.prodEquivOfIsCompl I J hIJ) (ι.symm (colOf 0 X), φ (ι.symm (colOf 1 X))) : V) =
    _
  rw [Submodule.coe_prodEquivOfIsCompl']

end Theta

section Actions

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem left_action (H : Subgroup (GLV V)) (I J : Submodule (ZMod 2) V) (hIJ : IsCompl I J)
    (hI : Invariant H I) (α : ↥H ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (ι : ↥I ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2))
    (hι : ∀ (g : ↥H) (x : ↥I), ι (restrictHom H I hI g x) =
      ((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ ι x)
    (φ : ↥I ≃ₗ[ZMod 2] ↥J)
    (hφ : ∀ k ∈ H, ∀ i j : ↥I, k (i : V) = (j : V) →
      k ((φ i : ↥J) : V) = ((φ j : ↥J) : V))
    (g : ↥H) (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    (g : GLV V) (thetaEquiv I J hIJ ι φ X) =
      thetaEquiv I J hIJ ι φ (((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X) := by
  have h2 : ∀ u : Fin 2 → GaloisField 2 2, restrictHom H I hI g (ι.symm u) =
      ι.symm (((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ u) := by
    intro u
    have := hι g (ι.symm u)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, LinearEquiv.symm_apply_apply]
  rw [thetaEquiv_apply, thetaEquiv_apply, map_add]
  have h1 : ∀ u : Fin 2 → GaloisField 2 2, (g : GLV V) ((ι.symm u : ↥I) : V) =
      ((ι.symm (((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ u) : ↥I) : V) := by
    intro u
    rw [← h2 u, coe_restrictHom]
  have h3 : ∀ u : Fin 2 → GaloisField 2 2, (g : GLV V) ((φ (ι.symm u) : ↥J) : V) =
      ((φ (ι.symm (((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ u)) : ↥J) : V) := by
    intro u
    rw [← h2 u]
    exact hφ g g.2 (ι.symm u) (restrictHom H I hI g (ι.symm u)) (coe_restrictHom g _).symm
  rw [h1, h3, colOf_mul, colOf_mul]

end Actions

section RightAction

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_right_action (H C : Subgroup (GLV V))
    (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V)
    (α : ↥H ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (hact : ∀ (g : ↥H) X, (g : GLV V) (Θ X) =
      Θ (((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X))
    (hcent : C ≤ Subgroup.centralizer (H : Set (GLV V)))
    (hCperf : commutator ↥C = ⊤) (hCcard : Nat.card ↥C = 60) :
    ∃ β : ↥C ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2), ∀ (c : ↥C) X,
      (c : GLV V) (Θ X) = Θ (X * (((β c)⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2))) := by
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hright : ∀ c : ↥C, ∃ B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2),
      ∀ X, (c : GLV V) (Θ X) = Θ (X * B) := by
    intro c
    obtain ⟨B, hB⟩ := exists_mul_of_commute_sl2
      (fun X => Θ.symm ((c : GLV V) (Θ X)))
      (fun X Y => by simp only [map_add])
      (fun A X => by
        set h : ↥H := α.symm A with hh
        have hA : α h = A := α.apply_symm_apply A
        have h1 : Θ ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X) = (h : GLV V) (Θ X) := by
          rw [hact h X, hA]
        have h2 : (c : GLV V) ((h : GLV V) (Θ X)) = (h : GLV V) ((c : GLV V) (Θ X)) := by
          have := Subgroup.mem_centralizer_iff.1 (hcent c.2) (h : GLV V) h.2
          exact (congrArg (fun g : GLV V => g (Θ X)) this).symm
        show Θ.symm ((c : GLV V) (Θ ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X))) = _
        rw [h1, h2]
        conv_lhs => rw [← LinearEquiv.apply_symm_apply Θ ((c : GLV V) (Θ X))]
        rw [hact h, hA, LinearEquiv.symm_apply_apply])
    refine ⟨B, fun X => ?_⟩
    have := hB X
    rw [← this]
    exact (LinearEquiv.apply_symm_apply Θ _).symm
  choose R hR using hright
  have hR1 : R 1 = 1 := by
    apply Θ.injective
    have h1 := hR 1 1
    rw [Matrix.one_mul] at h1
    exact h1.symm
  have hRmul : ∀ c c' : ↥C, R (c * c') = R c' * R c := by
    intro c c'
    apply Θ.injective
    have h1 := hR (c * c') 1
    have h2 : ((c * c' : ↥C) : GLV V) (Θ 1) = (c : GLV V) ((c' : GLV V) (Θ 1)) := rfl
    rw [h2, hR c' 1, hR c, Matrix.one_mul, Matrix.one_mul] at h1
    exact h1.symm
  let b : ↥C →* Matrix (Fin 2) (Fin 2) (GaloisField 2 2) :=
    { toFun := fun c => R c⁻¹
      map_one' := by rw [inv_one, hR1]
      map_mul' := fun c c' => by rw [_root_.mul_inv_rev, hRmul] }
  have hb : Function.Injective b := by
    intro c c' h
    have h' : R c⁻¹ = R c'⁻¹ := h
    have : c⁻¹ = c'⁻¹ := by
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      obtain ⟨X, rfl⟩ := Θ.surjective v
      show ((c⁻¹ : ↥C) : GLV V) (Θ X) = ((c'⁻¹ : ↥C) : GLV V) (Θ X)
      rw [hR c⁻¹ X, hR c'⁻¹ X, h']
    exact inv_injective this
  obtain ⟨β, hβ⟩ := exists_mulEquiv_specialLinear hK4 hCperf hCcard b hb
  refine ⟨β, fun c X => ?_⟩
  have h1 : (((β c)⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = R c := by
    rw [← map_inv, hβ]
    show R (c⁻¹)⁻¹ = R c
    rw [inv_inv]
  rw [h1]
  exact hR c X

end RightAction

section Natural

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem natural_of_decomposition (H C : Subgroup (GLV V)) (I J : Submodule (ZMod 2) V)
    (hIJ : IsCompl I J) (hI : Invariant H I)
    (α : ↥H ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (ι : ↥I ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2))
    (hι : ∀ (g : ↥H) (x : ↥I), ι (restrictHom H I hI g x) =
      ((α g : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ ι x)
    (φ : ↥I ≃ₗ[ZMod 2] ↥J)
    (hφ : ∀ k ∈ H, ∀ i j : ↥I, k (i : V) = (j : V) →
      k ((φ i : ↥J) : V) = ((φ j : ↥J) : V))
    (hcent : C ≤ Subgroup.centralizer (H : Set (GLV V)))
    (hCperf : commutator ↥C = ⊤) (hCcard : Nat.card ↥C = 60) :
    IsNaturalMatrixModule (H ⊔ C) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) := by
  have hact := left_action H I J hIJ hI α ι hι φ hφ
  obtain ⟨β, hβ⟩ := exists_right_action H C (thetaEquiv I J hIJ ι φ) α hact hcent hCperf hCcard
  refine isNaturalMatrixModule_of_tensor H C (thetaEquiv I J hIJ ι φ) ?_ ?_ ?_ ?_
  · intro h hh
    exact ⟨α ⟨h, hh⟩, fun X => hact ⟨h, hh⟩ X⟩
  · intro A
    exact ⟨(α.symm A : ↥H), (α.symm A).2, fun X => by rw [hact, α.apply_symm_apply]⟩
  · intro c hc
    exact ⟨β ⟨c, hc⟩, fun X => hβ ⟨c, hc⟩ X⟩
  · intro B
    exact ⟨(β.symm B : ↥C), (β.symm B).2, fun X => by rw [hβ, β.apply_symm_apply]⟩

end Natural

end Tensor

end SzG11S

end G11

end CFSG.Quasithin

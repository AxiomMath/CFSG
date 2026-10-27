module

public import CFSG.Quasithin.Background.Harris.Sp4.Setup
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem commutator_eq_self_of_perfect' {G : Type*} [Group G] {S : Subgroup G}
    (hS : Group.IsPerfect S) : ⁅S, S⁆ = S := by
  have h := congrArg (Subgroup.map S.subtype) (Group.isPerfect_def.1 hS)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem commutator_statedSp_eq {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ⁅CFSG.Assembly.LowTwoRank.StatedSp 2 F, CFSG.Assembly.LowTwoRank.StatedSp 2 F⁆ =
      CFSG.Assembly.LowTwoRank.StatedSp 2 F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset F)) (n := 4) (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact commutator_eq_self_of_perfect'
    (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F (Or.inl ⟨s, hs⟩))

@[expose] def coordEquiv {F : Type} [Field F] [Algebra (ZMod 2) F] (θ : V ≃+ (Fin 4 → F)) :
    V ≃ₗ[ZMod 2] ((Fin 2 ⊕ Fin 2) → F) :=
  (LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 θ.toAddMonoidHom) θ.symm θ.left_inv
    θ.right_inv).trans (LinearEquiv.funCongrLeft (ZMod 2) F antiIdx)

theorem coordEquiv_apply {F : Type} [Field F] [Algebra (ZMod 2) F] (θ : V ≃+ (Fin 4 → F)) (v : V) (s : Fin 2 ⊕ Fin 2) :
    coordEquiv θ v s = θ v (antiIdx s) := rfl

theorem isNatural_of_twist {f : ℕ} (hf : 2 ≤ f) {L : Subgroup (GLV V)}
    (φ : ↥L ≃* antiSp (GaloisField 2 f)) (i : ℕ) (θ : V ≃+ (Fin 4 → GaloisField 2 f))
    (hθ : ∀ (g : antiSp (GaloisField 2 f)) (w : V), θ (piOf L φ g w) =
      (glMat (((minorAut (GaloisField 2 f) ^ i) g : antiSp (GaloisField 2 f)) :
        GL (Fin 4) (GaloisField 2 f))).mulVec (θ w)) :
    IsNaturalMatrixModule L ⁅CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f),
      CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : CharP (GaloisField 2 f) 2 := inferInstance
  have hperf := commutator_statedSp_eq h4
  let Φ : ↥L ≃* ↥⁅CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f),
      CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 f)⁆ :=
    (((φ.trans (show antiSp (GaloisField 2 f) ≃* antiSp (GaloisField 2 f) from
      minorAut (GaloisField 2 f) ^ i)).trans
      (antiSpEquiv (GaloisField 2 f))).trans (MulEquiv.subgroupCongr hperf.symm))
  refine ⟨Φ, coordEquiv θ, fun h v => ?_⟩
  have hg := hθ (φ h) v
  rw [piOf_apply, MulEquiv.symm_apply_apply] at hg
  funext s
  rw [coordEquiv_apply, hg]
  have hmat : ((Φ h : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 f)) =
      (glMat (((minorAut (GaloisField 2 f) ^ i) (φ h) : antiSp (GaloisField 2 f)) :
        GL (Fin 4) (GaloisField 2 f))).submatrix antiIdx antiIdx := rfl
  have hco : (coordEquiv θ v) ∘ antiIdx.symm = θ v := by
    funext c
    show θ v (antiIdx (antiIdx.symm c)) = θ v c
    rw [Equiv.apply_symm_apply]
  rw [hmat, Matrix.submatrix_mulVec_equiv, hco]
  rfl

end CFSG.Quasithin.G11.Harris.Sp4

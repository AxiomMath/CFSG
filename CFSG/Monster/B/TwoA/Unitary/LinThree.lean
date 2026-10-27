
module

public import CFSG.Monster.B.TwoA.Unitary.LinThreeBase
import all CFSG.Monster.B.TwoA.Unitary.LinThreeBase

public import CFSG.Monster.B.TwoA.Unitary.WStab
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary.LinThree

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.LinearGroups CFSG.Monster.B.TwoA
open CFSG.Monster.Code (AutPerm)
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

theorem closure_nativeGen :
    Subgroup.closure (Set.range nativeGen) = P₂ := by
  have e : (AutPerm.subtype ∘ n6Aut) = nativeGen := funext fun k => (nativeGen_eq k).symm
  rw [P₂_eq_map, ← closure_n6Aut, MonoidHom.map_closure, ← Set.range_comp, e]

attribute [local instance] restAction

theorem closure_genP :
    Subgroup.closure (Set.range genP) = ⊤ := by
  apply Subgroup.map_injective (f := P₂.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact closure_nativeGen

theorem range_rhoN_le :
    rhoN.range ≤ rhoS.range := by
  rw [MonoidHom.range_eq_map, ← closure_genP, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨genElt k, (rhoN_genP k).symm⟩

theorem range_rhoN_eq :
    rhoN.range = rhoS.range := by
  have : Finite rhoS.range := Nat.finite_of_card_ne_zero (by rw [natCard_range_rhoS]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge range_rhoN_le ?_
  rw [natCard_range_rhoS, ← Nat.card_congr (MonoidHom.ofInjective rhoN_injective).toEquiv,
    natCard_P₂]

@[expose] noncomputable def psi :
    P₂ ≃* SigmaL3 :=
  (MonoidHom.ofInjective rhoN_injective).trans ((MulEquiv.subgroupCongr range_rhoN_eq).trans
    (MonoidHom.ofInjective rhoS_injective).symm)

theorem rhoS_psi
    (p : P₂) : rhoS (psi p) = rhoN p := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective rhoS_injective)
    ((MulEquiv.subgroupCongr range_rhoN_eq) ((MonoidHom.ofInjective rhoN_injective) p))
  exact congrArg Subtype.val h

theorem psi_smul_j
    (p : P₂) (i : NativeCoord) : psi p • j i = j (restP p i) :=
  (congrArg (fun f : Equiv.Perm PlanePoint => f (j i)) (rhoS_psi p)).trans (rhoN_j p i)

theorem psi_genP
    (k : Fin 6) : psi (genP k) = genElt k :=
  rhoS_injective ((rhoS_psi _).trans (rhoN_genP k))

theorem closure_genElt :
    Subgroup.closure (Set.range genElt) = ⊤ := by
  have h : Set.range genElt = psi.toMonoidHom '' Set.range genP := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun k => (psi_genP k).symm)
  rw [h, ← MonoidHom.map_closure, closure_genP,
    Subgroup.map_top_of_surjective _ psi.surjective]

@[expose] noncomputable def P₂L :
    Subgroup P₂ :=
  (SemidirectProduct.inl : PSL(3, F4) →* SigmaL3).range.comap psi.toMonoidHom

theorem natCard_P₂L :
    Nat.card P₂L = 20160 := by
  have e : P₂L ≃ (SemidirectProduct.inl : PSL(3, F4) →* SigmaL3).range :=
    Equiv.subtypeEquiv psi.toEquiv fun _ => Iff.rfl
  rw [Nat.card_congr e, ← Nat.card_congr (MonoidHom.ofInjective
    (SemidirectProduct.inl_injective (φ := frobHom))).toEquiv, natCard_PSL3]

theorem mem_P₂L_iff
    (p : P₂) : p ∈ P₂L ↔ (psi p).right = 1 := by
  change psi p ∈ (SemidirectProduct.inl : PSL(3, F4) →* SigmaL3).range ↔ _
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]

theorem genP_mem_P₂L_iff
    (k : Fin 6) : genP k ∈ P₂L ↔ genFrob k = 0 := by
  rw [mem_P₂L_iff, psi_genP]
  change Multiplicative.ofAdd (genFrob k) = 1 ↔ _
  exact ofAdd_eq_one

theorem native_point_stabilizer_linear_three_isomorphism :
    Function.Bijective j ∧
    nativeLines.card = 21 ∧ (∀ d ∈ nativeLines, ∀ i ∈ d, 3 ≤ (i : ℕ)) ∧
    Set.InjOn (fun d : Finset (Fin 24) => j '' {i : NativeCoord | (i : Fin 24) ∈ d})
      ↑nativeLines ∧
    (fun d : Finset (Fin 24) => j '' {i : NativeCoord | (i : Fin 24) ∈ d}) '' ↑nativeLines =
      {S | ∃ f : Module.Dual F4 (Fin 3 → F4), f ≠ 0 ∧ S = {p : PlanePoint | f p.rep = 0}} ∧
    (∀ x : SigmaL3, (∀ p : PlanePoint, x • p = p) → x = 1) ∧
    (∀ k : Fin 6, nativeGen k ∈ P₂) ∧ Subgroup.closure (Set.range nativeGen) = P₂ ∧
    Function.Injective restP ∧
    (∀ k : Fin 6, (genMat k).det = 1) ∧ genFrob = ![0, 0, 0, 0, 0, 1] ∧
    (∀ (k : Fin 6) (i : NativeCoord),
      normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (jVec i)) =
        jIdx (restP (genP k) i)) ∧
    (∀ (k : Fin 6) (i : NativeCoord),
      j (restP (genP k) i) = pairElt (genSL k) (genFrob k) • j i) ∧
    (∃ Ψ : P₂ ≃* SigmaL3,
      (∀ (p : P₂) (i : NativeCoord), j (restP p i) = Ψ p • j i) ∧
      (∀ k : Fin 6, Ψ (genP k) = pairElt (genSL k) (genFrob k)) ∧
      Nat.card ((SemidirectProduct.inl : PSL(3, F4) →* SigmaL3).range.comap Ψ.toMonoidHom) =
        20160 ∧
      ∀ k : Fin 6, genP k ∈ (SemidirectProduct.inl : PSL(3, F4) →* SigmaL3).range.comap
        Ψ.toMonoidHom ↔ genFrob k = 0) ∧
    Subgroup.closure (Set.range fun k => pairElt (genSL k) (genFrob k)) = ⊤ ∧
    frobHom (Multiplicative.ofAdd 1) = frobPSL ∧
    (∀ p : PlanePoint, (⟨1, Multiplicative.ofAdd 1⟩ : SigmaL3) • p = frobP p) ∧
    Nat.card P₂ = 40320 ∧ Nat.card PSL(3, F4) = 20160 ∧ Nat.card SigmaL3 = 40320 :=
  ⟨j_bijective, card_nativeLines, fun _ hd => nativeLines_ge hd, injOn_image_nativeLines,
    image_nativeLines, eq_one_of_smul_eq, nativeGen_mem, closure_nativeGen, restP_injective,
    genMat_det, rfl, normIdx_pairVec, fun k i => (genElt_smul_j k i).symm,
    ⟨psi, fun p i => (psi_smul_j p i).symm, psi_genP, natCard_P₂L, genP_mem_P₂L_iff⟩,
    closure_genElt, frobPow_one, frob_smul, natCard_P₂, natCard_PSL3, natCard_SigmaL3⟩

end CFSG.Monster.B.TwoA.Unitary.LinThree

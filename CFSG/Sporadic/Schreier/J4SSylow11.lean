module

public import CFSG.Sporadic.Schreier.J4SReal
public import CFSG.Sporadic.Schreier.J4SEleven
public import CFSG.Sporadic.Schreier.J4SCentGen

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowLin_sub_one_eq (h : J) :
    ((rowLin h : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id =
      Matrix.mulVecLin (φ h⁻¹ - 1)ᵀ := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, rowLin_apply, LinearMap.id_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_sub, Matrix.vecMul_one, φ_apply,
    Subgroup.coe_inv]

theorem rank_rowLin_sub_one (h : J) :
    Module.finrank (ZMod 2) (LinearMap.range
      (((rowLin h : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
        (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id)) =
      (φ h⁻¹ - 1).rank := by
  rw [rowLin_sub_one_eq, ← Matrix.rank_transpose (φ h⁻¹ - 1)]
  rfl

theorem small_rank_rowGroup :
    ∀ g ∈ rowGroup, (orderOf g = 2 ∨ orderOf g = 3) →
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range
      ((g : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id)) := by
  rintro _ ⟨h, rfl⟩ ho
  rw [rank_rowLin_sub_one]
  have hoh : orderOf h⁻¹ = orderOf (rowLin h) := by
    rw [orderOf_inv, orderOf_injective rowLin rowLin_injective h]
  have h3 := R3E_J4_elements_of_order_two_or_three_have_rank_at_least_three h⁻¹ (hoh ▸ ho)
  rwa [← φ_apply] at h3

theorem ker_rowLin_qz : LinearMap.ker
    (((rowLin qz : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - 1) = rowFix (φ qz) := by
  ext v
  rw [LinearMap.mem_ker, mem_rowFix, LinearMap.sub_apply, LinearEquiv.coe_coe, rowLin_apply,
    Module.End.one_apply, sub_eq_zero]
  have e1 : (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) * φ qz = 1 := by
    rw [φ_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 : φ qz * (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) = 1 := by
    rw [φ_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    calc v ᵥ* φ qz = (v ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2))) ᵥ* φ qz := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, e1, Matrix.vecMul_one]
  · intro h
    calc v ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)) =
        (v ᵥ* φ qz) ᵥ* (((qz : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, e2, Matrix.vecMul_one]

theorem finrank_ker_rowLin_qz :
    Module.finrank (ZMod 2) (LinearMap.ker
    (((rowLin qz : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
      (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - 1)) = 2 := by
  rw [ker_rowLin_qz, finrank_rowFix_qz]

theorem closure_Q11_gens :
    Subgroup.closure ({⟨qx, qx_mem⟩, ⟨qy, qy_mem⟩} : Set Q11) = ⊤ := by
  apply Subgroup.map_injective Q11.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show Subgroup.closure ({qx, qy} : Set J) = Q11
  rfl

theorem qz_eq_commutator :
    (⟨qz, qz_mem⟩ : Q11) = ⁅(⟨qx, qx_mem⟩ : Q11), ⟨qy, qy_mem⟩⁆ := Subtype.ext rfl

theorem odd_card_pointwiseFixingAut_Q11 :
    Odd (Nat.card (pointwiseFixingAut Q11)) :=
  @odd_card_pointwiseFixingAut_of_realization (Fin 112 → ZMod 2) _ _ J (Subgroup.toGroup J) _ _
    jq jq_nondegenerate rowLin rowLin_injective rowGroup_le_orthogonal small_rank_rowGroup
    isoHom isoHom_injective isoHom_mem rowLin_aut Q11 isExtraspecial_Q11 card_Q11 exponent_Q11
    ⟨qx, qx_mem⟩ ⟨qy, qy_mem⟩ ⟨qz, qz_mem⟩ closure_Q11_gens qz_eq_commutator
    (Module.finrank_fin_fun (ZMod 2)) finrank_ker_rowLin_qz

theorem card_pointwiseFixingAut_congr {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    (Q : Subgroup G) :
    Nat.card (pointwiseFixingAut Q) = Nat.card (pointwiseFixingAut (Q.map ψ.toMonoidHom)) := by
  have hmap : (pointwiseFixingAut Q).map (MulAut.congr ψ).toMonoidHom =
      pointwiseFixingAut (Q.map ψ.toMonoidHom) := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      rw [SetLike.mem_coe, mem_pointwiseFixingAut] at hα
      rw [mem_pointwiseFixingAut]
      rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
      rw [hα q hq]
    · intro hβ
      refine ⟨(MulAut.congr ψ).symm β, ?_, by rw [MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]⟩
      rw [SetLike.mem_coe, mem_pointwiseFixingAut]
      intro q hq
      have h := (mem_pointwiseFixingAut.1 hβ) (ψ q) ⟨q, hq, rfl⟩
      have e1 : (MulAut.congr ψ).symm β q = ψ.symm (β (ψ q)) := rfl
      rw [e1, h, MulEquiv.symm_apply_apply]
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.congr ψ).injective]

theorem odd_card_pointwiseFixingAut_of_sylow {G H : Type*} [Group G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H) (P₀ : Sylow p H)
    (h₀ : Odd (Nat.card (pointwiseFixingAut (P₀ : Subgroup H)))) (Q : Sylow p G) :
    Odd (Nat.card (pointwiseFixingAut (Q : Subgroup G))) := by
  have hGH : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card ((Q : Subgroup G).map e.toMonoidHom) =
      p ^ (Nat.card H).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity, hGH]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P₀ (Sylow.ofCard _ hcard)
  have hQg : (Q : Subgroup G).map e.toMonoidHom =
      (P₀ : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow p H => (P : Subgroup H)) hg
    simp only [Sylow.coe_ofCard] at h1
    rw [← h1, Sylow.coe_subgroup_smul]
    rfl
  rw [card_pointwiseFixingAut_congr e, hQg, ← card_pointwiseFixingAut_congr (MulAut.conj g)]
  exact h₀

theorem R3E_J4_Sylow_eleven_full_automorphism_centralizer_odd
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.J4)) (Q : Sylow 11 T) :
    Odd (Nat.card (pointwiseFixingAut (Q : Subgroup T))) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hT
  exact @odd_card_pointwiseFixingAut_of_sylow T J _ (Subgroup.toGroup J) _ 11 _
    (e.trans (seedEquiv j4Facts.mat)) Q11Sylow odd_card_pointwiseFixingAut_Q11 Q

end CFSG.Sporadic.J4Schreier

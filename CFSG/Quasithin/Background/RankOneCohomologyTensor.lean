module

public import CFSG.Quasithin.Background.QuadraticCocycle

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open scoped TensorProduct

theorem exists_tensor_cocycle_normalForm
    {B Q X Z : Type*} [Group B] [Finite B]
    [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    (ρQ : Representation (ZMod 2) B Q)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ))
    (hH1 : Module.finrank (ZMod 2)
      (H1 (Representation.dual ρQ)) ≤ 1)
    (c : B → (Q ⊗[ZMod 2] X →ₗ[ZMod 2] Z))
    (hc : c ∈ Z1 (Representation.linHom
      (ρQ.tprod (Representation.trivial (ZMod 2) B X))
      (Representation.trivial (ZMod 2) B Z))) :
    ∃ ξ : X →ₗ[ZMod 2] Z,
      ∃ t : Q ⊗[ZMod 2] X →ₗ[ZMod 2] Z,
        ∀ g q x,
          c g (q ⊗ₜ[ZMod 2] x) =
            (d g q) • ξ x +
              (t ((ρQ g⁻¹ q) ⊗ₜ[ZMod 2] x) -
                t (q ⊗ₜ[ZMod 2] x)) := by
  classical
  have : Module.Finite (ZMod 2) X := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) Q) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) Q => (f : Q → ZMod 2))
      DFunLike.coe_injective
  let bX : Module.Basis (Fin (Module.finrank (ZMod 2) X)) (ZMod 2) X := Module.finBasis (ZMod 2) X
  let bZ : Module.Basis (Fin (Module.finrank (ZMod 2) Z)) (ZMod 2) Z := Module.finBasis (ZMod 2) Z
  let cij : Fin (Module.finrank (ZMod 2) X) → Fin (Module.finrank (ZMod 2) Z) →
      B → Module.Dual (ZMod 2) Q :=
    fun i j g =>
      (bZ.coord j).comp ((c g).comp ((TensorProduct.mk (ZMod 2) Q X).flip (bX i)))
  have hcij : ∀ i j, cij i j ∈ Z1 (Representation.dual ρQ) := by
    intro i j g h
    ext q
    have hgh := DFunLike.congr_fun (hc g h) (q ⊗ₜ[ZMod 2] bX i)
    simp only [Representation.linHom_apply, Representation.tprod_apply] at hgh
    simpa [cij, LinearMap.add_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, map_add] using
      congrArg (bZ.coord j) hgh
  have hcases : ∀ i j, ∃ (a : ZMod 2) (t : Module.Dual (ZMod 2) Q),
      ∀ g q, cij i j g q = a * d g q + (t (ρQ g⁻¹ q) - t q) := by
    intro i j
    by_cases hB1 : cij i j ∈ B1 (Representation.dual ρQ)
    · rw [B1, LinearMap.mem_range] at hB1
      obtain ⟨t, ht⟩ := hB1
      refine ⟨0, t, fun g q => ?_⟩
      have hg : cij i j g = (Representation.dual ρQ) g t - t := by
        rw [← congrFun ht g]
        rfl
      calc
        cij i j g q = ((Representation.dual ρQ) g t - t) q := DFunLike.congr_fun hg q
        _ = ((Representation.dual ρQ) g t) q - t q := rfl
        _ = t (ρQ g⁻¹ q) - t q := by
          rw [Representation.dual_apply, Module.Dual.transpose_apply]
          rfl
        _ = 0 * d g q + (t (ρQ g⁻¹ q) - t q) := by rw [zero_mul, zero_add]
    · obtain ⟨t, ht⟩ :=
        exists_coboundary_of_mem_Z1_of_not_mem_B1_of_finrank_H1_le_one
          (Representation.dual ρQ) hH1 (hcij i j) hd hB1 hdn
      refine ⟨1, t, fun g q => ?_⟩
      have hg : cij i j g = d g + coboundary (Representation.dual ρQ) t g := by
        simpa only [Pi.add_apply] using congrFun ht g
      calc
        cij i j g q = d g q + (((Representation.dual ρQ) g t) q - t q) := by
          have hq := DFunLike.congr_fun hg q
          simpa [LinearMap.add_apply, coboundary] using hq
        _ = d g q + (t (ρQ g⁻¹ q) - t q) := by
          rw [Representation.dual_apply, Module.Dual.transpose_apply]
          rfl
        _ = 1 * d g q + (t (ρQ g⁻¹ q) - t q) := by rw [one_mul]
  let a : Fin (Module.finrank (ZMod 2) X) → Fin (Module.finrank (ZMod 2) Z) → ZMod 2 :=
    fun i j => Classical.choose (hcases i j)
  let tf : Fin (Module.finrank (ZMod 2) X) → Fin (Module.finrank (ZMod 2) Z) →
      Module.Dual (ZMod 2) Q :=
    fun i j => Classical.choose (Classical.choose_spec (hcases i j))
  have hform : ∀ i j g q, cij i j g q =
      a i j * d g q + (tf i j (ρQ g⁻¹ q) - tf i j q) :=
    fun i j g q => Classical.choose_spec (Classical.choose_spec (hcases i j)) g q
  let ξ : X →ₗ[ZMod 2] Z := bX.constr (ZMod 2) fun i => ∑ j, a i j • bZ j
  let T : X →ₗ[ZMod 2] (Q →ₗ[ZMod 2] Z) :=
    bX.constr (ZMod 2) fun i => ∑ j, (tf i j).smulRight (bZ j)
  let Φ : Q →ₗ[ZMod 2] X →ₗ[ZMod 2] Z := T.flip
  let t : Q ⊗[ZMod 2] X →ₗ[ZMod 2] Z := TensorProduct.lift Φ
  have hξ_coord : ∀ i k, bZ.coord k (ξ (bX i)) = a i k := by
    intro i k
    have hsum : bZ.coord k (∑ j, a i j • bZ j) = a i k := by
      rw [map_sum]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp [hjk]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    simpa only [ξ, Module.Basis.constr_basis] using hsum
  have ht_coord : ∀ i k q, bZ.coord k (t (q ⊗ₜ[ZMod 2] bX i)) = tf i k q := by
    intro i k q
    have hsum : bZ.coord k (∑ j, (tf i j q) • bZ j) = tf i k q := by
      rw [map_sum]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp [hjk]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have htq : t (q ⊗ₜ[ZMod 2] bX i) = ∑ j, (tf i j q) • bZ j := by
      simp only [t, TensorProduct.lift.tmul, Φ, LinearMap.flip_apply, T, Module.Basis.constr_basis,
        LinearMap.sum_apply, LinearMap.smulRight_apply]
    rw [htq]
    exact hsum
  refine ⟨ξ, t, ?_⟩
  intro g q x
  let L1 : X →ₗ[ZMod 2] Z := (c g).comp ((TensorProduct.mk (ZMod 2) Q X) q)
  let L2 : X →ₗ[ZMod 2] Z :=
    (d g q) • ξ +
      (t.comp ((TensorProduct.mk (ZMod 2) Q X) (ρQ g⁻¹ q)) -
        t.comp ((TensorProduct.mk (ZMod 2) Q X) q))
  have hL : L1 = L2 := by
    apply bX.ext
    intro i
    apply bZ.ext_elem
    intro k
    have h1 : bZ.coord k (L1 (bX i)) = cij i k g q := by
      simp only [L1, LinearMap.comp_apply, TensorProduct.mk_apply, cij, LinearMap.flip_apply]
    have h2 : bZ.coord k (L2 (bX i)) =
        (d g q) * a i k + (tf i k (ρQ g⁻¹ q) - tf i k q) := by
      simp only [L2, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, TensorProduct.mk_apply, map_add, map_sub, map_smul,
        hξ_coord i k, ht_coord i k (ρQ g⁻¹ q), ht_coord i k q, smul_eq_mul]
    simp only [Module.Basis.coord_apply] at h1 h2
    rw [h1, h2, hform i k g q, mul_comm]
  have hx := DFunLike.congr_fun hL x
  simpa [L1, L2, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, TensorProduct.mk_apply] using hx

end CFSG.Quasithin.JonesParshall

module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9CDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Frame
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.FrameRoute

open Polynomial Matrix CFSG.Open CFSG.StandardType

theorem P9C1_card_adjoinRoot {g : (ZMod 2)[X]} [Fact (Irreducible g)]
    (hgd : g ∣ cyclotomic 3 (ZMod 2)) : Nat.card (AdjoinRoot g) = 4 := by
  classical
  have hg0 : g ≠ 0 := (Fact.out : Irreducible g).ne_zero
  haveI : Module.Finite (ZMod 2) (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have hcard : Nat.card (AdjoinRoot g) = 2 ^ g.natDegree := by
    have hfin : Module.finrank (ZMod 2) (AdjoinRoot g) = g.natDegree := by
      rw [(AdjoinRoot.powerBasis hg0).finrank, AdjoinRoot.powerBasis_dim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := AdjoinRoot g), hfin, Nat.card_zmod]
  have hle : g.natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hgd (cyclotomic_ne_zero 3 (ZMod 2))
    rwa [natDegree_cyclotomic, Nat.totient_prime Nat.prime_three] at this
  have hge : 2 ≤ g.natDegree := by
    by_contra hlt
    have hpos : 0 < g.natDegree :=
      natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible (Fact.out : Irreducible g))
    have h1 : g.natDegree = 1 := by omega
    haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod 2)
    haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
    have hL2 : Fintype.card (AdjoinRoot g) = 2 := by
      rw [← Nat.card_eq_fintype_card, hcard, h1]
      norm_num
    have hprim := CoordSL.root_isPrimitiveRoot Nat.prime_three
      (by decide : ((3 : ℕ) : ZMod 2) ≠ 0) hgd
    have hne0 : AdjoinRoot.root g ≠ 0 := hprim.ne_zero (by norm_num)
    have h2 := FiniteField.pow_card_sub_one_eq_one (AdjoinRoot.root g) hne0
    rw [hL2] at h2
    exact hprim.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num) (by simpa using h2)
  rw [hcard, le_antisymm hle hge]
  norm_num

theorem P9C1_algEquiv_F4 {L : Type} [Field L] [Algebra (ZMod 2) L] [Finite L]
    (hL : Nat.card L = 4) : Nonempty (L ≃ₐ[ZMod 2] F4) := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  haveI : Fintype F4 := Fintype.ofFinite F4
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  exact ⟨FiniteField.algEquivOfCardEq 2 (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hL, P9_F4_card])⟩

theorem P9C1_matrices {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) (ZMod 2)))
    (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (hSp : ∀ x ∈ S, x ^ 3 = 1) :
    ∃ (s r : ℕ) (Θ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin s → F4) × (Fin r → ZMod 2))),
      ∀ x ∈ S, ∃ c : Fin s → F4, (∀ i, c i ^ 3 = 1) ∧
        ∀ v, Θ (x *ᵥ v) = ((fun i => c i * (Θ v).1 i), (Θ v).2) := by
  classical
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three (ZMod 2)
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hp3 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  obtain ⟨s, r, ε, A₀, hframe⟩ := CoordSL.exists_frame g Nat.prime_three hp3 hgd S hSc hSp
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  haveI : Module.Finite (ZMod 2) (AdjoinRoot g) := (CoordSL.rootPB g).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod 2)
  obtain ⟨σ⟩ := P9C1_algEquiv_F4 (L := AdjoinRoot g) (P9C1_card_adjoinRoot hgd)
  set A : Matrix (Fin n) (Fin n) (ZMod 2) := (A₀ : Matrix (Fin n) (Fin n) (ZMod 2)) with hA
  set Ai : Matrix (Fin n) (Fin n) (ZMod 2) :=
    ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    with hAi
  have hAAi : A * Ai = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hAiA : Ai * A = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  let Ainv : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofLinear (Matrix.toLin' Ai) (Matrix.toLin' A)
      (by rw [← Matrix.toLin'_mul, hAiA, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hAAi, Matrix.toLin'_one])
  have hAinv : ∀ v, Ainv v = Ai *ᵥ v := fun v => by
    simp [Ainv, Matrix.toLin'_apply]
  let fc := CoordSL.frameCoords g ε
  let Θ0 : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin s → AdjoinRoot g) × (Fin r → ZMod 2)) :=
    Ainv.trans fc.symm
  let τ : ((Fin s → AdjoinRoot g) × (Fin r → ZMod 2)) ≃ₗ[ZMod 2]
      ((Fin s → F4) × (Fin r → ZMod 2)) :=
    LinearEquiv.prodCongr (LinearEquiv.piCongrRight fun _ => σ.toLinearEquiv)
      (LinearEquiv.refl (ZMod 2) (Fin r → ZMod 2))
  refine ⟨s, r, Θ0.trans τ, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hframe x hx
  have hrot : ∀ v, Θ0 (x *ᵥ v) =
      ((fun i => AdjoinRoot.root g ^ k i * (Θ0 v).1 i), (Θ0 v).2) := by
    intro v
    have hix : Ai * x = SLNS.nsMat ε (CoordSL.rootMat g) k * Ai := by
      calc Ai * x = Ai * x * (A * Ai) := by rw [hAAi, Matrix.mul_one]
        _ = Ai * (x * A) * Ai := by simp only [Matrix.mul_assoc]
        _ = Ai * (A * SLNS.nsMat ε (CoordSL.rootMat g) k) * Ai := by rw [hk]
        _ = SLNS.nsMat ε (CoordSL.rootMat g) k * Ai := by
          rw [← Matrix.mul_assoc, hAiA, Matrix.one_mul]
    have h1 : Ainv (x *ᵥ v) = SLNS.nsMat ε (CoordSL.rootMat g) k *ᵥ (Ai *ᵥ v) := by
      rw [hAinv, Matrix.mulVec_mulVec, hix, ← Matrix.mulVec_mulVec]
    have h2 : Ai *ᵥ v = fc (Θ0 v) := by
      change Ai *ᵥ v = fc (fc.symm (Ainv v))
      rw [LinearEquiv.apply_symm_apply, hAinv]
    change fc.symm (Ainv (x *ᵥ v)) = _
    rw [h1, h2, CoordSL.nsMat_mulVec_frameCoords, LinearEquiv.symm_apply_apply]
  refine ⟨fun i => σ (AdjoinRoot.root g ^ k i), fun i => ?_, fun v => ?_⟩
  · rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, map_one]
  · change τ (Θ0 (x *ᵥ v)) = _
    rw [hrot v]
    refine Prod.ext (funext fun i => ?_) rfl
    simp [τ, Θ0, map_mul]

theorem P9_C1_linear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : IsElemAbelian 3 E) :
    ∃ (t d : ℕ) (Φ : V ≃ₗ[ZMod 2] ((Fin t → F4) × (Fin d → ZMod 2))),
      ∀ g ∈ E, ∃ c : Fin t → F4, (∀ i, c i ^ 3 = 1) ∧
        ∀ v, Φ (g v) = ((fun i => c i * (Φ v).1 i), (Φ v).2) := by
  classical
  let Ψ : V ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    (Module.finBasis (ZMod 2) V).equivFun
  let mat : (V ≃ₗ[ZMod 2] V) →
      Matrix (Fin (Module.finrank (ZMod 2) V)) (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) :=
    fun e => LinearMap.toMatrix' ((Ψ.symm.trans (e.trans Ψ)).toLinearMap)
  have hmat_apply : ∀ (e : V ≃ₗ[ZMod 2] V) (v : V), mat e *ᵥ Ψ v = Ψ (e v) := by
    intro e v
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    simp
  have hmat_mul : ∀ e e' : V ≃ₗ[ZMod 2] V, mat (e * e') = mat e * mat e' := by
    intro e e'
    refine Matrix.toLin'.injective ?_
    rw [Matrix.toLin'_mul]
    refine LinearMap.ext fun w => ?_
    simp [mat, Matrix.toLin'_toMatrix']
  have hmat_one : mat 1 = 1 := by
    refine Matrix.toLin'.injective ?_
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun w => ?_
    simp [mat, Matrix.toLin'_toMatrix']
  obtain ⟨t, d, Θ, hΘ⟩ := P9C1_matrices (Set.image mat (E : Set (V ≃ₗ[ZMod 2] V)))
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      show mat e * mat e' = mat e' * mat e
      rw [← hmat_mul, ← hmat_mul, IsElemAbelian.comm hE he he'])
    (by
      rintro _ ⟨e, he, rfl⟩
      have h3 : mat (e ^ 3) = mat e ^ 3 := by
        rw [pow_three, pow_three, hmat_mul, hmat_mul]
      rw [← h3, hE.2 e he, hmat_one])
  refine ⟨t, d, Ψ.trans Θ, fun g hg => ?_⟩
  obtain ⟨c, hc3, hc⟩ := hΘ (mat g) ⟨g, hg, rfl⟩
  refine ⟨c, hc3, fun v => ?_⟩
  change Θ (Ψ (g v)) = _
  rw [← hmat_apply, hc]
  rfl

end CFSG.StandardType.FrameRoute

end

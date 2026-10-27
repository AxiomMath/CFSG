module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSL

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

section Root

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)]

@[expose] noncomputable def rootPB : PowerBasis K (AdjoinRoot g) :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero

@[expose] noncomputable def rootMat : Matrix (Fin (rootPB g).dim) (Fin (rootPB g).dim) K :=
  Algebra.leftMulMatrix (rootPB g).basis (AdjoinRoot.root g)

theorem rootMat_pow (j : ℕ) :
    rootMat g ^ j = Algebra.leftMulMatrix (rootPB g).basis (AdjoinRoot.root g ^ j) := by
  rw [rootMat, map_pow]

variable {g} {ℓ : ℕ}

theorem root_isPrimitiveRoot (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) :
    IsPrimitiveRoot (AdjoinRoot.root g) ℓ :=
  NSFrame.root_isPrimitiveRoot hℓ hℓK hgd

theorem rootMat_pow_eq_one (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) :
    rootMat g ^ ℓ = 1 := by
  rw [rootMat_pow, (root_isPrimitiveRoot hℓ hℓK hgd).pow_eq_one, map_one]

theorem det_rootMat [Finite K] (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1) (hℓK : (ℓ : K) ≠ 0)
    (hgd : g ∣ cyclotomic ℓ K) : (rootMat g).det = 1 := by
  have hζ := root_isPrimitiveRoot hℓ hℓK hgd
  have hnorm : Algebra.norm K (AdjoinRoot.root g) = 1 := by
    refine OrdPNS.eq_one_of_pow_eq_one hℓ hK ?_
    rw [← map_pow, hζ.pow_eq_one, map_one]
  rw [rootMat, ← Algebra.norm_eq_matrix_det, hnorm]

theorem isUnit_rootMat_pow_sub [Finite K] (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1)
    (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) (j : ℕ) (hj : ¬ ℓ ∣ j) (c : K) :
    IsUnit (rootMat g ^ j - c • 1) := by
  have hζ := root_isPrimitiveRoot hℓ hℓK hgd
  have hne : AdjoinRoot.root g ^ j - algebraMap K (AdjoinRoot g) c ≠ 0 := by
    intro h0
    have h1 : AdjoinRoot.root g ^ j = algebraMap K (AdjoinRoot g) c := sub_eq_zero.mp h0
    have hc : c ^ ℓ = 1 := by
      apply (algebraMap K (AdjoinRoot g)).injective
      rw [map_pow, ← h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, map_one]
    have hc1 := OrdPNS.eq_one_of_pow_eq_one hℓ hK hc
    rw [hc1, map_one] at h1
    exact hj (hζ.dvd_of_pow_eq_one j h1)
  have h2 : rootMat g ^ j - c • 1 =
      Algebra.leftMulMatrix (rootPB g).basis
        (AdjoinRoot.root g ^ j - algebraMap K (AdjoinRoot g) c) := by
    rw [rootMat_pow, map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rw [h2]
  exact (IsUnit.mk0 _ hne).map (Algebra.leftMulMatrix (rootPB g).basis)

end Root

section Frame

variable {K : Type} [Field K] [Finite K] {ℓ n : ℕ} (g : K[X]) [Fact (Irreducible g)]

theorem exists_frame (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    (S : Set (Matrix (Fin n) (Fin n) K)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) :
    ∃ (s r : ℕ) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin n) K),
      ∀ x ∈ S, ∃ k : Fin s → ℕ, x * (A₀ : Matrix (Fin n) (Fin n) K) =
        (A₀ : Matrix (Fin n) (Fin n) K) * SLNS.nsMat ε (rootMat g) k := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set pb := rootPB g with hpb
  have : Module.Finite K (AdjoinRoot g) := pb.finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  set β := pb.basis with hβ
  obtain ⟨ι, κ, _, _, Φ, hΦ⟩ := NSFrame.exists_blockFrame (g := g) hℓ hℓK hgd
    (V := Fin n → K) (Matrix.toLinAlgEquiv' '' S)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hSc x hx y hy).map _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hSp x hx, map_one])
  set eι := Fintype.equivFin ι with heι
  set eκ := Fintype.equivFin κ with heκ
  set Ψ := (NSFrame.coords β eι eκ).symm.trans Φ with hΨ
  have hcard : Fintype.card ((Fin pb.dim × Fin (Fintype.card ι)) ⊕ Fin (Fintype.card κ)) = n := by
    have h1 := Ψ.finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at h1
  set ε := (Fintype.equivFinOfCardEq hcard).symm with hε
  set Ψ' := (LinearEquiv.funCongrLeft K K ε).symm.trans Ψ with hΨ'
  set Q := LinearMap.toMatrix' (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K)) with hQ
  set Q' := LinearMap.toMatrix' (Ψ'.symm : (Fin n → K) →ₗ[K] (Fin n → K)) with hQ'
  have hQQ' : Q * Q' = 1 := by
    rw [hQ, hQ', ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hrel : ∀ x ∈ S, ∃ k : Fin (Fintype.card ι) → ℕ, x * Q = Q * SLNS.nsMat ε (rootMat g) k := by
    intro x hx
    obtain ⟨k, hk⟩ := hΦ (Matrix.toLinAlgEquiv' x) ⟨x, hx, rfl⟩
    refine ⟨k ∘ eι.symm, Matrix.toLin'.injective ?_⟩
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hQ, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    set uw := (NSFrame.coords β eι eκ).symm (w ∘ ε.symm) with huw
    have hw : w ∘ ε.symm = NSFrame.coords β eι eκ uw := (LinearEquiv.apply_symm_apply _ _).symm
    have h1 : (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K)) w = Φ uw := rfl
    have h2 : (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K))
        (SLNS.nsMat ε (rootMat g) (k ∘ eι.symm) *ᵥ w) =
        Φ ((NSFrame.coords β eι eκ).symm
          ((SLNS.nsMat ε (rootMat g) (k ∘ eι.symm) *ᵥ w) ∘ ε.symm)) := rfl
    have h3 : (SLNS.nsMat ε (rootMat g) (k ∘ eι.symm) *ᵥ w) ∘ ε.symm =
        NSFrame.coords β eι eκ (fun i => AdjoinRoot.root g ^ k i * uw.1 i, uw.2) := by
      rw [rootMat, NSFrame.coords_mul, ← hw, SLNS.nsMat, submatrix_mulVec_equiv,
        Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
    rw [h1, h2, h3, LinearEquiv.symm_apply_apply]
    have h4 := hk uw.1 uw.2
    rw [Matrix.toLinAlgEquiv'_apply] at h4
    exact h4
  have hdetQ : Q.det * Q'.det = 1 := by rw [← det_mul, hQQ', det_one]
  have hQ0 : Q.det ≠ 0 := left_ne_zero_of_mul_eq_one hdetQ
  by_cases hs : Fintype.card ι = 0
  ·
    refine ⟨Fintype.card ι, Fintype.card κ, ε, 1, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hrel x hx
    refine ⟨k, ?_⟩
    rw [NSFrame.nsMat_eq_one_of_isEmpty ε _ k hs, Matrix.mul_one] at hk
    have hx1 : x = 1 := by
      calc x = x * Q * Q' := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        _ = 1 := by rw [hk, hQQ']
    rw [hx1, NSFrame.nsMat_eq_one_of_isEmpty ε _ k hs, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one]
  · obtain ⟨E, hEdet, hEcomm⟩ := NSFrame.exists_det_comm β ε (AdjoinRoot.root g)
      (⟨0, Nat.pos_of_ne_zero hs⟩ : Fin (Fintype.card ι)) Q.det⁻¹
    have hA₀ : (Q * E).det = 1 := by rw [det_mul, hEdet, mul_inv_cancel₀ hQ0]
    refine ⟨Fintype.card ι, Fintype.card κ, ε, ⟨Q * E, hA₀⟩, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hrel x hx
    refine ⟨k, ?_⟩
    change x * (Q * E) = Q * E * SLNS.nsMat ε (rootMat g) k
    rw [← Matrix.mul_assoc, hk, Matrix.mul_assoc, Matrix.mul_assoc, rootMat, hEcomm k]

end Frame

section Gal

theorem pow_val_pow_val {M : Type*} [Monoid M] {ℓ : ℕ} {x : M} (hx : x ^ ℓ = 1) (a b : ZMod ℓ) :
    (x ^ a.val) ^ b.val = x ^ (a * b).val := by
  rw [← pow_mul, pow_eq_pow_mod _ hx, ZMod.val_mul, ← pow_eq_pow_mod _ hx]

theorem pow_val_add {M : Type*} [Monoid M] {ℓ : ℕ} [NeZero ℓ] {x : M} (hx : x ^ ℓ = 1)
    (a b : ZMod ℓ) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, pow_eq_pow_mod (a.val + b.val) hx, ZMod.val_add, ← pow_eq_pow_mod _ hx]

theorem pow_val_one {M : Type*} [Monoid M] {ℓ : ℕ} {x : M} (hx : x ^ ℓ = 1) :
    x ^ (1 : ZMod ℓ).val = x := by
  rcases Nat.lt_or_ge ℓ 2 with hℓ | hℓ
  · interval_cases ℓ
    · simp
    · rw [pow_one] at hx
      rw [hx, one_pow]
  · have : Fact (1 < ℓ) := ⟨by omega⟩
    rw [ZMod.val_one, pow_one]

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] {ℓ : ℕ}

@[expose] def galExp (hζ : AdjoinRoot.root g ^ ℓ = 1) : Subgroup (ZMod ℓ)ˣ where
  carrier := {u | ∃ σ : AdjoinRoot g ≃ₐ[K] AdjoinRoot g,
    σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ (u : ZMod ℓ).val}
  mul_mem' := by
    rintro u v ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ * τ, ?_⟩
    rw [AlgEquiv.mul_apply, hτ, map_pow, hσ, pow_val_pow_val hζ, Units.val_mul]
  one_mem' := ⟨AlgEquiv.refl, by rw [Units.val_one, pow_val_one hζ]; rfl⟩
  inv_mem' := by
    rintro u ⟨σ, hσ⟩
    refine ⟨σ.symm, ?_⟩
    have h1 : σ (AdjoinRoot.root g ^ ((u⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ).val) = AdjoinRoot.root g := by
      rw [map_pow, hσ, pow_val_pow_val hζ, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        pow_val_one hζ]
    calc σ.symm (AdjoinRoot.root g)
        = σ.symm (σ (AdjoinRoot.root g ^ ((u⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ).val)) := by rw [h1]
      _ = _ := σ.symm_apply_apply _

theorem mem_galExp {hζ : AdjoinRoot.root g ^ ℓ = 1} {u : (ZMod ℓ)ˣ} :
    u ∈ galExp g hζ ↔ ∃ σ : AdjoinRoot g ≃ₐ[K] AdjoinRoot g,
      σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ (u : ZMod ℓ).val :=
  Iff.rfl

end Gal

section Move

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] {n s r : ℕ}

@[expose] noncomputable def frameCoords (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) ≃ₗ[K] (Fin n → K) :=
  (NSFrame.coords (rootPB g).basis (Equiv.refl _) (Equiv.refl _)).trans
    (LinearEquiv.funCongrLeft K K ε)

theorem nsMat_mulVec_frameCoords (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (k : Fin s → ℕ) (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    SLNS.nsMat ε (rootMat g) k *ᵥ frameCoords g ε x =
      frameCoords g ε (fun i => AdjoinRoot.root g ^ k i * x.1 i, x.2) := by
  obtain ⟨u, w⟩ := x
  change SLNS.nsMat ε (rootMat g) k *ᵥ
      ((NSFrame.coords (rootPB g).basis (Equiv.refl _) (Equiv.refl _) (u, w)) ∘ ε) =
    (NSFrame.coords (rootPB g).basis (Equiv.refl _) (Equiv.refl _)
      (fun i => AdjoinRoot.root g ^ k i * u i, w)) ∘ ε
  rw [rootMat, NSFrame.coords_mul, SLNS.nsMat, submatrix_mulVec_equiv, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id]
  rfl

@[expose] noncomputable def moveEquiv (π : Equiv.Perm (Fin s))
    (σ : Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g)) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) ≃ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun x := (fun i => σ i (x.1 (π i)), x.2)
  invFun x := (fun j => (σ (π.symm j)).symm (x.1 (π.symm j)), x.2)
  map_add' x y := Prod.ext (funext fun i => map_add (σ i) _ _) rfl
  map_smul' c x := Prod.ext (funext fun i => map_smul (σ i) c _) rfl
  left_inv x := Prod.ext (funext fun j => by simp) rfl
  right_inv x := Prod.ext (funext fun i => by simp) rfl

theorem exists_move [Finite K] (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (π : Equiv.Perm (Fin s)) (σ : Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g)) :
    ∃ M : Matrix.SpecialLinearGroup (Fin n) K, ∀ k k' : Fin s → ℕ,
      (∀ i, AdjoinRoot.root g ^ k i = σ i (AdjoinRoot.root g) ^ k' (π i)) →
        SLNS.nsMat ε (rootMat g) k * (M : Matrix (Fin n) (Fin n) K) =
          (M : Matrix (Fin n) (Fin n) K) * SLNS.nsMat ε (rootMat g) k' := by
  classical
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  set f : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (frameCoords g ε).symm.trans ((moveEquiv g π σ).trans (frameCoords g ε)) with hf
  set M₀ := LinearMap.toMatrix' (f : (Fin n → K) →ₗ[K] (Fin n → K)) with hM₀
  have hrel : ∀ k k' : Fin s → ℕ,
      (∀ i, AdjoinRoot.root g ^ k i = σ i (AdjoinRoot.root g) ^ k' (π i)) →
        SLNS.nsMat ε (rootMat g) k * M₀ = M₀ * SLNS.nsMat ε (rootMat g) k' := by
    intro k k' hk
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hM₀, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (frameCoords g ε).surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      nsMat_mulVec_frameCoords]
    simp only [hf, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [nsMat_mulVec_frameCoords]
    congr 1
    refine Prod.ext (funext fun i => ?_) rfl
    change AdjoinRoot.root g ^ k i * σ i (x.1 (π i)) =
      σ i (AdjoinRoot.root g ^ k' (π i) * x.1 (π i))
    rw [map_mul, map_pow, hk i]
  have hdet : IsUnit M₀.det := by
    rw [hM₀, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' f
  rcases Nat.eq_zero_or_pos s with hs | hs
  · refine ⟨1, fun k k' _ => ?_⟩
    rw [NSFrame.nsMat_eq_one_of_isEmpty ε _ k hs, NSFrame.nsMat_eq_one_of_isEmpty ε _ k' hs]
    simp
  · obtain ⟨E, hEdet, hEcomm⟩ := NSFrame.exists_det_comm (rootPB g).basis ε (AdjoinRoot.root g)
      ⟨0, hs⟩ M₀.det⁻¹
    refine ⟨⟨M₀ * E, by rw [det_mul, hEdet, mul_inv_cancel₀ hdet.ne_zero]⟩,
      fun k k' hk => ?_⟩
    change SLNS.nsMat ε (rootMat g) k * (M₀ * E) = M₀ * E * SLNS.nsMat ε (rootMat g) k'
    have hE' : SLNS.nsMat ε (rootMat g) k' * E = E * SLNS.nsMat ε (rootMat g) k' :=
      (hEcomm k').symm
    rw [← Matrix.mul_assoc, hrel k k' hk, Matrix.mul_assoc, hE', Matrix.mul_assoc]

end Move

section Normalizer

open Multiplicative

theorem mem_normalizer_range_of_conj {G : Type*} [Group G] {r p : ℕ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {w : G} (π : Equiv.Perm (Fin r))
    (η : Fin r → (ZMod p)ˣ)
    (hw : ∀ t, w⁻¹ * ι (ofAdd t) * w = ι (ofAdd fun i => (η i : ZMod p) * t (π i))) :
    w ∈ Subgroup.normalizer (ι.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨ofAdd fun j => ((η (π.symm j))⁻¹ : (ZMod p)ˣ) * toAdd a (π.symm j), ?_⟩
    have h1 := hw (fun j => ((η (π.symm j))⁻¹ : (ZMod p)ˣ) * toAdd a (π.symm j))
    have h2 : (fun i => (η i : ZMod p) *
        ((((η (π.symm (π i)))⁻¹ : (ZMod p)ˣ) : ZMod p) * toAdd a (π.symm (π i)))) = toAdd a := by
      funext i
      simp only [Equiv.symm_apply_apply]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [h2, ofAdd_toAdd] at h1
    rw [← h1]
    group
  · rintro ⟨a, ha⟩
    refine ⟨ofAdd fun i => (η i : ZMod p) * toAdd a (π i), ?_⟩
    rw [← hw, ofAdd_toAdd, ha]
    group

end Normalizer

end CoordSL

end CFSG.StandardType

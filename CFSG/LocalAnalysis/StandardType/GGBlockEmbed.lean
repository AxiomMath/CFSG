module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Artinian.Ring

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix

private abbrev gbeAux_alg {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K)))

private abbrev gbeAux_Ve {n : ℕ} {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) :
    Submodule K (Fin n → K) :=
  LinearMap.range e.mulVecLin

private lemma gbeAux_exists_blockField {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {B : GL (Fin n) K} (hodd : Odd (orderOf B)) {e : Matrix (Fin n) (Fin n) K}
    (he : IsPrimIdemIn (gbeAux_alg B) e) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Finite F) (_ : CharP F 2)
      (π : gbeAux_alg B →ₐ[K] F),
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ a * e = 0) ∧
        Module.finrank K F = blockDegree (gbeAux_alg B) e ∧
        Nat.card F = Nat.card K ^ blockDegree (gbeAux_alg B) e := by
  have hS : ∀ s ∈ ({B} : Set (GL (Fin n) K)), ∀ s' ∈ ({B} : Set (GL (Fin n) K)),
      Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  have hodd' : ∀ s ∈ ({B} : Set (GL (Fin n) K)), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hodd
  obtain ⟨F, hFld, hAlg, hFin, π, hπ, hker, hdim⟩ :=
    exists_blockField (S := ({B} : Set (GL (Fin n) K))) hS hodd' he
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K := Fintype.ofFinite K
  have hChar : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  refine ⟨F, inferInstance, inferInstance, inferInstance, hChar, π, hπ, hker, hdim, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := K), hdim]

private lemma gbeAux_mulVec_mem_Ve {n : ℕ} {K : Type} [Field K]
    {e a : Matrix (Fin n) (Fin n) K} (hea : e * a = a * e) {w : Fin n → K}
    (hw : w ∈ gbeAux_Ve e) : a *ᵥ w ∈ gbeAux_Ve e := by
  obtain ⟨v, hv⟩ := hw
  refine ⟨a *ᵥ v, ?_⟩
  rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  change e *ᵥ (a *ᵥ v) = a *ᵥ (e *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hea]

private lemma gbeAux_mulVec_eq_of_mem_Ve {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) {w : Fin n → K}
    (hw : w ∈ gbeAux_Ve e) : e *ᵥ w = w := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply]
  change e *ᵥ (e *ᵥ v) = e *ᵥ v
  rw [Matrix.mulVec_mulVec, he]

private lemma gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) {w : Fin n → K}
    (hw : w ∈ gbeAux_Ve e) : (1 - e) *ᵥ w = 0 := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply]
  change (1 - e) *ᵥ (e *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec]
  have h : (1 - e) * e = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, he, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma gbeAux_add_one_sub_mulVec {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    e *ᵥ v + (1 - e) *ᵥ v = v := by
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

private lemma gbeAux_e_mulVec_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (v : Fin n → K) :
    e *ᵥ ((1 - e) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have h : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma gbeAux_one_sub_mulVec_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (v : Fin n → K) :
    (1 - e) *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have h : (1 - e) * (1 - e) = 1 - e := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, he]
    abel
  rw [h]

private lemma gbeAux_comm_of_mem_alg {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) {e : Matrix (Fin n) (Fin n) K} (he : e ∈ gbeAux_alg B) :
    ∀ a ∈ gbeAux_alg B, e * a = a * e := by
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (gbeAux_alg B) := Algebra.adjoinCommSemiringOfComm K hcommP
  intro a ha
  have h := congrArg Subtype.val (mul_comm (⟨a, ha⟩ : gbeAux_alg B) (⟨e, he⟩ : gbeAux_alg B))
  simpa using h.symm

private lemma gbeAux_factor {A B E : Type*} [Ring A] [Ring B] [Ring E]
    (π : A →+* B) (hπ : Function.Surjective π) (ρ : A →+* E)
    (hker : ∀ a, π a = 0 → ρ a = 0) :
    ∃ φ : B →+* E, ∀ a, φ (π a) = ρ a :=
  ⟨RingHom.liftOfSurjective π hπ ⟨ρ, fun a ha => hker a ha⟩,
    fun a => RingHom.liftOfSurjective_comp_apply π hπ ⟨ρ, fun a ha => hker a ha⟩ a⟩

private lemma gbeAux_module {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (hcomm : ∀ a ∈ gbeAux_alg B, e * a = a * e)
    {F : Type} [Field F] [Algebra K F]
    (π : gbeAux_alg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a, π a = 0 ↔ a * e = 0) :
    ∃ (_ : Module F (gbeAux_Ve e)) (_ : IsScalarTower K F (gbeAux_Ve e)),
      ∀ (a : gbeAux_alg B) (w : gbeAux_Ve e),
        ((π a • w : gbeAux_Ve e) : Fin n → K) =
          (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) := by
  classical
  have hmem : ∀ a : gbeAux_alg B, ∀ w ∈ gbeAux_Ve e,
      (a : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ gbeAux_Ve e :=
    fun a w hw => gbeAux_mulVec_mem_Ve (hcomm a a.2) hw
  let ρA : gbeAux_alg B →+* Module.End K (gbeAux_Ve e) :=
    { toFun := fun a => ((a : Matrix (Fin n) (Fin n) K).mulVecLin).restrict (hmem a)
      map_one' := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (1 : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = (w : Fin n → K)
        rw [Matrix.one_mulVec]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((a : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) K)) *ᵥ
            (w : Fin n → K) =
          (a : Matrix (Fin n) (Fin n) K) *ᵥ
            ((b : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
        rw [Matrix.mulVec_mulVec]
      map_zero' := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (0 : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = 0
        rw [Matrix.zero_mulVec]
      map_add' := by
        intro a b
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((a : Matrix (Fin n) (Fin n) K) + (b : Matrix (Fin n) (Fin n) K)) *ᵥ
            (w : Fin n → K) =
          (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) +
            (b : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)
        rw [Matrix.add_mulVec] }
  have hker' : ∀ a : gbeAux_alg B, π a = 0 → ρA a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = 0
    obtain ⟨v, hv⟩ := w.2
    rw [← hv, Matrix.mulVecLin_apply]
    change (a : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, hae, Matrix.zero_mulVec]
  have hker'' : ∀ a : gbeAux_alg B, π.toRingHom a = 0 → ρA a = 0 := fun a h => hker' a h
  obtain ⟨φ, hφ⟩ := @gbeAux_factor (gbeAux_alg B) F (Module.End K (gbeAux_Ve e))
    _ _ _ π.toRingHom hπ ρA hker''
  have hφ' : ∀ a : gbeAux_alg B, φ (π a) = ρA a := fun a => hφ a
  letI : Module F (gbeAux_Ve e) := Module.compHom (gbeAux_Ve e) φ
  have hsmul : ∀ (κ : F) (w : gbeAux_Ve e), κ • w = φ κ w := fun _ _ => rfl
  refine ⟨inferInstance, ?_, ?_⟩
  · refine IsScalarTower.of_algebraMap_smul fun c w => ?_
    rw [hsmul]
    have h1 : φ (algebraMap K F c) = ρA (algebraMap K (gbeAux_alg B) c) := by
      rw [← AlgHom.commutes π c, hφ']
    rw [h1]
    refine Subtype.ext ?_
    change (algebraMap K (gbeAux_alg B) c : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      c • (w : Fin n → K)
    rw [Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_mulVec]
  · intro a w
    rw [hsmul, hφ' a]
    rfl

private def gbeAux_ker {n : ℕ} {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) :
    Submodule K (Fin n → K) :=
  LinearMap.ker e.mulVecLin

private lemma gbeAux_mulVec_eq_zero_of_ker {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} {w : Fin n → K} (hw : w ∈ gbeAux_ker e) :
    e *ᵥ w = 0 := by
  simpa [Matrix.mulVecLin_apply] using (LinearMap.mem_ker).mp hw

private lemma gbeAux_one_sub_mulVec_eq_of_ker {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} {w : Fin n → K} (hw : w ∈ gbeAux_ker e) :
    (1 - e) *ᵥ w = w := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, gbeAux_mulVec_eq_zero_of_ker hw, sub_zero]

private def gbeAux_eL {n : ℕ} {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : gbeAux_Ve e :=
  ⟨e *ᵥ v, ⟨v, Matrix.mulVecLin_apply e v⟩⟩

private lemma gbeAux_eL_coe {n : ℕ} {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : ((gbeAux_eL e v : gbeAux_Ve e) : Fin n → K) = e *ᵥ v := rfl

private lemma gbeAux_eL_eq_of_mem {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (w : gbeAux_Ve e) :
    gbeAux_eL e (w : Fin n → K) = w :=
  Subtype.ext (gbeAux_mulVec_eq_of_mem_Ve he w.2)

private noncomputable def gbeAux_decomp {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) :
    (Fin n → K) ≃ₗ[K] (gbeAux_Ve e × gbeAux_ker e) where
  toFun v := (gbeAux_eL e v,
    ⟨(1 - e) *ᵥ v, by
      change e *ᵥ ((1 - e) *ᵥ v) = 0
      exact gbeAux_e_mulVec_one_sub he v⟩)
  invFun p := (p.1 : Fin n → K) + (p.2 : Fin n → K)
  left_inv v := by
    change e *ᵥ v + (1 - e) *ᵥ v = v
    exact gbeAux_add_one_sub_mulVec e v
  right_inv p := by
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      change e *ᵥ ((p.1 : Fin n → K) + (p.2 : Fin n → K)) = (p.1 : Fin n → K)
      rw [Matrix.mulVec_add, gbeAux_mulVec_eq_of_mem_Ve he p.1.2,
        gbeAux_mulVec_eq_zero_of_ker p.2.2, add_zero]
    · refine Subtype.ext ?_
      change (1 - e) *ᵥ ((p.1 : Fin n → K) + (p.2 : Fin n → K)) = (p.2 : Fin n → K)
      rw [Matrix.mulVec_add, gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve he p.1.2,
        gbeAux_one_sub_mulVec_eq_of_ker p.2.2, zero_add]
  map_add' v w := by
    refine Prod.ext ?_ ?_ <;> refine Subtype.ext ?_
    · change e *ᵥ (v + w) = e *ᵥ v + e *ᵥ w
      rw [Matrix.mulVec_add]
    · change (1 - e) *ᵥ (v + w) = (1 - e) *ᵥ v + (1 - e) *ᵥ w
      rw [Matrix.mulVec_add]
  map_smul' c v := by
    refine Prod.ext ?_ ?_ <;> refine Subtype.ext ?_
    · change e *ᵥ (c • v) = c • (e *ᵥ v)
      rw [Matrix.mulVec_smul]
    · change (1 - e) *ᵥ (c • v) = c • ((1 - e) *ᵥ v)
      rw [Matrix.mulVec_smul]

private noncomputable def gbeAux_restrict {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) : gbeAux_Ve e ≃ₗ[K] gbeAux_Ve e where
  toFun := g
  invFun := g.symm
  left_inv := g.left_inv
  right_inv := g.right_inv
  map_add' := g.map_add
  map_smul' := fun c w => by
    show g (c • w) = c • g w
    rw [← IsScalarTower.algebraMap_smul (A := F) c w, g.map_smul]
    exact IsScalarTower.algebraMap_smul (A := F) c (g w)

private lemma gbeAux_e_mulVec_add_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (w : gbeAux_Ve e) (v : Fin n → K) :
    e *ᵥ ((w : Fin n → K) + (1 - e) *ᵥ v) = (w : Fin n → K) := by
  rw [Matrix.mulVec_add, gbeAux_mulVec_eq_of_mem_Ve he w.2, gbeAux_e_mulVec_one_sub he v,
    add_zero]

private lemma gbeAux_one_sub_mulVec_add {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (w : gbeAux_Ve e) (v : Fin n → K) :
    (1 - e) *ᵥ ((w : Fin n → K) + (1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
  rw [Matrix.mulVec_add, gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve he w.2,
    gbeAux_one_sub_mulVec_one_sub he v, zero_add]

private lemma gbeAux_eL_add_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (he : e * e = e) (w : gbeAux_Ve e) (v : Fin n → K) :
    gbeAux_eL e ((w : Fin n → K) + (1 - e) *ᵥ v) = w :=
  Subtype.ext (gbeAux_e_mulVec_add_one_sub he w v)

private noncomputable def gbeAux_ext {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (gbeAux_decomp e he).trans
    (((gbeAux_restrict (F := F) e g).prodCongr
      (LinearEquiv.refl K (gbeAux_ker e))).trans (gbeAux_decomp e he).symm)

private lemma gbeAux_ext_apply {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (v : Fin n → K) :
    (gbeAux_ext (F := F) e he g) v =
      (g (gbeAux_eL e v) : Fin n → K) + (1 - e) *ᵥ v := by
  change (gbeAux_decomp e he).symm
    (((gbeAux_restrict (F := F) e g).prodCongr
      (LinearEquiv.refl K (gbeAux_ker e))) ((gbeAux_decomp e he) v)) =
    (g (gbeAux_eL e v) : Fin n → K) + (1 - e) *ᵥ v
  rfl

private noncomputable def gbeAux_extHom {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)] :
    (gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) where
  toFun := gbeAux_ext (F := F) e he
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rw [gbeAux_ext_apply]
    show e *ᵥ v + (1 - e) *ᵥ v = v
    exact gbeAux_add_one_sub_mulVec e v
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    change (gbeAux_ext (F := F) e he (g * h)) v =
      (gbeAux_ext (F := F) e he g) ((gbeAux_ext (F := F) e he h) v)
    conv_lhs => rw [gbeAux_ext_apply]
    conv_rhs =>
      rw [gbeAux_ext_apply]
      rw [gbeAux_ext_apply]
    congr 1
    · rw [LinearEquiv.mul_apply, gbeAux_eL_add_one_sub he (h (gbeAux_eL e v)) v]
    · exact (gbeAux_one_sub_mulVec_add he (h (gbeAux_eL e v)) v).symm

private lemma gbeAux_ext_injective {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)] :
    Function.Injective (gbeAux_extHom (F := F) e he) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro w
  have h2 := congrArg (fun f : (Fin n → K) ≃ₗ[K] (Fin n → K) => f (w : Fin n → K)) hgh
  change (gbeAux_ext (F := F) e he g) (w : Fin n → K) =
    (gbeAux_ext (F := F) e he h) (w : Fin n → K) at h2
  rw [gbeAux_ext_apply, gbeAux_ext_apply] at h2
  simp only [gbeAux_eL_eq_of_mem he w, gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve he w.2,
    add_zero] at h2
  exact Subtype.ext h2

private lemma gbeAux_ext_eq_on_Ve {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (w : gbeAux_Ve e) :
    (gbeAux_extHom (F := F) e he g) (w : Fin n → K) = (g w : Fin n → K) := by
  change (gbeAux_ext (F := F) e he g) (w : Fin n → K) = (g w : Fin n → K)
  rw [gbeAux_ext_apply]
  rw [gbeAux_eL_eq_of_mem he w, gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve he w.2, add_zero]

private lemma gbeAux_ext_fix {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (v : Fin n → K) :
    (gbeAux_extHom (F := F) e he g) ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
  change (gbeAux_ext (F := F) e he g) ((1 - e) *ᵥ v) = (1 - e) *ᵥ v
  rw [gbeAux_ext_apply, show gbeAux_eL e ((1 - e) *ᵥ v) = 0 from
    Subtype.ext (gbeAux_e_mulVec_one_sub he v), map_zero]
  rw [show (((0 : gbeAux_Ve e) : Fin n → K)) = 0 from rfl, zero_add,
    gbeAux_one_sub_mulVec_one_sub he v]

private lemma gbeAux_e_mulVec_B {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K}
    (hBe : e * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * e)
    (v : Fin n → K) :
    e *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBe]

private lemma gbeAux_one_sub_mulVec_B {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K}
    (hBe : e * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * e)
    (v : Fin n → K) :
    (1 - e) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) := by
  have h : (1 - e) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (1 - e) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hBe]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private lemma gbeAux_ext_comm_lin {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) (B : GL (Fin n) K)
    (hBe : e * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (π : gbeAux_alg B →ₐ[K] F)
    (hact : ∀ (a : gbeAux_alg B) (w : gbeAux_Ve e),
      ((π a • w : gbeAux_Ve e) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (hBmem : (B : Matrix (Fin n) (Fin n) K) ∈ gbeAux_alg B)
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (v : Fin n → K) :
    (gbeAux_extHom (F := F) e he g) ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ ((gbeAux_extHom (F := F) e he g) v) := by
  have harg_vec : e *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((π ⟨B, hBmem⟩ • gbeAux_eL e v : gbeAux_Ve e) : Fin n → K) := by
    rw [hact ⟨B, hBmem⟩ (gbeAux_eL e v), gbeAux_eL_coe]
    simpa using gbeAux_e_mulVec_B hBe v
  have harg : gbeAux_eL e ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      π ⟨B, hBmem⟩ • gbeAux_eL e v := Subtype.ext harg_vec
  change (gbeAux_ext (F := F) e he g) ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
    (B : Matrix (Fin n) (Fin n) K) *ᵥ ((gbeAux_ext (F := F) e he g) v)
  rw [gbeAux_ext_apply, gbeAux_ext_apply, harg, map_smul,
    hact ⟨B, hBmem⟩ (g (gbeAux_eL e v)), Matrix.mulVec_add, gbeAux_one_sub_mulVec_B hBe v]

private lemma gbeAux_ext_comm_e {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (v : Fin n → K) :
    (gbeAux_extHom (F := F) e he g) (e *ᵥ v) = e *ᵥ ((gbeAux_extHom (F := F) e he g) v) := by
  change (gbeAux_ext (F := F) e he g) (e *ᵥ v) = e *ᵥ ((gbeAux_ext (F := F) e he g) v)
  have h1 : gbeAux_eL e (e *ᵥ v) = gbeAux_eL e v :=
    Subtype.ext (by
      change e *ᵥ (e *ᵥ v) = e *ᵥ v
      rw [Matrix.mulVec_mulVec, he])
  have h2 : (1 - e) *ᵥ (e *ᵥ v) = 0 :=
    gbeAux_one_sub_mulVec_eq_zero_of_mem_Ve he ⟨v, Matrix.mulVecLin_apply e v⟩
  rw [gbeAux_ext_apply, gbeAux_ext_apply, h1, h2, add_zero, Matrix.mulVec_add,
    gbeAux_mulVec_eq_of_mem_Ve he (g (gbeAux_eL e v)).2, gbeAux_e_mulVec_one_sub he v, add_zero]

private lemma gbeAux_rank_pos {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) (he : e ≠ 0) : 0 < Matrix.rank e := by
  have hrank : Matrix.rank e = Module.finrank K (gbeAux_Ve e) := rfl
  rw [hrank]
  have hne : gbeAux_Ve e ≠ ⊥ := by
    intro h
    have h0 : e.mulVecLin = 0 := (LinearMap.range_eq_bot).mp h
    refine he ?_
    ext i j
    have h1 : e.col j = 0 := by
      have := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f (Pi.single j 1)) h0
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this
    simpa using congrFun h1 i
  haveI : Nontrivial (gbeAux_Ve e) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos (R := K) (M := gbeAux_Ve e)

private noncomputable def gbeAux_psi {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)] :
    (gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) →* GL (Fin n) K :=
  (Matrix.GeneralLinearGroup.toLin.symm).toMonoidHom.comp
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm).toMonoidHom.comp
      (gbeAux_extHom (F := F) e he))

private lemma gbeAux_psi_mulVec {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)]
    (g : gbeAux_Ve e ≃ₗ[F] gbeAux_Ve e) (u : Fin n → K) :
    (gbeAux_psi (F := F) e he g : Matrix (Fin n) (Fin n) K) *ᵥ u =
      (gbeAux_extHom (F := F) e he g) u := by
  let X : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm
      (gbeAux_extHom (F := F) e he g))
  change (X : Matrix (Fin n) (Fin n) K) *ᵥ u = _
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply X u]
  have h1 : Matrix.GeneralLinearGroup.toLin X =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm
        (gbeAux_extHom (F := F) e he g) := by
    dsimp only [X]
    exact MulEquiv.apply_symm_apply _ _
  rw [h1]
  rfl

private lemma gbeAux_psi_injective {n : ℕ} {K F : Type} [Field K] [Field F] [Algebra K F]
    (e : Matrix (Fin n) (Fin n) K) (he : e * e = e)
    [Module F (gbeAux_Ve e)] [IsScalarTower K F (gbeAux_Ve e)] :
    Function.Injective (gbeAux_psi (F := F) e he) := by
  unfold gbeAux_psi
  rw [MonoidHom.coe_comp]
  refine Function.Injective.comp (Matrix.GeneralLinearGroup.toLin.symm.injective) ?_
  rw [MonoidHom.coe_comp]
  exact Function.Injective.comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm.injective
    (gbeAux_ext_injective e he)

theorem exists_blockEmbed {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {B : GL (Fin n) K}
    (hodd : Odd (orderOf B)) {A : Subalgebra K (Matrix (Fin n) (Fin n) K)}
    (hA : A = Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))))
    {e : Matrix (Fin n) (Fin n) K} (he : IsPrimIdemIn A e) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Finite F) (_ : CharP F 2)
      (π : A →ₐ[K] F) (_ : Module F (LinearMap.range e.mulVecLin))
      (_ : IsScalarTower K F (LinearMap.range e.mulVecLin))
      (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K),
      Function.Surjective π ∧ (∀ a : A, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) ∧
      Module.finrank K F = blockDegree A e ∧ Nat.card F = Nat.card K ^ blockDegree A e ∧
      (∀ (a : A) (w : LinearMap.range e.mulVecLin),
        ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
          (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)) ∧
      Matrix.rank e = Module.finrank K F * Module.finrank F (LinearMap.range e.mulVecLin) ∧
      0 < Module.finrank F (LinearMap.range e.mulVecLin) ∧
      Function.Injective ψ ∧
      (∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
          (w : LinearMap.range e.mulVecLin),
        (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
          ((g w : LinearMap.range e.mulVecLin) : Fin n → K)) ∧
      (∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) ∧
      (∀ g, e * (ψ g : Matrix (Fin n) (Fin n) K) = (ψ g : Matrix (Fin n) (Fin n) K) * e) ∧
      (∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K)) := by
  subst hA
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hπ, hker, hdim, hcard⟩ :=
    gbeAux_exists_blockField hodd he
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  have he' : e * e = e := IsIdempotentElem.eq he.2.1
  have hcomm : ∀ a ∈ gbeAux_alg B, e * a = a * e := gbeAux_comm_of_mem_alg B he.1
  obtain ⟨hM, hT, hact⟩ := gbeAux_module hcomm π hπ hker
  letI : Module F (gbeAux_Ve e) := hM
  letI : IsScalarTower K F (gbeAux_Ve e) := hT
  have hBmem : (B : Matrix (Fin n) (Fin n) K) ∈ gbeAux_alg B :=
    Algebra.subset_adjoin ⟨B, Set.mem_singleton B, rfl⟩
  have hBe : e * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * e :=
    hcomm (B : Matrix (Fin n) (Fin n) K) hBmem
  haveI : Module.Finite K (gbeAux_Ve e) := Module.Finite.of_finite
  haveI : Module.Finite F (gbeAux_Ve e) :=
    Module.Finite.of_restrictScalars_finite K F (gbeAux_Ve e)
  haveI : Module.Free F (gbeAux_Ve e) := Module.Free.of_divisionRing F (gbeAux_Ve e)
  have hrank : Matrix.rank e = Module.finrank K F * Module.finrank F (gbeAux_Ve e) := by
    rw [show Matrix.rank e = Module.finrank K (gbeAux_Ve e) from rfl,
      ← Module.finrank_mul_finrank K F (gbeAux_Ve e)]
  have hpos : 0 < Module.finrank F (gbeAux_Ve e) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := gbeAux_rank_pos e he.2.2.1
    rw [hrank, h0, mul_zero] at h1
    exact lt_irrefl 0 h1
  refine ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, gbeAux_psi (F := F) e he', hπ, hker, hdim,
    hcard, hact, hrank, hpos, gbeAux_psi_injective e he', ?_, ?_, ?_, ?_⟩
  · intro g w
    rw [gbeAux_psi_mulVec]
    exact gbeAux_ext_eq_on_Ve e he' g w
  · intro g
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, gbeAux_psi_mulVec, gbeAux_ext_fix e he' g v]
  · intro g
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gbeAux_psi_mulVec,
      gbeAux_psi_mulVec]
    exact (gbeAux_ext_comm_e e he' g v).symm
  · intro g
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gbeAux_psi_mulVec,
      gbeAux_psi_mulVec]
    exact gbeAux_ext_comm_lin e he' B hBe π hact hBmem g v

end CFSG.StandardType

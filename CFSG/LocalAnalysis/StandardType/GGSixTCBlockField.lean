module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.ClassicalPosition

section BlockSpace

section Basic

variable {ι F : Type} [Fintype ι] [Field F]

@[expose] def blockSpace (e : Matrix ι ι F) : Submodule F (ι → F) :=
  LinearMap.range e.mulVecLin

lemma mulVec_mem_blockSpace {e a : Matrix ι ι F} (hea : e * a = a * e) {w : ι → F}
    (hw : w ∈ blockSpace e) : a.mulVec w ∈ blockSpace e := by
  obtain ⟨v, rfl⟩ := hw
  refine ⟨a.mulVec v, ?_⟩
  change e.mulVec (a.mulVec v) = a.mulVec (e.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hea]

end Basic

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

theorem adjoin_commute {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

theorem commute_adjoin_of_commute_gens {S : Set (GL ι F)} {g : GL ι F}
    (hg : ∀ s ∈ S, (g : Matrix ι ι F) * (s : Matrix ι ι F) =
      (s : Matrix ι ι F) * (g : Matrix ι ι F)) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (g : Matrix ι ι F) * a = a * (g : Matrix ι ι F) := by
  intro a ha
  refine Algebra.adjoin_induction
    (p := fun x _ => (g : Matrix ι ι F) * x = x * (g : Matrix ι ι F)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    exact hg s hs
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · intro x y _ _ hx hy
    rw [mul_add, add_mul, hx, hy]
  · intro x y _ _ hx hy
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

private lemma tck_factor {A K E : Type*} [Ring A] [Ring K] [Ring E] (π : A →+* K)
    (hπ : Function.Surjective π) (ρ : A →+* E) (hker : ∀ a, π a = 0 → ρ a = 0) :
    ∃ φ : K →+* E, ∀ a, φ (π a) = ρ a :=
  ⟨RingHom.liftOfSurjective π hπ ⟨ρ, fun a ha => hker a ha⟩, fun a =>
    RingHom.liftOfSurjective_comp_apply π hπ ⟨ρ, fun a ha => hker a ha⟩ a⟩

private theorem tck_blockModule_aux (A : Subalgebra F (Matrix ι ι F)) {e : Matrix ι ι F}
    (hcomm : ∀ a ∈ A, e * a = a * e) {K : Type} [Field K] [Algebra F K]
    (π : A →ₐ[F] K) (hπs : Function.Surjective π)
    (hπk : ∀ a : A, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) :
    ∃ (_ : Module K (blockSpace e)) (_ : IsScalarTower F K (blockSpace e)),
      ∀ (a : A) (w : blockSpace e),
        ((π a • w : blockSpace e) : ι → F) = (a : Matrix ι ι F).mulVec (w : ι → F) := by
  classical
  have hmem : ∀ a : A, ∀ w ∈ blockSpace e, (a : Matrix ι ι F).mulVec w ∈ blockSpace e :=
    fun a w hw => mulVec_mem_blockSpace (hcomm a a.2) hw
  let ρA : A →+* Module.End F (blockSpace e) :=
    { toFun := fun a => ((a : Matrix ι ι F).mulVecLin).restrict (hmem a)
      map_one' := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (1 : Matrix ι ι F).mulVec (w : ι → F) = (w : ι → F)
        rw [Matrix.one_mulVec]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((a : Matrix ι ι F) * (b : Matrix ι ι F)).mulVec (w : ι → F) =
          (a : Matrix ι ι F).mulVec ((b : Matrix ι ι F).mulVec (w : ι → F))
        rw [Matrix.mulVec_mulVec]
      map_zero' := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (0 : Matrix ι ι F).mulVec (w : ι → F) = 0
        rw [Matrix.zero_mulVec]
      map_add' := by
        intro a b
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((a : Matrix ι ι F) + (b : Matrix ι ι F)).mulVec (w : ι → F) =
          (a : Matrix ι ι F).mulVec (w : ι → F) + (b : Matrix ι ι F).mulVec (w : ι → F)
        rw [Matrix.add_mulVec] }
  have hker : ∀ a : A, π a = 0 → ρA a = 0 := by
    intro a h0
    have hae : (a : Matrix ι ι F) * e = 0 := (hπk a).mp h0
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨v, hv⟩ := w.2
    have : (a : Matrix ι ι F).mulVec (w : ι → F) = 0 := by
      rw [← hv]
      change (a : Matrix ι ι F).mulVec (e.mulVec v) = 0
      rw [Matrix.mulVec_mulVec, hae]
      simp
    exact this
  obtain ⟨φ, hφ⟩ := @tck_factor ↥A K (Module.End F (blockSpace e)) _ _ _ π.toRingHom hπs ρA hker
  let : Module K (blockSpace e) := Module.compHom (blockSpace e) φ
  have hsmul : ∀ (κ : K) (w : blockSpace e), κ • w = φ κ w := fun κ w => rfl
  refine ⟨inferInstance, ?_, ?_⟩
  · refine IsScalarTower.of_algebraMap_smul fun c w => ?_
    rw [hsmul]
    have h1 : φ (algebraMap F K c) = ρA (algebraMap F A c) := by
      rw [← hφ]
      exact congrArg φ (AlgHom.commutes π c).symm
    rw [h1]
    refine Subtype.ext ?_
    change (algebraMap F A c : Matrix ι ι F).mulVec (w : ι → F) = c • (w : ι → F)
    rw [Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_mulVec]
  · intro a w
    rw [hsmul]
    exact congrArg (fun T : Module.End F (blockSpace e) => ((T w : blockSpace e) : ι → F))
      (hφ a)

theorem exists_blockModule [Finite F] [CharP F 2] {S : Set (GL ι F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (_ : Module K (blockSpace e)) (_ : IsScalarTower F K (blockSpace e))
      (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K),
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) ∧
      Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : blockSpace e),
        ((π a • w : blockSpace e) : ι → F) = (a : Matrix ι ι F).mulVec (w : ι → F) := by
  obtain ⟨K, hKf, hKa, hKfin, π, hπs, hπk, hπd⟩ := exists_blockField hS hodd he
  let : Field K := hKf
  let : Algebra F K := hKa
  obtain ⟨hM, hT, hact⟩ := tck_blockModule_aux (Algebra.adjoin F (Units.val '' S))
    (fun a ha => (adjoin_commute hS e he.1 a ha).eq) π hπs hπk
  exact ⟨K, hKf, hKa, hKfin, hM, hT, π, hπs, hπk, hπd, hact⟩

theorem exists_subgroup_index_le_blockBound [Finite F] [CharP F 2] {Γ : Type} [Group Γ]
    (ρ₀ : Γ →* GL ι F) {S : Set (GL ι F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hΓA : ∀ γ : Γ, ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (ρ₀ γ : Matrix ι ι F) * a = a * (ρ₀ γ : Matrix ι ι F))
    (hΓc : ∀ γ γ' : Γ, ρ₀ γ * ρ₀ γ' = ρ₀ γ' * ρ₀ γ) {p : ℕ} (hp : (p : F) ≠ 0)
    (hΓp : ∀ γ : Γ, ∃ c : F, (ρ₀ γ : Matrix ι ι F) ^ p = Matrix.scalar ι c) :
    ∃ Γ₀ : Subgroup Γ,
      (∀ γ : Γ, ∀ c : F, (ρ₀ γ : Matrix ι ι F) = Matrix.scalar ι c → γ ∈ Γ₀) ∧
      (∀ γ ∈ Γ₀, ∃ a ∈ Algebra.adjoin F (Units.val '' S),
        (ρ₀ γ : Matrix ι ι F) * e = a * e) ∧
      Γ₀.index ≤ p ^ (Matrix.rank e / blockDegree (Algebra.adjoin F (Units.val '' S)) e - 1) := by
  classical
  obtain ⟨K, hKf, hKa, hKfin, hM, hT, π, hπs, hπk, hπd, hact⟩ := exists_blockModule hS hodd he
  let : Field K := hKf
  let : Algebra F K := hKa
  let : Module K (blockSpace e) := hM
  have := hT
  have : FiniteDimensional K (blockSpace e) :=
    Module.Finite.of_restrictScalars_finite F K (blockSpace e)
  have heE : ∀ γ : Γ, e * (ρ₀ γ : Matrix ι ι F) = (ρ₀ γ : Matrix ι ι F) * e :=
    fun γ => (hΓA γ e he.1).symm
  have hEinv : ∀ γ : Γ, e * (((ρ₀ γ)⁻¹ : GL ι F) : Matrix ι ι F) =
      (((ρ₀ γ)⁻¹ : GL ι F) : Matrix ι ι F) * e :=
    fun γ => by
      have h := hΓA γ⁻¹ e he.1
      rw [map_inv] at h
      exact h.symm
  let act : Γ → (blockSpace e ≃ₗ[K] blockSpace e) := fun γ =>
    { toFun := fun w => ⟨(ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F),
        mulVec_mem_blockSpace (heE γ) w.2⟩
      map_add' := fun w w' => Subtype.ext (by
        change (ρ₀ γ : Matrix ι ι F).mulVec ((w : ι → F) + (w' : ι → F)) =
          (ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F) + (ρ₀ γ : Matrix ι ι F).mulVec (w' : ι → F)
        rw [Matrix.mulVec_add])
      map_smul' := fun κ w => by
        obtain ⟨a, rfl⟩ := hπs κ
        refine Subtype.ext ?_
        change (ρ₀ γ : Matrix ι ι F).mulVec ((π a • w : blockSpace e) : ι → F) =
          ((π a • (⟨(ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F),
            mulVec_mem_blockSpace (heE γ) w.2⟩ : blockSpace e) : blockSpace e) : ι → F)
        rw [hact, hact]
        change (ρ₀ γ : Matrix ι ι F).mulVec ((a : Matrix ι ι F).mulVec (w : ι → F)) =
          (a : Matrix ι ι F).mulVec ((ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hΓA γ a a.2]
      invFun := fun w => ⟨(((ρ₀ γ)⁻¹ : GL ι F) : Matrix ι ι F).mulVec (w : ι → F),
        mulVec_mem_blockSpace (hEinv γ) w.2⟩
      left_inv := fun w => Subtype.ext (by
        change (((ρ₀ γ)⁻¹ : GL ι F) : Matrix ι ι F).mulVec
          ((ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F)) = (w : ι → F)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec])
      right_inv := fun w => Subtype.ext (by
        change (ρ₀ γ : Matrix ι ι F).mulVec
          ((((ρ₀ γ)⁻¹ : GL ι F) : Matrix ι ι F).mulVec (w : ι → F)) = (w : ι → F)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]) }
  have hact_apply : ∀ (γ : Γ) (w : blockSpace e),
      ((act γ w : blockSpace e) : ι → F) = (ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F) :=
    fun γ w => rfl
  let ρ : Γ →* (blockSpace e ≃ₗ[K] blockSpace e) :=
    { toFun := act
      map_one' := LinearEquiv.ext fun w => Subtype.ext (by
        rw [hact_apply]
        change (((ρ₀ 1 : GL ι F)) : Matrix ι ι F).mulVec (w : ι → F) = (w : ι → F)
        rw [map_one, Units.val_one, Matrix.one_mulVec])
      map_mul' := fun s t => LinearEquiv.ext fun w => Subtype.ext (by
        rw [hact_apply]
        change (((ρ₀ (s * t) : GL ι F)) : Matrix ι ι F).mulVec (w : ι → F) =
          ((act s (act t w) : blockSpace e) : ι → F)
        rw [hact_apply, hact_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul]) }
  have hρ : ∀ (γ : Γ) (w : blockSpace e),
      ((ρ γ w : blockSpace e) : ι → F) = (ρ₀ γ : Matrix ι ι F).mulVec (w : ι → F) :=
    fun γ w => rfl
  have hscal : ∀ (γ : Γ) (c : F), (ρ₀ γ : Matrix ι ι F) = Matrix.scalar ι c →
      ρ γ ∈ HeisRank.scalarAut K (blockSpace e) := by
    intro γ c hγc
    refine ⟨algebraMap F K c, fun w => ?_⟩
    refine Subtype.ext ?_
    rw [hρ, hγc, IsScalarTower.algebraMap_smul]
    change (Matrix.scalar ι c : Matrix ι ι F).mulVec (w : ι → F) = c • (w : ι → F)
    rw [Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    simp
  have hp' : (p : K) ≠ 0 := by
    intro h
    apply hp
    have h0 : algebraMap F K (p : F) = 0 := by simpa using h
    exact (map_eq_zero (algebraMap F K)).mp h0
  have hc : ∀ s t : Γ, ρ s * ρ t = ρ t * ρ s := fun s t => by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    change (ρ₀ s : Matrix ι ι F).mulVec ((ρ₀ t : Matrix ι ι F).mulVec (w : ι → F)) =
      (ρ₀ t : Matrix ι ι F).mulVec ((ρ₀ s : Matrix ι ι F).mulVec (w : ι → F))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hΓc s t]
  have hpow : ∀ γ : Γ, ρ γ ^ p ∈ HeisRank.scalarAut K (blockSpace e) := by
    intro γ
    obtain ⟨c, hcp⟩ := hΓp γ
    rw [← map_pow]
    refine hscal (γ ^ p) c ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact hcp
  have key := (index_scalarAut_le (U := blockSpace e) hp' ρ hpow hc).2
  let Z : Subgroup Γ := (HeisRank.scalarAut K (blockSpace e)).comap ρ
  have hrank : Module.finrank K (blockSpace e) =
      Matrix.rank e / blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
    have h1 := Module.finrank_mul_finrank F K (blockSpace e)
    have hrk : Module.finrank F (blockSpace e) = Matrix.rank e := rfl
    have hpos : 0 < Module.finrank F K := Module.finrank_pos
    rw [hrk, hπd] at h1
    rw [hπd] at hpos
    rw [← h1, Nat.mul_div_cancel_left _ hpos]
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro γ c hγc
    exact hscal γ c hγc
  · intro γ hγ
    obtain ⟨κ, hκ⟩ := hγ
    obtain ⟨a, rfl⟩ := hπs κ
    refine ⟨a, a.2, ?_⟩
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hw : e.mulVec v ∈ blockSpace e := ⟨v, rfl⟩
    have h1 := hκ ⟨e.mulVec v, hw⟩
    have h2 := congrArg (fun x : blockSpace e => (x : ι → F)) h1
    simp only [hρ, hact] at h2
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h2
  · rw [← hrank]
    exact key

theorem exists_blockDegree_mul_eq_rank [Finite F] [CharP F 2] {S : Set (GL ι F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    0 < blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      ∃ k : ℕ, blockDegree (Algebra.adjoin F (Units.val '' S)) e * k = Matrix.rank e := by
  obtain ⟨K, hKf, hKa, hKfin, hM, hT, π, hπs, hπk, hπd, hact⟩ := exists_blockModule hS hodd he
  let : Field K := hKf
  let : Algebra F K := hKa
  let : Module K (blockSpace e) := hM
  have := hT
  have : FiniteDimensional K (blockSpace e) :=
    Module.Finite.of_restrictScalars_finite F K (blockSpace e)
  have hpos : 0 < Module.finrank F K := Module.finrank_pos
  refine ⟨hπd ▸ hpos, Module.finrank K (blockSpace e), ?_⟩
  rw [← hπd]
  exact Module.finrank_mul_finrank F K (blockSpace e)

theorem commute_of_blockScalar {A : Subalgebra F (Matrix ι ι F)} {ε a : Matrix ι ι F}
    (hε : ε ∈ A) (ha : a ∈ A) {t u : GL ι F}
    (htA : ∀ b ∈ A, (t : Matrix ι ι F) * b = b * (t : Matrix ι ι F))
    (huA : ∀ b ∈ A, (u : Matrix ι ι F) * b = b * (u : Matrix ι ι F))
    (hu1 : (u : Matrix ι ι F) * (1 - ε) = 1 - ε)
    (hta : (t : Matrix ι ι F) * ε = a * ε) : t * u = u * t := by
  set T : Matrix ι ι F := (t : Matrix ι ι F) with hT
  set U : Matrix ι ι F := (u : Matrix ι ι F) with hU
  have hTε : T * ε = ε * T := htA ε hε
  have hUε : U * ε = ε * U := huA ε hε
  have hUa : U * a = a * U := huA a ha
  have hcore : T * U * ε = U * T * ε := by
    calc T * U * ε = T * (U * ε) := by rw [Matrix.mul_assoc]
      _ = T * (ε * U) := by rw [hUε]
      _ = (T * ε) * U := by rw [Matrix.mul_assoc]
      _ = (a * ε) * U := by rw [hta]
      _ = a * (ε * U) := by rw [Matrix.mul_assoc]
      _ = a * (U * ε) := by rw [hUε]
      _ = (a * U) * ε := by rw [Matrix.mul_assoc]
      _ = (U * a) * ε := by rw [hUa]
      _ = U * (a * ε) := by rw [Matrix.mul_assoc]
      _ = U * (T * ε) := by rw [hta]
      _ = U * T * ε := by rw [Matrix.mul_assoc]
  have hcomp : T * U * (1 - ε) = U * T * (1 - ε) := by
    have h1 : T * U * (1 - ε) = T * (1 - ε) := by
      rw [Matrix.mul_assoc, hu1]
    have h2 : U * T * (1 - ε) = T * (1 - ε) := by
      have hT1 : T * (1 - ε) = (1 - ε) * T := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hTε]
      rw [Matrix.mul_assoc, hT1, ← Matrix.mul_assoc, hu1]
    rw [h1, h2]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change T * U = U * T
  have hsum : ∀ M : Matrix ι ι F, M = M * ε + M * (1 - ε) := by
    intro M
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hsum (T * U), hsum (U * T), hcore, hcomp]

theorem matrix_inv_comm_of_comm {e : Matrix ι ι F} {t : GL ι F}
    (hte : e * (t : Matrix ι ι F) = (t : Matrix ι ι F) * e) :
    e * ((t⁻¹ : GL ι F) : Matrix ι ι F) = ((t⁻¹ : GL ι F) : Matrix ι ι F) * e := by
  have h1 : (t : Matrix ι ι F) * ((t⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((t⁻¹ : GL ι F) : Matrix ι ι F) * (t : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc e * ((t⁻¹ : GL ι F) : Matrix ι ι F)
      = (((t⁻¹ : GL ι F) : Matrix ι ι F) * (t : Matrix ι ι F)) * e *
          ((t⁻¹ : GL ι F) : Matrix ι ι F) := by rw [h2, Matrix.one_mul]
    _ = ((t⁻¹ : GL ι F) : Matrix ι ι F) * ((t : Matrix ι ι F) * e) *
          ((t⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = ((t⁻¹ : GL ι F) : Matrix ι ι F) * (e * (t : Matrix ι ι F)) *
          ((t⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hte]
    _ = ((t⁻¹ : GL ι F) : Matrix ι ι F) * e *
          ((t : Matrix ι ι F) * ((t⁻¹ : GL ι F) : Matrix ι ι F)) := by
        simp only [Matrix.mul_assoc]
    _ = ((t⁻¹ : GL ι F) : Matrix ι ι F) * e := by rw [h1, Matrix.mul_one]

@[expose] noncomputable def blockAct (e : Matrix ι ι F) (t : GL ι F)
    (hte : e * (t : Matrix ι ι F) = (t : Matrix ι ι F) * e) :
    blockSpace e ≃ₗ[F] blockSpace e where
  toFun w := ⟨(t : Matrix ι ι F).mulVec (w : ι → F), mulVec_mem_blockSpace hte w.2⟩
  map_add' w w' := Subtype.ext (Matrix.mulVec_add _ _ _)
  map_smul' c w := Subtype.ext (by simp [Matrix.mulVec_smul])
  invFun w := ⟨((t⁻¹ : GL ι F) : Matrix ι ι F).mulVec (w : ι → F),
    mulVec_mem_blockSpace (matrix_inv_comm_of_comm hte) w.2⟩
  left_inv w := Subtype.ext (by
    change ((t⁻¹ : GL ι F) : Matrix ι ι F).mulVec ((t : Matrix ι ι F).mulVec (w : ι → F)) =
      (w : ι → F)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec])
  right_inv w := Subtype.ext (by
    change (t : Matrix ι ι F).mulVec (((t⁻¹ : GL ι F) : Matrix ι ι F).mulVec (w : ι → F)) =
      (w : ι → F)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])

theorem card_le_pow_rank_div_blockDegree [Finite F] [CharP F 2] {ι₀ : Type} [Finite ι₀]
    (t : ι₀ → GL ι F) {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (htA : ∀ i, ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (t i : Matrix ι ι F) * a = a * (t i : Matrix ι ι F))
    (htc : ∀ i j, t i * t j = t j * t i) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (htp : ∀ i, ∃ c : F, c ≠ 0 ∧ (t i : Matrix ι ι F) ^ p = Matrix.scalar ι c)
    (hinj : ∀ i j (c : F), c ≠ 0 →
      (t i : Matrix ι ι F) * e = c • ((t j : Matrix ι ι F) * e) → i = j) :
    Nat.card ι₀ ≤ p ^ (Matrix.rank e / blockDegree (Algebra.adjoin F (Units.val '' S)) e) := by
  classical
  obtain ⟨K, hKf, hKa, hKfin, hM, hT, π, hπs, hπk, hπd, hact⟩ := exists_blockModule hS hodd he
  let : Field K := hKf
  let : Algebra F K := hKa
  let : Module K (blockSpace e) := hM
  have := hT
  have : FiniteDimensional K (blockSpace e) :=
    Module.Finite.of_restrictScalars_finite F K (blockSpace e)
  have hte : ∀ i, e * (t i : Matrix ι ι F) = (t i : Matrix ι ι F) * e :=
    fun i => (htA i e he.1).symm
  let g : ι₀ → (blockSpace e ≃ₗ[F] blockSpace e) := fun i => blockAct e (t i) (hte i)
  have hgapp : ∀ i (w : blockSpace e),
      ((g i w : blockSpace e) : ι → F) = (t i : Matrix ι ι F).mulVec (w : ι → F) :=
    fun i w => rfl
  have hp' : (p : K) ≠ 0 := by
    intro h
    apply hpF
    have h0 : algebraMap F K (p : F) = 0 := by simpa using h
    exact (map_eq_zero (algebraMap F K)).mp h0
  have hcomm : ∀ i j, g i * g j = g j * g i := by
    intro i j
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    change (t i : Matrix ι ι F).mulVec ((t j : Matrix ι ι F).mulVec (w : ι → F)) =
      (t j : Matrix ι ι F).mulVec ((t i : Matrix ι ι F).mulVec (w : ι → F))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, htc i j]
  have hK : ∀ i (c : K) (v : blockSpace e), g i (c • v) = c • g i v := by
    intro i c v
    obtain ⟨a, rfl⟩ := hπs c
    apply Subtype.ext
    rw [hgapp, hact, hact, hgapp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htA i a a.2]
  have hgpow : ∀ i (k : ℕ) (w : blockSpace e),
      (((g i) ^ k) w : blockSpace e).1 = ((t i : Matrix ι ι F) ^ k).mulVec (w : ι → F) := by
    intro i k
    induction k with
    | zero => intro w; simp [Matrix.one_mulVec]
    | succ k ih =>
      intro w
      rw [pow_succ]
      change (((g i) ^ k) (g i w) : blockSpace e).1 = _
      rw [ih, hgapp, Matrix.mulVec_mulVec, pow_succ]
  have hpow : ∀ i, ∃ u : Fˣ, g i ^ p = scalarEquiv F (blockSpace e) u := by
    intro i
    obtain ⟨c, hc0, hc⟩ := htp i
    refine ⟨Units.mk0 c hc0, ?_⟩
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hgpow, hc, scalarEquiv_apply]
    change (Matrix.scalar ι c : Matrix ι ι F).mulVec (w : ι → F) = c • (w : ι → F)
    rw [Matrix.scalar_apply]
    funext j
    rw [Matrix.mulVec_diagonal]
    simp
  have hginj : ∀ i j (u : Fˣ), g i = g j * scalarEquiv F (blockSpace e) u → i = j := by
    intro i j u hij
    refine hinj i j (u : F) u.ne_zero ?_
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hw : e.mulVec v ∈ blockSpace e := ⟨v, rfl⟩
    have h1 := congrArg (fun f : blockSpace e ≃ₗ[F] blockSpace e => (f ⟨e.mulVec v, hw⟩).1) hij
    simp only [hgapp] at h1
    change (t i : Matrix ι ι F).mulVec (e.mulVec v) =
      (t j : Matrix ι ι F).mulVec ((u : F) • e.mulVec v) at h1
    rw [Matrix.mulVec_smul] at h1
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1
  have key := card_le_pow_finrank (K := K) (V := blockSpace e) hp hp' g hcomm hK hpow hginj
  have hrank : Module.finrank K (blockSpace e) =
      Matrix.rank e / blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
    have h1 := Module.finrank_mul_finrank F K (blockSpace e)
    have hrk : Module.finrank F (blockSpace e) = Matrix.rank e := rfl
    have hpos : 0 < Module.finrank F K := Module.finrank_pos
    rw [hrk, hπd] at h1
    rw [hπd] at hpos
    rw [← h1, Nat.mul_div_cancel_left _ hpos]
  rw [← hrank]
  exact key

end BlockSpace

theorem card_le_mul_of_surjective_of_index_le {E B : Type*} [Group E] [Group B] [Finite E]
    (φ : E →* B) (hφ : Function.Surjective φ) {E₀ : Subgroup E} (hker : φ.ker ≤ E₀)
    {D : Subgroup B} (hD : E₀.map φ ≤ D) {m : ℕ} (hm : E₀.index ≤ m) :
    Nat.card B ≤ Nat.card D * m := by
  have : Finite B := Finite.of_surjective φ hφ
  have hcomap : (E₀.map φ).comap φ = E₀ := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  have hidx : (E₀.map φ).index = E₀.index := by
    calc (E₀.map φ).index = ((E₀.map φ).comap φ).index :=
          (Subgroup.index_comap_of_surjective (E₀.map φ) hφ).symm
      _ = E₀.index := by rw [hcomap]
  have hB : Nat.card B = (E₀.map φ).index * Nat.card (E₀.map φ) := by
    rw [mul_comm]
    exact (Subgroup.card_mul_index (E₀.map φ)).symm
  have hD' : Nat.card (E₀.map φ) ≤ Nat.card D := Subgroup.card_le_of_le hD
  calc Nat.card B = (E₀.map φ).index * Nat.card (E₀.map φ) := hB
    _ ≤ m * Nat.card D := Nat.mul_le_mul (hidx.trans_le hm) hD'
    _ = Nat.card D * m := Nat.mul_comm _ _

section DualPair

open CFSG.StandardType.ClassicalPosition.Geo

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

private lemma kt3_formAdj_idem (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det)
    {e : Matrix ι ι F} (he : IsIdempotentElem e) : IsIdempotentElem (formAdj σ G e) := by
  rw [isIdempotentElem_iff] at he ⊢
  rw [← formAdj_mul σ hG, he]

private lemma kt3_formAdj_zero (σ : F →+* F) (G : Matrix ι ι F) : formAdj σ G 0 = 0 := by
  unfold formAdj
  rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

private lemma kt3_primIdem_formAdj [Finite F] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x)
    {G : Matrix ι ι F} (hG : IsUnit G.det) (hGh : Matrix.transpose (G.map σ) = G)
    {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) (formAdj σ G e) := by
  have heA : e ∈ Algebra.adjoin F (Units.val '' S) := he.1
  have hesA : formAdj σ G e ∈ Algebra.adjoin F (Units.val '' S) :=
    formAdj_mem_adjoin σ hG hSU he.1
  unfold IsPrimIdemIn
  refine ⟨hesA, kt3_formAdj_idem σ hG he.2.1, ?_, ?_⟩
  · intro h0
    apply he.2.2.1
    calc e = formAdj σ G (formAdj σ G e) := (formAdj_formAdj σ hσ hG hGh e).symm
      _ = formAdj σ G 0 := by rw [h0]
      _ = 0 := kt3_formAdj_zero σ G
  · intro e' he'A he'idem he'e
    have hfA : formAdj σ G e' ∈ Algebra.adjoin F (Units.val '' S) :=
      formAdj_mem_adjoin σ hG hSU he'A
    have hfidem : IsIdempotentElem (formAdj σ G e') := kt3_formAdj_idem σ hG he'idem
    have h1 := congrArg (formAdj σ G) he'e
    rw [formAdj_mul σ hG e' (formAdj σ G e), formAdj_formAdj σ hσ hG hGh e] at h1
    have hfe : formAdj σ G e' * e = formAdj σ G e' :=
      (adjoin_commute hS _ hfA _ heA).eq.trans h1
    rcases he.2.2.2 (formAdj σ G e') hfA hfidem hfe with h0 | h0
    · left
      calc e' = formAdj σ G (formAdj σ G e') := (formAdj_formAdj σ hσ hG hGh e').symm
        _ = formAdj σ G 0 := by rw [h0]
        _ = 0 := kt3_formAdj_zero σ G
    · right
      calc e' = formAdj σ G (formAdj σ G e') := (formAdj_formAdj σ hσ hG hGh e').symm
        _ = formAdj σ G e := by rw [h0]

theorem exists_mem_mul_add_formAdj_eq_of_isometry [Finite F] [CharP F 2] (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj σ G e ≠ e) {t : GL ι F}
    (ht : Matrix.transpose ((t : Matrix ι ι F).map σ) * G * (t : Matrix ι ι F) = G)
    (htA : ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (t : Matrix ι ι F) * a = a * (t : Matrix ι ι F))
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (hta : (t : Matrix ι ι F) * e = a * e) :
    ∃ c ∈ Algebra.adjoin F (Units.val '' S),
      (t : Matrix ι ι F) * (e + formAdj σ G e) = c * (e + formAdj σ G e) := by
  have hesA : formAdj σ G e ∈ Algebra.adjoin F (Units.val '' S) :=
    formAdj_mem_adjoin σ hG hSU he.1
  have hfa : formAdj σ G a ∈ Algebra.adjoin F (Units.val '' S) :=
    formAdj_mem_adjoin σ hG hSU ha
  have he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) (formAdj σ G e) :=
    kt3_primIdem_formAdj σ hσ hG hGh hSU hS he
  have hesidem : IsIdempotentElem (formAdj σ G e) := he'.2.1
  obtain ⟨hz1, hz2⟩ := mul_formAdj_eq_zero_of_dualPair σ hσ hG hGh hSU hS he hpair
  have hTinv : formAdj σ G (t : Matrix ι ι F) = ((t⁻¹ : GL ι F) : Matrix ι ι F) :=
    formAdj_eq_inv_of_isometry σ hG t ht
  have hTiT : ((t⁻¹ : GL ι F) : Matrix ι ι F) * (t : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hstar_ta : formAdj σ G e * ((t⁻¹ : GL ι F) : Matrix ι ι F) =
      formAdj σ G e * formAdj σ G a := by
    have h := congrArg (formAdj σ G) hta
    rw [formAdj_mul σ hG (t : Matrix ι ι F) e, formAdj_mul σ hG a e, hTinv] at h
    exact h
  have hc0A : formAdj σ G e * formAdj σ G a ∈ Algebra.adjoin F (Units.val '' S) :=
    Subalgebra.mul_mem _ hesA hfa
  have hkey : formAdj σ G e = (t : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a) := by
    calc formAdj σ G e
        = formAdj σ G e * (((t⁻¹ : GL ι F) : Matrix ι ι F) * (t : Matrix ι ι F)) := by
          rw [hTiT, mul_one]
      _ = (formAdj σ G e * ((t⁻¹ : GL ι F) : Matrix ι ι F)) * (t : Matrix ι ι F) :=
          (mul_assoc _ _ _).symm
      _ = (formAdj σ G e * formAdj σ G a) * (t : Matrix ι ι F) := by rw [hstar_ta]
      _ = formAdj σ G e * (formAdj σ G a * (t : Matrix ι ι F)) := mul_assoc _ _ _
      _ = formAdj σ G e * ((t : Matrix ι ι F) * formAdj σ G a) := by rw [← htA _ hfa]
      _ = (formAdj σ G e * (t : Matrix ι ι F)) * formAdj σ G a := (mul_assoc _ _ _).symm
      _ = ((t : Matrix ι ι F) * formAdj σ G e) * formAdj σ G a := by rw [← htA _ hesA]
      _ = (t : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a) := mul_assoc _ _ _
  have hc0e : (formAdj σ G e * formAdj σ G a) * formAdj σ G e =
      formAdj σ G e * formAdj σ G a := by
    have hcm : Commute (formAdj σ G a) (formAdj σ G e) := adjoin_commute hS _ hfa _ hesA
    calc (formAdj σ G e * formAdj σ G a) * formAdj σ G e
        = formAdj σ G e * (formAdj σ G a * formAdj σ G e) := mul_assoc _ _ _
      _ = formAdj σ G e * (formAdj σ G e * formAdj σ G a) := by rw [hcm.eq]
      _ = (formAdj σ G e * formAdj σ G e) * formAdj σ G a := (mul_assoc _ _ _).symm
      _ = formAdj σ G e * formAdj σ G a := by rw [hesidem.eq]
  obtain ⟨K, hKf, hKa, -, π', hπs, hπk, -⟩ := exists_blockField hS hodd he'
  let : Field K := hKf
  let : Algebra F K := hKa
  obtain ⟨E1, hE1⟩ : ∃ x : Algebra.adjoin F (Units.val '' S),
      (x : Matrix ι ι F) = formAdj σ G e := ⟨⟨formAdj σ G e, hesA⟩, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ x : Algebra.adjoin F (Units.val '' S),
      (x : Matrix ι ι F) = formAdj σ G e * formAdj σ G a := ⟨⟨_, hc0A⟩, rfl⟩
  have hE1mul : E1 * E1 = E1 := Subtype.ext (by rw [Subalgebra.coe_mul, hE1, hesidem.eq])
  have hπe : π' E1 = 1 := by
    have hidem : π' E1 * π' E1 = π' E1 := by
      rw [← map_mul, hE1mul]
    have hne : π' E1 ≠ 0 := by
      intro h0
      have h1 : formAdj σ G e * formAdj σ G e = 0 := by
        have h2 := (hπk E1).mp h0
        rw [hE1] at h2
        exact h2
      rw [hesidem.eq] at h1
      exact he'.2.2.1 h1
    exact mul_left_cancel₀ hne (hidem.trans (mul_one _).symm)
  have hc0ne : π' C0 ≠ 0 := by
    intro h0
    have h1 := (hπk C0).mp h0
    rw [hC0, hc0e] at h1
    apply he'.2.2.1
    rw [hkey, h1, mul_zero]
  obtain ⟨c1, hc1⟩ := hπs ((π' C0)⁻¹)
  have hprod : π' (c1 * C0) = π' E1 := by
    rw [map_mul, hc1, inv_mul_cancel₀ hc0ne, hπe]
  have hw : ((c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a) - formAdj σ G e) *
      formAdj σ G e = 0 := by
    have h0 : π' (c1 * C0 - E1) = 0 := by
      rw [map_sub, hprod, sub_self]
    have h2 := (hπk (c1 * C0 - E1)).mp h0
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, hC0, hE1] at h2
    exact h2
  have hc1c0 : (c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a) = formAdj σ G e := by
    have h1 : ((c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a)) * formAdj σ G e =
        formAdj σ G e := by
      rw [sub_mul, hesidem.eq, sub_eq_zero] at hw
      exact hw
    calc (c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a)
        = (c1 : Matrix ι ι F) * ((formAdj σ G e * formAdj σ G a) * formAdj σ G e) := by
          rw [hc0e]
      _ = ((c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a)) * formAdj σ G e :=
          (mul_assoc _ _ _).symm
      _ = formAdj σ G e := h1
  have hTestar : (t : Matrix ι ι F) * formAdj σ G e = (c1 : Matrix ι ι F) * formAdj σ G e := by
    calc (t : Matrix ι ι F) * formAdj σ G e
        = (t : Matrix ι ι F) * ((c1 : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a)) := by
          rw [hc1c0]
      _ = ((t : Matrix ι ι F) * (c1 : Matrix ι ι F)) * (formAdj σ G e * formAdj σ G a) :=
          (mul_assoc _ _ _).symm
      _ = ((c1 : Matrix ι ι F) * (t : Matrix ι ι F)) * (formAdj σ G e * formAdj σ G a) := by
          rw [htA _ c1.2]
      _ = (c1 : Matrix ι ι F) * ((t : Matrix ι ι F) * (formAdj σ G e * formAdj σ G a)) :=
          mul_assoc _ _ _
      _ = (c1 : Matrix ι ι F) * formAdj σ G e := by rw [← hkey]
  have hX1 : a * e * e = a * e := by rw [mul_assoc, he.2.1.eq]
  have hX2 : a * e * formAdj σ G e = 0 := by rw [mul_assoc, hz1, mul_zero]
  have hY1 : (c1 : Matrix ι ι F) * formAdj σ G e * e = 0 := by
    rw [mul_assoc, hz2, mul_zero]
  have hY2 : (c1 : Matrix ι ι F) * formAdj σ G e * formAdj σ G e =
      (c1 : Matrix ι ι F) * formAdj σ G e := by
    rw [mul_assoc, hesidem.eq]
  have hcA : a * e + (c1 : Matrix ι ι F) * formAdj σ G e ∈ Algebra.adjoin F (Units.val '' S) :=
    Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha he.1) (Subalgebra.mul_mem _ c1.2 hesA)
  refine ⟨a * e + (c1 : Matrix ι ι F) * formAdj σ G e, hcA, ?_⟩
  have hexp : (a * e + (c1 : Matrix ι ι F) * formAdj σ G e) * (e + formAdj σ G e) =
      a * e + (c1 : Matrix ι ι F) * formAdj σ G e := by
    rw [add_mul, mul_add, mul_add, hX1, hX2, hY1, hY2, add_zero, zero_add]
  rw [hexp, mul_add, hta, hTestar]

end DualPair

section Field

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

private lemma t2_aeval_eq_zero {M : Matrix ι ι F} {p : ℕ} {c : F}
    (hpc : M ^ p = Matrix.scalar ι c) :
    Polynomial.aeval M (Polynomial.X ^ p - Polynomial.C c) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hpc]
  exact sub_eq_zero.mpr rfl

theorem isPrimIdemIn_one_adjoin_singleton_of_not_pow [Nonempty ι] {p : ℕ} (hp : p.Prime)
    {s : GL ι F} {c : F} (hpc : (s : Matrix ι ι F) ^ p = Matrix.scalar ι c)
    (hc : ∀ b : F, b ^ p ≠ c) :
    IsPrimIdemIn (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))) (1 : Matrix ι ι F) := by
  have hA : Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))) =
      (Polynomial.aeval (s : Matrix ι ι F)).range := by
    rw [Set.image_singleton, Algebra.adjoin_singleton_eq_range_aeval]
  have haeval := t2_aeval_eq_zero hpc
  have hPirr : Irreducible (Polynomial.X ^ p - Polynomial.C c : Polynomial F) :=
    X_pow_sub_C_irreducible_of_prime hp hc
  have hPmonic : (Polynomial.X ^ p - Polynomial.C c : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C c hp.ne_zero
  have hmin := minpoly.eq_of_irreducible_of_monic hPirr haeval hPmonic
  have hprime : Prime (Polynomial.X ^ p - Polynomial.C c : Polynomial F) := hPirr.prime
  unfold IsPrimIdemIn
  refine ⟨?_, IsIdempotentElem.one, one_ne_zero, ?_⟩
  · rw [hA]
    exact Subalgebra.one_mem _
  · intro e' he' hidem _
    rw [hA, AlgHom.mem_range] at he'
    obtain ⟨f, rfl⟩ := he'
    have hidem' : Polynomial.aeval (s : Matrix ι ι F) f * Polynomial.aeval (s : Matrix ι ι F) f =
        Polynomial.aeval (s : Matrix ι ι F) f := hidem
    have h0 : Polynomial.aeval (s : Matrix ι ι F) (f * (f - 1)) = 0 := by
      rw [map_mul, map_sub, map_one, mul_sub, mul_one, hidem', sub_self]
    have hdvd : (Polynomial.X ^ p - Polynomial.C c : Polynomial F) ∣ f * (f - 1) := by
      rw [hmin]
      exact minpoly.dvd F _ h0
    rcases hprime.dvd_or_dvd hdvd with h | h
    · left
      obtain ⟨g, hg⟩ := h
      rw [hg, map_mul, haeval, zero_mul]
    · right
      obtain ⟨g, hg⟩ := h
      have h1 : Polynomial.aeval (s : Matrix ι ι F) (f - 1) = 0 := by
        rw [hg, map_mul, haeval, zero_mul]
      rw [map_sub, map_one] at h1
      exact sub_eq_zero.mp h1

theorem two_le_blockDegree_one_adjoin_singleton_of_not_pow [Nonempty ι] {p : ℕ} (_hp : p.Prime)
    {s : GL ι F} {c : F} (hpc : (s : Matrix ι ι F) ^ p = Matrix.scalar ι c)
    (hc : ∀ b : F, b ^ p ≠ c) :
    2 ≤ blockDegree (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))) (1 : Matrix ι ι F) := by
  have hMA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))) :=
    Algebra.subset_adjoin ⟨s, Set.mem_singleton s, rfl⟩
  have h1A : (1 : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))) :=
    Subalgebra.one_mem _
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))))).map
      (LinearMap.mulRight F (1 : Matrix ι ι F)) =
      Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))) := by
    have h : LinearMap.mulRight F (1 : Matrix ι ι F) = LinearMap.id := by
      ext x
      simp
    rw [h, Submodule.map_id]
  have hli : LinearIndependent F ![(1 : Matrix ι ι F), (s : Matrix ι ι F)] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hb : b = 0 := by
      by_contra hb
      apply hc (-(a / b))
      have h4 : b • (s : Matrix ι ι F) = (-a) • (1 : Matrix ι ι F) := by
        linear_combination (norm := module) hab
      have h3 : (s : Matrix ι ι F) = (-(a / b)) • (1 : Matrix ι ι F) := by
        calc (s : Matrix ι ι F) = b⁻¹ • (b • (s : Matrix ι ι F)) := by
              rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = b⁻¹ • ((-a) • (1 : Matrix ι ι F)) := by rw [h4]
          _ = (-(a / b)) • (1 : Matrix ι ι F) := by
              rw [smul_smul]
              congr 1
              ring
      have hMeq : (s : Matrix ι ι F) = Matrix.scalar ι (-(a / b)) := by
        rw [h3, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      have hscal : Matrix.scalar ι ((-(a / b)) ^ p) = Matrix.scalar ι c := by
        rw [map_pow, ← hMeq, hpc]
      exact Matrix.scalar_inj.mp hscal
    subst hb
    have h1 : a • (1 : Matrix ι ι F) = 0 := by simpa using hab
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h2 := congrFun (congrFun h1 i) i
    exact ⟨by simpa using h2, rfl⟩
  unfold blockDegree
  rw [hT]
  let v : Fin 2 → Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))) :=
    ![⟨1, h1A⟩, ⟨(s : Matrix ι ι F), hMA⟩]
  have hv : LinearIndependent F v := by
    apply LinearIndependent.of_comp
      (Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))))).subtype
    have hcomp : (Subalgebra.toSubmodule
        (Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))))).subtype ∘ v =
        ![(1 : Matrix ι ι F), (s : Matrix ι ι F)] := by
      ext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact hli
  have hcard := hv.fintype_card_le_finrank
  simpa using hcard

end Field

section Avg

open CFSG.StandardType.ClassicalPosition.Geo

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

@[expose] noncomputable def avgPow (s : GL ι F) (p : ℕ) : Matrix ι ι F :=
  ∑ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F)

private lemma avgPow_aux_sum_shift {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ)
    (h : g n = g 0) :
    ∑ i ∈ Finset.range n, g (i + 1) = ∑ i ∈ Finset.range n, g i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ (fun i => g (i + 1)) m, Finset.sum_range_succ' g m, h]

private lemma avgPow_aux_cast_odd [CharP F 2] {p : ℕ} (hp : Odd p) : (p : F) = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  push_cast
  rw [h2, zero_mul, zero_add]

private lemma avgPow_aux_nsmul_odd [CharP F 2] {M : Type*} [AddCommMonoid M] [Module F M]
    {p : ℕ} (hp : Odd p) (A : M) : p • A = A := by
  rw [← Nat.cast_smul_eq_nsmul F, avgPow_aux_cast_odd (F := F) hp, one_smul]

private lemma avgPow_aux_pow_left_fix {s : GL ι F} {A : Matrix ι ι F}
    (hA : (s : Matrix ι ι F) * A = A) (i : ℕ) :
    ((s ^ i : GL ι F) : Matrix ι ι F) * A = A := by
  induction i with
  | zero => rw [pow_zero, Units.val_one, Matrix.one_mul]
  | succ i ih => rw [pow_succ', Units.val_mul, Matrix.mul_assoc, ih, hA]

private lemma avgPow_aux_formAdj_sum (σ : F →+* F) (G : Matrix ι ι F) (f : ℕ → Matrix ι ι F)
    (p : ℕ) :
    formAdj σ G (∑ i ∈ Finset.range p, f i) = ∑ i ∈ Finset.range p, formAdj σ G (f i) := by
  induction p with
  | zero => simp [formAdj]
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, formAdj_add, ih]

private lemma avgPow_aux_isom_pow (σ : F →+* F) {G : Matrix ι ι F} {s : GL ι F}
    (hs : Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G) (i : ℕ) :
    Matrix.transpose (((s ^ i : GL ι F) : Matrix ι ι F).map σ) * G *
      ((s ^ i : GL ι F) : Matrix ι ι F) = G := by
  induction i with
  | zero =>
    rw [pow_zero, Units.val_one, Matrix.map_one σ (map_zero σ) (map_one σ),
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | succ i ih =>
    have key : Matrix.transpose ((s : Matrix ι ι F).map σ) *
        Matrix.transpose (((s ^ i : GL ι F) : Matrix ι ι F).map σ) * G *
        (((s ^ i : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F)) =
        Matrix.transpose ((s : Matrix ι ι F).map σ) *
        (Matrix.transpose (((s ^ i : GL ι F) : Matrix ι ι F).map σ) * G *
          ((s ^ i : GL ι F) : Matrix ι ι F)) * (s : Matrix ι ι F) := by
      simp only [Matrix.mul_assoc]
    rw [pow_succ, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, key, ih, hs]

theorem mul_avgPow {s : GL ι F} {p : ℕ} (hsp : s ^ p = 1) :
    (s : Matrix ι ι F) * avgPow s p = avgPow s p := by
  have key : ∀ i : ℕ, (s : Matrix ι ι F) * ((s ^ i : GL ι F) : Matrix ι ι F) =
      ((s ^ (i + 1) : GL ι F) : Matrix ι ι F) := by
    intro i
    rw [← Units.val_mul, ← pow_succ']
  have hk : ∀ i ∈ Finset.range p, (s : Matrix ι ι F) * ((s ^ i : GL ι F) : Matrix ι ι F) =
      ((s ^ (i + 1) : GL ι F) : Matrix ι ι F) := fun i _ => key i
  have hzero : ((s ^ p : GL ι F) : Matrix ι ι F) = ((s ^ 0 : GL ι F) : Matrix ι ι F) := by
    rw [hsp, pow_zero]
  have htel := avgPow_aux_sum_shift (fun i => ((s ^ i : GL ι F) : Matrix ι ι F)) p hzero
  unfold avgPow
  rw [Finset.mul_sum, Finset.sum_congr rfl hk]
  exact htel

theorem avgPow_mul {s : GL ι F} {p : ℕ} (hsp : s ^ p = 1) :
    avgPow s p * (s : Matrix ι ι F) = avgPow s p := by
  have key : ∀ i : ℕ, ((s ^ i : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) =
      ((s ^ (i + 1) : GL ι F) : Matrix ι ι F) := by
    intro i
    rw [← Units.val_mul, ← pow_succ]
  have hk : ∀ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) =
      ((s ^ (i + 1) : GL ι F) : Matrix ι ι F) := fun i _ => key i
  have hzero : ((s ^ p : GL ι F) : Matrix ι ι F) = ((s ^ 0 : GL ι F) : Matrix ι ι F) := by
    rw [hsp, pow_zero]
  have htel := avgPow_aux_sum_shift (fun i => ((s ^ i : GL ι F) : Matrix ι ι F)) p hzero
  unfold avgPow
  rw [Finset.sum_mul, Finset.sum_congr rfl hk]
  exact htel

theorem isIdempotentElem_avgPow [CharP F 2] {s : GL ι F} {p : ℕ} (hp : Odd p) (hsp : s ^ p = 1) :
    IsIdempotentElem (avgPow s p) := by
  have hk : ∀ i ∈ Finset.range p,
      ((s ^ i : GL ι F) : Matrix ι ι F) * avgPow s p = avgPow s p :=
    fun i _ => avgPow_aux_pow_left_fix (mul_avgPow hsp) i
  unfold IsIdempotentElem
  calc avgPow s p * avgPow s p
      = (∑ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F)) * avgPow s p := rfl
    _ = ∑ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F) * avgPow s p := by
        rw [Finset.sum_mul]
    _ = ∑ _i ∈ Finset.range p, avgPow s p := Finset.sum_congr rfl hk
    _ = p • avgPow s p := by rw [Finset.sum_const, Finset.card_range]
    _ = avgPow s p := avgPow_aux_nsmul_odd (F := F) hp _

theorem avgPow_mul_eq_self [CharP F 2] {s : GL ι F} {p : ℕ} (hp : Odd p) {a : Matrix ι ι F}
    (ha : (s : Matrix ι ι F) * a = a) : avgPow s p * a = a := by
  have hk : ∀ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F) * a = a :=
    fun i _ => avgPow_aux_pow_left_fix ha i
  calc avgPow s p * a
      = (∑ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F)) * a := rfl
    _ = ∑ i ∈ Finset.range p, ((s ^ i : GL ι F) : Matrix ι ι F) * a := by
        rw [Finset.sum_mul]
    _ = ∑ _i ∈ Finset.range p, a := Finset.sum_congr rfl hk
    _ = p • a := by rw [Finset.sum_const, Finset.card_range]
    _ = a := avgPow_aux_nsmul_odd (F := F) hp a

theorem formAdj_avgPow (σ : F →+* F) (_hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F}
    (hG : IsUnit G.det) {s : GL ι F}
    (hs : Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G) {p : ℕ}
    (hsp : s ^ p = 1) : formAdj σ G (avgPow s p) = avgPow s p := by
  have hinv : ∀ i ∈ Finset.range p, (s ^ i)⁻¹ = s ^ (p - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show i + (p - i) = p by omega, hsp]
  have hrefl : ∑ j ∈ Finset.range p, ((s ^ (p - j) : GL ι F) : Matrix ι ι F) =
      ∑ j ∈ Finset.range p, ((s ^ (j + 1) : GL ι F) : Matrix ι ι F) := by
    have h := Finset.sum_range_reflect (fun j => ((s ^ (j + 1) : GL ι F) : Matrix ι ι F)) p
    rw [← h]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    show ((s ^ (p - j) : GL ι F) : Matrix ι ι F) = ((s ^ (p - 1 - j + 1) : GL ι F) : Matrix ι ι F)
    rw [show p - j = p - 1 - j + 1 by omega]
  have hstep : ∑ i ∈ Finset.range p, formAdj σ G ((s ^ i : GL ι F) : Matrix ι ι F) =
      ∑ i ∈ Finset.range p, ((s ^ (p - i) : GL ι F) : Matrix ι ι F) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [formAdj_eq_inv_of_isometry σ hG (s ^ i) (avgPow_aux_isom_pow σ hs i), hinv i hi]
  have hzero : ((s ^ p : GL ι F) : Matrix ι ι F) = ((s ^ 0 : GL ι F) : Matrix ι ι F) := by
    rw [hsp, pow_zero]
  have htel := avgPow_aux_sum_shift (fun i => ((s ^ i : GL ι F) : Matrix ι ι F)) p hzero
  unfold avgPow
  rw [avgPow_aux_formAdj_sum, hstep, hrefl]
  exact htel

theorem avgPow_mem_adjoin {S : Set (GL ι F)} {s : GL ι F} (hs : s ∈ S) (p : ℕ) :
    avgPow s p ∈ Algebra.adjoin F (Units.val '' S) := by
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  unfold avgPow
  refine Subalgebra.sum_mem _ (fun i _ => ?_)
  rw [Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ hsA i

end Avg

end CFSG.StandardType.TableCRes

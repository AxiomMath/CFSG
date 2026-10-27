module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelRing
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelBasic
import CFSG.LocalAnalysis.StandardType.ZS.TableWeylChar
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def sgnR {R : Type} [Ring R] (b : Bool) : R := if b then 1 else -1

structure ReflTable (R : Type) (n m N : ℕ) where
  root : Fin N → Fin n → R
  coroot : Fin N → Fin n → R
  gen : Fin m → Fin N
  conj : Fin m → Fin N → Fin N
  sign : Fin m → Fin N → Bool
  word : Fin N → List (Fin m)
  cls : Fin N → Fin m

namespace ReflTable

variable {R : Type} [CommRing R] {n m N : ℕ} (T : ReflTable R n m N)

@[expose] def wconj (w : List (Fin m)) (j : Fin N) : Fin N := w.foldr T.conj j

@[expose] def ConjRel (i k k' : Fin N) (s : Bool) : Prop :=
  (2 : R) • T.root k - dotProduct (T.coroot i) (T.root k) • T.root i =
      ((2 : R) * sgnR s) • T.root k' ∧
    (2 : R) • T.coroot k - dotProduct (T.coroot k) (T.root i) • T.coroot i =
      ((2 : R) * sgnR s) • T.coroot k'

instance [DecidableEq R] (i k k' : Fin N) (s : Bool) : Decidable (T.ConjRel i k k' s) :=
  instDecidableAnd

structure Valid (good : R → Prop) : Prop where
  coroot_root : ∀ j, dotProduct (T.coroot j) (T.root j) = 4
  conj : ∀ k j, T.ConjRel (T.gen k) j (T.conj k j) (T.sign k j)
  word : ∀ j, T.wconj (T.word j) (T.gen (T.cls j)) = j
  root_good : ∀ j i, T.root j i = 0 ∨ good (T.root j i)
  coroot_good : ∀ j i, T.coroot j i = 0 ∨ good (T.coroot j i)

end ReflTable

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {R : Type} [CommRing R] {n : ℕ}

@[expose] noncomputable def vecR (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (v : Fin n → R) : U :=
  ∑ i, φ (v i) • f i

@[expose] noncomputable def covecR (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (c : Fin n → R) : Module.Dual (ZMod p) U :=
  ∑ i, ((2 : ZMod p)⁻¹ * φ (c i)) • f.coord i

private theorem vecR_add (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (v w : Fin n → R) : vecR φ f (v + w) = vecR φ f v + vecR φ f w := by
  simp only [vecR, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

private theorem vecR_smul (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (a : R) (v : Fin n → R) : vecR φ f (a • v) = φ a • vecR φ f v := by
  simp only [vecR, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

private theorem vecR_sub (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (v w : Fin n → R) : vecR φ f (v - w) = vecR φ f v - vecR φ f w := by
  simp only [vecR, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

private theorem vecR_single (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (i : Fin n) : vecR φ f (Pi.single i (1 : R)) = f i := by
  rw [vecR, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem vecR_finset_sum {ι : Type*} (φ : R →+* ZMod p)
    (f : Module.Basis (Fin n) (ZMod p) U) (s : Finset ι) (a : ι → R) (v : ι → Fin n → R) :
    vecR φ f (∑ l ∈ s, a l • v l) = ∑ l ∈ s, φ (a l) • vecR φ f (v l) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [vecR]
  · intro x s hx ih
    rw [Finset.sum_insert hx, Finset.sum_insert hx, vecR_add, vecR_smul, ih]

private theorem map_sgnR (φ : R →+* ZMod p) (s : Bool) :
    φ (sgnR (R := R) s) = sgnR (R := ZMod p) s := by
  cases s <;> simp [sgnR]

private theorem sgnR_mul_self {K : Type} [Ring K] (s : Bool) :
    (sgnR (R := K) s) * sgnR (R := K) s = 1 := by
  cases s <;> simp [sgnR]

private theorem covecR_sub (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (c d : Fin n → R) : covecR φ f (c - d) = covecR φ f c - covecR φ f d := by
  simp only [covecR, Pi.sub_apply, map_sub, mul_sub]
  rw [show (∑ x, (2⁻¹ * φ (c x) - 2⁻¹ * φ (d x)) • f.coord x) =
      ∑ x, ((2⁻¹ * φ (c x)) • f.coord x - (2⁻¹ * φ (d x)) • f.coord x) from
    Finset.sum_congr rfl fun x _ => sub_smul (2⁻¹ * φ (c x)) (2⁻¹ * φ (d x)) (f.coord x)]
  rw [Finset.sum_sub_distrib]

private theorem covecR_smul (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (a : R) (c : Fin n → R) : covecR φ f (a • c) = φ a • covecR φ f c := by
  simp only [covecR, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  module

theorem coord_vecR (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U) (v : Fin n → R)
    (i : Fin n) : f.coord i (vecR φ f v) = φ (v i) := by
  rw [vecR]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg hji, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem covecR_vecR (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U) (c v : Fin n → R) :
    covecR φ f c (vecR φ f v) = (2 : ZMod p)⁻¹ * φ (dotProduct c v) := by
  simp only [covecR, LinearMap.sum_apply, LinearMap.smul_apply, coord_vecR, dotProduct,
    map_sum, map_mul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem covecR_basis (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U) (c : Fin n → R)
    (i : Fin n) : covecR φ f c (f i) = (2 : ZMod p)⁻¹ * φ (c i) := by
  simp only [covecR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · intro j _ hji
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hji, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem vecR_ne_of_good {good : R → Prop} {φ : R →+* ZMod p} (hgood : ∀ x, good x → φ x ≠ 0)
    (f : Module.Basis (Fin n) (ZMod p) U) {v w : Fin n → R} (h : ∃ l, good (v l - w l)) :
    vecR φ f v ≠ vecR φ f w := by
  obtain ⟨l, hl⟩ := h
  intro heq
  have h1 : φ (v l) = φ (w l) := by
    rw [← coord_vecR φ f v l, ← coord_vecR φ f w l, heq]
  have h2 : φ (v l - w l) = 0 := by rw [map_sub, h1, sub_self]
  exact hgood _ hl h2

theorem vecR_mem_span_image_iff {good : R → Prop} {φ : R →+* ZMod p}
    (hgood : ∀ x, good x → φ x ≠ 0) (f : Module.Basis (Fin n) (ZMod p) U) (I : Finset (Fin n))
    {v : Fin n → R} (hv : ∀ i, v i = 0 ∨ good (v i)) :
    vecR φ f v ∈ Submodule.span (ZMod p) (f '' ↑I) ↔ ∀ i ∉ I, v i = 0 := by
  constructor
  · intro hmem i hi
    by_contra hvi
    have hgoodi : good (v i) := (hv i).resolve_left hvi
    have hne : φ (v i) ≠ 0 := hgood _ hgoodi
    have hsupp := Module.Basis.repr_support_subset_of_mem_span f (↑I : Set (Fin n)) hmem
    have : i ∈ (f.repr (vecR φ f v)).support := by
      simp only [Finsupp.mem_support_iff]
      rw [← Module.Basis.coord_apply]
      rwa [coord_vecR]
    exact hi (hsupp this)
  · intro hv0
    have hsum : vecR φ f v = ∑ i ∈ I, φ (v i) • f i := by
      rw [vecR, ← Finset.sum_subset (Finset.subset_univ I)]
      intro i _ hi
      rw [hv0 i hi, map_zero, zero_smul]
    rw [hsum]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_image_of_mem f (by simpa using hi))

theorem mem_span_of_sum_smul_eq (hp : p ≠ 2) (φ : R →+* ZMod p)
    (f : Module.Basis (Fin n) (ZMod p) U) {k s : ℕ} {v : Fin k → Fin n → R} (a : Fin k → R)
    (i : Fin n) (h : ∑ l, a l • v l = (2 : R) ^ s • Pi.single i 1) :
    f i ∈ Submodule.span (ZMod p) (Set.range fun l => vecR φ f (v l)) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hlin : vecR φ f (∑ l, a l • v l) =
      ∑ l, φ (a l) • vecR φ f (v l) := by
    have := vecR_finset_sum φ f Finset.univ a v
    simpa using this
  have hmain : vecR φ f ((2 : R) ^ s • Pi.single i 1) = (2 : ZMod p) ^ s • f i := by
    rw [vecR_smul, vecR_single, map_pow, map_ofNat]
  have heq : vecR φ f ((2 : R) ^ s • Pi.single i 1) = vecR φ f (∑ l, a l • v l) := by
    rw [← h]
  have hkey : (2 : ZMod p) ^ s • f i ∈ Submodule.span (ZMod p)
      (Set.range fun l => vecR φ f (v l)) := by
    rw [← hmain, heq, hlin]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hpow : (2 : ZMod p) ^ s ≠ 0 := pow_ne_zero _ h2
  have := Submodule.smul_mem _ ((2 : ZMod p) ^ s)⁻¹ hkey
  rwa [inv_smul_smul₀ hpow] at this

namespace ReflTable

variable {m N : ℕ} (T : ReflTable R n m N) (φ : R →+* ZMod p)
  (f : Module.Basis (Fin n) (ZMod p) U)

@[expose] noncomputable def vecU (j : Fin N) : U := vecR φ f (T.root j)

@[expose] noncomputable def covecU (j : Fin N) : Module.Dual (ZMod p) U := covecR φ f (T.coroot j)

@[expose] noncomputable def refl (j : Fin N) : U ≃ₗ[ZMod p] U :=
  if h : T.covecU φ f j (T.vecU φ f j) = 2 then Module.reflection h else 1

@[expose] noncomputable def group : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure (Set.range fun k => T.refl φ f (T.gen k))

@[expose] noncomputable def pairProd (i j : Fin N) (w : List Bool) : U ≃ₗ[ZMod p] U :=
  (w.map fun x => T.refl φ f (if x then i else j)).prod

variable {T φ f} {good : R → Prop}

theorem covecU_vecU (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    T.covecU φ f j (T.vecU φ f j) = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [show T.covecU φ f j (T.vecU φ f j) =
      (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot j) (T.root j)) from
    covecR_vecR φ f (T.coroot j) (T.root j), hv.coroot_root j, map_ofNat]
  field_simp [h2]
  norm_num

theorem refl_apply (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) (v : U) :
    T.refl φ f j v = v - T.covecU φ f j v • T.vecU φ f j := by
  rw [ReflTable.refl, dif_pos (covecU_vecU hv hp j), Module.reflection_apply]

theorem refl_mul_self (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    T.refl φ f j * T.refl φ f j = 1 := by
  have hinv : (T.refl φ f j)⁻¹ = T.refl φ f j := by
    rw [ReflTable.refl, dif_pos (covecU_vecU hv hp j), Module.reflection_inv]
  nth_rewrite 2 [← hinv]
  exact mul_inv_cancel _

theorem isRefl_refl (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) : IsRefl p (T.refl φ f j) := by
  let : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  refine (isRefl_iff hp _).mpr ⟨T.vecU φ f j, T.covecU φ f j, covecU_vecU hv hp j, ?_⟩
  rw [ReflTable.refl, dif_pos (covecU_vecU hv hp j)]

theorem movedSpace_refl (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    HardMathSupport.Kantor79.movedSpace (T.refl φ f j) =
      Submodule.span (ZMod p) {T.vecU φ f j} := by
  rw [HardMathSupport.Kantor79.movedSpace]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change T.refl φ f j v - v ∈ Submodule.span (ZMod p) {T.vecU φ f j}
    have h : T.refl φ f j v - v = (-(T.covecU φ f j v)) • T.vecU φ f j := by
      rw [refl_apply hv hp j v]
      rw [show (v - T.covecU φ f j v • T.vecU φ f j) - v
          = -(T.covecU φ f j v • T.vecU φ f j) by abel]
      rw [neg_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    rintro _ hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨-(2 : ZMod p)⁻¹ • T.vecU φ f j, ?_⟩
    have hcu : T.covecU φ f j (-(2 : ZMod p)⁻¹ • T.vecU φ f j) = -1 := by
      rw [map_smul, covecU_vecU hv hp j, smul_eq_mul]
      have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
      field_simp [h2]
    change T.refl φ f j (-(2 : ZMod p)⁻¹ • T.vecU φ f j) -
      (-(2 : ZMod p)⁻¹ • T.vecU φ f j) = T.vecU φ f j
    rw [refl_apply hv hp j]
    rw [hcu]
    simp

theorem ker_refl_sub_one (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    LinearMap.ker ((T.refl φ f j : U →ₗ[ZMod p] U) - 1) = LinearMap.ker (T.covecU φ f j) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hvec : T.vecU φ f j ≠ 0 := by
    intro h0
    have h := covecU_vecU (φ := φ) (f := f) hv hp j
    rw [h0, map_zero] at h
    exact h2 h.symm
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have h : ((T.refl φ f j : U →ₗ[ZMod p] U) - 1) v =
      -(T.covecU φ f j v • T.vecU φ f j) := by
    change T.refl φ f j v - v = _
    rw [refl_apply hv hp j v]
    abel
  rw [h, neg_eq_zero, smul_eq_zero]
  constructor
  · rintro (hc | hu)
    · exact hc
    · exact absurd hu hvec
  · intro hc; exact Or.inl hc

theorem refl_apply_basis_eq_self_iff (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (j : Fin N) (i : Fin n) : T.refl φ f j (f i) = f i ↔ T.coroot j i = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hvec : T.vecU φ f j ≠ 0 := by
    intro h0
    have h := covecU_vecU (φ := φ) (f := f) hv hp j
    rw [h0, map_zero] at h
    exact h2 h.symm
  have hcv : T.covecU φ f j (f i) = (2 : ZMod p)⁻¹ * φ (T.coroot j i) :=
    covecR_basis φ f (T.coroot j) i
  rw [refl_apply hv hp j (f i)]
  constructor
  · intro heq
    have hx : T.covecU φ f j (f i) • T.vecU φ f j = 0 := by
      have h : f i + 0 = f i + T.covecU φ f j (f i) • T.vecU φ f j := by
        simpa using (sub_eq_iff_eq_add.mp heq).symm
      exact (add_left_cancel h).symm
    have hc : T.covecU φ f j (f i) = 0 := (smul_eq_zero.mp hx).resolve_right hvec
    rw [hcv] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (inv_ne_zero h2)
    · rcases hv.coroot_good j i with h0 | hg
      · exact h0
      · exact absurd h (hgood _ hg)
  · intro hc
    rw [hcv, hc, map_zero, mul_zero, zero_smul, sub_zero]

theorem forall_refl_sub_mem_ker_coord_iff (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (j : Fin N) (i : Fin n) :
    (∀ v, T.refl φ f j v - v ∈ LinearMap.ker (f.coord i)) ↔ T.root j i = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcoord : ∀ v, f.coord i (T.refl φ f j v - v) =
      -(T.covecU φ f j v * φ (T.root j i)) := by
    intro v
    have h1 : T.refl φ f j v - v = -(T.covecU φ f j v • T.vecU φ f j) := by
      rw [refl_apply hv hp j v]
      abel
    rw [h1, map_neg, map_smul, smul_eq_mul]
    rw [show T.vecU φ f j = vecR φ f (T.root j) from rfl, coord_vecR]
  constructor
  · intro h
    have h1 := h (T.vecU φ f j)
    rw [LinearMap.mem_ker, hcoord] at h1
    rw [covecU_vecU hv hp j] at h1
    have hphi : φ (T.root j i) = 0 := by
      have h2' : (2 : ZMod p) * φ (T.root j i) = 0 := neg_eq_zero.mp h1
      exact (mul_eq_zero.mp h2').resolve_left h2
    rcases hv.root_good j i with h0 | hg
    · exact h0
    · exact absurd hphi (hgood _ hg)
  · intro hr v
    rw [LinearMap.mem_ker, hcoord, hr, map_zero, mul_zero, neg_zero]

theorem refl_apply_vecR (hv : T.Valid good) (hp : p ≠ 2) {j : Fin N} {v w : Fin n → R}
    (h : (2 : R) • v - dotProduct (T.coroot j) v • T.root j = (2 : R) • w) :
    T.refl φ f j (vecR φ f v) = vecR φ f w := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hlin : (2 : ZMod p) • vecR φ f v -
      φ (dotProduct (T.coroot j) v) • vecR φ f (T.root j) = (2 : ZMod p) • vecR φ f w := by
    have h' : vecR φ f ((2 : R) • v - dotProduct (T.coroot j) v • T.root j) =
        (2 : ZMod p) • vecR φ f w := by rw [h, vecR_smul, map_ofNat]
    rw [← h']
    rw [vecR_sub, vecR_smul, vecR_smul, map_ofNat]
  have hw : vecR φ f w = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • vecR φ f v -
      φ (dotProduct (T.coroot j) v) • vecR φ f (T.root j)) := by
    rw [hlin]
    exact (inv_smul_smul₀ h2 _).symm
  rw [refl_apply hv hp j, hw]
  have hc : T.covecU φ f j (vecR φ f v) =
      (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot j) v) :=
    covecR_vecR φ f (T.coroot j) v
  rw [hc]
  rw [show T.vecU φ f j = vecR φ f (T.root j) from rfl]
  rw [smul_sub, inv_smul_smul₀ h2, ← smul_assoc, smul_eq_mul]

private theorem covecR_conjrel {i k k' : Fin N} {s : Bool} (h : T.ConjRel i k k' s) :
    (2 : ZMod p) • T.covecU φ f k -
      φ (dotProduct (T.coroot k) (T.root i)) • T.covecU φ f i =
      ((2 : ZMod p) * sgnR s) • T.covecU φ f k' := by
  have hd := congrArg (covecR φ f) h.2
  simpa only [covecR_sub, covecR_smul, ReflTable.covecU, map_ofNat, map_mul, map_sgnR]
    using hd

private theorem covecU_refl_conj (hv : T.Valid good) (hp : p ≠ 2) {i k k' : Fin N} {s : Bool}
    (h : T.ConjRel i k k' s) (v : U) :
    T.covecU φ f k (T.refl φ f i v) = sgnR s * T.covecU φ f k' v := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hdual := congrArg (fun l : Module.Dual (ZMod p) U => l v)
    (covecR_conjrel (T := T) (φ := φ) (f := f) h)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hdual
  have hphi : φ (dotProduct (T.coroot k) (T.root i)) =
      2 * T.covecU φ f k (T.vecU φ f i) := by
    rw [show T.covecU φ f k (T.vecU φ f i) =
        (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot k) (T.root i)) from
      covecR_vecR φ f (T.coroot k) (T.root i)]
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  rw [hphi] at hdual
  rw [refl_apply hv hp i v, map_sub, map_smul, smul_eq_mul]
  have h2eq : (2 : ZMod p) * (T.covecU φ f k v -
      T.covecU φ f i v * T.covecU φ f k (T.vecU φ f i)) =
      (2 : ZMod p) * (sgnR s * T.covecU φ f k' v) := by
    linear_combination hdual
  exact mul_left_cancel₀ h2 h2eq

private theorem refl_vecU_conj (hv : T.Valid good) (hp : p ≠ 2) {i k k' : Fin N} {s : Bool}
    (h : T.ConjRel i k k' s) :
    T.refl φ f i (T.vecU φ f k) = (sgnR s : ZMod p) • T.vecU φ f k' := by
  have h1 := refl_apply_vecR (T := T) (φ := φ) (f := f) hv hp (j := i)
    (v := T.root k) (w := (sgnR s : R) • T.root k') (by rw [← mul_smul]; exact h.1)
  rw [show T.vecU φ f k = vecR φ f (T.root k) from rfl, h1, vecR_smul, map_sgnR]
  rfl

private theorem refl_refl_apply (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) (v : U) :
    T.refl φ f j (T.refl φ f j v) = v := by
  rw [ReflTable.refl, dif_pos (covecU_vecU (φ := φ) (f := f) hv hp j)]
  exact Module.involutive_reflection (covecU_vecU (φ := φ) (f := f) hv hp j) v

private theorem sgnR_smul_smul (s : Bool) (c : ZMod p) (r : U) :
    ((sgnR s : ZMod p) * c) • ((sgnR s : ZMod p) • r) = c • r := by
  rw [mul_smul, smul_comm c (sgnR s : ZMod p), ← mul_smul,
    show (sgnR s * sgnR s : ZMod p) = 1 from sgnR_mul_self s, one_smul]

private theorem vecR_reindex (e : Fin n ≃ Fin n) (w : Fin n → R) :
    vecR φ (f.reindex e) w = vecR φ f (fun l => w (e l)) := by
  rw [vecR, vecR]
  simp only [Module.Basis.reindex_apply]
  rw [← Equiv.sum_comp e.symm (fun l => φ (w (e l)) • f l)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Equiv.apply_symm_apply]

private theorem covecR_reindex (e : Fin n ≃ Fin n) (c : Fin n → R) :
    covecR φ f c = covecR φ (f.reindex e) (fun k => c (e.symm k)) := by
  ext x
  rw [covecR, covecR]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
  rw [show (∑ k, (2⁻¹ * φ (c (e.symm k))) * (f.repr x) (e.symm k)) =
      ∑ k, (2⁻¹ * φ (c k)) * (f.repr x) k from by
    rw [← Equiv.sum_comp e.symm (fun l => (2⁻¹ * φ (c l)) * (f.repr x) l)]]

theorem refl_conj_eq (hv : T.Valid good) (hp : p ≠ 2) {i k k' : Fin N} {s : Bool}
    (h : T.ConjRel i k k' s) : T.refl φ f i * T.refl φ f k * (T.refl φ f i)⁻¹ = T.refl φ f k' := by
  have hii : (T.refl φ f i)⁻¹ = T.refl φ f i := by
    rw [ReflTable.refl, dif_pos (covecU_vecU (φ := φ) (f := f) hv hp i), Module.reflection_inv]
  rw [hii]
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  calc T.refl φ f i (T.refl φ f k (T.refl φ f i v))
      = T.refl φ f i
          (T.refl φ f i v - T.covecU φ f k (T.refl φ f i v) • T.vecU φ f k) := by
        rw [refl_apply hv hp k]
    _ = T.refl φ f i (T.refl φ f i v) -
          T.covecU φ f k (T.refl φ f i v) • T.refl φ f i (T.vecU φ f k) := by
        rw [map_sub, map_smul]
    _ = v - T.covecU φ f k (T.refl φ f i v) • T.refl φ f i (T.vecU φ f k) := by
        rw [refl_refl_apply (T := T) (φ := φ) (f := f) hv hp i v]
    _ = v - (sgnR s * T.covecU φ f k' v) • ((sgnR s : ZMod p) • T.vecU φ f k') := by
        rw [covecU_refl_conj (T := T) (φ := φ) (f := f) hv hp h,
          refl_vecU_conj (T := T) (φ := φ) (f := f) hv hp h]
    _ = T.refl φ f k' v := by
        rw [refl_apply hv hp k']
        rw [sgnR_smul_smul s (T.covecU φ f k' v) (T.vecU φ f k')]

theorem refl_wconj (hv : T.Valid good) (hp : p ≠ 2) (w : List (Fin m)) (j : Fin N) :
    T.refl φ f (T.wconj w j) = (w.map fun k => T.refl φ f (T.gen k)).prod * T.refl φ f j *
      ((w.map fun k => T.refl φ f (T.gen k)).prod)⁻¹ := by
  induction w with
  | nil => simp [ReflTable.wconj]
  | cons k w ih =>
    have hstep : T.refl φ f (T.wconj (k :: w) j) =
        T.refl φ f (T.gen k) * T.refl φ f (T.wconj w j) * (T.refl φ f (T.gen k))⁻¹ := by
      rw [show T.wconj (k :: w) j = T.conj k (T.wconj w j) from rfl]
      exact (refl_conj_eq (φ := φ) (f := f) hv hp (hv.conj k (T.wconj w j))).symm
    rw [hstep, ih, List.map_cons, List.prod_cons]
    group

theorem refl_mem_group (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    T.refl φ f j ∈ T.group φ f := by
  rw [← hv.word j, refl_wconj hv hp]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.inv_mem _ ?_)
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  · exact Subgroup.subset_closure ⟨T.cls j, rfl⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩

theorem exists_conj_of_cls_eq (hv : T.Valid good) (hp : p ≠ 2) {j j' : Fin N}
    (h : T.cls j = T.cls j') : ∃ g ∈ T.group φ f, T.refl φ f j' = g * T.refl φ f j * g⁻¹ := by
  let P : U ≃ₗ[ZMod p] U := ((T.word j).map fun k => T.refl φ f (T.gen k)).prod
  let P' : U ≃ₗ[ZMod p] U := ((T.word j').map fun k => T.refl φ f (T.gen k)).prod
  have hP : T.refl φ f j = P * T.refl φ f (T.gen (T.cls j)) * P⁻¹ := by
    have := refl_wconj (T := T) (φ := φ) (f := f) hv hp (T.word j) (T.gen (T.cls j))
    rwa [hv.word j] at this
  have hP' : T.refl φ f j' = P' * T.refl φ f (T.gen (T.cls j')) * P'⁻¹ := by
    have := refl_wconj (T := T) (φ := φ) (f := f) hv hp (T.word j') (T.gen (T.cls j'))
    rwa [hv.word j'] at this
  have hmemP : P ∈ T.group φ f := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  have hmemP' : P' ∈ T.group φ f := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  refine ⟨P' * P⁻¹, Subgroup.mul_mem _ hmemP' (Subgroup.inv_mem _ hmemP), ?_⟩
  have hA : T.refl φ f (T.gen (T.cls j)) = P⁻¹ * T.refl φ f j * P := by
    rw [hP]; group
  rw [hP', ← h, hA]; group

theorem exists_conj_eq_refl (hv : T.Valid good) (hp : p ≠ 2) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ T.group φ f) (j : Fin N) : ∃ j', g * T.refl φ f j * g⁻¹ = T.refl φ f j' := by
  have key : ∀ g ∈ T.group φ f, ∀ i, ∃ i', g * T.refl φ f i * g⁻¹ = T.refl φ f i' := by
    intro g hg
    refine Subgroup.closure_induction''
      (p := fun g _ => ∀ i, ∃ i', g * T.refl φ f i * g⁻¹ = T.refl φ f i') ?_ ?_ ?_ ?_ hg
    · rintro x ⟨k, rfl⟩ i
      exact ⟨T.conj k i, refl_conj_eq (φ := φ) (f := f) hv hp (hv.conj k i)⟩
    · rintro x ⟨k, rfl⟩ i
      have hxx : (T.refl φ f (T.gen k))⁻¹ = T.refl φ f (T.gen k) :=
        inv_eq_of_mul_eq_one_right (refl_mul_self (φ := φ) (f := f) hv hp (T.gen k))
      exact ⟨T.conj k i,
        by simpa only [hxx] using refl_conj_eq (φ := φ) (f := f) hv hp (hv.conj k i)⟩
    · intro i
      exact ⟨i, by rw [one_mul, inv_one, mul_one]⟩
    · intro a b ha hb iha ihb i
      obtain ⟨i'', hi''⟩ := ihb i
      obtain ⟨i', hi'⟩ := iha i''
      refine ⟨i', ?_⟩
      rw [mul_inv_rev]
      calc a * b * T.refl φ f i * (b⁻¹ * a⁻¹)
          = a * (b * T.refl φ f i * b⁻¹) * a⁻¹ := by group
        _ = a * T.refl φ f i'' * a⁻¹ := by rw [hi'']
        _ = T.refl φ f i' := hi'
  exact key g hg j

theorem exists_eq_refl (hv : T.Valid good) (hp : p ≠ 2)
    (htv : QTwoLin.TransvectionFree (T.group φ f)) {t : U ≃ₗ[ZMod p] U} (ht : t ∈ T.group φ f)
    (hrt : IsRefl p t) : ∃ j, t = T.refl φ f j := by
  let : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  obtain ⟨g, hg, s, hs, hts⟩ := exists_conj_of_isRefl_mem_closure (p := p) hp
    (S := Set.range fun k => T.refl φ f (T.gen k))
    (fun s hs => by
      obtain ⟨k, rfl⟩ := hs
      exact isRefl_refl (T := T) (φ := φ) (f := f) hv hp (T.gen k)) htv ht hrt
  obtain ⟨k, rfl⟩ := hs
  obtain ⟨j', hj'⟩ := exists_conj_eq_refl (T := T) (φ := φ) (f := f) hv hp hg (T.gen k)
  exact ⟨j', by rw [hts, hj']⟩

theorem toMatrix_refl (hv : T.Valid good) (hp : p ≠ 2) (j : Fin N) :
    LinearMap.toMatrix f f (T.refl φ f j : U →ₗ[ZMod p] U) =
      evMat φ 1 (reflZ (T.root j) (T.coroot j)) := by
  rw [ReflTable.refl, dif_pos (covecU_vecU (φ := φ) (f := f) hv hp j)]
  rw [toMatrix_reflection f (covecU_vecU (φ := φ) (f := f) hv hp j), evMat_reflZ hp]
  congr 1
  ext i k
  simp only [Matrix.vecMulVec_apply]
  have h1 : f.repr (T.vecU φ f j) i = φ (T.root j i) := by
    rw [← Module.Basis.coord_apply]
    exact coord_vecR φ f (T.root j) i
  have h2 : T.covecU φ f j (f k) = (2 : ZMod p)⁻¹ * φ (T.coroot j k) :=
    covecR_basis φ f (T.coroot j) k
  rw [h1, h2]

theorem eq_refl_of_toMatrix (hv : T.Valid good) (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U} {j : Fin N}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = M)
    (hM : evMat φ 1 (reflZ (T.root j) (T.coroot j)) = M) : t = T.refl φ f j := by
  refine eq_of_toMatrix_eq f ?_
  rw [ht, toMatrix_refl (T := T) (φ := φ) (f := f) hv hp j, hM]

theorem basisClosure_eq_group (hv : T.Valid good) (hp : p ≠ 2)
    {M : Fin m → Matrix (Fin n) (Fin n) (ZMod p)}
    (hM : ∀ k, evMat φ 1 (reflZ (T.root (T.gen k)) (T.coroot (T.gen k))) = M k) :
    basisClosure f (Set.range M) = T.group φ f := by
  rw [basisClosure, ReflTable.group]
  congr 1
  apply Set.ext
  intro g
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (eq_refl_of_toMatrix (T := T) (φ := φ) (f := f) (hv := hv) (hp := hp)
      (j := T.gen k) hk.symm (hM k)).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [toMatrix_refl (T := T) (φ := φ) (f := f) hv hp (T.gen k), hM k]⟩

theorem pow_mul_refl_eq_one (hv : T.Valid good) (hp : p ≠ 2) {i j : Fin N} {e : ℕ}
    (h : (reflZ (T.root i) (T.coroot i) * reflZ (T.root j) (T.coroot j)) ^ e =
      (4 : R) ^ e • (1 : Matrix (Fin n) (Fin n) R)) : (T.refl φ f i * T.refl φ f j) ^ e = 1 := by
  refine eq_of_toMatrix_eq f ?_
  have hcoe : (((T.refl φ f i * T.refl φ f j) ^ e : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
      = ((T.refl φ f i : U →ₗ[ZMod p] U) * (T.refl φ f j : U →ₗ[ZMod p] U)) ^ e := by
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod p) (M := U)
      ((T.refl φ f i * T.refl φ f j) ^ e)) = _
    rw [map_pow, map_mul]
    rfl
  rw [hcoe]
  rw [← LinearMap.toMatrix_pow, LinearMap.toMatrix_mul,
    toMatrix_refl (T := T) (φ := φ) (f := f) hv hp i,
    toMatrix_refl (T := T) (φ := φ) (f := f) hv hp j, ← evMat_mul, ← evMat_pow]
  rw [show (reflZ (T.root i) (T.coroot i) * reflZ (T.root j) (T.coroot j)) ^ e =
      (2 : R) ^ (2 * e) • (1 : Matrix (Fin n) (Fin n) R) from by
    rw [h, show (4 : R) ^ e = (2 : R) ^ (2 * e) by
      rw [show (4 : R) = (2 : R) ^ 2 by norm_num, ← pow_mul]]]
  rw [evMat_two_pow_smul_one hp,
    show (↑(1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = (1 : U →ₗ[ZMod p] U) from
      LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_one]

theorem mul_refl_ne_one (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0) (hp : p ≠ 2)
    {i j : Fin N} {a b : Fin n}
    (h : good ((reflZ (T.root i) (T.coroot i) * reflZ (T.root j) (T.coroot j) -
      (4 : R) • (1 : Matrix (Fin n) (Fin n) R)) a b)) : T.refl φ f i * T.refl φ f j ≠ 1 := by
  intro heq
  have hmat : evMat φ 2 (reflZ (T.root i) (T.coroot i) * reflZ (T.root j) (T.coroot j)) = 1 := by
    have ht := congrArg (fun t : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U))
      heq
    rw [show (↑(T.refl φ f i * T.refl φ f j) : U →ₗ[ZMod p] U) =
        (T.refl φ f i : U →ₗ[ZMod p] U) * (T.refl φ f j : U →ₗ[ZMod p] U) from
      LinearEquiv.coe_toLinearMap_mul] at ht
    rw [show (↑(1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = (1 : U →ₗ[ZMod p] U) from
      LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_one] at ht
    rw [LinearMap.toMatrix_mul, toMatrix_refl (T := T) (φ := φ) (f := f) hv hp i,
      toMatrix_refl (T := T) (φ := φ) (f := f) hv hp j, ← evMat_mul] at ht
    exact ht
  exact (evMat_ne_one φ hgood (M := reflZ (T.root i) (T.coroot i) *
      reflZ (T.root j) (T.coroot j)) (a := a) (b := b)
    (by rw [show (2 : R) ^ 2 = 4 by norm_num]; exact h)) hmat

theorem refl_eq_refl_reindex (hv : T.Valid good) {m' N' : ℕ} {T' : ReflTable R n m' N'}
    {good' : R → Prop} (hv' : T'.Valid good') (hp : p ≠ 2) (e : Fin n ≃ Fin n) {j : Fin N}
    {i : Fin N'} {s : Bool} (hr : (fun l => T.root j (e.symm l)) = (sgnR s : R) • T'.root i)
    (hc : (fun l => T.coroot j (e.symm l)) = (sgnR s : R) • T'.coroot i) :
    T.refl φ f j = T'.refl φ (f.reindex e) i := by
  have hrU : T.vecU φ f j = (sgnR s : ZMod p) • T'.vecU φ (f.reindex e) i := by
    have h1 : vecR φ f (T.root j) =
        vecR φ (f.reindex e) (fun l => T.root j (e.symm l)) := by
      have h2 : vecR φ f (T.root j) =
          vecR φ f (fun l => T.root j (e.symm (e l))) := by
        congr 1
        ext l; rw [Equiv.symm_apply_apply]
      rw [h2, vecR_reindex (φ := φ) (f := f) e (fun k => T.root j (e.symm k))]
    rw [show T.vecU φ f j = vecR φ f (T.root j) from rfl, h1, hr, vecR_smul, map_sgnR]
    rfl
  have hcU : T.covecU φ f j = (sgnR s : ZMod p) • T'.covecU φ (f.reindex e) i := by
    rw [show T.covecU φ f j = covecR φ f (T.coroot j) from rfl,
      covecR_reindex (φ := φ) (f := f) e (T.coroot j), hc, covecR_smul, map_sgnR]
    rfl
  ext v
  rw [refl_apply hv hp j v, refl_apply (T := T') (φ := φ) (f := f.reindex e) hv' hp i v,
    hrU, hcU, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  exact sgnR_smul_smul s (T'.covecU φ (f.reindex e) i v) (T'.vecU φ (f.reindex e) i)

theorem pairProd_mem_closure (i j : Fin N) (w : List Bool) :
    T.pairProd φ f i j w ∈ Subgroup.closure {T.refl φ f i, T.refl φ f j} := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  cases b
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem refl_foldr_rc (hv : T.Valid good) (hp : p ≠ 2) {rc : Fin N → Fin N → Fin N}
    {rs : Fin N → Fin N → Bool} (hrc : ∀ a k, T.ConjRel a k (rc a k) (rs a k)) (i j : Fin N)
    (w : List Bool) (k : Fin N) :
    T.refl φ f (w.foldr (fun x k => rc (if x then i else j) k) k) =
      T.pairProd φ f i j w * T.refl φ f k * (T.pairProd φ f i j w)⁻¹ := by
  induction w with
  | nil => simp [ReflTable.pairProd]
  | cons b w ih =>
    have hstep : T.refl φ f (List.foldr (fun x k => rc (if x then i else j) k) k (b :: w)) =
        T.refl φ f (if b then i else j) *
          T.refl φ f (List.foldr (fun x k => rc (if x then i else j) k) k w) *
          (T.refl φ f (if b then i else j))⁻¹ := by
      rw [List.foldr_cons]
      exact (refl_conj_eq (φ := φ) (f := f) hv hp (hrc (if b then i else j) _)).symm
    rw [hstep, ih]
    simp only [ReflTable.pairProd, List.map_cons, List.prod_cons]
    group

theorem refl_foldr_rc_mem_closure (hv : T.Valid good) (hp : p ≠ 2) {rc : Fin N → Fin N → Fin N}
    {rs : Fin N → Fin N → Bool} (hrc : ∀ a k, T.ConjRel a k (rc a k) (rs a k)) (i j : Fin N)
    (w : List Bool) (b : Bool) :
    T.refl φ f (w.foldr (fun x k => rc (if x then i else j) k) (if b then i else j)) ∈
      Subgroup.closure {T.refl φ f i, T.refl φ f j} := by
  rw [refl_foldr_rc (T := T) (φ := φ) (f := f) hv hp hrc i j w]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _
    (pairProd_mem_closure (T := T) (φ := φ) (f := f) i j w) ?_)
    (Subgroup.inv_mem _ (pairProd_mem_closure (T := T) (φ := φ) (f := f) i j w))
  cases b <;> exact Subgroup.subset_closure (by simp)

theorem refl_mul_comm (hv : T.Valid good) (hp : p ≠ 2) {i j : Fin N}
    (h₁ : dotProduct (T.coroot i) (T.root j) = 0) (h₂ : dotProduct (T.coroot j) (T.root i) = 0) :
    T.refl φ f i * T.refl φ f j = T.refl φ f j * T.refl φ f i := by
  rw [ReflTable.refl, dif_pos (covecU_vecU (φ := φ) (f := f) hv hp i),
    ReflTable.refl, dif_pos (covecU_vecU (φ := φ) (f := f) hv hp j)]
  refine reflection_mul_comm (covecU_vecU (φ := φ) (f := f) hv hp i)
    (covecU_vecU (φ := φ) (f := f) hv hp j) ?_ ?_
  · rw [show T.covecU φ f i (T.vecU φ f j) =
        (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot i) (T.root j)) from
      covecR_vecR φ f (T.coroot i) (T.root j), h₁, map_zero, mul_zero]
  · rw [show T.covecU φ f j (T.vecU φ f i) =
        (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot j) (T.root i)) from
      covecR_vecR φ f (T.coroot j) (T.root i), h₂, map_zero, mul_zero]

theorem vecU_not_mem_span_pair (hgood : ∀ x, good x → φ x ≠ 0) (hp : p ≠ 2) (ℓ : Fin n → R)
    {i i' j : Fin N} (hi : dotProduct ℓ (T.root i) = 0) (hi' : dotProduct ℓ (T.root i') = 0)
    (hj : good (dotProduct ℓ (T.root j))) :
    T.vecU φ f j ∉ Submodule.span (ZMod p) {T.vecU φ f i, T.vecU φ f i'} := by
  intro hmem
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hℓi : covecR φ f ℓ (T.vecU φ f i) = 0 := by
    rw [show T.vecU φ f i = vecR φ f (T.root i) from rfl, covecR_vecR, hi, map_zero, mul_zero]
  have hℓi' : covecR φ f ℓ (T.vecU φ f i') = 0 := by
    rw [show T.vecU φ f i' = vecR φ f (T.root i') from rfl, covecR_vecR, hi', map_zero,
      mul_zero]
  have hle : Submodule.span (ZMod p) {T.vecU φ f i, T.vecU φ f i'} ≤
      LinearMap.ker (covecR φ f ℓ) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change covecR φ f ℓ (T.vecU φ f i) = 0; exact hℓi
    · change covecR φ f ℓ (T.vecU φ f i') = 0; exact hℓi'
  have hmemker : T.vecU φ f j ∈ LinearMap.ker (covecR φ f ℓ) := hle hmem
  rw [LinearMap.mem_ker, show T.vecU φ f j = vecR φ f (T.root j) from rfl, covecR_vecR]
    at hmemker
  rcases mul_eq_zero.mp hmemker with h | h
  · exact h2 (inv_eq_zero.mp h)
  · exact hgood _ hj h

theorem setOf_isRefl_sub_mem_ker_coord (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (htv : QTwoLin.TransvectionFree (T.group φ f)) (i : Fin n) :
    {g | g ∈ T.group φ f ∧ IsRefl p g ∧ ∀ v, g v - v ∈ LinearMap.ker (f.coord i)} =
      (fun j => T.refl φ f j) '' {j | T.root j i = 0} := by
  ext g
  constructor
  · rintro ⟨hg, hgr, hgker⟩
    obtain ⟨j, rfl⟩ := exists_eq_refl (T := T) (φ := φ) (f := f) hv hp htv hg hgr
    exact ⟨j, (forall_refl_sub_mem_ker_coord_iff (T := T) (φ := φ) (f := f) hv hgood hp j
      i).mp hgker, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨refl_mem_group (T := T) (φ := φ) (f := f) hv hp j,
      isRefl_refl (T := T) (φ := φ) (f := f) hv hp j,
      (forall_refl_sub_mem_ker_coord_iff (T := T) (φ := φ) (f := f) hv hgood hp j i).mpr hj⟩

theorem setOf_isRefl_apply_basis (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (htv : QTwoLin.TransvectionFree (T.group φ f)) (i : Fin n) :
    {t | t ∈ T.group φ f ∧ IsRefl p t ∧ t (f i) = f i} =
      (fun j => T.refl φ f j) '' {j | T.coroot j i = 0} := by
  ext g
  constructor
  · rintro ⟨hg, hgr, hgker⟩
    obtain ⟨j, rfl⟩ := exists_eq_refl (T := T) (φ := φ) (f := f) hv hp htv hg hgr
    exact ⟨j, (refl_apply_basis_eq_self_iff (T := T) (φ := φ) (f := f) hv hgood hp j
      i).mp hgker, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨refl_mem_group (T := T) (φ := φ) (f := f) hv hp j,
      isRefl_refl (T := T) (φ := φ) (f := f) hv hp j,
      (refl_apply_basis_eq_self_iff (T := T) (φ := φ) (f := f) hv hgood hp j i).mpr hj⟩

theorem commutatorSpace_closure_image_refl (hv : T.Valid good) (hp : p ≠ 2) (J : Set (Fin N)) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure ((fun j => T.refl φ f j) '' J)) =
      Submodule.span (ZMod p) ((fun j => T.vecU φ f j) '' J) := by
  let : FiniteDimensional (ZMod p) U := Module.Finite.of_basis f
  rw [Set.image_eq_range]
  rw [HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace]
  rw [show (⨆ j : J, HardMathSupport.Kantor79.movedSpace (T.refl φ f (j : Fin N))) =
      ⨆ j : J, Submodule.span (ZMod p) {T.vecU φ f (j : Fin N)} from
    iSup_congr fun j => movedSpace_refl (T := T) (φ := φ) (f := f) hv hp (j : Fin N)]
  rw [← Submodule.span_iUnion, Set.iUnion_singleton_eq_range, Set.image_eq_range]

private theorem mem_centralizerSpace_closure_iff {S : Set (U ≃ₗ[ZMod p] U)} {v : U} :
    v ∈ centralizerSpace (Subgroup.closure S) ↔ ∀ s ∈ S, s v = v := by
  constructor
  · intro hv s hs
    exact (mem_centralizerSpace.mp hv) s (Subgroup.subset_closure hs)
  · intro hv
    refine mem_centralizerSpace.mpr fun g hg => ?_
    refine Subgroup.closure_induction (p := fun g _ => g v = v) (fun x hx => hv x hx) ?_ ?_ ?_ hg
    · rfl
    · intro a b ha hb iha ihb
      rw [LinearEquiv.mul_apply, ihb, iha]
    · intro a ha iha
      calc a⁻¹ v = a⁻¹ (a v) := by rw [iha]
        _ = (a⁻¹ * a) v := (LinearEquiv.mul_apply a⁻¹ a v).symm
        _ = v := by rw [inv_mul_cancel]; rfl

theorem centralizerSpace_closure_image_refl (hv : T.Valid good) (hp : p ≠ 2) (J : Set (Fin N)) :
    centralizerSpace (Subgroup.closure ((fun j => T.refl φ f j) '' J)) =
      ⨅ j ∈ J, LinearMap.ker (T.covecU φ f j) := by
  ext v
  rw [mem_centralizerSpace_closure_iff, Submodule.mem_iInf]
  constructor
  · intro hfixall j
    rw [Submodule.mem_iInf]
    intro hj
    rw [LinearMap.mem_ker]
    have hfix := hfixall (T.refl φ f j) ⟨j, hj, rfl⟩
    have hmem : v ∈ LinearMap.ker ((T.refl φ f j : U →ₗ[ZMod p] U) - 1) := by
      rw [LinearMap.mem_ker]
      change T.refl φ f j v - v = 0
      rw [hfix, sub_self]
    rwa [ker_refl_sub_one (T := T) (φ := φ) (f := f) hv hp j, LinearMap.mem_ker] at hmem
  · intro hk s hs
    rw [Set.mem_image] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    simp only [Submodule.mem_iInf] at hk
    have hk' : v ∈ LinearMap.ker (T.covecU φ f j) := hk j hj
    have hmem : v ∈ LinearMap.ker ((T.refl φ f j : U →ₗ[ZMod p] U) - 1) := by
      rw [ker_refl_sub_one (T := T) (φ := φ) (f := f) hv hp j, LinearMap.mem_ker]
      exact hk'
    rw [LinearMap.mem_ker] at hmem
    change T.refl φ f j v - v = 0 at hmem
    rwa [sub_eq_zero] at hmem

theorem exists_conj_le_inf_ker (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (htv : QTwoLin.TransvectionFree (T.group φ f)) (I : Finset (Fin n))
    (j₁ : Fin N) (w : Fin N → Fin N)
    (hw : ∀ j, (∀ i ∉ I, T.root j i = 0) →
      (∀ i ∉ I, T.root (w j) i = 0) ∧ dotProduct (T.coroot j) (T.root (w j)) = 0 ∧
        T.cls (w j) = T.cls j₁) :
    ∀ x ∈ T.group φ f, IsRefl p x →
      HardMathSupport.Kantor79.movedSpace x ≤ Submodule.span (ZMod p) (f '' ↑I) →
      ∃ g ∈ T.group φ f, HardMathSupport.Kantor79.movedSpace (g * T.refl φ f j₁ * g⁻¹) ≤
        Submodule.span (ZMod p) (f '' ↑I) ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  intro x hx hxr hle
  obtain ⟨j, rfl⟩ := exists_eq_refl (T := T) (φ := φ) (f := f) hv hp htv hx hxr
  have hroot : ∀ i ∉ I, T.root j i = 0 := by
    rw [movedSpace_refl (T := T) (φ := φ) (f := f) hv hp j] at hle
    exact (vecR_mem_span_image_iff hgood f I (hv.root_good j)).mp
      ((Submodule.span_singleton_le_iff_mem (T.vecU φ f j) _).mp hle)
  obtain ⟨hw1, hw2, hw3⟩ := hw j hroot
  obtain ⟨g, hg, hgconj⟩ := exists_conj_of_cls_eq (T := T) (φ := φ) (f := f) hv hp
    (j := j₁) (j' := w j) hw3.symm
  refine ⟨g, hg, ?_⟩
  rw [← hgconj, movedSpace_refl (T := T) (φ := φ) (f := f) hv hp (w j)]
  rw [Submodule.span_le]
  rintro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [SetLike.mem_coe, Submodule.mem_inf]
  constructor
  · exact (vecR_mem_span_image_iff hgood f I (hv.root_good (w j))).mpr hw1
  · rw [ker_refl_sub_one (T := T) (φ := φ) (f := f) hv hp j, LinearMap.mem_ker,
      show T.covecU φ f j (T.vecU φ f (w j)) =
        (2 : ZMod p)⁻¹ * φ (dotProduct (T.coroot j) (T.root (w j))) from
      covecR_vecR φ f (T.coroot j) (T.root (w j)), hw2, map_zero, mul_zero]

private noncomputable def diagForm (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (D : Fin n → R) : LinearMap.BilinForm (ZMod p) U :=
  Matrix.toBilin f (Matrix.diagonal fun i => φ (D i))

private theorem diagForm_apply (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (D : Fin n → R) (x y : U) :
    diagForm φ f D x y = ∑ i, φ (D i) * f.coord i x * f.coord i y := by
  rw [diagForm, Matrix.toBilin_apply]
  simp only [Matrix.diagonal_apply, Module.Basis.coord_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]; ring
  · intro j _ hij
    rw [if_neg (fun h : i = j => hij h.symm)]
    ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem diagForm_isSymm (φ : R →+* ZMod p) (f : Module.Basis (Fin n) (ZMod p) U)
    (D : Fin n → R) : (diagForm φ f D).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [diagForm_apply, diagForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem diagForm_nondegenerate (φ : R →+* ZMod p)
    (f : Module.Basis (Fin n) (ZMod p) U) (D : Fin n → R)
    (hgood : ∀ x, good x → φ x ≠ 0) (hD : ∀ i, good (D i)) :
    (diagForm φ f D).Nondegenerate := by
  rw [diagForm]
  refine Matrix.Nondegenerate.toBilin ?_ f
  rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hgood _ (hD i)

private theorem diagForm_hcoord (D : Fin n → R)
    (hform : ∀ k, (∑ i, D i * T.root (T.gen k) i ^ 2) • T.coroot (T.gen k) =
      (4 : R) • fun i => D i * T.root (T.gen k) i) (k : Fin m) (i : Fin n) :
    φ (∑ j, D j * T.root (T.gen k) j ^ 2) * φ (T.coroot (T.gen k) i) =
      4 * (φ (D i) * φ (T.root (T.gen k) i)) := by
  have h := congrFun (hform k) i
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have h' := congrArg φ h
  simpa only [map_mul, map_ofNat] using h'

private theorem diagForm_self (D : Fin n → R) (k : Fin m) :
    diagForm φ f D (T.vecU φ f (T.gen k)) (T.vecU φ f (T.gen k)) =
      φ (∑ j, D j * T.root (T.gen k) j ^ 2) := by
  rw [diagForm_apply]
  have hcoord2 : ∀ i, f.coord i (T.vecU φ f (T.gen k)) = φ (T.root (T.gen k) i) :=
    fun i => coord_vecR φ f (T.root (T.gen k)) i
  simp only [hcoord2]
  rw [show (∑ i, φ (D i) * φ (T.root (T.gen k) i) * φ (T.root (T.gen k) i)) =
      ∑ i, φ (D i * T.root (T.gen k) i ^ 2) by
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_mul, ← map_mul]
    congr 1
    ring]
  rw [← map_sum]

private theorem covecU_gen_apply (k : Fin m) (v : U) :
    T.covecU φ f (T.gen k) v =
      ∑ i, (2⁻¹ * φ (T.coroot (T.gen k) i)) * f.coord i v := by
  rw [show T.covecU φ f (T.gen k) = covecR φ f (T.coroot (T.gen k)) from rfl]
  simp only [covecR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem diagForm_hcB (_hv : T.Valid good) (_hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (D : Fin n → R) (_hD : ∀ i, good (D i))
    (hform : ∀ k, (∑ i, D i * T.root (T.gen k) i ^ 2) • T.coroot (T.gen k) =
      (4 : R) • fun i => D i * T.root (T.gen k) i) (k : Fin m) :
    ∀ v, diagForm φ f D (T.vecU φ f (T.gen k)) (T.vecU φ f (T.gen k)) *
        T.covecU φ f (T.gen k) v =
      2 * diagForm φ f D (T.vecU φ f (T.gen k)) v := by
  intro v
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcoord2 : ∀ i, f.coord i (T.vecU φ f (T.gen k)) = φ (T.root (T.gen k) i) :=
    fun i => coord_vecR φ f (T.root (T.gen k)) i
  rw [diagForm_self (T := T) (φ := φ) (f := f) D k,
    covecU_gen_apply (T := T) (φ := φ) (f := f) k v, diagForm_apply]
  simp only [hcoord2]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h4 : φ (∑ j, D j * T.root (T.gen k) j ^ 2) *
      (2⁻¹ * φ (T.coroot (T.gen k) i)) =
      2 * (φ (D i) * φ (T.root (T.gen k) i)) := by
    calc φ (∑ j, D j * T.root (T.gen k) j ^ 2) * (2⁻¹ * φ (T.coroot (T.gen k) i))
        = 2⁻¹ * (φ (∑ j, D j * T.root (T.gen k) j ^ 2) *
            φ (T.coroot (T.gen k) i)) := by ring
      _ = 2⁻¹ * (4 * (φ (D i) * φ (T.root (T.gen k) i))) := by
            rw [diagForm_hcoord (T := T) (φ := φ) D hform k i]
      _ = 2 * (φ (D i) * φ (T.root (T.gen k) i)) := by
            field_simp [h2]
            ring
  rw [← mul_assoc, h4]
  ring

private theorem diagForm_gen_isometry (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (D : Fin n → R) (hD : ∀ i, good (D i))
    (hform : ∀ k, (∑ i, D i * T.root (T.gen k) i ^ 2) • T.coroot (T.gen k) =
      (4 : R) • fun i => D i * T.root (T.gen k) i) (k : Fin m) :
    ∀ x y, diagForm φ f D (T.refl φ f (T.gen k) x) (T.refl φ f (T.gen k) y) =
      diagForm φ f D x y := by
  have hB := diagForm_isSymm φ f D
  have hnd := diagForm_nondegenerate φ f D hgood hD
  have hc := covecU_vecU (T := T) (φ := φ) (f := f) hv hp (T.gen k)
  have hcB := diagForm_hcB (T := T) (φ := φ) (f := f) hv hgood hp D hD hform k
  have hrefl : T.refl φ f (T.gen k) = Module.reflection hc := by
    rw [ReflTable.refl, dif_pos hc]
  rw [hrefl]
  exact reflection_isometry hp (diagForm φ f D) hB hnd hc hcB

theorem transvectionFree_group (hv : T.Valid good) (hgood : ∀ x, good x → φ x ≠ 0)
    (hp : p ≠ 2) (D : Fin n → R) (hD : ∀ i, good (D i))
    (hform : ∀ k, (∑ i, D i * T.root (T.gen k) i ^ 2) • T.coroot (T.gen k) =
      (4 : R) • fun i => D i * T.root (T.gen k) i) :
    QTwoLin.TransvectionFree (T.group φ f) := by
  have hB := diagForm_isSymm φ f D
  have hnd := diagForm_nondegenerate φ f D hgood hD
  refine transvectionFree_of_isometry hp (diagForm φ f D) hB hnd ?_
  intro g hg x y
  refine isometry_of_mem_closure (diagForm φ f D) ?_ hg x y
  intro s hs x y
  obtain ⟨k, rfl⟩ := hs
  exact diagForm_gen_isometry (T := T) (φ := φ) (f := f) hv hgood hp D hD hform k x y

end ReflTable

end CFSG.StandardType.ZS.PrimModel

end

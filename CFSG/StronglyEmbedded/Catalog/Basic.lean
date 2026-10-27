module

public import TauCeti.GroupTheory.FixedPointCandidate
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU

public section

namespace CFSG.BenderSuzuki.Catalog

open Subgroup Polynomial

@[expose] noncomputable def derivedCentralQuotientEquiv {H P : Type*} [Group H] [Group P] [IsSimpleGroup P]
    (hP : ¬ IsMulCommutative P) (φ : H →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center H) : TauCeti.DerivedCentralQuotient H ≃* P := by
  let f : ↥(commutator H) →* P := φ.comp (commutator H).subtype
  have hperf := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hP
  have hK : center P = ⊥ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hP
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, commutator_def,
      map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφ, ← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hc : center ↥(commutator H) = f.ker := by
    refine le_antisymm (MonoidHom.center_le_ker f hf hK) fun x hx => ?_
    have hx' : (x : H) ∈ center H := hker hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx' y)
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]

@[expose] noncomputable def galoisEmbedding (k : ℕ) : GaloisField p k →+* K :=
  letI := ZMod.algebra K p
  (IsAlgClosed.lift (R := ZMod p) (M := K) (S := GaloisField p k)).toRingHom

variable {p K}

theorem galoisField_pow_card {k : ℕ} (hk : k ≠ 0) (y : GaloisField p k) : y ^ (p ^ k) = y := by
  let := Fintype.ofFinite (GaloisField p k)
  have h := FiniteField.pow_card y
  rwa [← Nat.card_eq_fintype_card, GaloisField.card p k hk] at h

theorem exists_galoisEmbedding_eq_iff {k : ℕ} (hk : k ≠ 0) (x : K) :
    (∃ y, galoisEmbedding p K k y = x) ↔ x ^ (p ^ k) = x := by
  classical
  constructor
  · rintro ⟨y, rfl⟩
    rw [← map_pow, galoisField_pow_card hk]
  · intro hx
    let := Fintype.ofFinite (GaloisField p k)
    let ι := galoisEmbedding p K k
    let S := ((X ^ (p ^ k) - X : K[X]).roots).toFinset
    have hp : 1 < p := (Fact.out : p.Prime).one_lt
    have hne : (X ^ (p ^ k) - X : K[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K hk hp
    have hmem : ∀ z : K, z ∈ S ↔ z ^ (p ^ k) = z := fun z => by
      simp [S, Multiset.mem_toFinset, mem_roots hne, sub_eq_zero]
    have hsub : Finset.univ.image ι ⊆ S := fun z hz => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
      rw [hmem, ← map_pow, galoisField_pow_card hk]
    have hcard : S.card ≤ (Finset.univ.image ι).card := by
      rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card, GaloisField.card p k hk]
      calc S.card ≤ (X ^ (p ^ k) - X : K[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ (p ^ k) - X : K[X]).natDegree := card_roots' _
        _ = p ^ k := FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hk hp
    have hxS : x ∈ S := (hmem x).mpr hx
    rw [← Finset.eq_of_subset_of_card_le hsub hcard] at hxS
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hxS
    exact ⟨y, hy⟩

theorem exists_map_galoisEmbedding_eq {k : ℕ} (hk : k ≠ 0) {m n : Type*}
    (g : Matrix m n K) (hg : ∀ i j, g i j ^ (p ^ k) = g i j) :
    ∃ A : Matrix m n (GaloisField p k), A.map (galoisEmbedding p K k) = g := by
  choose y hy using fun i j => (exists_galoisEmbedding_eq_iff hk (g i j)).mpr (hg i j)
  exact ⟨Matrix.of y, Matrix.ext fun i j => hy i j⟩

variable {m : Type*} [Fintype m] [DecidableEq m]

variable (p K) in
noncomputable def slMap (k : ℕ) :
    Matrix.SpecialLinearGroup m (GaloisField p k) →* Matrix.SpecialLinearGroup m K :=
  Matrix.SpecialLinearGroup.map (galoisEmbedding p K k)

theorem slMap_injective (k : ℕ) : Function.Injective (slMap p K k (m := m)) := by
  intro A B h
  ext i j
  exact (galoisEmbedding p K k).injective (congrArg (fun g : Matrix.SpecialLinearGroup m K =>
    (g : Matrix m m K) i j) h)

variable (K) in
noncomputable abbrev slFrobenius (k : ℕ) :
    Matrix.SpecialLinearGroup m K →* Matrix.SpecialLinearGroup m K :=
  Matrix.SpecialLinearGroup.map (iterateFrobenius K p k)

omit [IsAlgClosed K] in
theorem mem_fixedSubgroup_slFrobenius_iff (k : ℕ) (g : Matrix.SpecialLinearGroup m K) :
    g ∈ TauCeti.fixedSubgroup (slFrobenius (p := p) K k) ↔
      ∀ i j, (g : Matrix m m K) i j ^ (p ^ k) = (g : Matrix m m K) i j := by
  rw [TauCeti.mem_fixedSubgroup]
  constructor
  · intro h i j
    have := congrArg (fun g : Matrix.SpecialLinearGroup m K => (g : Matrix m m K) i j) h
    simpa [iterateFrobenius_def] using this
  · intro h
    ext i j
    simpa [iterateFrobenius_def] using h i j

theorem slMap_mem_fixedSubgroup {k : ℕ} (hk : k ≠ 0)
    (A : Matrix.SpecialLinearGroup m (GaloisField p k)) :
    slMap p K k A ∈ TauCeti.fixedSubgroup (slFrobenius (p := p) K k) := by
  rw [mem_fixedSubgroup_slFrobenius_iff]
  intro i j
  simp [slMap, ← map_pow, galoisField_pow_card hk]

noncomputable def slFixedEquiv {k : ℕ} (hk : k ≠ 0) :
    Matrix.SpecialLinearGroup m (GaloisField p k) ≃*
      ↥(TauCeti.fixedSubgroup (slFrobenius (p := p) (m := m) K k)) :=
  MulEquiv.ofBijective ((slMap p K k).codRestrict _ (slMap_mem_fixedSubgroup hk)) <| by
    refine ⟨fun A B h => slMap_injective k (congrArg Subtype.val h), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨A, hA⟩ := exists_map_galoisEmbedding_eq hk (g : Matrix m m K)
      ((mem_fixedSubgroup_slFrobenius_iff k g).mp hg)
    have hdet : A.det = 1 := by
      apply (galoisEmbedding p K k).injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, g.2, map_one]
    exact ⟨⟨A, hdet⟩, Subtype.ext (Subtype.ext hA)⟩

@[expose] noncomputable def fixedPointCandidateEquivPSL {k : ℕ} (hk : k ≠ 0)
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup m (GaloisField p k))]
    (hP : ¬ IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup m (GaloisField p k))) :
    TauCeti.FixedPointCandidate (slFrobenius (p := p) (m := m) K k) ≃*
      Matrix.ProjectiveSpecialLinearGroup m (GaloisField p k) :=
  let e := slFixedEquiv (m := m) (K := K) hk
  derivedCentralQuotientEquiv hP ((QuotientGroup.mk' _).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective) fun h hh => by
      have hc : e.symm h ∈ center _ := by
        rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hh
      simpa using GorensteinWalter.preambleCenter_mem_map e hc

end CFSG.BenderSuzuki.Catalog

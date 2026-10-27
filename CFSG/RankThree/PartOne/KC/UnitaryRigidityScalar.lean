module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityExact
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock

public section

namespace CFSG.RankThree.PartOne.KCUnitaryScalar

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryBlock

section Eigen

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem X_sub_C_mem_primaryFactors {x : Module.End K V} {μ : K} (hμ : x.HasEigenvalue μ) :
    (X - C μ : K[X]) ∈ primaryFactors x :=
  mem_primaryFactors.mpr ⟨irreducible_X_sub_C μ, monic_X_sub_C μ,
    dvd_iff_isRoot.mpr (Module.End.hasEigenvalue_iff_isRoot.mp hμ)⟩

omit [FiniteDimensional K V] in
theorem mem_primaryComponent_X_sub_C {x : Module.End K V} {μ : K} {v : V} :
    v ∈ primaryComponent x (X - C μ) ↔ x v = μ • v := by
  rw [mem_primaryComponent]
  simp [sub_eq_zero]

theorem primaryMultiplicity_X_sub_C (x : Module.End K V) (μ : K) :
    primaryMultiplicity x (X - C μ) = Module.finrank K (primaryComponent x (X - C μ)) := by
  have : Fact (Irreducible (X - C μ : K[X])) := ⟨irreducible_X_sub_C μ⟩
  have h := finrank_primaryComponent x (X - C μ)
  rw [natDegree_X_sub_C, one_mul] at h
  exact h.symm

end Eigen

section Good

variable {ℓ f : ℕ} {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {hK : UnitaryFieldData ℓ f K}

theorem isGoodBlock_X_sub_C {x : LinearMap.GeneralLinearGroup K V} {μ : K}
    (hmem : (X - C μ : K[X]) ∈ primaryFactors (x : Module.End K V))
    (hm : 2 ≤ Module.finrank K (primaryComponent (x : Module.End K V) (X - C μ)))
    (hexc : (Module.finrank K (primaryComponent (x : Module.End K V) (X - C μ)), ℓ ^ f) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) :
    IsGoodBlock hK x ⟨X - C μ, hmem⟩ := by
  rw [← primaryMultiplicity_X_sub_C] at hm hexc
  refine ⟨hm, fun _ => ?_⟩
  show (primaryMultiplicity (x : Module.End K V) (X - C μ),
    ℓ ^ (f * (X - C μ : K[X]).natDegree)) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))
  rw [natDegree_X_sub_C, mul_one]
  exact hexc

end Good

section Compare

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_of_eScalar {x : Module.End K V} {a : K[X]} [Fact (Irreducible a)]
    {Y : Module.End K V} {c : AdjoinRoot a}
    (hc : ∀ v : primaryComponent x a, Y (v : V) = ((c • v : primaryComponent x a) : V))
    {v w : V} (hv : v ∈ primaryComponent x a) (hw : w ∈ primaryComponent x a) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) {c₁ c₂ : K} (hYv : Y v = c₁ • v) (hYw : Y w = c₂ • w) : c₁ = c₂ := by
  have key : ∀ {u : V} (hu : u ∈ primaryComponent x a), u ≠ 0 → ∀ {d : K}, Y u = d • u →
      c = algebraMap K (AdjoinRoot a) d := by
    intro u hu hu0 d hYu
    have h1 := hc ⟨u, hu⟩
    rw [hYu, ← coe_algebraMap_smul_primaryComponent x a d ⟨u, hu⟩] at h1
    have h2 : (algebraMap K (AdjoinRoot a) d) • (⟨u, hu⟩ : primaryComponent x a) =
        c • ⟨u, hu⟩ := Subtype.ext h1
    have h3 : (c - algebraMap K (AdjoinRoot a) d) • (⟨u, hu⟩ : primaryComponent x a) = 0 := by
      rw [sub_smul, ← h2, sub_self]
    have h4 := (smul_eq_zero.mp h3).resolve_right (fun h => hu0 (congrArg Subtype.val h))
    exact sub_eq_zero.mp h4
  exact (algebraMap K (AdjoinRoot a)).injective ((key hv hv0 hYv).symm.trans (key hw hw0 hYw))

end Compare

section Plane

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem commute_toLinU {M x : primeFormUnitary h (idGram K n)} (hMx : M * x = x * M) :
    Commute (toLinU h n M) (toLinU h n x) := Commute.map (show Commute M x from hMx) (toLinU h n)

theorem exists_eScalar_of_commute_block (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) (a : GoodBlockIdx h x) (M : primeFormUnitary h (idGram K n))
    (hMx : M * liftUnitary x = liftUnitary x * M)
    (hblock : ∀ g ∈ idSpecialBlock h x (a.1 : K[X]), M * g = g * M) :
    ∃ c : AdjoinRoot (a.1 : K[X]), ∀ v : primaryComponent ((toLinU h n (liftUnitary x) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a.1 : K[X]),
      ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (v : Fin n → K) =
        ((c • v : primaryComponent ((toLinU h n (liftUnitary x) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
            (a.1 : K[X])) : Fin n → K) := by
  have hq2 := two_le_pow_of h
  have H := (S.planeData hx).primaryData
  have hY : toLinU h n M ∈ unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) :=
    (mem_centralizer_iff_toLinU x M).mp (Subgroup.mem_centralizer_singleton_iff.mpr hMx)
  refine (commute_specialBlock_iff_scalar H hq2 a.1 a.2 hY).mp fun g hg => ?_
  rw [← map_toLinU_idSpecialBlock] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
  exact commute_toLinU (hblock g₀ hg₀)

theorem exists_scalar_of_commute_block_X_sub_C (S : PlaneSetup h n p Ahat)
    {x : gramSU h (idGram K n)} (hx : x ∈ Ahat) {μ : K}
    (hmem : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (toLinU h n (liftUnitary x)) ⟨X - C μ, hmem⟩)
    (M : primeFormUnitary h (idGram K n)) (hMx : M * liftUnitary x = liftUnitary x * M)
    (hblock : ∀ g ∈ idSpecialBlock h x (X - C μ), M * g = g * M) :
    ∃ c : K, ∀ v : Fin n → K, ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v = μ • v →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  obtain ⟨c', hc'⟩ := exists_eScalar_of_commute_block S hx ⟨⟨X - C μ, hmem⟩, hgood⟩ M hMx hblock
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective c'
  refine ⟨r.eval μ, fun v hv => ?_⟩
  have hvmem : v ∈ primaryComponent ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C μ) :=
    mem_primaryComponent_X_sub_C.mpr hv
  have h1 := hc' ⟨v, hvmem⟩
  rw [coe_mk_smul_primaryComponent] at h1
  by_cases hv0 : v = 0
  · simp [hv0]
  have heig : Module.End.HasEigenvector ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) μ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector heig] at h1
  rw [← toLinU_apply_eq]
  exact h1

end Plane

end CFSG.RankThree.PartOne.KCUnitaryScalar

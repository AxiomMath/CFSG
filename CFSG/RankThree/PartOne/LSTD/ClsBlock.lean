module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem perfect_hom_eq_one {G A : Type*} [Group G] [CommGroup A] (hG : Group.IsPerfect G)
    (φ : G →* A) (g : G) : φ g = 1 := by
  have hφ : (⊤ : Subgroup G) ≤ φ.ker := by
    rw [← hG.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact MonoidHom.mem_ker.mp (hφ (Subgroup.mem_top g))

theorem submatrix_mul_of_vanish {k n : ℕ} {e : Fin k → Fin n} (he : Function.Injective e)
    {m m' : Matrix (Fin n) (Fin n) K} (hm : ∀ a j, j ∉ Set.range e → m (e a) j = 0) :
    (m * m').submatrix e e = m.submatrix e e * m'.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := e)
    (f := fun l => m (e a) l * m' l (e b)) (fun x _ y _ h => he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  rw [hm a l (fun ⟨c, hc⟩ => hl (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)), zero_mul]

theorem gram_submatrix {k n : ℕ} {e : Fin k → Fin n} (he : Function.Injective e) (σ : K →+* K)
    {m : Matrix (Fin n) (Fin n) K} (hcol : ∀ l a, l ∉ Set.range e → m l (e a) = 0)
    (hgram : (m.map σ)ᵀ * m = 1) :
    ((m.submatrix e e).map σ)ᵀ * m.submatrix e e = 1 := by
  ext a b
  have h1 := congrFun (congrFun hgram (e a)) (e b)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.one_apply] at h1 ⊢
  have hsum : ∑ c : Fin k, σ (m (e c) (e a)) * m (e c) (e b) =
      ∑ l, σ (m l (e a)) * m l (e b) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := e)
      (f := fun l => σ (m l (e a)) * m l (e b)) (fun x _ y _ h => he h)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    rw [hcol l a (fun ⟨c, hc⟩ => hl (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)), map_zero,
      zero_mul]
  rw [hsum, h1]
  simp [he.eq_iff]

section Block

variable {f : ℕ}

@[expose] noncomputable def blockHomSU {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (T : Subgroup ↥(unitarySU 2 f K n))
    (hT : ∀ h ∈ T, ∀ a j, j ∉ Set.range e →
      ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0) : ↥T →* GL (Fin k) K :=
  ({ toFun := fun h => ((h : ↥(unitarySU 2 f K n)) : GL (Fin n) K).val.submatrix e e
     map_one' := by
       show ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e = 1
       rw [Units.val_one]
       exact Matrix.submatrix_one e he
     map_mul' := fun h h' => by
       show ((h * h' : ↥(unitarySU 2 f K n)) : GL (Fin n) K).val.submatrix e e = _
       rw [Subgroup.coe_mul, Units.val_mul]
       exact submatrix_mul_of_vanish he (hT h h.2) } :
    ↥T →* Matrix (Fin k) (Fin k) K).toHomUnits

theorem blockHomSU_val {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (T : Subgroup ↥(unitarySU 2 f K n))
    (hT : ∀ h ∈ T, ∀ a j, j ∉ Set.range e →
      ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0) (h : ↥T) :
    ((blockHomSU e he T hT h : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      ((h : ↥(unitarySU 2 f K n)) : GL (Fin n) K).val.submatrix e e := rfl

theorem exists_block_hom (hU : UnitaryFieldData 2 f K) {k n : ℕ} (e : Fin k → Fin n)
    (he : Function.Injective e) (T : Subgroup ↥(unitarySU 2 f K n)) (hT : Group.IsPerfect ↥T)
    (hrow : ∀ h ∈ T, ∀ a j, j ∉ Set.range e →
      ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0)
    (hcol : ∀ h ∈ T, ∀ l a, l ∉ Set.range e →
      ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l (e a) = 0) :
    ∃ φ : ↥T →* ↥(unitarySU 2 f K k), ∀ h : ↥T,
      ((φ h : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        ((h : ↥(unitarySU 2 f K n)) : GL (Fin n) K).val.submatrix e e := by
  let β := blockHomSU e he T hrow
  have hdet : ∀ h : ↥T, Matrix.GeneralLinearGroup.det (β h) = 1 := fun h =>
    perfect_hom_eq_one hT (Matrix.GeneralLinearGroup.det.comp β) h
  have hmem : ∀ h : ↥T, β h ∈ unitarySU 2 f K k := by
    intro h
    rw [mem_unitarySU_iff hU]
    refine ⟨?_, ?_⟩
    · have := congrArg Units.val (hdet h)
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    · have hg := ((mem_unitarySU_iff hU).mp (h : ↥(unitarySU 2 f K n)).2).2
      rw [blockHomSU_val]
      exact gram_submatrix he hU.bar (fun l a hl => hcol h h.2 l a hl) hg
  exact ⟨β.codRestrict (unitarySU 2 f K k) hmem, fun h => rfl⟩

end Block

end CFSG.RankThree.PartOne.LSTD

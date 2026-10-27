module

public import CFSG.Quasithin.Background.FLcFlag
public import CFSG.LieType.SteinbergBRBinaryLinearSylow

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def slEquivGLt (n : ℕ) : SLt n ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

abbrev Ut (n : ℕ) : Subgroup (SLt n) := unitriangular n (ZMod 2)

abbrev QI (n : ℕ) (I : Set ℕ) : Subgroup (SLt n) := flagStabilizer n (ZMod 2) I

@[expose] def IsNode (n i : ℕ) : Prop := 1 ≤ i ∧ i < n

@[expose] def cuts {n : ℕ} (A : Subgroup (SLt n)) : Set ℕ := borelOvergroupCuts A

theorem upperTriangular_eq_Ut (n : ℕ) : upperTriangular n (ZMod 2) = Ut n :=
  CFSG.LieType.SteinbergBR.BinaryLinear.upperTriangular_eq_unitriangular (Nat.card_zmod 2)

theorem Ut_le_QI (n : ℕ) (I : Set ℕ) : Ut n ≤ QI n I := by
  rw [← upperTriangular_eq_Ut]
  exact upperTriangular_le_flagStabilizer I

theorem isNode_of_mem_cuts {n : ℕ} {A : Subgroup (SLt n)} {i : ℕ} (h : i ∈ cuts A) :
    IsNode n i := by
  obtain ⟨hi, hin, -⟩ := h
  exact ⟨hi, hin⟩

theorem eq_QI_cuts {n : ℕ} {A : Subgroup (SLt n)} (hA : Ut n ≤ A) : A = QI n (cuts A) := by
  rw [← upperTriangular_eq_Ut] at hA
  exact (borel_overgroups A hA).1

theorem cuts_QI {n : ℕ} {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i) : cuts (QI n I) = I := by
  have h := (borel_overgroups (QI n I) (by
    rw [upperTriangular_eq_Ut]
    exact Ut_le_QI n I)).2 I hI rfl
  exact h.symm

theorem reflection_mem_QI {n : ℕ} {I : Set ℕ} {i : ℕ} (hi : IsNode n i) :
    reflection n (ZMod 2) i hi.1 hi.2 ∈ QI n I ↔ i ∉ I :=
  (subflag_stabilizer_generation (K := ZMod 2) (n := n) I).2.2 i hi.1 hi.2

theorem QI_le_QI_iff {n : ℕ} {I J : Set ℕ} (hJ : ∀ j ∈ J, IsNode n j) :
    QI n I ≤ QI n J ↔ J ⊆ I := by
  constructor
  · intro h j hj
    by_contra hjI
    have hjn := hJ j hj
    have h1 : reflection n (ZMod 2) j hjn.1 hjn.2 ∈ QI n I := (reflection_mem_QI hjn).2 hjI
    have h2 := (reflection_mem_QI (I := J) hjn).1 (h h1)
    exact h2 hj
  · intro h g hg
    rw [mem_flagStabilizer] at hg ⊢
    exact fun j hj => hg j (h hj)

theorem le_iff_cuts {n : ℕ} {A A' : Subgroup (SLt n)} (hA : Ut n ≤ A) (hA' : Ut n ≤ A') :
    A ≤ A' ↔ cuts A' ⊆ cuts A := by
  have e1 := eq_QI_cuts hA
  have e2 := eq_QI_cuts hA'
  constructor
  · intro h
    rw [e1, e2] at h
    exact (QI_le_QI_iff fun j hj => isNode_of_mem_cuts hj).1 h
  · intro h
    rw [e1, e2]
    exact (QI_le_QI_iff fun j hj => isNode_of_mem_cuts hj).2 h

theorem eq_of_cuts_eq {n : ℕ} {A A' : Subgroup (SLt n)} (hA : Ut n ≤ A) (hA' : Ut n ≤ A')
    (h : cuts A = cuts A') : A = A' :=
  le_antisymm ((le_iff_cuts hA hA').2 h.ge) ((le_iff_cuts hA' hA).2 h.le)

theorem cuts_Ut {n : ℕ} : cuts (Ut n) = {i | IsNode n i} := by
  ext i
  constructor
  · exact isNode_of_mem_cuts
  · intro hi
    refine ⟨hi.1, hi.2, fun h => ?_⟩
    have h1 : reflection n (ZMod 2) i hi.1 hi.2 ∈ stabilizer (flagSpace n (ZMod 2) i) := by
      rw [← upperTriangular_eq_Ut] at h
      exact upperTriangular_le_stabilizer_flagSpace i h
    exact reflection_notMem_stabilizer hi.1 hi.2 h1

theorem Ut_eq_QI {n : ℕ} : Ut n = QI n {i | IsNode n i} := by
  have := eq_QI_cuts (le_refl (Ut n))
  rwa [cuts_Ut] at this

end CFSG.Quasithin.FLc

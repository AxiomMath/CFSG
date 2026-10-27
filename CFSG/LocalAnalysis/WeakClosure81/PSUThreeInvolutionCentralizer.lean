module

public import CFSG.LocalAnalysis.WeakClosure81.RankTwoCentralizerFrame
public import CFSG.LocalAnalysis.WeakClosure81.RankTwoScalarQuotient
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Quasithin CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem nParam_centralizer_le_one_of_psu3
    {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hf : 3 ≤ f)
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  classical
  letI : Fact p.Prime := ⟨h.prime⟩
  letI : CharP K p := h.charP
  haveI : Finite K := h.finite
  let F : Type := LieType.Steinberg.fixedSubfield K p f
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  obtain ⟨eSl⟩ := CFSG.ClassicalInvolution.Q3.TA3.Q5U3.nonempty_slPart_equiv h
  have hFcard : Nat.card F = p ^ f :=
    LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := f) h.card_eq_sq
  obtain ⟨π, hπrange, hCube, hπN1⟩ :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5U3.exists_frame (p := p) (f := f) (K := K) h hp2 (Y := G) (N := L)
      (e := e) (t := z) hzL hz2
  let N1 : GU2Stated (p ^ f) K := ⟨-1, CFSG.ClassicalInvolution.Q3.TA3.Q5U3.neg_one_mem_GU2 h⟩
  have hN1 : (N1 : GL (Fin 2) K) = -1 := rfl
  have hπN1' : π N1 = z := hπN1
  have hSquare : ∀ A : GU2Stated (p ^ f) K,
      A * A ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart (GU2Stated (p ^ f) K) ⊔
        Subgroup.center (GU2Stated (p ^ f) K) :=
    gu2Stated_sq_mem_slPart_sup_center h
  exact nParam_centralizer_le_one_of_rankTwoFrame_narrow (G := G) (L := L) hAS
    (K := K) (U := GU2Stated (p ^ f) K) π hπrange hCube
    (F := F) eSl (p := p) (f := f) h.prime hp2 hf hFcard
    (CFSG.ClassicalInvolution.Q3.TA3.Q5U3.slCentScalar_GU2 h) N1 hN1 hπN1' hSquare

theorem nParam_centralizer_le_one_of_psu3_of_five_lt
    {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  classical
  letI : Fact p.Prime := ⟨h.prime⟩
  letI : CharP K p := h.charP
  haveI : Finite K := h.finite
  let F : Type := LieType.Steinberg.fixedSubfield K p f
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  obtain ⟨eSl⟩ := CFSG.ClassicalInvolution.Q3.TA3.Q5U3.nonempty_slPart_equiv h
  have hFcard : Nat.card F = p ^ f :=
    LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := f) h.card_eq_sq
  obtain ⟨π, hπrange, hCube, hπN1⟩ :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5U3.exists_frame (p := p) (f := f) (K := K) h hp2
      (Y := G) (N := L) (e := e) (t := z) hzL hz2
  let N1 : GU2Stated (p ^ f) K :=
    ⟨-1, CFSG.ClassicalInvolution.Q3.TA3.Q5U3.neg_one_mem_GU2 h⟩
  have hN1 : (N1 : GL (Fin 2) K) = -1 := rfl
  have hπN1' : π N1 = z := hπN1
  have hSquare : ∀ A : GU2Stated (p ^ f) K,
      A * A ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart (GU2Stated (p ^ f) K) ⊔
        Subgroup.center (GU2Stated (p ^ f) K) :=
    gu2Stated_sq_mem_slPart_sup_center h
  exact nParam_centralizer_le_one_of_rankTwoFrame_of_five_lt (G := G) (L := L) hAS
    (K := K) (U := GU2Stated (p ^ f) K) π hπrange hCube
    (F := F) eSl (p := p) (f := f) h.prime hp2 h5 hFcard
    (CFSG.ClassicalInvolution.Q3.TA3.Q5U3.slCentScalar_GU2 h) N1 hN1 hπN1' hSquare

end CFSG.LocalAnalysis.WeakClosure81

end

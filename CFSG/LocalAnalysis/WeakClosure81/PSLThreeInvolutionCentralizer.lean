module

public import CFSG.LocalAnalysis.WeakClosure81.RankTwoCentralizerFrame
public import CFSG.LocalAnalysis.WeakClosure81.RankTwoScalarQuotient
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Frame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Quasithin CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem nParam_centralizer_le_one_of_psl3
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hcardK : Nat.card K = p ^ f)
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (e : L ≃* projectiveSL 3 K) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  classical
  have hodd : Odd (Nat.card K) := by
    rw [hcardK]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨Q, π, hπrange, hCube, hπN1, -⟩ :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5L3.exists_frame (K := K) hodd
      (Y := G) (N := L) (e := e) (t := z) hzL hz2
  let U : Subgroup (GL (Fin 2) K) := ⊤
  let N1 : U := ⟨-1, Subgroup.mem_top _⟩
  have hN1 : (N1 : GL (Fin 2) K) = -1 := rfl
  have hπN1' : π N1 = z := hπN1
  have hSquare : ∀ A : U,
      A * A ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔ Subgroup.center U := by
    intro A
    exact sq_mem_slPart_sup_center (H := U) (fun B => Subgroup.mem_top _) A
  exact nParam_centralizer_le_one_of_rankTwoFrame_narrow (G := G) (L := L) hAS
    (K := K) (U := U) π hπrange hCube
    (F := K) (ClassicalInvolution.Q3.TA3.Q5L3.slPartTopEquiv)
    (p := p) (f := f) hp hp2 hf hcardK
    (ClassicalInvolution.Q3.TA3.Q5L3.slCentScalar_top) N1 hN1 hπN1' hSquare

theorem nParam_centralizer_le_one_of_psl3_of_five_lt
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (hcardK : Nat.card K = p ^ f)
    {L : Subgroup G} (hAS : Vol2.Ch11.SecE3.AlmostSimple L)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (e : L ≃* projectiveSL 3 K) :
    E1.nParam (Subgroup.centralizer ({z} : Set G)) ≤ 1 := by
  classical
  have hodd : Odd (Nat.card K) := by
    rw [hcardK]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨Q, π, hπrange, hCube, hπN1, -⟩ :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5L3.exists_frame (K := K) hodd
      (Y := G) (N := L) (e := e) (t := z) hzL hz2
  let U : Subgroup (GL (Fin 2) K) := ⊤
  let N1 : U := ⟨-1, Subgroup.mem_top _⟩
  have hN1 : (N1 : GL (Fin 2) K) = -1 := rfl
  have hπN1' : π N1 = z := hπN1
  have hSquare : ∀ A : U,
      A * A ∈ ClassicalInvolution.Q3.TA3.Q5GL2.slPart U ⊔ Subgroup.center U := by
    intro A
    exact sq_mem_slPart_sup_center (H := U) (fun B => Subgroup.mem_top _) A
  exact nParam_centralizer_le_one_of_rankTwoFrame_of_five_lt (G := G) (L := L) hAS
    (K := K) (U := U) π hπrange hCube
    (F := K) (ClassicalInvolution.Q3.TA3.Q5L3.slPartTopEquiv)
    (p := p) (f := f) hp hp2 h5 hcardK
    (ClassicalInvolution.Q3.TA3.Q5L3.slCentScalar_top) N1 hN1 hπN1' hSquare

end CFSG.LocalAnalysis.WeakClosure81

end

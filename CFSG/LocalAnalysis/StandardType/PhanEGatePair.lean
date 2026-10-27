module

public import CFSG.LocalAnalysis.StandardType.PhanEGateDouble
public import CFSG.LocalAnalysis.StandardType.PhanEDMCoxeter
public import CFSG.Monster.B.Geometry.InitialIsometryProduct

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W}

@[expose] def IsClosestPair (cs : CoxeterSystem M W) (δ : C → C → W) (J K : Set ι) (a b x y : C) :
    Prop :=
  x ∈ residue cs δ J a ∧ y ∈ residue cs δ K b ∧
    ∀ x' ∈ residue cs δ J a, ∀ y' ∈ residue cs δ K b, cs.length (δ x y) ≤ cs.length (δ x' y')

@[expose] def projSet (cs : CoxeterSystem M W) (δ : C → C → W) (J : Set ι) (a : C) (S : Set C) :
    Set C :=
  resProj cs δ J a '' S

variable {J K : Set ι} {a b x y x' y' : C}

theorem exists_isClosestPair (cs : CoxeterSystem M W) (δ : C → C → W) (J K : Set ι) (a b : C) :
    ∃ x y, IsClosestPair cs δ J K a b x y := by
  classical
  have hex : ∃ n, ∃ x ∈ residue cs δ J a, ∃ y ∈ residue cs δ K b, cs.length (δ x y) = n :=
    ⟨_, a, self_mem_residue J a, b, self_mem_residue K b, rfl⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Nat.find_spec hex
  refine ⟨x, y, hx, hy, fun x' hx' y' hy' => ?_⟩
  rw [hxy]
  exact Nat.find_min' hex ⟨x', hx', y', hy', rfl⟩

theorem IsClosestPair.symm (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) : IsClosestPair cs δ K J b a y x := by
  refine ⟨h.2.1, h.1, fun y' hy' x' hx' => ?_⟩
  calc cs.length (δ y x) = cs.length (δ x y) := by rw [dist_inv hB x y, cs.length_inv]
    _ ≤ cs.length (δ x' y') := h.2.2 x' hx' y' hy'
    _ = cs.length (δ y' x') := by rw [dist_inv hB x' y', cs.length_inv]

theorem IsClosestPair.isMinimalDoubleCosetRep (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) : cs.IsMinimalDoubleCosetRep J K (δ x y) := by
  intro a' ha' b' hb'
  obtain ⟨x', hx'x, hx'y⟩ := exists_mem_residue_dist_eq_mul_left hB x y ha'
  obtain ⟨y', hy'y, hx'y'⟩ := exists_mem_residue_dist_eq_mul hB x' y hb'
  have hx'a : x' ∈ residue cs δ J a := by
    rw [← residue_eq_of_mem hB h.1]
    exact hx'x
  have hy'b : y' ∈ residue cs δ K b := by
    rw [← residue_eq_of_mem hB h.2.1]
    exact hy'y
  have hle := h.2.2 x' hx'a y' hy'b
  rw [hx'y', hx'y] at hle
  exact hle

theorem IsClosestPair.dist_eq (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) (h' : IsClosestPair cs δ J K a b x' y') :
    δ x y = δ x' y' := by
  obtain ⟨u, hu, v, hv, huv⟩ :=
    DoubleCoset.mem_doubleCoset.mp (dist_mem_doubleCoset hB h.1 h.2.1)
  obtain ⟨u', hu', v', hv', hu'v'⟩ :=
    DoubleCoset.mem_doubleCoset.mp (dist_mem_doubleCoset hB h'.1 h'.2.1)
  have hmin := IsClosestPair.isMinimalDoubleCosetRep hB h
  have hmin' := IsClosestPair.isMinimalDoubleCosetRep hB h'
  have key : δ x' y' = (u' * u⁻¹) * δ x y * (v⁻¹ * v') := by
    rw [hu'v', huv]
    group
  exact (CoxeterSystem.IsMinimalDoubleCosetRep.eq_of_eq_mul_mul hmin hmin'
    (mul_mem hu' (inv_mem hu)) (mul_mem (inv_mem hv) hv') key).symm

theorem IsClosestPair.eq_resProj_left (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) : resProj cs δ J a y = x := by
  have hle : ∀ q ∈ residue cs δ J x, cs.length (δ y x) ≤ cs.length (δ y q) := by
    intro q hq
    have hq' : q ∈ residue cs δ J a := by
      rw [← residue_eq_of_mem hB h.1]
      exact hq
    calc cs.length (δ y x) = cs.length (δ x y) := by rw [dist_inv hB x y, cs.length_inv]
      _ ≤ cs.length (δ q y) := h.2.2 q hq' y h.2.1
      _ = cs.length (δ y q) := by rw [dist_inv hB y q, cs.length_inv]
  have hmin := isMinimalCosetRep_of_forall_le hB (self_mem_residue J x) hle
  have hgate : ∀ q ∈ residue cs δ J x, cs.length (δ y q) = cs.length (δ y x) + cs.length (δ x q) :=
    fun q hq => (gate_of_isMinimalCosetRep hB (self_mem_residue J x) hmin hq).2
  have hp : IsProjection cs δ (residue cs δ J x) y x :=
    isProjection_of_gate hB (self_mem_residue J x) hgate
  rw [residue_eq_of_mem hB h.1] at hp
  exact resProj_eq hB hp

theorem IsClosestPair.eq_resProj_right (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) : resProj cs δ K b x = y :=
  IsClosestPair.eq_resProj_left hB (IsClosestPair.symm hB h)

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end

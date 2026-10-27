module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalElt
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.Quasithin.H13

abbrev V6 : Type := Fin 6 → ZMod 2

@[expose] def X0 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 1, 0]

@[expose] def S0 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem isoMat_X0 : IsoMat X0 := by
  unfold IsoMat X0
  decide +kernel

theorem isoMat_S0 : IsoMat S0 := by
  unfold IsoMat S0
  decide +kernel

@[expose] def x0 : H6 := ofIso X0 isoMat_X0

@[expose] def s0 : H6 := ofIso S0 isoMat_S0

theorem mat6_x0 : mat6 x0 = X0 := mat6_ofIso X0 isoMat_X0

theorem mat6_s0 : mat6 s0 = S0 := mat6_ofIso S0 isoMat_S0

theorem X0_pow_five : X0 ^ 5 = 1 := by
  unfold X0
  decide +kernel

theorem X0_ne_one : X0 ≠ 1 := by
  unfold X0
  decide +kernel

theorem S0_pow_three : S0 ^ 3 = 1 := by
  unfold S0
  decide +kernel

theorem x0_pow_five : x0 ^ 5 = 1 := by
  apply mat6_injective
  rw [map_pow, mat6_x0, X0_pow_five, map_one]

theorem x0_ne_one : x0 ≠ 1 := by
  intro h
  apply X0_ne_one
  rw [← mat6_x0, h, map_one]

theorem s0_pow_three : s0 ^ 3 = 1 := by
  apply mat6_injective
  rw [map_pow, mat6_s0, S0_pow_three, map_one]

theorem orderOf_x0 : orderOf x0 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime x0_pow_five x0_ne_one

@[expose] def Fmat (a0 a1 a3 : V6) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => ![a0, a1, X0.mulVec a1, a3, X0.mulVec (X0.mulVec a1),
    X0.mulVec (X0.mulVec (X0.mulVec a1)) + X0.mulVec (X0.mulVec a1)] j i

set_option maxRecDepth 100000 in
theorem fmat_cases : ∀ a0 : V6, X0.mulVec a0 = a0 → ∀ a3 : V6, X0.mulVec a3 = a3 → ∀ a1 : V6,
    IsoMat (Fmat a0 a1 a3) → Fmat a0 a1 a3 ^ 3 = 1 →
      Fmat a0 a1 a3 = 1 ∨ Fmat a0 a1 a3 = S0 ∨ Fmat a0 a1 a3 = S0 * S0 := by
  unfold Fmat X0 S0 IsoMat
  decide +kernel

theorem X0_single_zero : X0.mulVec (Pi.single 0 1) = (Pi.single 0 1 : V6) := by
  unfold X0
  decide +kernel

theorem X0_single_three : X0.mulVec (Pi.single 3 1) = (Pi.single 3 1 : V6) := by
  unfold X0
  decide +kernel

theorem X0_single_one : X0.mulVec (Pi.single 1 1) = (Pi.single 2 1 : V6) := by
  unfold X0
  decide +kernel

theorem X0_single_two : X0.mulVec (Pi.single 2 1) = (Pi.single 4 1 : V6) := by
  unfold X0
  decide +kernel

theorem X0_single_four :
    X0.mulVec (Pi.single 4 1) = (Pi.single 4 1 + Pi.single 5 1 : V6) := by
  unfold X0
  decide +kernel

theorem mulVec_comm_of_comm {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : M * X0 = X0 * M)
    (v : V6) : M.mulVec (X0.mulVec v) = X0.mulVec (M.mulVec v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem eq_fmat_of_comm {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : M * X0 = X0 * M) :
    M = Fmat (fun i => M i 0) (fun i => M i 1) (fun i => M i 3) := by
  have hv := mulVec_comm_of_comm hM
  have hc : ∀ j : Fin 6, M.mulVec (Pi.single j 1) = fun i => M i j :=
    fun j => Matrix.mulVec_single_one M j
  have c2 : (fun i => M i 2) = X0.mulVec (fun i => M i 1) := by
    rw [← hc, ← hc, ← X0_single_one, hv]
  have c4 : (fun i => M i 4) = X0.mulVec (fun i => M i 2) := by
    rw [← hc, ← hc, ← X0_single_two, hv]
  have c5 : (fun i => M i 5) = X0.mulVec (fun i => M i 4) + fun i => M i 4 := by
    have h := hv (Pi.single 4 1)
    rw [X0_single_four, Matrix.mulVec_add, hc, hc] at h
    funext i
    have h' := congrFun h i
    have key : ∀ a b c : ZMod 2, a + b = c → b = c + a := by decide
    exact key _ _ _ h'
  ext i j
  fin_cases j
  · rfl
  · rfl
  · exact congrFun c2 i
  · rfl
  · show M i 4 = X0.mulVec (X0.mulVec (fun i => M i 1)) i
    rw [← c2]
    exact congrFun c4 i
  · show M i 5 = (X0.mulVec (X0.mulVec (X0.mulVec (fun i => M i 1))) +
      X0.mulVec (X0.mulVec (fun i => M i 1))) i
    rw [← c2, ← c4]
    exact congrFun c5 i

theorem eq_one_or_s0_of_comm {g : H6} (hg : g * x0 = x0 * g) (h3 : g ^ 3 = 1) :
    g = 1 ∨ g = s0 ∨ g = s0 * s0 := by
  set M := mat6 g with hMdef
  have hM : M * X0 = X0 * M := by
    rw [hMdef, ← mat6_x0, ← map_mul, ← map_mul, hg]
  have hF := eq_fmat_of_comm hM
  have hv := mulVec_comm_of_comm hM
  have hc : ∀ j : Fin 6, M.mulVec (Pi.single j 1) = fun i => M i j :=
    fun j => Matrix.mulVec_single_one M j
  have ha0 : X0.mulVec (fun i => M i 0) = fun i => M i 0 := by
    rw [← hc, ← hv, X0_single_zero]
  have ha3 : X0.mulVec (fun i => M i 3) = fun i => M i 3 := by
    rw [← hc, ← hv, X0_single_three]
  have hIso' : IsoMat (Fmat (fun i => M i 0) (fun i => M i 1) (fun i => M i 3)) := by
    rw [← hF]
    exact mat6_isIso g
  have hM3 : (Fmat (fun i => M i 0) (fun i => M i 1) (fun i => M i 3)) ^ 3 = 1 := by
    rw [← hF, hMdef, ← map_pow, h3, map_one]
  rcases fmat_cases _ ha0 _ ha3 _ hIso' hM3 with h | h | h
  · left
    apply mat6_injective
    rw [map_one, ← h, ← hF]
  · right; left
    apply mat6_injective
    rw [mat6_s0, ← h, ← hF]
  · right; right
    apply mat6_injective
    rw [map_mul, mat6_s0, ← h, ← hF]

@[expose] def act6 : H6 →* Equiv.Perm V6 where
  toFun g :=
    { toFun := fun y => (mat6 g).mulVec y
      invFun := fun y => (mat6 g⁻¹).mulVec y
      left_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      right_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] }
  map_one' := by
    ext y
    simp
  map_mul' g h := by
    ext y
    simp [Matrix.mulVec_mulVec]

theorem act6_apply (g : H6) (y : V6) : act6 g y = (mat6 g).mulVec y :=
  rfl

@[expose] def D6 : Set V6 := {v | v 1 = 0 ∧ v 2 = 0 ∧ v 4 = 0 ∧ v 5 = 0}

theorem card_D6 : Nat.card D6 = 4 := by
  have : D6 = ↑(Finset.univ.filter fun v : V6 => v 1 = 0 ∧ v 2 = 0 ∧ v 4 = 0 ∧ v 5 = 0) := by
    ext v
    simp [D6]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide +kernel

theorem exists_S0_sub_eq : ∀ y : V6, y ∈ D6 → ∃ u : V6, S0.mulVec u + u = y := by
  unfold D6 S0
  decide +kernel

theorem S0_sub_mem : ∀ u : V6, S0.mulVec u + u ∈ D6 := by
  unfold D6 S0
  decide +kernel

theorem single_zero_mem : (Pi.single 0 1 : V6) ∈ D6 := by
  unfold D6
  decide +kernel

theorem single_three_mem : (Pi.single 3 1 : V6) ∈ D6 := by
  unfold D6
  decide +kernel

theorem fixes_D_of_perfect {P : Subgroup H6} (hP : Group.IsPerfect P)
    (hC : P ≤ Subgroup.centralizer ({s0} : Set H6)) :
    ∀ p ∈ P, act6 p (Pi.single 0 1) = Pi.single 0 1 ∧ act6 p (Pi.single 3 1) = Pi.single 3 1 := by
  have hY : Nat.card D6 ≤ 4 := card_D6.le
  have hinv : ∀ p ∈ P, ∀ y ∈ D6, act6 p y ∈ D6 := by
    intro p hp y hy
    obtain ⟨u, rfl⟩ := exists_S0_sub_eq y hy
    have hcomm : (mat6 p).mulVec (S0.mulVec u) = S0.mulVec ((mat6 p).mulVec u) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hC hp)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat6_s0, ← map_mul, ← map_mul, this]
    rw [act6_apply, Matrix.mulVec_add, hcomm]
    exact S0_sub_mem _
  have hfix := CFSG.RankThree.PartTwo.Sec8.Item8KFacts3.fixes_of_isPerfect act6 hP hY hinv
  exact fun p hp => ⟨hfix p hp _ single_zero_mem, hfix p hp _ single_three_mem⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611R

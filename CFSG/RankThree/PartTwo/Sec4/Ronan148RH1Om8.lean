module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L67
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.RankThree.PartTwo.Sec4.Ronan148L (E27Move)
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt baseA wreathW WreathFacts)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8 (ι Q8)
open CFSG.Open (StatedOmega StatedQuadMinus)
open Matrix
open scoped commutatorElement

namespace Om8Data

@[expose] def idx8 : ι → Fin 8
  | Sum.inl a => ⟨a.1, by omega⟩
  | Sum.inr (Sum.inl a) => ⟨3 + a.1, by omega⟩
  | Sum.inr (Sum.inr a) => ⟨6 + a.1, by omega⟩

@[expose] def toι (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  M.submatrix idx8 idx8

@[expose] def om8S0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S0i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S1i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def om8S2i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def om8R0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8R0i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8R1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8R1i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8R2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def om8R2i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def om8S12 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S12i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def om8S13 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 1, 0, 1, 1;
    1, 1, 0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 1, 0;
    1, 0, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 1, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def om8S13i : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 1, 0, 1, 1;
    1, 1, 0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 1, 0;
    1, 0, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 1, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def om8G : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 1;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 1, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 1]

@[expose] def om8Gi : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 1, 0, 0, 0, 1, 0]

theorem om8S0_mul : toι om8S0 * toι om8S0i = 1 := by decide +kernel
theorem om8S0_mul' : toι om8S0i * toι om8S0 = 1 := by decide +kernel
theorem om8S0_iso : ∀ v : ι → ZMod 2, Q8 (toι om8S0 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gS0 : GL ι (ZMod 2) := Units.mk (toι om8S0) (toι om8S0i) om8S0_mul om8S0_mul'
theorem gS0_mem : gS0 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8S0_iso v
theorem om8S1_mul : toι om8S1 * toι om8S1i = 1 := by decide +kernel
theorem om8S1_mul' : toι om8S1i * toι om8S1 = 1 := by decide +kernel
theorem om8S1_iso : ∀ v : ι → ZMod 2, Q8 (toι om8S1 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gS1 : GL ι (ZMod 2) := Units.mk (toι om8S1) (toι om8S1i) om8S1_mul om8S1_mul'
theorem gS1_mem : gS1 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8S1_iso v
theorem om8S2_mul : toι om8S2 * toι om8S2i = 1 := by decide +kernel
theorem om8S2_mul' : toι om8S2i * toι om8S2 = 1 := by decide +kernel
theorem om8S2_iso : ∀ v : ι → ZMod 2, Q8 (toι om8S2 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gS2 : GL ι (ZMod 2) := Units.mk (toι om8S2) (toι om8S2i) om8S2_mul om8S2_mul'
theorem gS2_mem : gS2 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8S2_iso v
theorem om8R0_mul : toι om8R0 * toι om8R0i = 1 := by decide +kernel
theorem om8R0_mul' : toι om8R0i * toι om8R0 = 1 := by decide +kernel
theorem om8R0_iso : ∀ v : ι → ZMod 2, Q8 (toι om8R0 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gR0 : GL ι (ZMod 2) := Units.mk (toι om8R0) (toι om8R0i) om8R0_mul om8R0_mul'
theorem gR0_mem : gR0 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8R0_iso v
theorem om8R1_mul : toι om8R1 * toι om8R1i = 1 := by decide +kernel
theorem om8R1_mul' : toι om8R1i * toι om8R1 = 1 := by decide +kernel
theorem om8R1_iso : ∀ v : ι → ZMod 2, Q8 (toι om8R1 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gR1 : GL ι (ZMod 2) := Units.mk (toι om8R1) (toι om8R1i) om8R1_mul om8R1_mul'
theorem gR1_mem : gR1 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8R1_iso v
theorem om8R2_mul : toι om8R2 * toι om8R2i = 1 := by decide +kernel
theorem om8R2_mul' : toι om8R2i * toι om8R2 = 1 := by decide +kernel
theorem om8R2_iso : ∀ v : ι → ZMod 2, Q8 (toι om8R2 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gR2 : GL ι (ZMod 2) := Units.mk (toι om8R2) (toι om8R2i) om8R2_mul om8R2_mul'
theorem gR2_mem : gR2 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8R2_iso v
theorem om8S12_mul : toι om8S12 * toι om8S12i = 1 := by decide +kernel
theorem om8S12_mul' : toι om8S12i * toι om8S12 = 1 := by decide +kernel
theorem om8S12_iso : ∀ v : ι → ZMod 2, Q8 (toι om8S12 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gS12 : GL ι (ZMod 2) := Units.mk (toι om8S12) (toι om8S12i) om8S12_mul om8S12_mul'
theorem gS12_mem : gS12 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8S12_iso v
theorem om8S13_mul : toι om8S13 * toι om8S13i = 1 := by decide +kernel
theorem om8S13_mul' : toι om8S13i * toι om8S13 = 1 := by decide +kernel
theorem om8S13_iso : ∀ v : ι → ZMod 2, Q8 (toι om8S13 *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gS13 : GL ι (ZMod 2) := Units.mk (toι om8S13) (toι om8S13i) om8S13_mul om8S13_mul'
theorem gS13_mem : gS13 ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8S13_iso v
theorem om8G_mul : toι om8G * toι om8Gi = 1 := by decide +kernel
theorem om8G_mul' : toι om8Gi * toι om8G = 1 := by decide +kernel
theorem om8G_iso : ∀ v : ι → ZMod 2, Q8 (toι om8G *ᵥ v) = Q8 v := by decide +kernel
@[expose] def gG : GL ι (ZMod 2) := Units.mk (toι om8G) (toι om8Gi) om8G_mul om8G_mul'
theorem gG_mem : gG ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => om8G_iso v

@[expose] def T : Fin 3 → Om8 := ![
  ⟨⁅gS0, gR0⁆, Subgroup.commutator_mem_commutator gS0_mem gR0_mem⟩,
  ⟨⁅gS1, gR1⁆, Subgroup.commutator_mem_commutator gS1_mem gR1_mem⟩,
  ⟨⁅gS2, gR2⁆, Subgroup.commutator_mem_commutator gS2_mem gR2_mem⟩]

@[expose] def tw : Om8 := ⟨⁅gS12, gS13⁆, Subgroup.commutator_mem_commutator gS12_mem gS13_mem⟩

@[expose] def eps : Om8 := ⟨⁅gS0, gS12⁆, Subgroup.commutator_mem_commutator gS0_mem gS12_mem⟩

@[expose] def tinv : Om8 := ⟨⁅gS2, gG⁆, Subgroup.commutator_mem_commutator gS2_mem gG_mem⟩

theorem pow_T : ∀ i, T i ^ 3 = 1 := by decide +kernel

theorem comm_T : ∀ i j, T i * T j = T j * T i := by decide +kernel

theorem inj_T : ∀ v : Fin 3 → ZMod 3, vecElt T v = 1 → v = 0 := by decide +kernel

theorem pow_tw : tw ^ 3 = 1 := by decide +kernel

theorem conj_T : tw * T 0 = T 1 * tw ∧ tw * T 1 = T 2 * tw ∧ tw * T 2 = T 0 * tw := by
  decide +kernel

theorem t_ne_T : ∀ v : Fin 3 → ZMod 3, vecElt T v ≠ tw := by decide +kernel

theorem wreathFacts : WreathFacts T tw where
  pow_z := pow_T
  comm_z := comm_T
  inj := inj_T
  pow_t := pow_tw
  conj0 := by rw [conj_T.1, mul_inv_cancel_right]
  conj1 := by rw [conj_T.2.1, mul_inv_cancel_right]
  conj2 := by rw [conj_T.2.2, mul_inv_cancel_right]
  t_ne := t_ne_T

theorem epsConj : ∀ j : Fin 3, ∃ w, eps * T j = vecElt T w * eps := by decide +kernel

set_option synthInstance.maxSize 2048 in
theorem moverCheck : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    (tw * vecElt T v ≠ vecElt T v * tw ∧ tw * vecElt T v ≠ vecElt T v ^ 2 * tw) ∨
    (eps * vecElt T v ≠ vecElt T v * eps ∧ eps * vecElt T v ≠ vecElt T v ^ 2 * eps) := by
  decide +kernel

theorem tinv_facts : tinv ≠ 1 ∧ tinv ^ 2 = 1 ∧ tinv * T 0 = T 0 * tinv ∧
    tinv * T 1 = T 1 * tinv := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Om8Data

open Om8Data

theorem gf2_hbc : ∀ s : GaloisField 2 1, s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro s
  rcases RonanK429F.gf2_eq_zero_or_one s with rfl | rfl
  · simp
  · rw [one_pow, one_mul, RonanK429F.gf2_one_add_one, zero_add]
    exact one_ne_zero

theorem card_om8 : Nat.card Om8 = 197406720 := RonanK429F.Om8.card_Om8 gf2_hbc

instance : Finite Om8 := Nat.finite_of_card_ne_zero (by rw [card_om8]; norm_num)

theorem factorization_card_om8 : (Nat.card Om8).factorization 3 = 4 := by
  rw [card_om8, show (197406720 : ℕ) = 3 ^ 4 * 2437120 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW_om8 : Nat.card (wreathW T tw) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (Item434Kit.isPGroup_wreathW wreathFacts)
  rw [factorization_card_om8] at hle
  have := Item434Kit.le_card_wreathW wreathFacts
  norm_num at hle
  omega

theorem e27Move_om8 : E27Move Om8 := by
  refine e27Move_of_wreath wreathFacts card_wreathW_om8 factorization_card_om8 fun v hv => ?_
  obtain ⟨n, hnN, h1, h2⟩ : ∃ n ∈ Subgroup.normalizer (baseA T : Set Om8),
      n * vecElt T v ≠ vecElt T v * n ∧ n * vecElt T v ≠ vecElt T v ^ 2 * n := by
    rcases moverCheck v hv with h | h
    · exact ⟨tw, Item434Kit.t_mem_normalizer wreathFacts, h⟩
    · refine ⟨eps, mem_normalizer_baseA fun i => ?_, h⟩
      obtain ⟨w, hw⟩ := epsConj i
      rw [hw, mul_inv_cancel_right]
      exact Item434Kit.vecElt_mem_baseA wreathFacts w
  refine ⟨n, hnN, not_mem_normalizer_of_conj ?_⟩
  have hx3 : vecElt T v ^ 3 = 1 :=
    (Item434Kit.isElemAbelian_baseA wreathFacts).2 _ (Item434Kit.vecElt_mem_baseA wreathFacts v)
  have hx1 : vecElt T v ≠ 1 := fun h => hv (Item434Kit.vecElt_injective wreathFacts
    (h.trans vecElt_zero.symm))
  refine not_mem_zpowers_of_ne hx3 ?_ ?_ ?_
  · intro h
    apply hx1
    have h' : n * vecElt T v = 1 * n := by
      calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
        _ = 1 * n := by rw [h]
    simpa using h'
  · intro h
    apply h1
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = vecElt T v * n := by rw [h]
  · intro h
    apply h2
    have hinv : (vecElt T v)⁻¹ = vecElt T v ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hx3
    calc n * vecElt T v = (n * vecElt T v * n⁻¹) * n := by group
      _ = (vecElt T v)⁻¹ * n := by rw [h]
      _ = vecElt T v ^ 2 * n := by rw [hinv]

theorem cubeInner_om8 : CubeInner Om8 := by
  obtain ⟨φ⟩ := RonanK429F.nonempty_projOmegaMinus_equiv_om8 gf2_hbc
  haveI : Finite (projOmegaMinus 3 (GaloisField 2 1) 1 1) := Finite.of_equiv _ φ.symm.toEquiv
  exact cubeInner_of_mulEquiv φ.symm (cubeInner_of_not_three_dvd_card_outer
    (RonanK429F.Om8.not_three_dvd_card_outer_projOmegaMinus gf2_hbc))

theorem rankThree_om8 : RankThreeData Om8 :=
  rankThreeData_of_wreath wreathFacts cubeInner_om8 tinv_facts.1 tinv_facts.2.1 tinv_facts.2.2.1
    tinv_facts.2.2.2

theorem om8_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 197406720 →
      197406720 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 197406720 →
      197406720 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 15) (by norm_num) (by decide +kernel)

section Row

theorem rowOf427_om8
    : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOf427 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc
  obtain ⟨φ⟩ := RonanK429F.nonempty_projOmegaMinus_equiv_om8 hbc
  have hcard : Nat.card (projOmegaMinus 3 (GaloisField 2 1) b c) = 197406720 := by
    rw [Nat.card_congr φ.toEquiv, card_om8]
  refine rowOf427_of_e27Move_model φ ?_ rankThree_om8 e27Move_om8
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    om8_orderChecks.1 om8_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end

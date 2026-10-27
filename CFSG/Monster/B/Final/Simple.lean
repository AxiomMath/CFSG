module

public import CFSG.Monster.B.Final.Assembly
public import CFSG.Monster.B.Dyadic.A0
public import CFSG.Monster.B.Gen.PacketGeneration
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.B.Dyadic.BetaFacts
public import CFSG.Monster.B.Dyadic.BinElim
public import CFSG.Monster.B.Dyadic.Jordan
public import CFSG.Monster.B.Rep4371.SmallFaithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint CFSG.Monster.B.Rep4371

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def conjWord0 : List ℕ := conjWord24.map (· - 1)

theorem conjWord0_lt : ∀ j ∈ conjWord0, j < 26 := by decide +kernel

@[expose] noncomputable def aS (g : ℕ → Cbar) : Sbp :=
  (wordS g conjWord0)⁻¹ * op Dyadic.a0Elt * wordS g conjWord0

theorem wordQ_conjWord0 : wordQ Qn conjWord0 = BWmat := by
  rw [BWmat_eq, wordQ, conjWord0, List.map_map]
  rfl

section Pair

variable (β : Cbar →* GL (Fin 4370) (ZMod 2)) (g : ℕ → Cbar)
  (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)
  (ha : ((betaRow β (op Dyadic.a0Elt) : MatBˣ) : MatB) = F0mat)

include hg ha in
theorem betaRow_aS : ((betaRow β (aS g) : MatBˣ) : MatB) = Fmat := by
  have hW := betaRow_wordS β g hg conjWord0 conjWord0_lt
  rw [wordQ_conjWord0] at hW
  have hu : IsUnit BWmat := by
    rw [← hW]
    exact Units.isUnit _
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [aS, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hW, ha,
    Matrix.mul_assoc, ← pair_matrix_facts.1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd,
    Matrix.one_mul]

include hg ha in
theorem isSimpleGroup_B_of_pair
    (hβ : Function.Injective β) (hτ : g 25 = taubar)
    (hg0 : g 0 ∈ Ebar) (hgJ : ∀ j, 1 ≤ j → j ≤ 24 → g j ∈ Jbar) :
    IsSimpleGroup NativeSporadic.B :=
  isSimpleGroup_B_of β hβ g hg hτ hg0 hgJ (aS g) (betaRow_aS β g hg ha)

end Pair

@[expose] noncomputable def gSeq (j : ℕ) : Cbar := if h : j < 26 then selGen ⟨j, h⟩ else 1

theorem gSeq_of_lt {j : ℕ} (h : j < 26) : gSeq j = selGen ⟨j, h⟩ := by
  rw [gSeq, dite_eq_left h]

theorem gSeq_last : gSeq 25 = taubar := by
  rw [gSeq_of_lt (by norm_num)]
  exact selGen_last

theorem gSeq_zero_mem : gSeq 0 ∈ Ebar := by
  rw [gSeq_of_lt (by norm_num), show (⟨0, by norm_num⟩ : Fin 26) = 0 from rfl, selGen_zero]
  exact kappa_rho_mem_Ebar (qElt_mem_centralizer 1)

theorem gSeq_mem_Jbar (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 24) : gSeq j ∈ Jbar := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e : gSeq (i + 1) = kappa ⟨hElt ⟨i, by omega⟩, hElt_mem_Cgen _⟩ := by
    rw [gSeq_of_lt (by omega)]
    exact selGen_succ ⟨i, by omega⟩
  rw [e]
  exact kappa_mem_Jbar (hElt_mem_Jstar _)

structure IsExplicitBinary (β : Cbar →* GL (Fin 4370) (ZMod 2)) : Prop where
  injective : Function.Injective β
  gen : ∀ j < 26, ((betaRow β (op (gSeq j)) : MatBˣ) : MatB) = Qn j
  a0 : ((betaRow β (op Dyadic.a0Elt) : MatBˣ) : MatB) = F0mat

theorem isSimpleGroup_B_of_explicit
    {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β) :
    IsSimpleGroup NativeSporadic.B :=
  isSimpleGroup_B_of_pair β gSeq hβ.gen hβ.a0 hβ.injective gSeq_last gSeq_zero_mem gSeq_mem_Jbar

section Explicit

attribute [local instance] Dyadic.instAddCommGroupVst

theorem betaS_explicit :
    IsExplicitBinary Dyadic.betaS := by
  have : IsSimpleGroup Cbar := Dyadic.isSimpleGroup_Cbar
  refine ⟨Dyadic.beta_injective Rbasis chi Dyadic.lamS_stable selGen Dyadic.chi_selGen_apply
    Dyadic.fbarS_fixed, fun j hj => ?_, ?_⟩
  · rw [coe_betaRow, unop_op, gSeq_of_lt hj, Dyadic.betaS_gen ⟨j, hj⟩, Matrix.transpose_transpose]
    exact (Qn_eq ⟨j, hj⟩).symm
  · rw [coe_betaRow, unop_op, Dyadic.betaS_a0, Matrix.transpose_transpose]
    rfl

end Explicit

theorem isSimpleGroup_B :
    IsSimpleGroup NativeSporadic.B :=
  isSimpleGroup_B_of_explicit betaS_explicit

theorem isSimpleGroup_B_of_rep
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (R : Module.Basis (Fin 4371) ℚ V) (ρ : Cbar →* (V ≃ₗ[ℚ] V))
    (_hN : ∀ k : Fin 48, ((k : ℕ) = 1 ∨ 23 ≤ (k : ℕ) ∨ (k : ℕ) ∈ [2, 4, 5, 10, 17]) →
      ∀ t : Fin 4371, (ρ (packetElt k) : V →ₗ[ℚ] V) (R t) = ∑ u : Fin 4371, packetQ k t u • R u) :
    IsSimpleGroup NativeSporadic.B :=
  isSimpleGroup_B

end CFSG.Monster.B

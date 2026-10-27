module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qData
public import CFSG.Quasithin.Recognition.St84.Gen.ModTwoNatL2
public import CFSG.Quasithin.Recognition.St84.Gen.ModOrthL2
public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qBase

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

namespace U4qBase

theorem isTwoNatType_L0 (B : X.U4qBase) :
    CFSG.Quasithin.F112R.St84.IsTwoNatType (X.L 0) (X.n 0) := by
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hn := n1_eq_two_mul B
  have hsec := B.isElemSec_Q0
  have hT : IsSylowTwoOf X.S (X.L 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L 0
  refine CFSG.Quasithin.F112R.St84.isTwoNatType_of_quadratic
    (by have := B.gen.hyp.two_le_n 0; omega) (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
    ?_ ?_ ?_ ?_ hT ?_ <;> rw [B.blockU_L0, B.blockZ_L0]
  · rw [hQ0]
    intro x hx u hu
    exact hsec.2.1 (Subgroup.commutator_mem_commutator hx hu)
  · exact hsec.2.2
  · rw [B.card_Q0, B.card_Z0, hn, ← pow_add]
    congr 1
    omega
  · intro u hu hl
    have hmem : u ∈ relCent (X.Q 0) (X.Z 0) (X.L 0) :=
      ⟨hu, mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 u (X.Q_le_Gi 0 hu)), fun l hl' => by
        simpa [commutatorElement_inv] using (X.Z 0).inv_mem (hl l hl')⟩
    rwa [B.relCent_L0] at hmem
  · intro t ht t' ht' u hu
    have h1 : ⁅t', u⁆ ∈ ⁅X.Q 0, X.S⁆ := by
      simpa [commutatorElement_inv] using
        (⁅X.Q 0, X.S⁆).inv_mem (Subgroup.commutator_mem_commutator hu ht')
    have h2 := (⁅⁅X.Q 0, X.S⁆, X.S⁆).inv_mem (Subgroup.commutator_mem_commutator h1 ht)
    exact B.quad (by simpa [commutatorElement_inv] using h2)

theorem isOmega4MinusType_L1 (B : X.U4qBase) :
    CFSG.Quasithin.IsOmega4MinusType (X.L 1) (X.n 0) := by
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 1)
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hn := n1_eq_two_mul B
  have hT : IsSylowTwoOf X.S (X.L 1) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L_succ 0
  obtain ⟨t, ht, t', ht', u, hu, hne⟩ := not_quadratic_Q1 B
  have hq := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  rw [show nOf Γ (X.vert 1) = 2 * X.n 0 from hn] at hq
  refine CFSG.Quasithin.F112R.St84.isOmega4MinusType_of_irreducible_of_not_quadratic
    (by have := B.gen.hyp.two_le_n 0; omega) hq ?_ ?_ ?_ ?_ hT ?_ <;> rw [hQ1]
  · exact B.elem_Q1
  · rw [B.card_Q1, hn]
    congr 1
    omega
  · exact B.Q1_irred hn
  · intro hL
    have hc : ⁅t', u⁆ = 1 := by
      have hcomm := Subgroup.mem_centralizer_iff.mp (hL (hT.1 ht')) u hu
      rw [commutatorElement_def, ← hcomm]
      group
    exact hne (by rw [hc, commutatorElement_one_right])
  · exact ⟨t, ht, t', ht', u, hu, hne⟩

theorem u4qLocalData (B : X.U4qBase) :
    CFSG.Quasithin.F112R.St84.U4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) :=
  B.u4qLocalData_of_types B.isTwoNatType_L0 B.isOmega4MinusType_L1

end U4qBase

theorem Comm48.u4qLocalData_of_eq_one {s r d : ℕ} (C : X.Comm48 s r d) (h1 : d = 1) :
    X.n 1 = 2 * X.n 0 ∧
      CFSG.Quasithin.F112R.St84.U4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) :=
  let B := C.u4qBase h1 (X.s48_0 C).2 (X.s48_1 C).1 (X.s48_2 C)
  ⟨B.n1_eq_two_mul, B.u4qLocalData⟩

end Setup

end CFSG.Quasithin.St84

end

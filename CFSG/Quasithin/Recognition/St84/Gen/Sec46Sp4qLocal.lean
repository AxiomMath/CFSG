module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qNat
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.NatSecCoord

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.F112R.St84
open scoped commutatorElement MatrixGroups

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

private theorem s46sp4q_pCoreOf_L (X : Setup Γ G) (i : ℤ) : pCoreOf 2 (X.L i) = X.Q i :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq

private theorem s46sp4q_pCoreOf_subgroupOf (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact CFSG.mem_openPCoreOf_iff x

theorem CaseBGen.isLin2Type (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsLin2Type (X.L i) (X.n i) := by
  classical
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  have hn := B.two_le_n i
  obtain ⟨hQZ, -, -⟩ := B.Q_eq_Z h8 hi
  have hnatQ : NatQuot (X.L i) (X.Q i) (centerOf (X.L i)) (X.n i) := hQZ ▸ h8.nat i hi
  have hcomm := B.Q_comm h8 hi
  have hZLQ : centerOf (X.L i) ≤ X.Q i := (X.centerOf_L_le_Z B.char i).trans (X.Z_le_Q i)
  have hT := X.isSylowTwoOf_S_L hi
  have hsec : IsElemSec (centerOf (X.L i)) (X.Q i) := by
    refine ⟨hZLQ, ?_, fun x hx => ?_⟩
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x hx y hy)]
      exact one_mem _
    · rw [(B.elem_Q h8 hi).2 x hx]
      exact one_mem _
  have hcore : ∀ x ∈ pCoreOf 2 (X.L i), ∀ e ∈ X.Q i, ⁅x, e⁆ ∈ centerOf (X.L i) := by
    rw [s46sp4q_pCoreOf_L X i]
    intro x hx e he
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x hx e he)]
    exact one_mem _
  have hnt : ∃ l ∈ X.L i, ∃ e ∈ X.Q i, ⁅l, e⁆ ∉ centerOf (X.L i) := by
    by_contra hcon
    push Not at hcon
    have hrel : relCent (X.Q i) (centerOf (X.L i)) X.S = X.Q i := by
      refine le_antisymm (fun _ h => h.1) fun x hx =>
        (mem_relCent ((X.Q_le_L i).trans (X.L_le_Gi i) |>.trans
          (X.Gi_le_normalizer_centerOf_L i))).mpr ⟨hx, fun s hs => ?_⟩
      have h := (centerOf (X.L i)).inv_mem (hcon s ((X.isSylowTwoOf_S_L hi).1 hs) x hx)
      rwa [commutatorElement_inv] at h
    have hline := hnatQ.line X.S hT
    rw [hrel, hnatQ.index] at hline
    have h2 := Nat.pow_right_injective le_rfl hline
    omega
  obtain ⟨α, hα, hker, β, hβ, hβker, hβeq⟩ :=
    exists_isNatSecOf_of_two_pow_le (L := X.L i) (E := X.Q i) (Z := centerOf (X.L i))
      (T := X.S) hn (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot hsec hnatQ.normal hcore
      hnatQ.index hnt hT (hnatQ.line X.S hT).ge
  have hU : blockU (X.L i) = X.Q i := by
    rw [blockU, blockQ, s46sp4q_pCoreOf_L X i]
    exact B.indec h8 hi
  have hZ : blockZ (X.L i) = centerOf (X.L i) := by
    rw [blockZ, hU]
    refine le_antisymm (fun x hx => ?_) (le_inf hZLQ inf_le_right)
    exact Subgroup.mem_inf.mpr ⟨X.Q_le_L i (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
  letI : Fintype (GaloisField 2 (X.n i)) := Fintype.ofFinite _
  let e : ↥(blockU (X.L i)) ≃* ↥(X.Q i) := MulEquiv.subgroupCongr hU
  refine ⟨GaloisField 2 (X.n i), inferInstance, inferInstance, ?_, α, hα, ?_,
    β.comp e.toMonoidHom, hβ.comp e.surjective, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (X.n i) (by omega)
  · rw [hker]
    exact s46sp4q_pCoreOf_subgroupOf (X.L i)
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hZ]
    rfl
  · intro ℓ u v huv
    exact hβeq ℓ (e u) (e v) huv

theorem CaseBGen.sp4qLocalData_of_step8 (B : X.CaseBGen) (h8 : X.CaseBStep8) :
    X.n 1 = X.n 0 ∧ Sp4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) := by
  have hn := h8.n_eq
  have h0 := B.card_Q (i := 0) (Or.inl rfl)
  have h1 := B.card_Q (i := 1) (Or.inr rfl)
  simp only [sub_zero, sub_self] at h0 h1
  have hlin1 := B.isLin2Type h8 (i := 1) (Or.inr rfl)
  rw [← hn] at hlin1
  refine ⟨hn.symm,
    { card_S := ?_
      card_left := ?_
      elem_left := ?_
      lin_left := B.isLin2Type h8 (i := 0) (Or.inl rfl)
      indec_left := ?_
      card_right := ?_
      elem_right := ?_
      lin_right := hlin1
      indec_right := ?_
      card_inf := ?_ }⟩
  · rw [B.card_S, ← hn]
    ring_nf
  · rw [s46sp4q_pCoreOf_L X 0, h0, ← hn]
    ring_nf
  · rw [s46sp4q_pCoreOf_L X 0]
    exact B.elem_Q h8 (Or.inl rfl)
  · rw [s46sp4q_pCoreOf_L X 0]
    exact B.indec h8 (Or.inl rfl)
  · rw [s46sp4q_pCoreOf_L X 1, h1, ← hn]
    ring_nf
  · rw [s46sp4q_pCoreOf_L X 1]
    exact B.elem_Q h8 (Or.inr rfl)
  · rw [s46sp4q_pCoreOf_L X 1]
    exact B.indec h8 (Or.inr rfl)
  · rw [s46sp4q_pCoreOf_L X 0, s46sp4q_pCoreOf_L X 1]
    exact B.card_Q_inf hn

theorem caseB_sp4q (X : Setup Γ G) (B : X.CaseBGen) :
    X.n 1 = X.n 0 ∧ Sp4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) :=
  B.sp4qLocalData_of_step8 B.step8

end Setup

end CFSG.Quasithin.St84

end

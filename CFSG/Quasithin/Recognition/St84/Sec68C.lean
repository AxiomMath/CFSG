module

public import CFSG.Quasithin.Recognition.St84.Sec68B

import CFSG.Quasithin.Recognition.St84.Gen.Sec6TorusCent

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def A : Subgroup G := X.Q 1 ⊓ X.Q (-1)

@[expose] def D : Subgroup G := X.Q 0 ⊓ Subgroup.centralizer (X.Ki 0 : Set G)

private theorem reverse_isMaxReg {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.reverse.IsMaxReg 0 (2 * (m : ℤ)) := by
  obtain ⟨hpos, hleft, hright, harcR, harcL⟩ := hreg
  have hGT : conjSub (X.τ ^ (-(m : ℤ))) X.GT = X.GT := by
    have hmem := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (zpow_mem X.tau_mem_normalizer_GT (-(m : ℤ)))
    simpa [conjSub] using hmem
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · have h := X.rightTransAt_add (-(m : ℤ)) 0 (2 * (m : ℤ)) hright
    simpa [Setup.LeftTransAt, Setup.RightTransAt, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using h
  · have h := X.leftTransAt_add (-(m : ℤ)) 0 (2 * (m : ℤ)) hleft
    simpa [Setup.LeftTransAt, Setup.RightTransAt, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using h
  · rw [Setup.reverse_arcStab, Setup.reverse_GT]
    have hshift := X.arcStab_add (m : ℤ) (-(2 * (m : ℤ) + 1)) 0
    have harcL' : X.arcStab (-1) (2 * (m : ℤ)) = X.GT := by simpa using harcL
    rw [show -(2 * (m : ℤ) + 1) + 2 * (m : ℤ) = -1 by ring,
      show (0 : ℤ) + 2 * (m : ℤ) = 2 * (m : ℤ) by ring, harcL'] at hshift
    calc X.arcStab (-(2 * (m : ℤ) + 1)) 0
        = conjSub ((X.τ ^ (m : ℤ))⁻¹)
            (conjSub (X.τ ^ (m : ℤ)) (X.arcStab (-(2 * (m : ℤ) + 1)) 0)) := by
          rw [conjSub_conjSub_inv]
      _ = conjSub ((X.τ ^ (m : ℤ))⁻¹) X.GT := by rw [← hshift]
      _ = X.GT := by
          rw [show (X.τ ^ (m : ℤ))⁻¹ = X.τ ^ (-(m : ℤ)) by simp]
          exact hGT
  · rw [Setup.reverse_arcStab, Setup.reverse_GT]
    have hshift := X.arcStab_add (m : ℤ) (-(2 * (m : ℤ))) 1
    rw [show -(2 * (m : ℤ)) + 2 * (m : ℤ) = 0 by ring,
      show (1 : ℤ) + 2 * (m : ℤ) = 2 * (m : ℤ) + 1 by ring, harcR] at hshift
    calc X.arcStab (-(2 * (m : ℤ))) 1
        = conjSub ((X.τ ^ (m : ℤ))⁻¹)
            (conjSub (X.τ ^ (m : ℤ)) (X.arcStab (-(2 * (m : ℤ))) 1)) := by
          rw [conjSub_conjSub_inv]
      _ = conjSub ((X.τ ^ (m : ℤ))⁻¹) X.GT := by rw [← hshift]
      _ = X.GT := by
          rw [show (X.τ ^ (m : ℤ))⁻¹ = X.τ ^ (-(m : ℤ)) by simp]
          exact hGT

private theorem Z_neg_one_le_Gi_two_and_not_le_Gi_three (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z (-1) ≤ X.Gi 2 ∧ ¬ X.Z (-1) ≤ X.Gi 3 := by
  have h := X.reverse.Z_one_b_facts hc
    (Or.inl (show 2 ≤ X.reverse.n 0 from by simpa using hn0)) hs hodd h5
    (X.reverse_hX hs hodd hX) (by simpa using hGT) (X.reverse_isMaxReg hreg)
  have h' : (X.Z (-1) ≤ X.Gi 2 ⊓ X.Gi (-4)) ∧ ¬ X.Z (-1) ≤ X.Gi (-5) ∧
      ¬ X.Z (-1) ≤ X.Gi 3 := by simpa [Setup.Gi] using h
  obtain ⟨h1, -, h4⟩ := h'
  exact ⟨fun x hx => (h1 hx).1, h4⟩

private theorem Z_neg_one_le_Gi_two (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z (-1) ≤ X.Gi 2 :=
  (X.Z_neg_one_le_Gi_two_and_not_le_Gi_three hc hn0 hs hodd h5 hX hGT hreg).1

theorem Z_neg_one_le_Q_one (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z (-1) ≤ X.Q 1 :=
  X.Z_le_Q_of_le_Gi (-1) 2 1
    (X.Z_neg_one_le_Gi_two hc hn0 hs hodd h5 hX hGT hreg)
    (Or.inr ⟨by norm_num, by norm_num⟩)

theorem A_le_Q_zero : X.A ≤ X.Q 0 := by
  have hA2 : IsPGroup 2 ↥X.A :=
    (X.isPGroup_edgeSylow 1).to_le ((inf_le_left : X.A ≤ X.Q 1).trans (X.Q_le_edgeSylow_left 1))
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := by
    have h := (X.Q_le_Gi_adj 1).trans
      (inf_le_left : X.Gi (1 - 1) ⊓ X.Gi (1 + 1) ≤ X.Gi (1 - 1))
    simpa using h
  have hQmG0 : X.Q (-1) ≤ X.Gi 0 := by
    have h := (X.Q_le_Gi_adj (-1)).trans
      (inf_le_right : X.Gi (-1 - 1) ⊓ X.Gi (-1 + 1) ≤ X.Gi (-1 + 1))
    simpa using h
  have hAG : X.A ≤ X.Gi 0 := by
    show X.Q 1 ⊓ X.Q (-1) ≤ X.Gi 0
    have h : X.Q 1 ⊓ X.Q (-1) ≤ X.Gi 0 ⊓ X.Gi 0 :=
      le_inf ((inf_le_left : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 1).trans hQ1G0)
        ((inf_le_right : X.Q 1 ⊓ X.Q (-1) ≤ X.Q (-1)).trans hQmG0)
    simpa using h
  have hAdj1 : Γ.Adj (X.vert 0) (X.vert 1) := X.adj 0
  have hAdjm : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa [show (-1 : ℤ) + 1 = 0 by norm_num] using (X.adj (-1)).symm
  have hne : X.vert 1 ≠ X.vert (-1) := by
    intro h; have := X.vert_injective h; omega
  exact le_pCoreOf_of_isPGroup_fixes_two X.hyp hA2 hAG hAdj1 hAdjm hne
    (fun y hy => MulAction.mem_stabilizer_iff.mp
      ((X.Q_le_Gi 1) ((inf_le_left : X.A ≤ X.Q 1) hy)))
    (fun y hy => MulAction.mem_stabilizer_iff.mp
      ((X.Q_le_Gi (-1)) ((inf_le_right : X.A ≤ X.Q (-1)) hy)))

private theorem Q_two_inf_Q_neg_one_le_Q_one : X.Q 2 ⊓ X.Q (-1) ≤ X.Q 1 := by
  have hP2 : IsPGroup 2 ↥(X.Q 2 ⊓ X.Q (-1)) :=
    (X.isPGroup_edgeSylow 1).to_le
      ((inf_le_left : X.Q 2 ⊓ X.Q (-1) ≤ X.Q 2).trans (X.Q_le_edgeSylow 1))
  have hQ2G1 : X.Q 2 ≤ X.Gi 1 := by
    have h := (X.Q_le_Gi_adj 2).trans
      (inf_le_left : X.Gi (2 - 1) ⊓ X.Gi (2 + 1) ≤ X.Gi (2 - 1))
    simpa using h
  have hQmG0 : X.Q (-1) ≤ X.Gi 0 := by
    have h := (X.Q_le_Gi_adj (-1)).trans
      (inf_le_right : X.Gi (-1 - 1) ⊓ X.Gi (-1 + 1) ≤ X.Gi (-1 + 1))
    simpa using h
  have hPG1 : X.Q 2 ⊓ X.Q (-1) ≤ X.Gi 1 :=
    (inf_le_left : X.Q 2 ⊓ X.Q (-1) ≤ X.Q 2).trans hQ2G1
  have hne : X.vert 0 ≠ X.vert 2 := by
    intro h; have := X.vert_injective h; omega
  exact le_pCoreOf_of_isPGroup_fixes_two X.hyp hP2 hPG1 (X.adj 0).symm (X.adj 1) hne
    (fun y hy => MulAction.mem_stabilizer_iff.mp
      (hQmG0 ((inf_le_right : X.Q 2 ⊓ X.Q (-1) ≤ X.Q (-1)) hy)))
    (fun y hy => MulAction.mem_stabilizer_iff.mp
      ((X.Q_le_Gi 2) ((inf_le_left : X.Q 2 ⊓ X.Q (-1) ≤ X.Q 2) hy)))

private theorem Q_two_inf_A_eq : X.Q 2 ⊓ X.A = X.Q 2 ⊓ X.Q (-1) := by
  rw [Setup.A, ← inf_assoc, inf_comm (X.Q 2) (X.Q 1), inf_assoc,
    inf_eq_right.mpr X.Q_two_inf_Q_neg_one_le_Q_one]

private theorem Z_one_le_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 1 ≤ X.A := by
  obtain ⟨h1, -, -⟩ := X.Z_one_b_facts hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  refine le_inf (X.Z_le_Q 1) ?_
  exact X.Z_le_Q_of_le_Gi 1 (-2) (-1) (fun x hx => (h1 hx).1) (Or.inr ⟨by norm_num, by norm_num⟩)

private theorem Z_neg_one_le_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z (-1) ≤ X.A :=
  le_inf (X.Z_neg_one_le_Q_one hc hn0 hs hodd h5 hX hGT hreg) (X.Z_le_Q (-1))

theorem Z_four_le_V2 (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 4 ≤ X.V2 := by
  have hZ4Z3 : X.Z 4 ≤ X.Z 3 := by
    rw [X.Z_three_eq_Z_two_sup_Z_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact le_sup_right
  rw [X.V2_eq_Z_one_sup_Z_three hc hn0 hs hodd h5 hX
    hGT hreg]
  exact hZ4Z3.trans le_sup_right

theorem Gi_zero_le_normalizer_V0 (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Gi 0 ≤ Subgroup.normalizer (X.V0 : Set G) := by
  have hV0 := X.V0_eq_Z_one_sup_Z_neg_one hc hn0 hs hodd h5 hX hGT hreg
  have hZ1E : X.Z 1 ≤ X.E X.QT 0 :=
    le_inf ((X.Z_one_le_A hc hn0 hs hodd h5 hX hGT hreg).trans X.A_le_Q_zero)
      (X.Z_le_normalizer_QT 1)
  have hZmE : X.Z (-1) ≤ X.E X.QT 0 :=
    le_inf ((X.Z_neg_one_le_A hc hn0 hs hodd h5 hX hGT hreg).trans X.A_le_Q_zero)
      (X.Z_le_normalizer_QT (-1))
  have hV0E : X.V0 ≤ X.E X.QT 0 := by
    rw [hV0]
    exact sup_le hZ1E hZmE
  have hM0 : X.normGi X.QT 0 ≤ Subgroup.normalizer (X.V0 : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hV0E le_rfl).trans
      (X.commutator_E_normGi_le hc hn0 hs hodd h5 hX hGT hreg)
  have hQ0N1 : X.Q 0 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 q ((X.Q_le_Gi_adj 0).trans inf_le_right hq)
  have hQ0Nm : X.Q 0 ≤ Subgroup.normalizer (X.Z (-1) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal (-1) q ((X.Q_le_Gi_adj 0).trans inf_le_left hq)
  have hQ0 : X.Q 0 ≤ Subgroup.normalizer (X.V0 : Set G) := by
    rw [hV0]
    exact (le_inf hQ0N1 hQ0Nm).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (X.Z 1) (X.Z (-1)))
  have hU : X.IsSK X.QT :=
    (X.isSKMax_QT hGT hs hodd h5 hX).1
  have hL : X.L 0 = X.Lst X.QT 0 ⊔ X.Q 0 :=
    X.L_eq_Lst_sup_Q hU (Or.inr hn0)
  have hM : X.normGi X.QT 0 = X.Lst X.QT 0 ⊔ X.K :=
    X.normGi_eq_Lst_sup_K hU (Or.inr hn0)
  have hG0 : X.Gi 0 = X.normGi X.QT 0 ⊔ X.Q 0 := by
    rw [X.Gi_eq_L_sup_K 0, hL, hM]
    ac_rfl
  rw [hG0]
  exact sup_le hM0 hQ0

private theorem Gi_two_le_normalizer_V2 (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Gi 2 ≤ Subgroup.normalizer (X.V2 : Set G) := by
  have h := conjSub_mono X.τ (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg)
  rw [← conjSub_normalizer] at h
  have hG : conjSub X.τ (X.Gi 0) = X.Gi 2 := by simpa using (X.Gi_add 1 0).symm
  rw [hG] at h
  simpa [Setup.V2] using h

private theorem Q_zero_inf_Q_one_inf_Q_zero_inf_Q_neg_one_eq_A :
    (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) = X.A := by
  have hAQ0 : X.A ≤ X.Q 0 := X.A_le_Q_zero
  ext x
  constructor
  · rintro ⟨⟨-, hx1⟩, -, hxm⟩
    exact Subgroup.mem_inf.mpr ⟨hx1, hxm⟩
  · intro hx
    exact ⟨⟨hAQ0 hx, (Subgroup.mem_inf.mp hx).1⟩,
      ⟨hAQ0 hx, (Subgroup.mem_inf.mp hx).2⟩⟩

theorem commutator_V2_Q_two_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.V2, X.Q 2⁆ ≤ X.Z 2 := by
  have hV2 := X.V2_eq_Z_one_sup_Z_three hc hn0 hs hodd h5 hX hGT hreg
  have hZ1Gi2 : X.Z 1 ≤ X.Gi 2 := by
    obtain ⟨h1, -, -⟩ := X.Z_one_b_facts hc (Or.inl hn0) hs hodd h5 hX hGT hreg
    intro x hx
    exact X.mem_Gi_of_between (h1 hx).1 (h1 hx).2 (by omega) (by omega)
  have hZ3Gi2 : X.Z 3 ≤ X.Gi 2 :=
    (X.Z_le_Q 3).trans ((X.Q_le_Gi_adj 3).trans inf_le_left)
  have hV2le : X.V2 ≤ X.Gi 2 := by
    rw [hV2]
    exact sup_le hZ1Gi2 hZ3Gi2
  have hV2M : X.V2 ≤ X.V2 ⊔ X.Q 2 := le_sup_left
  have hQ2M : X.Q 2 ≤ X.V2 ⊔ X.Q 2 := le_sup_right
  have hZ1M : X.Z 1 ≤ X.V2 ⊔ X.Q 2 :=
    (show X.Z 1 ≤ X.V2 by rw [hV2]; exact le_sup_left).trans hV2M
  have hZ3M : X.Z 3 ≤ X.V2 ⊔ X.Q 2 :=
    (show X.Z 3 ≤ X.V2 by rw [hV2]; exact le_sup_right).trans hV2M
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := by
    rw [X.Z_one_eq_Z_zero_sup_Z_two hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact le_sup_right
  have hZ2V : X.Z 2 ≤ X.V2 := by
    rw [hV2]
    exact hZ2Z1.trans le_sup_left
  have hZ2M : X.Z 2 ≤ X.V2 ⊔ X.Q 2 := hZ2V.trans hV2M
  set M : Subgroup G := X.V2 ⊔ X.Q 2 with hM
  have hMle : M ≤ X.Gi 2 := sup_le hV2le (X.Q_le_Gi 2)
  haveI hfinM : Finite ↥M := finite_of_le_stabilizer X.hyp hMle
  haveI hQ2normal : ((X.Q 2).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hMle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))
  have h1 : ⁅X.Z 1, X.Q 2⁆ ≤ X.Z 2 :=
    (Subgroup.commutator_mono le_rfl (X.Q_le_edgeSylow 1)).trans
      (X.commutator_Z_one_edgeSylow_le hc (Or.inl hn0) hs hodd h5 hX hGT hreg)
  have h2 : ⁅X.Z 3, X.Q 2⁆ ≤ X.Z 2 := by
    have hQ0S : X.Q 0 ≤ X.S := by
      rw [← X.edgeSylow_zero]
      exact X.Q_le_edgeSylow_left 0
    have h0 : ⁅X.Z 1, X.Q 0⁆ ≤ X.Z 0 :=
      (Subgroup.commutator_mono le_rfl hQ0S).trans
        (X.commutator_Z_one_S_le hc (Or.inl hn0) hs hodd h5 hX hGT hreg)
    have hconj : conjSub X.τ ⁅X.Z 1, X.Q 0⁆ ≤ conjSub X.τ (X.Z 0) :=
      conjSub_mono X.τ h0
    rw [← conjSub_commutator] at hconj
    have hZ1 : conjSub X.τ (X.Z 1) = X.Z 3 := by simpa using (X.Z_add 1 1).symm
    have hQ0 : conjSub X.τ (X.Q 0) = X.Q 2 := by simpa using (X.Q_add 1 0).symm
    have hZ0 : conjSub X.τ (X.Z 0) = X.Z 2 := by simpa using (X.Z_add 1 0).symm
    rwa [hZ1, hQ0, hZ0] at hconj
  have h1M : ⁅(X.Z 1).subgroupOf M, (X.Q 2).subgroupOf M⁆ ≤
      (X.Z 2).subgroupOf M := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := M), Subgroup.map_commutator]
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZ1M,
      inf_eq_left.mpr hQ2M, inf_eq_left.mpr hZ2M] using h1
  have h2M : ⁅(X.Z 3).subgroupOf M, (X.Q 2).subgroupOf M⁆ ≤
      (X.Z 2).subgroupOf M := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := M), Subgroup.map_commutator]
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZ3M,
      inf_eq_left.mpr hQ2M, inf_eq_left.mpr hZ2M] using h2
  have hsup_eq : (X.Z 1).subgroupOf M ⊔ (X.Z 3).subgroupOf M =
      (X.V2).subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hZ1M hZ3M, ← hV2]
  have hleM : ⁅(X.V2).subgroupOf M, (X.Q 2).subgroupOf M⁆ ≤
      (X.Z 2).subgroupOf M := by
    rw [← hsup_eq, Subgroup.commutator_sup_right]
    exact sup_le h1M h2M
  have hmap := (Subgroup.map_subtype_le_map_subtype (G' := M)).mpr hleM
  rw [Subgroup.map_commutator] at hmap
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV2M,
    inf_eq_left.mpr hQ2M, inf_eq_left.mpr hZ2M] using hmap

theorem A_eq_Z_neg_one_sup_Q_two_inf_Q_neg_one (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.A = X.Z (-1) ⊔ (X.Q 2 ⊓ X.Q (-1)) := by
  have hZQ1 : X.Z (-1) ≤ X.Q 1 := X.Z_neg_one_le_Q_one hc hn0 hs hodd h5 hX hGT hreg
  have hZleA : X.Z (-1) ≤ X.A := le_inf hZQ1 (X.Z_le_Q (-1))
  obtain ⟨-, hnot3⟩ := X.Z_neg_one_le_Gi_two_and_not_le_Gi_three hc hn0 hs hodd h5 hX hGT hreg
  have hZedge : X.Z (-1) ≤ X.edgeSylow 1 := hZQ1.trans (X.Q_le_edgeSylow_left 1)
  have hnot : ¬ X.Z (-1) ≤ X.Q 2 := by
    intro h
    exact hnot3 (h.trans ((X.Q_le_Gi_adj 2).trans inf_le_right))
  have hK : X.K ≤ Subgroup.normalizer (X.Z (-1) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal (-1) k (X.K_le_Gi (-1) hk)
  have hS : X.Z (-1) ⊔ X.Q 2 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_gen 1 (inf_le_left.trans hK) hZedge hnot
  have hAle : X.A ≤ X.Z (-1) ⊔ X.Q 2 := by
    rw [hS]
    exact (inf_le_left : X.A ≤ X.Q 1).trans (X.Q_le_edgeSylow_left 1)
  have hZGi2 : X.Z (-1) ≤ X.Gi 2 :=
    hZQ1.trans ((X.Q_le_Gi_adj 1).trans inf_le_right)
  have hZQ2n : X.Z (-1) ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    hZGi2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hsplit : X.A = X.Z (-1) ⊔ (X.Q 2 ⊓ X.A) := by
    refine le_antisymm ?_ (sup_le hZleA inf_le_right)
    have hprod : (↑(X.Z (-1) ⊔ X.Q 2) : Set G) = (X.Z (-1) : Set G) * (X.Q 2 : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-1)) (X.Q 2) hZQ2n
    intro a ha
    have ha' : a ∈ (X.Z (-1) : Set G) * (X.Q 2 : Set G) := by
      rw [← hprod]
      exact hAle ha
    obtain ⟨z, hz, q, hq, hzq⟩ := Set.mem_mul.mp ha'
    have hzA : z ∈ X.A := hZleA hz
    have hqA : q ∈ X.A := by
      have hqeq : q = z⁻¹ * a := by rw [← hzq]; group
      rw [hqeq]
      exact X.A.mul_mem (X.A.inv_mem hzA) ha
    rw [← hzq]
    exact Subgroup.mul_mem_sup hz (Subgroup.mem_inf.mpr ⟨hq, hqA⟩)
  rw [hsplit, X.Q_two_inf_A_eq]

theorem commutator_A_Z_four_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.A, X.Z 4⁆ ≤ X.Z 1 := by
  have hZ4G0 : X.Z 4 ≤ X.Gi 0 := X.Z_four_le_Gi_zero
          hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  have hZ4V2 : X.Z 4 ≤ X.V2 := X.Z_four_le_V2 hc hn0 hs hodd h5 hX hGT hreg
  have hZmG2 : X.Z (-1) ≤ X.Gi 2 := X.Z_neg_one_le_Gi_two hc hn0 hs hodd h5 hX hGT hreg
  have hV0N := X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg
  have hV2N := X.Gi_two_le_normalizer_V2 hc hn0 hs hodd h5 hX hGT hreg
  have hV0com : ⁅X.V0, X.Gi 0⁆ ≤ X.V0 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hV0N
  have hV2com : ⁅X.V2, X.Gi 2⁆ ≤ X.V2 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hV2N
  have hZmV0 : X.Z (-1) ≤ X.V0 := by
    rw [X.V0_eq_Z_one_sup_Z_neg_one hc hn0 hs hodd h5 hX hGT hreg]
    exact le_sup_right
  have hZmZ1 : ⁅X.Z (-1), X.Z 4⁆ ≤ X.Z 1 := by
    have h1 : ⁅X.Z (-1), X.Z 4⁆ ≤ X.V0 :=
      (Subgroup.commutator_mono hZmV0 hZ4G0).trans hV0com
    have h2 : ⁅X.Z (-1), X.Z 4⁆ ≤ X.V2 := by
      have hle := Subgroup.commutator_mono hZmG2 hZ4V2
      have hV2com' : ⁅X.Gi 2, X.V2⁆ ≤ X.V2 := by
        rw [Subgroup.commutator_comm (X.Gi 2) (X.V2)]
        exact hV2com
      exact hle.trans hV2com'
    exact (le_inf h1 h2).trans
      (X.V0_inf_V2_le hc hn0 hs hodd h5 hX hGT hreg)
  have hB : ⁅X.Q 2 ⊓ X.Q (-1), X.Z 4⁆ ≤ X.Z 2 := by
    have hle := Subgroup.commutator_mono
      (inf_le_left : X.Q 2 ⊓ X.Q (-1) ≤ X.Q 2) hZ4V2
    have h6 := X.commutator_V2_Q_two_le hc hn0 hs hodd h5 hX hGT hreg
    have h6' : ⁅X.Q 2, X.V2⁆ ≤ X.Z 2 := by
      rw [Subgroup.commutator_comm (X.Q 2) (X.V2)]
      exact h6
    exact hle.trans h6'
  have hZ1B : X.Z (-1) ≤ Subgroup.normalizer (X.Q 2 ⊓ X.Q (-1) : Set G) := by
    have hinf : X.Z (-1) ≤
        Subgroup.normalizer (X.Q 2 : Set G) ⊓ Subgroup.normalizer (X.Q (-1) : Set G) :=
      le_inf (hZmG2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))
        ((X.Z_le_Gi (-1)).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1))))
    exact hinf.trans Subgroup.inf_normalizer_le_normalizer_inf
  have hprod : (↑(X.Z (-1) ⊔ (X.Q 2 ⊓ X.Q (-1))) : Set G) =
      (X.Z (-1) : Set G) * ((X.Q 2 ⊓ X.Q (-1)) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-1)) (X.Q 2 ⊓ X.Q (-1)) hZ1B
  rw [X.A_eq_Z_neg_one_sup_Q_two_inf_Q_neg_one hc hn0 hs hodd h5 hX hGT hreg]
  refine Subgroup.commutator_le.mpr ?_
  intro h hh z hz
  have hh' : h ∈ (X.Z (-1) : Set G) * ((X.Q 2 ⊓ X.Q (-1)) : Set G) := by
    rw [← hprod]
    exact hh
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hh'
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hbz : ⁅b, z⁆ ∈ X.Z 2 := hB (Subgroup.commutator_mem_commutator hb hz)
  have hconj : a * ⁅b, z⁆ * a⁻¹ ∈ X.Z 2 := by
    have haGi2 : a ∈ X.Gi 2 := hZmG2 ha
    have hmem := mul_mem_conjSub (g := a) (H := X.Z 2) hbz
    rwa [X.Z_normal 2 a haGi2] at hmem
  have haz : ⁅a, z⁆ ∈ X.Z 1 := hZmZ1 (Subgroup.commutator_mem_commutator ha hz)
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := by
    rw [X.Z_one_eq_Z_zero_sup_Z_two hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact le_sup_right
  exact (X.Z 1).mul_mem (hZ2Z1 hconj) haz

theorem commutator_A_Z_neg_four_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.A, X.Z (-4)⁆ ≤ X.Z (-1) := by
  have h := X.reverse.commutator_A_Z_four_le hc (by simpa using hn0) hs hodd h5
    (X.reverse_hX hs hodd hX) (by simpa using hGT) (X.reverse_isMaxReg hreg)
  simpa [Setup.A, inf_comm] using h

theorem Gi_zero_le_normalizer_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) := by
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.A : Set G) := by
    have h1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      ((X.Q_le_Gi_adj 0).trans inf_le_right).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
    have h2 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
      simpa using ((X.Q_le_Gi_adj 0).trans inf_le_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKN : X.K ≤ Subgroup.normalizer (X.A : Set G) := by
    have h1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
    have h2 : X.K ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
      simpa using (X.K_le_Gi (-1)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZ4N : X.Z 4 ≤ Subgroup.normalizer (X.A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((X.commutator_A_Z_four_le hc hn0 hs hodd h5 hX hGT hreg).trans
        (X.Z_one_le_A hc hn0 hs hodd h5 hX hGT hreg))
  have hZm4N : X.Z (-4) ≤ Subgroup.normalizer (X.A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((X.commutator_A_Z_neg_four_le hc hn0 hs hodd h5 hX hGT hreg).trans
        (X.Z_neg_one_le_A hc hn0 hs hodd h5 hX hGT hreg))
  have hL0N : X.L 0 ≤ Subgroup.normalizer (X.A : Set G) := by
    rw [X.L_zero_eq_Z_four_sup hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact sup_le (sup_le hZ4N hZm4N) hQ0N
  rw [X.Gi_eq_L_sup_K 0]
  exact sup_le hL0N hKN

private theorem commutator_Q_zero_Q_zero_le_A (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.Q 0, X.Q 0⁆ ≤ X.A := by
  have hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg
  have hsq' : ∀ q ∈ X.Q 0, q ^ 2 ∈ X.A := fun q hq => by
    simpa [Setup.A, inf_comm] using X.sq_mem_Q_neg_one_inf_Q_one hq
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hcA : b⁻¹ * (a ^ 2)⁻¹ * b * (b ^ 2)⁻¹ ∈ X.A := by
    have hconj : b⁻¹ * (a ^ 2)⁻¹ * b ∈ X.A := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hA ((X.Gi 0).inv_mem (X.Q_le_Gi 0 hb))) (a ^ 2)⁻¹).mp (X.A.inv_mem (hsq' a ha))
    exact X.A.mul_mem hconj (X.A.inv_mem (hsq' b hb))
  have heq : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * (a ^ 2)⁻¹ * b * (b ^ 2)⁻¹) := by
    simp only [commutatorElement_def, pow_two]; group
  rw [heq]
  exact X.A.mul_mem (hsq' (a * b) ((X.Q 0).mul_mem ha hb)) hcA

private theorem Ki_zero_le_normalizer_Q_zero_inf (j : ℤ) :
    X.Ki 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q j : Subgroup G) : Set G) := fun k hk =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (X.L_le_Gi 0 hk.2),
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi j) (X.K_le_Gi j hk.1)⟩

private theorem exists_conj_Q_zero_inf_Q_one :
    ∃ y ∈ X.L 0 ⊓ Subgroup.normalizer (X.Ki 0 : Set G),
      conjSub y (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q (-1) := by
  obtain ⟨y, hy, hyv⟩ := X.exists_normalizer_Ki_move
  have hyG0 : y ∈ X.Gi 0 := X.L_le_Gi 0 hy.1
  have hGy : conjSub y (X.Gi 0) = X.Gi 0 := by
    rw [← stabilizer_smul_eq_conjSub y (X.vert 0), MulAction.mem_stabilizer_iff.mp hyG0]
  have hQ0y : conjSub y (X.Q 0) = X.Q 0 := by rw [Setup.Q, ← pCoreOf_conjSub, hGy]
  have hG1y : conjSub y (X.Gi 1) = X.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub y (X.vert 1), hyv]
  have hQ1y : conjSub y (X.Q 1) = X.Q (-1) := by rw [Setup.Q, ← pCoreOf_conjSub, hG1y]
  exact ⟨y, hy, by rw [conjSub_inf, hQ0y, hQ1y]⟩

private theorem Q_zero_le_relCent (hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G))
    (hQ0comm : ⁅X.Q 0, X.Q 0⁆ ≤ X.A) : X.Q 0 ≤ relCent (X.L 0) X.A (X.Q 0) := by
  intro g hg
  rw [mem_relCent ((X.L_le_Gi 0).trans hA)]
  exact ⟨le_oTwoPrime_of_isPGroup
    ((X.isPGroup_edgeSylow 0).to_le (X.Q_le_edgeSylow_left 0)) (X.Q_le_Gi 0) hg,
    fun x hx => hQ0comm (Subgroup.commutator_mem_commutator hg hx)⟩

private theorem L_zero_le_normalizer_relCent
    (hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G)) :
    X.L 0 ≤ Subgroup.normalizer ((relCent (X.L 0) X.A (X.Q 0) : Subgroup G) : Set G) := by
  have hEZ : X.L 0 ≤ Subgroup.normalizer (X.A : Set G) := (X.L_le_Gi 0).trans hA
  have hstep : ∀ n ∈ X.L 0, conjSub n (relCent (X.L 0) X.A (X.Q 0)) ≤
      relCent (X.L 0) X.A (X.Q 0) := by
    intro n hn c hc
    rw [mem_conjSub] at hc
    rw [mem_relCent hEZ] at hc ⊢
    refine ⟨?_, ?_⟩
    · have hmem : n * (n⁻¹ * c * n) * n⁻¹ ∈ X.L 0 :=
        (X.L 0).mul_mem ((X.L 0).mul_mem hn hc.1) ((X.L 0).inv_mem hn)
      have heq : n * (n⁻¹ * c * n) * n⁻¹ = c := by group
      rwa [heq] at hmem
    · intro x hx
      have hxQ : n⁻¹ * x * n ∈ X.Q 0 := by
        have hnN : n ∈ Subgroup.normalizer (X.Q 0 : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (X.L_le_Gi 0 hn)
        have h := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X.Q 0 : Set G)).inv_mem hnN) x).mp hx
        simpa using h
      have hcomm := hc.2 _ hxQ
      have hconj : n⁻¹ * ⁅c, x⁆ * n = ⁅n⁻¹ * c * n, n⁻¹ * x * n⁆ := by
        have h := conjugate_commutatorElement (g₁ := c) (g₂ := x) n⁻¹
        simpa using h
      have hmem : n * ⁅n⁻¹ * c * n, n⁻¹ * x * n⁆ * n⁻¹ ∈ X.A :=
        ((Subgroup.mem_normalizer_iff.mp (hA (X.L_le_Gi 0 hn))) _).mp hcomm
      rw [← hconj] at hmem
      simpa [mul_assoc] using hmem
  have hCeq : ∀ n ∈ X.L 0, conjSub n (relCent (X.L 0) X.A (X.Q 0)) =
      relCent (X.L 0) X.A (X.Q 0) := by
    intro n hn
    have h1 : relCent (X.L 0) X.A (X.Q 0) ≤
        conjSub n⁻¹ (relCent (X.L 0) X.A (X.Q 0)) := by
      have := conjSub_mono n⁻¹ (hstep n hn)
      rwa [conjSub_conjSub_inv] at this
    have h2 : conjSub n⁻¹ (relCent (X.L 0) X.A (X.Q 0)) ≤
        relCent (X.L 0) X.A (X.Q 0) :=
      hstep n⁻¹ ((X.L 0).inv_mem hn)
    have heqinv : conjSub n⁻¹ (relCent (X.L 0) X.A (X.Q 0)) =
        relCent (X.L 0) X.A (X.Q 0) := le_antisymm h2 h1
    calc conjSub n (relCent (X.L 0) X.A (X.Q 0))
        = conjSub n (conjSub n⁻¹ (relCent (X.L 0) X.A (X.Q 0))) := by rw [heqinv]
      _ = relCent (X.L 0) X.A (X.Q 0) := conjSub_inv_conjSub n _
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjSub] using hCeq n hn

private theorem normal_Q_zero_subgroupOf_L_zero :
    ((X.Q 0).subgroupOf (X.L 0)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))

attribute [local instance] normal_Q_zero_subgroupOf_L_zero

private theorem isSimpleGroup_quot_L_zero (hn0 : 2 ≤ X.n 0) :
    IsSimpleGroup (↥(X.L 0) ⧸ (X.Q 0).subgroupOf (X.L 0)) := by
  have hpc : pCoreOf 2 (X.L 0) = X.Q 0 := by
    simpa [Setup.Q, Setup.Gi] using (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hqe : (X.Q 0).subgroupOf (X.L 0) = CFSG.pCore 2 ↥(X.L 0) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (X.L 0), hpc]
  have hL2 : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) :=
    X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) := by
    simpa [IsL2Quot, oTwoQuot] using hL2.quot
  obtain ⟨e⟩ := hquot
  have hn0' : X.n 0 ≠ 0 := by omega
  have hcard : 4 ≤ Nat.card (GaloisField 2 (X.n 0)) := by
    rw [GaloisField.card (p := 2) (n := X.n 0) hn0']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
  have hsimpleQ : IsSimpleGroup (oTwoQuot ↥(X.L 0)) :=
    e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard)
  exact (QuotientGroup.quotientMulEquivOfEq hqe.symm).isSimpleGroup_congr.mp hsimpleQ

private theorem Q_zero_inf_Q_one_le_L_zero : X.Q 0 ⊓ X.Q 1 ≤ X.L 0 := by
  have hV1E : X.Q 0 ⊓ X.Q 1 ≤ X.edgeSylow 0 :=
    (le_inf ((inf_le_left : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0).trans (X.Q_le_edgeSylow_left 0))
      ((inf_le_right : X.Q 0 ⊓ X.Q 1 ≤ X.Q 1).trans
        (by simpa using X.Q_le_edgeSylow 0))).trans
      (le_of_eq (inf_idem (X.edgeSylow 0)))
  exact le_oTwoPrime_of_isPGroup ((X.isPGroup_edgeSylow 0).to_le hV1E)
    ((inf_le_left : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0).trans (X.Q_le_Gi 0))

private theorem Q_one_le_L_zero : X.Q 1 ≤ X.L 0 := by
  refine le_oTwoPrime_of_isPGroup
    ((X.isPGroup_edgeSylow 0).to_le (X.Q_le_edgeSylow 0)) ?_
  simpa using (X.Q_le_Gi_adj 1).trans inf_le_left

private theorem relCent_le_Q_zero (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    relCent (X.L 0) X.A (X.Q 0) ≤ X.Q 0 := by
  have hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg
  have hQ0comm : ⁅X.Q 0, X.Q 0⁆ ≤ X.A :=
    X.commutator_Q_zero_Q_zero_le_A hc hn0 hs hodd h5 hX hGT hreg
  have hCnorm := X.L_zero_le_normalizer_relCent hA
  haveI hCN : ((relCent (X.L 0) X.A (X.Q 0)).subgroupOf (X.L 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCnorm
  let π : ↥(X.L 0) →* (↥(X.L 0) ⧸ (X.Q 0).subgroupOf (X.L 0)) :=
    QuotientGroup.mk' ((X.Q 0).subgroupOf (X.L 0))
  let Cbar : Subgroup (↥(X.L 0) ⧸ (X.Q 0).subgroupOf (X.L 0)) :=
    ((relCent (X.L 0) X.A (X.Q 0)).subgroupOf (X.L 0)).map π
  haveI hCbarN : Cbar.Normal :=
    Subgroup.Normal.map hCN π (QuotientGroup.mk'_surjective _)
  haveI hsimple := X.isSimpleGroup_quot_L_zero hn0
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Cbar with hbot | htop
  · have hCsub_le : (relCent (X.L 0) X.A (X.Q 0)).subgroupOf (X.L 0) ≤
        (X.Q 0).subgroupOf (X.L 0) := by
      have h := (Subgroup.map_eq_bot_iff
        ((relCent (X.L 0) X.A (X.Q 0)).subgroupOf (X.L 0)) (f := π)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    intro g hg
    have hgL : g ∈ X.L 0 := hg.1
    have hgsub : (⟨g, hgL⟩ : ↥(X.L 0)) ∈
        (relCent (X.L 0) X.A (X.Q 0)).subgroupOf (X.L 0) :=
      Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_subgroupOf.mp (hCsub_le hgsub)
  · have hLC : X.L 0 ≤ relCent (X.L 0) X.A (X.Q 0) := by
      intro n hn
      have hmem : π ⟨n, hn⟩ ∈ Cbar := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hmem
      obtain ⟨q, hq, hcq⟩ :=
        (QuotientGroup.mk'_eq_mk' ((X.Q 0).subgroupOf (X.L 0))).mp hceq
      have hcC : (c : G) ∈ relCent (X.L 0) X.A (X.Q 0) := Subgroup.mem_subgroupOf.mp hc
      have hqQ0 : (q : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hq
      have hqC : (q : G) ∈ relCent (X.L 0) X.A (X.Q 0) :=
        X.Q_zero_le_relCent hA hQ0comm hqQ0
      have hn_eq : (n : G) = (c : G) * (q : G) := by
        have := congrArg Subtype.val hcq.symm
        simpa using this
      have hmemC : (n : G) ∈ relCent (X.L 0) X.A (X.Q 0) := by
        rw [hn_eq]
        exact (relCent (X.L 0) X.A (X.Q 0)).mul_mem hcC hqC
      exact hmemC
    obtain ⟨-, -, -, hnot, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
    have hEZ : X.L 0 ≤ Subgroup.normalizer (X.A : Set G) := (X.L_le_Gi 0).trans hA
    set V1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hV1
    set Vm : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hVm
    have hVmQ0 : Vm ≤ X.Q 0 := by rw [hVm]; exact inf_le_left
    have hV1L : V1 ≤ X.L 0 := by rw [hV1]; exact X.Q_zero_inf_Q_one_le_L_zero
    have hQ1L : X.Q 1 ≤ X.L 0 := X.Q_one_le_L_zero
    have hAVm : X.A ≤ Vm :=
      le_inf X.A_le_Q_zero (inf_le_right : X.A ≤ X.Q (-1))
    have hV1N : V1 ≤ Subgroup.normalizer (Vm : Set G) := by
      refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
      have hleA : ⁅V1, Vm⁆ ≤ X.A := by
        refine Subgroup.commutator_le.mpr ?_
        intro v hv mm hm
        exact ((mem_relCent hEZ).mp (hLC (hV1L hv))).2 mm (hVmQ0 hm)
      exact hleA.trans hAVm
    have hQ1N : X.Q 1 ≤ Subgroup.normalizer (Vm : Set G) := by
      refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
      have hleA : ⁅X.Q 1, Vm⁆ ≤ X.A := by
        refine Subgroup.commutator_le.mpr ?_
        intro q hq mm hm
        exact ((mem_relCent hEZ).mp (hLC (hQ1L hq))).2 mm (hVmQ0 hm)
      exact hleA.trans hAVm
    exact (hnot ⟨hV1N, hQ1N⟩).elim

private theorem fixSet_neg_one_commutator_Q_zero_inf_Q_one {N : Subgroup G}
    (hNK : N ≤ X.Ki 0)
    (hNm : N ≤ Fan86.fixSet G (Γ.neighborSet (X.vert (-1)))) :
    ∀ n ∈ N, ∀ v ∈ X.Q 0 ⊓ X.Q 1, ⁅v, n⁆ ∈ X.A := by
  intro n hn v hv
  have hnKi : n ∈ X.Ki 0 := hNK hn
  have hnfix := Fan86.mem_fixSet.mp (hNm hn)
  have hv0 : v ∈ X.Q 0 := (Subgroup.mem_inf.mp hv).1
  have hv1 : v ∈ X.Q 1 := (Subgroup.mem_inf.mp hv).2
  have hvfix : v • X.vert (-1) = X.vert (-1) :=
    MulAction.mem_stabilizer_iff.mp ((X.Q_le_Gi_adj 0).trans inf_le_left hv0)
  have hvfix' : v⁻¹ • X.vert (-1) = X.vert (-1) := by
    simpa using congrArg (fun z => v⁻¹ • z) hvfix.symm
  have hnfixm2 : n⁻¹ • X.vert (-2) = X.vert (-2) := by
    calc n⁻¹ • X.vert (-2) = n⁻¹ • (n • X.vert (-2)) := by
          rw [X.K_fix n hnKi.1 (-2)]
      _ = X.vert (-2) := by simp
  have hnfix0 : n⁻¹ • X.vert 0 = X.vert 0 := by
    calc n⁻¹ • X.vert 0 = n⁻¹ • (n • X.vert 0) := by rw [X.K_fix n hnKi.1 0]
      _ = X.vert 0 := by simp
  have hvnGm : ⁅v, n⁆ ∈ X.Gi (-1) := by
    have hvG : v ∈ X.Gi (-1) := (X.Q_le_Gi_adj 0).trans inf_le_left hv0
    have hnG : n ∈ X.Gi (-1) := X.K_le_Gi (-1) hnKi.1
    have : v * n * v⁻¹ * n⁻¹ ∈ X.Gi (-1) :=
      (X.Gi (-1)).mul_mem ((X.Gi (-1)).mul_mem ((X.Gi (-1)).mul_mem hvG hnG)
        ((X.Gi (-1)).inv_mem hvG)) ((X.Gi (-1)).inv_mem hnG)
    simpa [commutatorElement_def] using this
  have hvnQ1 : ⁅v, n⁆ ∈ X.Q 1 := by
    have hnv : n * v * n⁻¹ ∈ X.Q 0 ⊓ X.Q 1 :=
      (Subgroup.mem_normalizer_iff.mp (X.Ki_zero_le_normalizer_Q_zero_inf 1 hnKi) v).mp hv
    have heq : v * n * v⁻¹ * n⁻¹ = v * (n * v * n⁻¹)⁻¹ := by group
    change v * n * v⁻¹ * n⁻¹ ∈ X.Q 1
    rw [heq]
    exact (X.Q 1).mul_mem hv1 ((X.Q 1).inv_mem hnv.2)
  have hvn2 : ∃ a : ℕ, ⁅v, n⁆ ^ 2 ^ a = 1 := by
    have hzp : IsPGroup 2 (Subgroup.zpowers ⁅v, n⁆) :=
      (pCoreOf_isPGroup' (X.Gi 1)).to_le (Subgroup.zpowers_le.mpr hvnQ1)
    obtain ⟨a, ha⟩ := hzp ⟨⁅v, n⁆, Subgroup.mem_zpowers _⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hfixm2 : ⁅v, n⁆ • X.vert (-2) = X.vert (-2) := by
    rw [commutatorElement_def]
    calc (v * n * v⁻¹ * n⁻¹) • X.vert (-2)
        = v • (n • (v⁻¹ • (n⁻¹ • X.vert (-2)))) := by simp [mul_smul]
      _ = v • (n • (v⁻¹ • X.vert (-2))) := by rw [hnfixm2]
      _ = v • (v⁻¹ • X.vert (-2)) := by
          rw [hnfix _ (by
            rw [SimpleGraph.mem_neighborSet]
            have h := (X.hyp.adj_smul v⁻¹ (X.vert (-2)) (X.vert (-1))).mpr
              (by simpa using X.adj (-2))
            simpa [hvfix'] using h.symm)]
      _ = X.vert (-2) := by simp
  have hfix0 : ⁅v, n⁆ • X.vert 0 = X.vert 0 := by
    rw [commutatorElement_def]
    calc (v * n * v⁻¹ * n⁻¹) • X.vert 0
        = v • (n • (v⁻¹ • (n⁻¹ • X.vert 0))) := by simp [mul_smul]
      _ = v • (n • (v⁻¹ • X.vert 0)) := by rw [hnfix0]
      _ = v • (v⁻¹ • X.vert 0) := by
          rw [hnfix _ (by
            rw [SimpleGraph.mem_neighborSet]
            have h := (X.hyp.adj_smul v⁻¹ (X.vert 0) (X.vert (-1))).mpr
              (by simpa using (X.adj (-1)).symm)
            simpa [hvfix'] using h.symm)]
      _ = X.vert 0 := by simp
  have hvnQm : ⁅v, n⁆ ∈ X.Q (-1) := by
    refine mem_pCoreOf_of_fixes_two X.hyp hvnGm hvn2 ?_ ?_ ?_ hfixm2 hfix0
    · simpa using (X.adj (-2)).symm
    · simpa using X.adj (-1)
    · intro h; have := X.vert_injective h; omega
  exact Subgroup.mem_inf.mpr ⟨hvnQ1, hvnQm⟩

private theorem fixSet_one_commutator_Q_zero_inf_Q_neg_one {N : Subgroup G}
    (hNK : N ≤ X.Ki 0)
    (hN1 : N ≤ Fan86.fixSet G (Γ.neighborSet (X.vert 1))) :
    ∀ n ∈ N, ∀ mm ∈ X.Q 0 ⊓ X.Q (-1), ⁅mm, n⁆ ∈ X.A := by
  intro n hn mm hm
  have hnKi : n ∈ X.Ki 0 := hNK hn
  have hnfix := Fan86.mem_fixSet.mp (hN1 hn)
  have hm0 : mm ∈ X.Q 0 := (Subgroup.mem_inf.mp hm).1
  have hmm : mm ∈ X.Q (-1) := (Subgroup.mem_inf.mp hm).2
  have hmfix : mm • X.vert 1 = X.vert 1 :=
    MulAction.mem_stabilizer_iff.mp ((X.Q_le_Gi_adj 0).trans inf_le_right hm0)
  have hmfix' : mm⁻¹ • X.vert 1 = X.vert 1 := by
    simpa using congrArg (fun z => mm⁻¹ • z) hmfix.symm
  have hnfix0 : n⁻¹ • X.vert 0 = X.vert 0 := by
    calc n⁻¹ • X.vert 0 = n⁻¹ • (n • X.vert 0) := by rw [X.K_fix n hnKi.1 0]
      _ = X.vert 0 := by simp
  have hnfix2 : n⁻¹ • X.vert 2 = X.vert 2 := by
    calc n⁻¹ • X.vert 2 = n⁻¹ • (n • X.vert 2) := by rw [X.K_fix n hnKi.1 2]
      _ = X.vert 2 := by simp
  have hmnG1 : ⁅mm, n⁆ ∈ X.Gi 1 := by
    have hmG : mm ∈ X.Gi 1 := (X.Q_le_Gi_adj 0).trans inf_le_right hm0
    have hnG : n ∈ X.Gi 1 := X.K_le_Gi 1 hnKi.1
    have : mm * n * mm⁻¹ * n⁻¹ ∈ X.Gi 1 :=
      (X.Gi 1).mul_mem ((X.Gi 1).mul_mem ((X.Gi 1).mul_mem hmG hnG)
        ((X.Gi 1).inv_mem hmG)) ((X.Gi 1).inv_mem hnG)
    simpa [commutatorElement_def] using this
  have hmnQm : ⁅mm, n⁆ ∈ X.Q (-1) := by
    have hnm : n * mm * n⁻¹ ∈ X.Q 0 ⊓ X.Q (-1) :=
      (Subgroup.mem_normalizer_iff.mp (X.Ki_zero_le_normalizer_Q_zero_inf (-1) hnKi)
        mm).mp hm
    have heq : mm * n * mm⁻¹ * n⁻¹ = mm * (n * mm * n⁻¹)⁻¹ := by group
    change mm * n * mm⁻¹ * n⁻¹ ∈ X.Q (-1)
    rw [heq]
    exact (X.Q (-1)).mul_mem hmm ((X.Q (-1)).inv_mem hnm.2)
  have hmn2 : ∃ a : ℕ, ⁅mm, n⁆ ^ 2 ^ a = 1 := by
    have hzp : IsPGroup 2 (Subgroup.zpowers ⁅mm, n⁆) :=
      (pCoreOf_isPGroup' (X.Gi (-1))).to_le (Subgroup.zpowers_le.mpr hmnQm)
    obtain ⟨a, ha⟩ := hzp ⟨⁅mm, n⁆, Subgroup.mem_zpowers _⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hfix0 : ⁅mm, n⁆ • X.vert 0 = X.vert 0 := by
    rw [commutatorElement_def]
    calc (mm * n * mm⁻¹ * n⁻¹) • X.vert 0
        = mm • (n • (mm⁻¹ • (n⁻¹ • X.vert 0))) := by simp [mul_smul]
      _ = mm • (n • (mm⁻¹ • X.vert 0)) := by rw [hnfix0]
      _ = mm • (mm⁻¹ • X.vert 0) := by
          rw [hnfix _ (by
            rw [SimpleGraph.mem_neighborSet]
            have h := (X.hyp.adj_smul mm⁻¹ (X.vert 0) (X.vert 1)).mpr
              (by simpa using X.adj 0)
            simpa [hmfix'] using h.symm)]
      _ = X.vert 0 := by simp
  have hfix2 : ⁅mm, n⁆ • X.vert 2 = X.vert 2 := by
    rw [commutatorElement_def]
    calc (mm * n * mm⁻¹ * n⁻¹) • X.vert 2
        = mm • (n • (mm⁻¹ • (n⁻¹ • X.vert 2))) := by simp [mul_smul]
      _ = mm • (n • (mm⁻¹ • X.vert 2)) := by rw [hnfix2]
      _ = mm • (mm⁻¹ • X.vert 2) := by
          rw [hnfix _ (by
            rw [SimpleGraph.mem_neighborSet]
            have h := (X.hyp.adj_smul mm⁻¹ (X.vert 2) (X.vert 1)).mpr
              (by simpa using (X.adj 1).symm)
            simpa [hmfix'] using h.symm)]
      _ = X.vert 2 := by simp
  have hmmQ1 : ⁅mm, n⁆ ∈ X.Q 1 := by
    refine mem_pCoreOf_of_fixes_two X.hyp hmnG1 hmn2 ?_ ?_ ?_ hfix0 hfix2
    · simpa using (X.adj 0).symm
    · simpa using X.adj 1
    · intro h; have := X.vert_injective h; omega
  exact Subgroup.mem_inf.mpr ⟨hmmQ1, hmnQm⟩

private theorem inf_fixSet_le_relCent (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {N : Subgroup G} (hNK : N ≤ X.Ki 0)
    (hNm : N ≤ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))))
    (hN1 : N ≤ Fan86.fixSet G (Γ.neighborSet (X.vert 1))) :
    N ≤ relCent (X.L 0) X.A (X.Q 0) := by
  have hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg
  obtain ⟨hQ0eq, -, -, -, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  have hNQ1 := X.fixSet_neg_one_commutator_Q_zero_inf_Q_one hNK hNm
  have hNQm := X.fixSet_one_commutator_Q_zero_inf_Q_neg_one hNK hN1
  intro n hn
  rw [mem_relCent ((X.L_le_Gi 0).trans hA)]
  refine ⟨(hNK hn).2, ?_⟩
  intro x hx
  have hx' : x ∈ (↑(X.Q 0 ⊓ X.Q 1) : Set G) * (↑(X.Q 0 ⊓ X.Q (-1)) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (X.Q 0 ⊓ X.Q 1)
      (X.Q 0 ⊓ X.Q (-1)) X.Q_zero_inf_Q_one_le_normalizer_Q_zero_inf_Q_neg_one,
      ← hQ0eq]
    exact hx
  obtain ⟨v, hv, mm, hm, hvm⟩ := Set.mem_mul.mp hx'
  have hvA : ⁅v, n⁆ ∈ X.A := hNQ1 n hn v hv
  have hmA : ⁅mm, n⁆ ∈ X.A := hNQm n hn mm hm
  have hvG0 : v ∈ X.Gi 0 :=
    X.Q_le_Gi 0 ((inf_le_left : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0) hv)
  have hxn : ⁅x, n⁆ ∈ X.A := by
    rw [show x = v * mm from hvm.symm, commutatorElement_mul_left_eq_conj_mul]
    exact (X.A).mul_mem ((Subgroup.mem_normalizer_iff.mp (hA hvG0) _).mp hmA) hvA
  simpa [commutatorElement_inv] using (X.A).inv_mem hxn

private theorem Ki_zero_inf_fixSet_neg_one_le_fixSet_one :
    X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) ≤
      Fan86.fixSet G (Γ.neighborSet (X.vert 1)) := by
  obtain ⟨y, hy, hyv⟩ := X.exists_normalizer_Ki_move
  set N : Subgroup G := X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) with hN
  have hNle : N ≤ X.Ki 0 := by rw [hN]; exact inf_le_left
  have hyK : y ∈ Subgroup.normalizer (X.Ki 0 : Set G) := hy.2
  have hyKi' : y⁻¹ ∈ Subgroup.normalizer (X.Ki 0 : Set G) := Subgroup.inv_mem _ hyK
  have hconjle : conjSub y⁻¹ N ≤ X.Ki 0 := by
    intro g hg
    rw [conjSub, Subgroup.mem_map] at hg
    obtain ⟨n, hn, rfl⟩ := hg
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hyKi' n).mp (hNle hn)
  have hconjfix : conjSub y⁻¹ N ≤ Fan86.fixSet G (Γ.neighborSet (X.vert 1)) := by
    intro g hg
    rw [conjSub, Subgroup.mem_map] at hg
    obtain ⟨n, hn, rfl⟩ := hg
    rw [Fan86.mem_fixSet]
    intro w hw
    have hwadj : Γ.Adj (X.vert (-1)) (y • w) := by
      have h := (X.hyp.adj_smul y (X.vert 1) w).mpr hw
      simpa [hyv] using h
    have hnfix := Fan86.mem_fixSet.mp (Subgroup.mem_inf.mp hn).2 (y • w) hwadj
    change (MulAut.conj y⁻¹ n) • w = w
    rw [MulAut.conj_apply]
    calc (y⁻¹ * n * (y⁻¹)⁻¹) • w = y⁻¹ • (n • (y • w)) := by simp [mul_smul]
      _ = y⁻¹ • (y • w) := by rw [hnfix]
      _ = w := by simp
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (fun x hx => X.L_le_Gi 0 hx.2)
  haveI : IsCyclic ↥(X.Ki 0) := X.isCyclic_Ki 0
  have hcard : Nat.card ↥(N.subgroupOf (X.Ki 0)) =
      Nat.card ↥((conjSub y⁻¹ N).subgroupOf (X.Ki 0)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconjle).toEquiv, card_conjSub]
  have heq : N.subgroupOf (X.Ki 0) = (conjSub y⁻¹ N).subgroupOf (X.Ki 0) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  intro n hn
  have hmem : (⟨n, hNle hn⟩ : ↥(X.Ki 0)) ∈ N.subgroupOf (X.Ki 0) :=
    Subgroup.mem_subgroupOf.mpr hn
  rw [heq] at hmem
  exact hconjfix (Subgroup.mem_subgroupOf.mp hmem)

private theorem Ki_zero_inf_fixSet_neg_one
    (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) = ⊥ := by
  have hrel := X.inf_fixSet_le_relCent hc hn0 hs hodd h5 hX hGT hreg
    (N := X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1)))) inf_le_left inf_le_right
    X.Ki_zero_inf_fixSet_neg_one_le_fixSet_one
  have hleQ : X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) ≤ X.Q 0 :=
    hrel.trans (X.relCent_le_Q_zero hc hn0 hs hodd h5 hX hGT hreg)
  have hKQ : X.K ⊓ X.Q 0 = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (A := X.K) (B := X.Q 0) X.odd_card_K
      (pCoreOf_isPGroup' (X.Gi 0))
  refine le_bot_iff.mp ?_
  calc X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1)))
      ≤ X.K ⊓ X.Q 0 := le_inf (inf_le_left.trans inf_le_left) hleQ
    _ = ⊥ := hKQ

private theorem fixedPointFree_Q_zero_inf_Q_one_mod_A (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G}
    (hk : k ∈ X.Ki 0) (hk1 : k ≠ 1) :
    ∀ v ∈ X.Q 0 ⊓ X.Q 1, ⁅v, k⁆ ∈ X.A → v ∈ X.A := by
  have hKcomm : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a :=
    fun a ha b hb => X.mul_comm_of_mem_K hc hn0 hs hodd h5 hX hGT ha hb
  obtain ⟨c, hcKi, hcs⟩ := X.exists_Ki_smul_eq_of_mem_K hKcomm (-1) hk.1
  have hn1eq : X.n 1 = X.n 0 := X.n_one_eq_n_zero hc hn0 hs hodd h5 hX hGT
  have hnm : 2 ≤ X.n (-1) := by rw [X.n_neg_one, hn1eq]; exact hn0
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hk1
    have hfix : k ∈ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) := by
      rw [Fan86.mem_fixSet]
      intro w hw
      have h := hcs w hw
      rw [hc1, one_smul] at h
      exact h.symm
    have hmem : k ∈ X.Ki 0 ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert (-1))) :=
      Subgroup.mem_inf.mpr ⟨hk, hfix⟩
    rw [X.Ki_zero_inf_fixSet_neg_one hc hn0 hs hodd h5 hX hGT hreg] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfixpts : ∀ a : V, Γ.Adj (X.vert (-1)) a →
      (c • a = a ↔ a = X.vert (-2) ∨ a = X.vert 0) := by
    intro a ha
    have h := X.torus_fixed (-1) hnm hcKi hc1 a ha
    simpa [show (-1 : ℤ) - 1 = -2 by norm_num,
      show (-1 : ℤ) + 1 = 0 by norm_num] using h
  intro v hv hvA
  have hv0 : v ∈ X.Q 0 := (Subgroup.mem_inf.mp hv).1
  have hv1 : v ∈ X.Q 1 := (Subgroup.mem_inf.mp hv).2
  have hvGm : v ∈ X.Gi (-1) := (X.Q_le_Gi_adj 0).trans inf_le_left hv0
  have hvG0 : v ∈ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left hv1
  have hvkQm : ⁅v, k⁆ ∈ X.Q (-1) := (inf_le_right : X.A ≤ X.Q (-1)) hvA
  have hwadj : Γ.Adj (X.vert (-1)) (v • X.vert (-2)) := by
    have hvfix : v • X.vert (-1) = X.vert (-1) := MulAction.mem_stabilizer_iff.mp hvGm
    have h := (X.hyp.adj_smul v (X.vert (-2)) (X.vert (-1))).mpr
      (by simpa using X.adj (-2))
    simpa [hvfix] using h.symm
  have hkfix_w : k • (v • X.vert (-2)) = v • X.vert (-2) := by
    have hzadj : Γ.Adj (X.vert (-1)) (k • (v • X.vert (-2))) := by
      have hkfix : k • X.vert (-1) = X.vert (-1) := X.K_fix k hk.1 (-1)
      have h := (X.hyp.adj_smul k (v • X.vert (-2)) (X.vert (-1))).mpr hwadj.symm
      simpa [hkfix] using h.symm
    have hzfix : ⁅v, k⁆ • (k • (v • X.vert (-2))) = k • (v • X.vert (-2)) :=
      X.Q_fixes_neighbors_vert (-1) _ hzadj _ hvkQm
    have hcommz : ⁅v, k⁆ • (k • (v • X.vert (-2))) = v • X.vert (-2) := by
      rw [commutatorElement_def]
      simp only [mul_smul, inv_smul_smul]
      rw [X.K_fix k hk.1 (-2)]
    exact hzfix.symm.trans hcommz
  have hcw : c • (v • X.vert (-2)) = v • X.vert (-2) :=
    (hcs _ hwadj).trans hkfix_w
  have hvm2 : v • X.vert (-2) = X.vert (-2) := by
    rcases (hfixpts _ hwadj).mp hcw with h | h
    · exact h
    · exfalso
      have hvfix0 : v • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hvG0
      have hEq : X.vert (-2) = X.vert 0 := by
        calc X.vert (-2) = v⁻¹ • (v • X.vert (-2)) := by simp
          _ = v⁻¹ • X.vert 0 := by rw [h]
          _ = X.vert 0 := by
              have := congrArg (fun z => v⁻¹ • z) hvfix0
              simpa using this.symm
      have := X.vert_injective hEq
      omega
  have hvm0 : v • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hvG0
  have hv2 : ∃ a : ℕ, v ^ 2 ^ a = 1 := by
    have hzp : IsPGroup 2 (Subgroup.zpowers v) :=
      (pCoreOf_isPGroup' (X.Gi 0)).to_le (Subgroup.zpowers_le.mpr hv0)
    obtain ⟨a, ha⟩ := hzp ⟨v, Subgroup.mem_zpowers v⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hvmQm : v ∈ X.Q (-1) := by
    refine mem_pCoreOf_of_fixes_two X.hyp hvGm hv2 (by simpa using (X.adj (-2)).symm)
      (by simpa using X.adj (-1)) ?_ hvm2 hvm0
    intro h; have := X.vert_injective h; omega
  exact Subgroup.mem_inf.mpr ⟨hv1, hvmQm⟩

private theorem commutator_left_mem_A_of_mul {v mm k : G}
    (hv : v ∈ X.Q 0 ⊓ X.Q 1) (hm : mm ∈ X.Q 0 ⊓ X.Q (-1))
    (hk : k ∈ X.Ki 0) (h : ⁅v * mm, k⁆ ∈ X.A) : ⁅v, k⁆ ∈ X.A := by
  set V1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hV1
  set Vm : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hVm
  have hAV1 : X.A ≤ V1 := by
    rw [hV1]
    exact le_inf X.A_le_Q_zero (inf_le_left : X.A ≤ X.Q 1)
  have hmmk : ⁅mm, k⁆ ∈ Vm := by
    have hconj : k * mm * k⁻¹ ∈ Vm :=
      (Subgroup.mem_normalizer_iff.mp (X.Ki_zero_le_normalizer_Q_zero_inf (-1) hk) mm).mp hm
    have h1 : ⁅k, mm⁆ ∈ Vm := Vm.mul_mem hconj (Vm.inv_mem hm)
    have h := Vm.inv_mem h1
    simpa [commutatorElement_inv] using h
  have hconjV : v * ⁅mm, k⁆ * v⁻¹ ∈ Vm :=
    (Subgroup.mem_normalizer_iff.mp
      (X.Q_zero_inf_Q_one_le_normalizer_Q_zero_inf_Q_neg_one hv) _).mp hmmk
  have hformula : ⁅v * mm, k⁆ = v * ⁅mm, k⁆ * v⁻¹ * ⁅v, k⁆ :=
    commutatorElement_mul_left_eq_conj_mul v mm k
  have hvk_V1 : ⁅v, k⁆ ∈ V1 := by
    have hkv : k * v * k⁻¹ ∈ V1 :=
      (Subgroup.mem_normalizer_iff.mp (X.Ki_zero_le_normalizer_Q_zero_inf 1 hk) v).mp hv
    have heq : v * k * v⁻¹ * k⁻¹ = v * (k * v * k⁻¹)⁻¹ := by group
    change v * k * v⁻¹ * k⁻¹ ∈ V1
    rw [heq]
    exact V1.mul_mem hv (V1.inv_mem hkv)
  have hmemV1 : v * ⁅mm, k⁆ * v⁻¹ ∈ V1 := by
    have heq : v * ⁅mm, k⁆ * v⁻¹ = ⁅v * mm, k⁆ * ⁅v, k⁆⁻¹ := by
      rw [hformula]; group
    rw [heq]
    exact V1.mul_mem (hAV1 h) (V1.inv_mem hvk_V1)
  have hconjV_A : v * ⁅mm, k⁆ * v⁻¹ ∈ X.A := by
    have hinf : v * ⁅mm, k⁆ * v⁻¹ ∈ V1 ⊓ Vm :=
      Subgroup.mem_inf.mpr ⟨hmemV1, hconjV⟩
    rwa [X.Q_zero_inf_Q_one_inf_Q_zero_inf_Q_neg_one_eq_A] at hinf
  have hmem : (v * ⁅mm, k⁆ * v⁻¹)⁻¹ * ⁅v * mm, k⁆ ∈ X.A :=
    (X.A).mul_mem ((X.A).inv_mem hconjV_A) h
  have heq : ⁅v, k⁆ = (v * ⁅mm, k⁆ * v⁻¹)⁻¹ * ⁅v * mm, k⁆ := by
    rw [hformula]; group
  rwa [heq]

private theorem commutator_right_mem_A_of_mul
    (hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G)) {v mm k : G}
    (hv : v ∈ X.Gi 0) (hvk : ⁅v, k⁆ ∈ X.A) (h : ⁅v * mm, k⁆ ∈ X.A) :
    ⁅mm, k⁆ ∈ X.A := by
  have hformula : ⁅v * mm, k⁆ = v * ⁅mm, k⁆ * v⁻¹ * ⁅v, k⁆ :=
    commutatorElement_mul_left_eq_conj_mul v mm k
  have hprod : ⁅v * mm, k⁆ * ⁅v, k⁆⁻¹ ∈ X.A :=
    (X.A).mul_mem h ((X.A).inv_mem hvk)
  have hconjA : v⁻¹ * (⁅v * mm, k⁆ * ⁅v, k⁆⁻¹) * v ∈ X.A := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (hA ((X.Gi 0).inv_mem hv)) _).mp hprod
    simpa using h
  have heq : ⁅mm, k⁆ = v⁻¹ * (⁅v * mm, k⁆ * ⁅v, k⁆⁻¹) * v := by
    rw [hformula]; group
  rwa [heq]

private theorem fixedPointFree_of_mem_Ki_zero (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G}
    (hk : k ∈ X.Ki 0) (hk1 : k ≠ 1) :
    ∀ x ∈ X.Q 0, ⁅x, k⁆ ∈ X.A → x ∈ X.A := by
  intro x hxQ hxcomm
  have hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg
  obtain ⟨hQ0eq, -, -, -, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  set V1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hV1
  set Vm : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hVm
  have hV1Q0 : V1 ≤ X.Q 0 := by rw [hV1]; exact inf_le_left
  have hx' : x ∈ (↑V1 : Set G) * (↑Vm : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V1 Vm
      (by rw [hV1, hVm]; exact X.Q_zero_inf_Q_one_le_normalizer_Q_zero_inf_Q_neg_one),
      ← hQ0eq]
    exact hxQ
  obtain ⟨v, hv, mm, hm, hvm⟩ := Set.mem_mul.mp hx'
  have hvG0 : v ∈ X.Gi 0 := X.Q_le_Gi 0 (hV1Q0 hv)
  have hvcomm : ⁅v, k⁆ ∈ X.A :=
    X.commutator_left_mem_A_of_mul hv hm hk (by simpa [← hvm] using hxcomm)
  have hvA : v ∈ X.A :=
    X.fixedPointFree_Q_zero_inf_Q_one_mod_A hc hn0 hs hodd h5 hX hGT hreg hk hk1 v hv
      hvcomm
  have hmmcomm : ⁅mm, k⁆ ∈ X.A :=
    X.commutator_right_mem_A_of_mul hA hvG0 hvcomm (by simpa [← hvm] using hxcomm)
  obtain ⟨y, hy, hV1y⟩ := X.exists_conj_Q_zero_inf_Q_one
  have hyK : y ∈ Subgroup.normalizer (X.Ki 0 : Set G) := hy.2
  have hyG0 : y ∈ X.Gi 0 := X.L_le_Gi 0 hy.1
  have hV1y' : conjSub y⁻¹ Vm = V1 := by
    rw [hVm, hV1, ← hV1y]
    exact conjSub_conjSub_inv y (X.Q 0 ⊓ X.Q 1)
  have hx'V1 : y⁻¹ * mm * y ∈ V1 := by
    have h := mul_mem_conjSub (g := y⁻¹) (H := Vm) hm
    rw [hV1y'] at h
    simpa using h
  have hconjmm : ⁅y⁻¹ * mm * y, y⁻¹ * k * y⁆ ∈ X.A := by
    have hleft : y⁻¹ * ⁅mm, k⁆ * y ∈ X.A := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (hA (Subgroup.inv_mem _ hyG0)) _).mp hmmcomm
    have heq : ⁅y⁻¹ * mm * y, y⁻¹ * k * y⁆ = y⁻¹ * ⁅mm, k⁆ * y := by
      simpa using (conjugate_commutatorElement (g₁ := mm) (g₂ := k) (g₃ := y⁻¹)).symm
    rw [heq]
    exact hleft
  have hk' : y⁻¹ * k * y ∈ X.Ki 0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyK) k).mp hk
    simpa using this
  have hk'1 : y⁻¹ * k * y ≠ 1 := by
    intro h
    apply hk1
    have hk_eq : k = 1 := by
      have hy1 : y * (y⁻¹ * k * y) * y⁻¹ = 1 := by rw [h]; group
      calc k = y * (y⁻¹ * k * y) * y⁻¹ := by group
        _ = 1 := hy1
    exact hk_eq
  have hmmA : y⁻¹ * mm * y ∈ X.A :=
    X.fixedPointFree_Q_zero_inf_Q_one_mod_A hc hn0 hs hodd h5 hX hGT hreg hk' hk'1
      (y⁻¹ * mm * y) hx'V1 hconjmm
  have hmmA' : mm ∈ X.A := by
    have h := (Subgroup.mem_normalizer_iff.mp (hA hyG0) (y⁻¹ * mm * y)).mp hmmA
    have heq : y * (y⁻¹ * mm * y) * y⁻¹ = mm := by group
    rwa [heq] at h
  rw [show x = v * mm from hvm.symm]
  exact (X.A).mul_mem hvA hmmA'

theorem fixedPointFree_Ki_zero (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ x ∈ X.Q 0, (∀ k ∈ X.Ki 0, ⁅x, k⁆ ∈ X.A) → x ∈ X.A := by
  intro x hxQ hxcomm
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (fun x hx => X.L_le_Gi 0 hx.2)
  have hcard : Nat.card ↥(X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  have h3 : 3 ≤ Nat.card ↥(X.Ki 0) := by
    rw [hcard]
    have h4 : 4 ≤ 2 ^ X.n 0 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
    omega
  have hne : X.Ki 0 ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot (X.Ki 0)).mp (by omega)
  obtain ⟨k, hk, hk1⟩ := (Subgroup.bot_or_exists_ne_one (X.Ki 0)).resolve_left hne
  exact X.fixedPointFree_of_mem_Ki_zero hc hn0 hs hodd h5 hX hGT hreg hk hk1 x hxQ
    (hxcomm k hk)

theorem Q_eq_commutator_sup (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Q 0 = ⁅X.Q 0, X.Ki 0⁆ ⊔ X.A := by
  have hA : X.Gi 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg
  have hAQ0 : X.A ≤ X.Q 0 := X.A_le_Q_zero
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (fun x hx => X.L_le_Gi 0 hx.2)
  have hcard : Nat.card ↥(X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  have hne : X.Ki 0 ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(X.Ki 0) = 1 := by rw [hbot]; simp
    rw [hcard] at h1
    have h4 : 4 ≤ 2 ^ X.n 0 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
    omega
  obtain ⟨k, hk, hkne⟩ := (Subgroup.bot_or_exists_ne_one (X.Ki 0)).resolve_left hne
  have hkG0 : k ∈ X.Gi 0 := X.L_le_Gi 0 hk.2
  have hkN : k ∈ Subgroup.normalizer (X.A : Set G) := hA hkG0
  have hfree : ∀ r ∈ X.Q 0, ⁅k, r⁆ ∈ X.A → r ∈ X.A := by
    intro r hr hkr
    apply X.fixedPointFree_of_mem_Ki_zero hc hn0 hs hodd h5 hX hGT hreg hk hkne r hr
    simpa [commutatorElement_inv] using (X.A).inv_mem hkr
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  have hkQ : k ∈ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hkG0
  have hex := exists_commutator_mul_of_fixedPointFree hAQ0
    ((X.Q_le_Gi 0).trans hA) hkQ hkN hfree
  have hcomm_le : ⁅X.Q 0, X.Ki 0⁆ ≤ X.Q 0 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp fun k' hk' =>
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (X.L_le_Gi 0 hk'.2)
  refine le_antisymm ?_ (sup_le hcomm_le hAQ0)
  intro u hu
  obtain ⟨v, hv, w, hw, rfl⟩ := hex u hu
  have hmem : ⁅v, k⁆ ∈ ⁅X.Q 0, X.Ki 0⁆ :=
    Subgroup.commutator_mem_commutator hv hk
  have hfin := (⁅X.Q 0, X.Ki 0⁆).inv_mem hmem
  have hmem' : ⁅k, v⁆ ∈ ⁅X.Q 0, X.Ki 0⁆ := by
    simpa [commutatorElement_inv] using hfin
  exact Subgroup.mul_mem_sup hmem' hw

theorem D_le_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.D ≤ X.A := by
  intro x hx
  rw [Setup.D] at hx
  have hxQ : x ∈ X.Q 0 := (Subgroup.mem_inf.mp hx).1
  have hxcent : x ∈ Subgroup.centralizer (X.Ki 0 : Set G) := (Subgroup.mem_inf.mp hx).2
  apply X.fixedPointFree_Ki_zero hc hn0 hs hodd h5 hX hGT hreg x hxQ
  intro k hk
  have hcomm : ⁅x, k⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp hxcent k hk).symm
  rw [hcomm]
  exact X.A.one_mem

end Setup

end CFSG.Quasithin.St84

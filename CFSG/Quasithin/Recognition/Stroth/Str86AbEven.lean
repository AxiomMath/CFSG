module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd
import CFSG.Quasithin.Recognition.F112Crit.Lemma65
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

@[expose] def Str86E1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F]
    [Finite F], Str86AbHyp L1 L2 S k m F → ∀ g : G,
    Z2 L1 L2 S ≤ MulAut.conj g • S → MulAut.conj g • Z2 L1 L2 S ≤ S →
    ¬ Z2 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S →
    ¬ MulAut.conj g • Z2 L1 L2 S ≤ Q2 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊔ Q2 L1 L2 S = S ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2 ∧ Nat.card (Z1 L1 L2 S) = 2 ^ m ∧
      ⁅Z2 L1 L2 S, MulAut.conj g • Z2 L1 L2 S⁆ = Z1 L1 L2 S ∧
      MulAut.conj g • Z1 L1 L2 S = Z1 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊓ Q2 L1 L2 S = Z1 L1 L2 S ∧
      ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S

variable {G : Type} [Group G] [Finite G]

theorem str86_critPath_e1 {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb : Even (str86CritB L1 L2 S)) (hb2 : 2 ≤ str86CritB L1 L2 S) :
    ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 0)) ∧
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) =
        omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))) ∧
      ⁅Vv (Z2 L1 L2 S) (lam 0), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ =
        omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) ∧
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 0)) =
        omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) ∧
      ⁅Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)),
          pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))⁆ =
        omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))) ∧
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊔ pCoreOf 2 (stab (lam 0)) =
        pCoreOf 2 (stab (lam 0) ⊓ stab (lam 1)) ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2 ∧ Nat.card (Z1 L1 L2 S) = 2 ^ m := by
  have hc := hI.critHypN
  obtain ⟨hGL1, -, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨h0, h1, hS0, hV0, -⟩ := str86_base_values hI
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
  obtain ⟨-, x, hx0, hx1⟩ := hP.smul hI
  have hb1 : 1 ≤ str86CritB L1 L2 S := by omega
  have hvb : vtype (lam (str86CritB L1 L2 S)) = false := hP.vtype_of_even hI le_rfl hb
  have hadjb : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [Nat.sub_add_cancel hb1] at h
  obtain ⟨y, hyb, hyb1⟩ := F112Crit.exists_edge_conj hvb
    (show lam (str86CritB L1 L2 S - 1) ∈ nbrs (lam (str86CritB L1 L2 S)) from hadjb.symm)
  have hQx0 : pCoreOf 2 (stab (lam 0)) = conjSub (x : G) (Q2 L1 L2 S) := by
    rw [hx0, (str86_vertex_smul hI x _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1, h0]
  have hQy0 : pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) = conjSub (y : G) (Q2 L1 L2 S) := by
    rw [hyb, (str86_vertex_smul hI y _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1, h0]
  have hQx1 : pCoreOf 2 (stab (lam 1)) = conjSub (x : G) (Q1 L1 L2 S) := by
    rw [hx1, (str86_vertex_smul hI x _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1, h1]
  have hQy1 : pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) =
      conjSub (y : G) (Q1 L1 L2 S) := by
    rw [hyb1, (str86_vertex_smul hI y _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1, h1]
  have hZx1 : omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) = conjSub (x : G) (Z1 L1 L2 S) := by
    rw [hx1, (str86_vertex_smul hI x _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.1, h1]
  have hZy1 : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))) =
      conjSub (y : G) (Z1 L1 L2 S) := by
    rw [hyb1, (str86_vertex_smul hI y _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.1, h1]
  have hVx : Vv (Z2 L1 L2 S) (lam 0) = conjSub (x : G) (Z2 L1 L2 S) := by
    rw [hx0, CosetGeom.Vv_smul_γ₀ hc.normalizes]
  have hVy : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) = conjSub (y : G) (Z2 L1 L2 S) := by
    rw [hyb, CosetGeom.Vv_smul_γ₀ hc.normalizes]
  have hSx : pCoreOf 2 (stab (lam 0) ⊓ stab (lam 1)) = conjSub (x : G) S := by
    rw [hx0, hx1, (str86_vertex_smul hI x _ _).2.2.1, hS0]
  have hSy : pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)) ⊓ stab (lam (str86CritB L1 L2 S))) =
      conjSub (y : G) S := by
    rw [hyb, hyb1, inf_comm, (str86_vertex_smul hI y _ _).2.2.1, hS0]
  set g : G := (x : G)⁻¹ * y with hg
  have hy : (y : G) = x * g := by rw [hg]; group
  have hcy : ∀ H : Subgroup G, conjSub (y : G) H = conjSub (x : G) (conjSub g H) := fun H => by
    rw [hy, conjSub_mul]
  have hn0 : lam 0 ∈ nbrs (lam 1) := (hP.isGeo.adj (i := 0) (by omega)).symm
  have hgZ : Z2 L1 L2 S ≤ MulAut.conj g • S := by
    have h := (hGL1 (lam 0) (lam (str86CritB L1 L2 S - 1)) hP.linear (by
      rw [hP.isGeo 0 _ (Nat.zero_le _) (by omega)]; omega)).trans
      (str86_pCoreOf_le_pCoreOf_inf hI hadjb)
    rw [hVx, hSy, hcy, F112Crit.conjSub_le_conjSub_iff, str86_conjSub_eq_smul] at h
    exact h
  have hZg : MulAut.conj g • Z2 L1 L2 S ≤ S := by
    have h := (hGL1 (lam (str86CritB L1 L2 S)) (lam 1) hvb (by
      rw [CosetGeom.dist_comm, hP.isGeo 1 _ (by omega) le_rfl]; omega)).trans
      ((str86_pCoreOf_le_pCoreOf_inf hI hn0).trans (le_of_eq (by rw [inf_comm])))
    rw [hVy, hSx, hcy, F112Crit.conjSub_le_conjSub_iff, str86_conjSub_eq_smul] at h
    exact h
  have hnc : ¬ Z2 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S := by
    intro h
    apply hP.critical
    rw [hVx, hQy0, hcy, F112Crit.conjSub_le_conjSub_iff, str86_conjSub_eq_smul]
    exact h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, -⟩ := hE1 G L1 L2 S k m F hI g hgZ hZg hnc
  simp only [← str86_conjSub_eq_smul] at e1 e2 e5 e6 e7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, e3, e4⟩
  · rw [hVy, hQx0, hcy, F112Crit.conjSub_le_conjSub_iff]
    exact e1
  · rw [hZx1, hZy1, hcy, e6]
  · rw [hVx, hVy, hcy, conjSub_commutator, e5, hZx1]
  · rw [hVy, hQx0, hcy, ← conjSub_inf, e7, hZx1]
  · obtain ⟨-, -, -, -, -, -, -, e8⟩ := hE1 G L1 L2 S k m F hI g hgZ hZg hnc
    rw [hVy, hZy1, hQy1, conjSub_commutator, e8]
  · rw [hVy, hQx0, hSx, hcy, ← conjSub_sup, e2]

theorem Str86CritPath.reverse {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb : Even (str86CritB L1 L2 S)) (hb2 : 2 ≤ str86CritB L1 L2 S) :
    Str86CritPath L1 L2 S (fun i => lam (str86CritB L1 L2 S - i)) := by
  refine ⟨?_, fun i j hij hj => ?_, ?_⟩
  · show vtype (lam (str86CritB L1 L2 S - 0)) = false
    rw [Nat.sub_zero]
    exact hP.vtype_of_even hI le_rfl hb
  · show CosetGeom.dist (lam (str86CritB L1 L2 S - i)) (lam (str86CritB L1 L2 S - j)) = j - i
    rw [CosetGeom.dist_comm, hP.isGeo _ _ (by omega) (by omega)]
    omega
  · show ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S - 0)) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - str86CritB L1 L2 S)))
    rw [Nat.sub_zero, Nat.sub_self]
    exact (str86_critPath_e1 hE1 hI hP hb hb2).1

theorem card_sup_of_inf_eq_bot {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hbot : H ⊓ K = ⊥) : Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have h1 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hHK).2
  rw [hbot, Subgroup.relIndex_bot_left] at h1
  have h2 := Subgroup.relIndex_mul_card K (H ⊔ K)
  rw [inf_eq_left.mpr (le_sup_right : K ≤ H ⊔ K), h1] at h2
  exact h2.symm

theorem str86_Vv_eq_sup_of_ne {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2) (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ m)
    {δ ε ε' : Str86Γ L1 L2 S} (hδ : vtype δ = false) (hε : ε ∈ nbrs δ) (hε' : ε' ∈ nbrs δ)
    (hne : ε ≠ ε') :
    Vv (Z2 L1 L2 S) δ =
      omegaOneCenterOf (pCoreOf 2 (stab ε)) ⊔ omegaOneCenterOf (pCoreOf 2 (stab ε')) := by
  have hc := hI.critHypN
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨-, h1, -, -, -⟩ := str86_base_values hI
  have hεt := F112Crit.vtype_eq_true_of_mem_nbrs hδ hε
  have hε't := F112Crit.vtype_eq_true_of_mem_nbrs hδ hε'
  have hle : ∀ γ : Str86Γ L1 L2 S, γ ∈ nbrs δ → vtype γ = true →
      omegaOneCenterOf (pCoreOf 2 (stab γ)) ≤ Vv (Z2 L1 L2 S) δ := fun γ hγ hγt =>
    (str86_edge_facts hI hγt (show δ ∈ nbrs γ from
      (show (graph _ _ _).Adj δ γ from hγ).symm)).1
  have hcard1 : ∀ γ : Str86Γ L1 L2 S, vtype γ = true →
      Nat.card (omegaOneCenterOf (pCoreOf 2 (stab γ))) = 2 ^ m := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hγ
    rw [(str86_vertex_smul hI g _ (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.1, h1,
      CosetGeom.card_conjSub]
    exact hZ1
  have hcardδ : Nat.card (Vv (Z2 L1 L2 S) δ) = (2 ^ m) ^ 2 := by
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
    rw [CosetGeom.Vv_smul_γ₀ hc.normalizes, CosetGeom.card_conjSub]
    exact hZ2
  have hE : IsElemAbelian 2 (Vv (Z2 L1 L2 S) δ) := by
    rw [hD41 δ hδ]
    exact SmithC27.isElemAbelian_omegaOneCenterOf _
  have hN : omegaOneCenterOf (pCoreOf 2 (stab ε)) ≤
      Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (stab ε')) : Set G) := by
    refine le_trans (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (Subgroup.centralizer_le_normalizer _)
    exact congrArg Subtype.val
      (hE.1.is_comm.comm ⟨y, hle ε' hε' hε't hy⟩ ⟨x, hle ε hε hεt hx⟩)
  have hbot := (str86_graph_F1 hI).1 δ ε ε' hδ hε hε' hne
  have hsup : omegaOneCenterOf (pCoreOf 2 (stab ε)) ⊔ omegaOneCenterOf (pCoreOf 2 (stab ε')) ≤
      Vv (Z2 L1 L2 S) δ := sup_le (hle ε hε hεt) (hle ε' hε' hε't)
  refine (Subgroup.eq_of_le_of_card_ge hsup ?_).symm
  rw [card_sup_of_inf_eq_bot hN hbot, hcard1 ε hεt, hcard1 ε' hε't, hcardδ, pow_two]

theorem str86_critB_ne_four {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F) :
    str86CritB L1 L2 S ≠ 4 := by
  intro hb
  obtain ⟨lam, hP, -, -⟩ := str86_exists_critPath hI
  have hev : Even (str86CritB L1 L2 S) := by rw [hb]; decide
  obtain ⟨-, hZ, -⟩ := str86_critPath_e1 hE1 hI hP hev (by omega)
  have h3 : str86CritB L1 L2 S - 1 = 3 := by omega
  rw [h3] at hZ
  have hv2 : vtype (lam 2) = false := hP.vtype_of_even hI (by omega) even_two
  have hv1 : vtype (lam 1) = true := hP.vtype_of_odd hI (by omega) odd_one
  have hn21 : lam 1 ∈ nbrs (lam 2) := (hP.isGeo.adj (i := 1) (by omega)).symm
  have hn23 : lam 3 ∈ nbrs (lam 2) := hP.isGeo.adj (i := 2) (by omega)
  have hne : lam 1 ≠ lam 3 := hP.isGeo.ne (by omega) (by omega)
  have hbot := (str86_graph_F1 hI).1 (lam 2) (lam 1) (lam 3) hv2 hn21 hn23 hne
  rw [← hZ, inf_idem] at hbot
  exact (str86_edge_facts hI hv1 ((hP.isGeo.adj (i := 0) (by omega)).symm)).2.2.2.2.2.1 hbot

theorem str86_critB_ne_six {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F) :
    str86CritB L1 L2 S ≠ 6 := by
  intro hb
  obtain ⟨lam, hP, -, -⟩ := str86_exists_critPath hI
  have hev : Even (str86CritB L1 L2 S) := by rw [hb]; decide
  obtain ⟨-, hZ, -, -, -, -, hc2, hc1⟩ := str86_critPath_e1 hE1 hI hP hev (by omega)
  have h5 : str86CritB L1 L2 S - 1 = 5 := by omega
  rw [h5] at hZ
  have hadj : ∀ i, i < 6 → (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam i)
      (lam (i + 1)) := fun i hi => hP.isGeo.adj (by omega)
  have hv2 : vtype (lam 2) = false := hP.vtype_of_even hI (by omega) even_two
  have hv4 : vtype (lam 4) = false := hP.vtype_of_even hI (by omega) ⟨2, rfl⟩
  have hv3 : vtype (lam 3) = true := hP.vtype_of_odd hI (by omega) ⟨1, rfl⟩
  have hV2 := str86_Vv_eq_sup_of_ne hI hc2 hc1 hv2 (hadj 1 (by omega)).symm (hadj 2 (by omega))
    (hP.isGeo.ne (show 1 < 3 by norm_num) (by omega))
  have hV4 := str86_Vv_eq_sup_of_ne hI hc2 hc1 hv4 (hadj 4 (by omega)) (hadj 3 (by omega)).symm
    (hP.isGeo.ne (show 3 < 5 by norm_num) (by omega)).symm
  have heq : Vv (Z2 L1 L2 S) (lam 2) = Vv (Z2 L1 L2 S) (lam 4) := by
    rw [hV2, hV4, hZ]
  exact (str86_graph_F1 hI).2 (lam 3) (lam 2) (lam 4) hv3 (hadj 2 (by omega)).symm
    (hadj 3 (by omega)) (hP.isGeo.ne (by omega) (by omega)) heq

end CFSG.Quasithin.Stroth

end

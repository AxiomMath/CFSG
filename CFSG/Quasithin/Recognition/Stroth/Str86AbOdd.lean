module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.Stroth.Str86AbBase
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2E1
import CFSG.Quasithin.Recognition.F112Crit.Lemma65
import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UCent
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

@[expose] def Str86UnitaryM6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F]
    [Finite F], Str86AbHyp L1 L2 S k m F → Z2 L1 L2 S ≤ Q1 L1 L2 S →
    ∀ t ∈ P1 L1 L2 S, t ∉ Q1 L1 L2 S → t * t = 1 →
      (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (conjClosure (Z2 L1 L2 S) L1)

@[expose] def Str86LemmaW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F]
    [Finite F], Str86AbHyp L1 L2 S k m F → Z2 L1 L2 S ≤ Q1 L1 L2 S →
    ∀ t ∈ P1 L1 L2 S, t ∉ Q1 L1 L2 S → t * t = 1 →
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (conjClosure (Z2 L1 L2 S) L1) ≤ (2 ^ k) ^ 3 → 2 * k ≤ m

variable {G : Type} [Group G] [Finite G]

theorem Str86CritPath.vtype_of_even {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam) {i : ℕ}
    (hi : i ≤ str86CritB L1 L2 S) (he : Even i) : vtype (lam i) = false :=
  CosetGeom.IsGeo.vtype_false_of_even_start hI.critHypN.amalgam.gen hP.isGeo hP.linear hi he

theorem Str86CritPath.vtype_of_odd {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam) {i : ℕ}
    (hi : i ≤ str86CritB L1 L2 S) (ho : Odd i) : vtype (lam i) = true :=
  CosetGeom.IsGeo.vtype_true_of_odd_start hI.critHypN.amalgam.gen hP.isGeo hP.linear hi ho

theorem str86_pCoreOf_le_pCoreOf_inf {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {δ ε : Str86Γ L1 L2 S} (hε : ε ∈ nbrs δ) :
    pCoreOf 2 (stab δ) ≤ pCoreOf 2 (stab δ ⊓ stab ε) :=
  (str86_graph_TI hI).1 δ ε hε _ (pCoreOf_isPGroup 2 _) (le_inf (pCoreOf_le 2 _)
    ((CosetGeom.pCoreOf_stab_le_ballStab_one hI.critHypN.amalgam δ).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hε).le)))

theorem str86_conj_s_inf_centralizer_le_q1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {g : G}
    (hg : g ∈ P1 L1 L2 S) :
    MulAut.conj g • S ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) ≤
      Q1 L1 L2 S := by
  classical
  have hF := hI.hF
  obtain ⟨-, hP1V, -⟩ := str86_conjClosure_frame hI hZQ
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB
      (Or.inr (Or.inl ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩))
  have hSH : S ≤ L1 ⊔ Q1 L1 L2 S :=
    hS1.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hLS : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
    le_antisymm (sup_le le_sup_left hSH) (sup_le le_sup_left (hQ1S.trans le_sup_right))
  have hHP : L1 ⊔ Q1 L1 L2 S ≤ P1 L1 L2 S := sup_le le_sup_left (pCoreOf_le 2 _)
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hgS2 : IsPGroup 2 (MulAut.conj g • S : Subgroup G) := by
    rw [← str86_conjSub_eq_smul]
    exact F7.isPGroup_conjSub hF.1.h1.pgroup
  have hgSP : MulAut.conj g • S ≤ P1 L1 L2 S := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ S := mem_conj_smul_iff'.mp hx
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).mul_mem hg (hBP (hSB' hx')))
      ((P1 L1 L2 S).inv_mem hg)
  have hgSH : MulAut.conj g • S ≤ L1 ⊔ Q1 L1 L2 S :=
    ((str86_le_lhat_of_isPGroup hI hgS2).1 hgSP).trans hLS.le
  have hHQ1 : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hHP.trans (le_normalizer_pCoreOf 2 _)
  have hHNC : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer
      (((L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :
        Subgroup G) : Set G) := fun x hx =>
    A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((hHP.trans (hP1V.trans (F7.normalizer_le_normalizer_centralizer _))) hx)
  have hK : ((L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G)) ⊔
      Q1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S := sup_le inf_le_left le_sup_right
  have hKn : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer
      ((((L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G)) ⊔
        Q1 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hHNC hHQ1
  have hpH : pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) = Q1 L1 L2 S := pCoreOf_sup_pCoreOf hF.1
  have hQK : pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) ≤
      ((L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G)) ⊔
        Q1 L1 L2 S := hpH.le.trans le_sup_right
  have hqLhat : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) (2 ^ k) := by
    refine Or.inr ⟨k, hI.hk, rfl, F, inferInstance, inferInstance, hI.hFc, ?_⟩
    rcases hI.hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  rcases eq_or_mem_pCoreOf_of_normal hqLhat hK hKn hQK with h | h
  ·
    exfalso
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    have hlt : L1 ⊓ bigB L1 L2 S < L1 := by
      rw [F1.inf_bigB_eq_borelOf hR]
      exact F1.lt_borelOf hR
    obtain ⟨l, hlL, hlB⟩ : ∃ l ∈ L1, l ∉ bigB L1 L2 S := by
      by_contra hcon
      refine hlt.ne (inf_eq_left.mpr fun l hl => ?_)
      by_contra hlB
      exact hcon ⟨l, hl, hlB⟩
    have hQC : Q1 L1 L2 S ≤ Subgroup.normalizer
        (((L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :
          Subgroup G) : Set G) := (le_sup_right : Q1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S).trans hHNC
    have hlK := h.symm.le ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S) hlL)
    obtain ⟨c, hc, q, hq, hcq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQC).mp hlK
    have hcN : c ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      ((Subgroup.centralizer_le (le_conjClosure (Z2 L1 L2 S) L1)).trans
        (Subgroup.centralizer_le_normalizer (Z2 L1 L2 S : Set G))) (Subgroup.mem_inf.mp hc).2
    have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hI.critHypN.normalizes
    have hqN : q ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hBZ (hSB' (hQ1S hq))
    have hlN : l ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hcq ▸ mul_mem hcN hqN
    apply str86_conj_z2_ne hI ((le_sup_left : L1 ≤ P1 L1 L2 S) hlL) hlB
    rw [← str86_conjSub_eq_smul]
    exact F1.conjSub_eq_of_mem_normalizer hlN
  · intro x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxK : x ∈ ((L1 ⊔ Q1 L1 L2 S) ⊓
        Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G)) ⊔ Q1 L1 L2 S :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgSH hxS, hxC⟩)
    obtain ⟨j, hj⟩ := hgS2 ⟨x, hxS⟩
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact hpH.le (h x hxK ⟨j, hj'⟩)

theorem str86_F4_at {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hb : 2 ≤ str86CritB L1 L2 S) {γ δ : Str86Γ L1 L2 S} (hγ : vtype γ = true)
    (hδ : δ ∈ nbrs γ) :
    pCoreOf 2 (stab δ ⊓ stab γ) ⊓ Subgroup.centralizer (Vv (Z2 L1 L2 S) γ : Set G) ≤
      pCoreOf 2 (stab γ) := by
  obtain ⟨-, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, h1, hS0, -, hV1⟩ := str86_base_values hI
  obtain ⟨g, rfl, rfl⟩ := F112Crit.exists_edge_conj (str86_vtype_of_mem_nbrs hγ hδ)
    (show γ ∈ nbrs δ from (show (graph _ _ _).Adj γ δ from hδ).symm)
  have hF4 := str86_conj_s_inf_centralizer_le_q1 hI (hZQ hb) (P1 L1 L2 S).one_mem
  rw [map_one, one_smul] at hF4
  rw [(str86_vertex_smul hI g (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.2.1, hS0,
    (str86_vertex_smul hI g (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.2.2.1, hV1,
    (str86_vertex_smul hI g (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1, h1]
  simp only [str86_conjSub_eq_smul]
  rw [← conj_smul_inf_centralizer]
  exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hF4

theorem Str86CritPath.odd_shape {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    vtype (lam 1) = true ∧ vtype (lam 2) = false ∧
      vtype (lam (str86CritB L1 L2 S - 1)) = false ∧ vtype (lam (str86CritB L1 L2 S)) = true ∧
      lam 0 ∈ nbrs (lam 1) ∧ lam 2 ∈ nbrs (lam 1) ∧ lam 1 ∈ nbrs (lam 2) ∧
      lam (str86CritB L1 L2 S) ∈ nbrs (lam (str86CritB L1 L2 S - 1)) ∧
      lam (str86CritB L1 L2 S - 1) ∈ nbrs (lam (str86CritB L1 L2 S)) := by
  have hb1 : 1 ≤ str86CritB L1 L2 S := by omega
  have hadjb : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [Nat.sub_add_cancel hb1] at h
  have hadj01 : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam 0) (lam 1) :=
    hP.isGeo.adj (i := 0) (by omega)
  have hadj12 : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam 1) (lam 2) :=
    hP.isGeo.adj (i := 1) (by omega)
  obtain ⟨j, hj⟩ := hodd
  exact ⟨hP.vtype_of_odd hI (by omega) odd_one, hP.vtype_of_even hI (by omega) even_two,
    hP.vtype_of_even hI (by omega) ⟨j, by omega⟩, hP.vtype_of_odd hI le_rfl ⟨j, hj⟩,
    hadj01.symm, hadj12, hadj12.symm, hadjb, hadjb.symm⟩

theorem str86_critPath_odd_O1 {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
        pCoreOf 2 (stab (lam 0)) ∧
      Vv (Z2 L1 L2 S) (lam 1) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) ∧
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 2)) ∧
      IsElemAbelian 2 (Vv (Z2 L1 L2 S) (lam 1)) ∧
      IsElemAbelian 2 (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))) ∧
      ⁅Vv (Z2 L1 L2 S) (lam 1), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ ≤
        Vv (Z2 L1 L2 S) (lam 1) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ∧
      (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))).relIndex
        (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ k ∧
      (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1))).relIndex
        (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))) ≤ 2 ^ k := by
  have hc := hI.critHypN
  obtain ⟨hGL1, hGL2, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, hAB2, -⟩ := str86_Vv_abelian hI
  obtain ⟨hv1, -, hvb1, hvb, -, hn12, hn21, -, hnb⟩ := hP.odd_shape hI hodd hb3
  have hd : ∀ i j, i ≤ j → j ≤ str86CritB L1 L2 S →
      CosetGeom.dist (lam i) (lam j) = j - i := hP.isGeo
  have h2 : Vv (Z2 L1 L2 S) (lam 1) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) := by
    refine hGL2 _ _ hv1 ?_
    rw [hd 1 _ (by omega) (by omega)]
    omega
  have h3 : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 2)) := by
    refine hGL2 _ _ hvb ?_
    rw [CosetGeom.dist_comm, hd 2 _ (by omega) le_rfl]
    omega
  have hQstab : ∀ δ ε : Str86Γ L1 L2 S, ε ∈ nbrs δ → pCoreOf 2 (stab δ) ≤ stab ε :=
    fun δ ε hε => (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam δ).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hε).le)
  refine ⟨?_, h2, h3, hAB2 hb3 _ hv1, hAB2 hb3 _ hvb, ?_, ?_, ?_⟩
  · refine (str86_edge_facts hI hvb hnb).1.trans (hGL1 _ _ hvb1 ?_)
    rw [CosetGeom.dist_comm, hd 0 _ (Nat.zero_le _) (by omega)]
    omega
  · refine F7.commutator_le_inf_of_normalizes ?_ ?_
    · exact h2.trans ((hQstab _ _ (show lam (str86CritB L1 L2 S) ∈
        nbrs (lam (str86CritB L1 L2 S - 1)) from (show (graph _ _ _).Adj
          (lam (str86CritB L1 L2 S)) (lam (str86CritB L1 L2 S - 1)) from hnb).symm)).trans
        (CosetGeom.stab_le_normalizer_Vv hc.normalizes _))
    · exact h3.trans ((hQstab _ _ hn21).trans (CosetGeom.stab_le_normalizer_Vv hc.normalizes _))
  · refine (str86_edge_facts hI hvb hnb).2.2.2.2.2.2 _ (hAB2 hb3 _ hv1) ?_
    rw [inf_comm]
    exact h2.trans (str86_pCoreOf_le_pCoreOf_inf hI (show lam (str86CritB L1 L2 S) ∈
      nbrs (lam (str86CritB L1 L2 S - 1)) from (show (graph _ _ _).Adj
        (lam (str86CritB L1 L2 S)) (lam (str86CritB L1 L2 S - 1)) from hnb).symm))
  · refine (str86_edge_facts hI hv1 hn12).2.2.2.2.2.2 _ (hAB2 hb3 _ hvb) ?_
    rw [inf_comm]
    exact h3.trans (str86_pCoreOf_le_pCoreOf_inf hI hn21)

theorem str86_critPath_odd_F4 {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    ¬ Vv (Z2 L1 L2 S) (lam 1) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ∧
      Vv (Z2 L1 L2 S) (lam 1) ⊓
          Subgroup.centralizer (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) : Set G) ≤
        pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ∧
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓
          Subgroup.centralizer (Vv (Z2 L1 L2 S) (lam 1) : Set G) ≤
        pCoreOf 2 (stab (lam 1)) ∧
      ⁅Vv (Z2 L1 L2 S) (lam 1), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ ≠ ⊥ := by
  obtain ⟨-, hO12, hO13, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hv1, -, -, hvb, hn01, hn12, hn21, hnb', hnb⟩ := hP.odd_shape hI hodd hb3
  have hZ0 : Vv (Z2 L1 L2 S) (lam 0) ≤ Vv (Z2 L1 L2 S) (lam 1) :=
    F112Crit.Vv_le_Vv_of_mem_nbrs hv1 hn01
  have h1 : ¬ Vv (Z2 L1 L2 S) (lam 1) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) :=
    fun h => hP.critical (hZ0.trans h)
  have h2 : Vv (Z2 L1 L2 S) (lam 1) ⊓
      Subgroup.centralizer (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) : Set G) ≤
        pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) :=
    (inf_le_inf_right _ (hO12.trans (str86_pCoreOf_le_pCoreOf_inf hI hnb'))).trans
      (str86_F4_at hI (by omega) hvb hnb)
  refine ⟨h1, h2, ?_, fun hbot => h1 ?_⟩
  · exact (inf_le_inf_right _ (hO13.trans (str86_pCoreOf_le_pCoreOf_inf hI hn21))).trans
      (str86_F4_at hI (by omega) hv1 hn12)
  · exact (le_inf le_rfl (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)).trans h2

theorem str86_critPath_odd_O5 {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    (hVQ : ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))) :
    ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)),
      ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) ∧
      Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 2)) ∧
      ∀ t ∈ Vv (Z2 L1 L2 S) μ,
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
          (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ k * 2 ^ m := by
  obtain ⟨-, -, -, -, -, -, hO17, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hGL1, -, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨hv1, -, -, hvb, -, -, hn21, -, -⟩ := hP.odd_shape hI hodd hb3
  obtain ⟨μ, hμ, hμQ⟩ : ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)),
      ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) := by
    by_contra hcon
    refine hVQ (F112Crit.Vv_le_of_forall_mem_nbrs hvb fun μ hμ => ?_)
    by_contra h
    exact hcon ⟨μ, hμ, h⟩
  have hvμ : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
  have hμ2 : Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 2)) := by
    refine hGL1 μ (lam 2) hvμ ?_
    have hadj : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj μ
        (lam (str86CritB L1 L2 S)) := (show (graph _ _ _).Adj (lam (str86CritB L1 L2 S)) μ
          from hμ).symm
    have htri := CosetGeom.dist_triangle_of_adj hadj (lam 2)
    rw [CosetGeom.dist_eq_one_iff_adj.mpr hadj, CosetGeom.dist_comm (lam _) (lam 2),
      hP.isGeo 2 _ (by omega) le_rfl] at htri
    omega
  refine ⟨μ, hμ, hμQ, ?_, fun t ht => ?_⟩
  · rw [inf_comm]
    exact hμ2.trans (str86_pCoreOf_le_pCoreOf_inf hI hn21)
  ·
    have hAμ : Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ≤
        pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ) :=
      inf_le_right.trans (str86_pCoreOf_le_pCoreOf_inf hI hμ)
    have hrμ := (str86_edge_facts hI hvb hμ).2.2.2.1
    have h1 : (pCoreOf 2 (stab μ)).relIndex
        (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤ 2 ^ m := by
      rw [← hrμ]
      exact Subgroup.relIndex_le_of_le_right hAμ (D15Proof.relIndex_ne_zero _ _)
    have hCt : (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ⊓
        pCoreOf 2 (stab μ) ≤
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      have ht' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab μ)) := by
        rw [← hD41 μ hvμ]
        exact ht
      exact inf_le_right.trans
        ((SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab μ)).trans
          (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr ht')))
    have hmul := Subgroup.relIndex_mul_relIndex
      ((Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ⊓
        pCoreOf 2 (stab μ))
      (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))
      (Vv (Z2 L1 L2 S) (lam 1)) inf_le_left inf_le_left
    rw [Subgroup.inf_relIndex_left] at hmul
    calc (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
          (Vv (Z2 L1 L2 S) (lam 1)) ≤
        ((Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ⊓
          pCoreOf 2 (stab μ)).relIndex (Vv (Z2 L1 L2 S) (lam 1)) :=
          Subgroup.relIndex_le_of_le_left hCt (D15Proof.relIndex_ne_zero _ _)
      _ = (pCoreOf 2 (stab μ)).relIndex
            (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) *
          (Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))).relIndex
            (Vv (Z2 L1 L2 S) (lam 1)) := hmul.symm
      _ ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 hO17
      _ = 2 ^ k * 2 ^ m := Nat.mul_comm _ _

end CFSG.Quasithin.Stroth

end

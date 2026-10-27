module

public import CFSG.Monster.B.GSide.TriangleData
public import CFSG.Monster.B.GSide.EdgeQCertL
public import CFSG.Monster.B.GSide.BT2Reduce
public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0)
open CFSG.Monster.B.Short (Wv wAct)

theorem clabel_mem_Ehat_of_cPi0
    {y : CVert} (hy : y ∈ cPi0) : clabel y ∈ Ehat := by
  have h := conj_clabel_mem_Ehat (s := 1) hy
  simpa using h

theorem psiW_clabel_cPi0
    (v : cPi0) :
    psiW ⟨clabel v, clabel_mem_Ehat_of_cPi0 v.2⟩ = (cpsi v : Wv v0) := by
  obtain ⟨v, hv⟩ := v
  obtain ⟨k, rfl⟩ := mem_cPi0.1 hv
  have e : (⟨clabel (cvOf (jhatS k)), clabel_mem_Ehat_of_cPi0 hv⟩ : Ehat) =
      ⟨(k : Dfull)⁻¹ * cQ * k, conj_mem_Ehat k.2 cQ_mem_Ehat⟩ :=
    Subtype.ext (clabel_cvOf (jhatS k))
  rw [e, psiW_conj k.2 cQ_mem_Ehat, show (⟨cQ, cQ_mem_Ehat⟩ : Ehat) = cE from rfl, psiW_cE,
    cpsi_cvOf]
  rfl

theorem cpsi_surjective :
    Function.Surjective cpsi := by
  rintro ⟨a, ⟨u, rfl⟩⟩
  obtain ⟨k, rfl⟩ := jhatToKv0_surjective u
  exact ⟨⟨cvOf (jhatS k), jhatS_mem_cPi0 k⟩, cpsi_cvOf k⟩

theorem exists_cPi0_clabel_eq
    {e : Ehat} (he : psiW e ∈ Unitary.OmegaW) :
    ∃ z ∈ cPi0, clabel z = e := by
  obtain ⟨z₀, hz₀⟩ := cpsi_surjective ⟨psiW e, he⟩
  have hψ : psiW ⟨clabel z₀, clabel_mem_Ehat_of_cPi0 z₀.2⟩ = psiW e := by
    rw [psiW_clabel_cPi0, hz₀]
  have h0 : psiW (e * (⟨clabel z₀, clabel_mem_Ehat_of_cPi0 z₀.2⟩ : Ehat)⁻¹) = 0 := by
    rw [psiW_mul, psiW_inv, hψ, add_neg_cancel]
  rcases (psiW_eq_zero_iff _).1 h0 with h | h
  · refine ⟨z₀, z₀.2, ?_⟩
    have := congrArg Subtype.val (mul_inv_eq_one.1 h)
    exact this.symm
  · obtain ⟨z', hz', hl⟩ := exists_partner_mem_cPi (s := 1) z₀.2
    refine ⟨z', hz', ?_⟩
    have h' : e = xhatE * ⟨clabel z₀, clabel_mem_Ehat_of_cPi0 z₀.2⟩ :=
      mul_inv_eq_iff_eq_mul.1 h
    rw [hl, h']
    have hx : clabel (z₀ : CVert) * xhat = xhat * clabel z₀ :=
      xhat_comm_of_mem_Jhat (Ehat_le_Jhat (clabel_mem_Ehat_of_cPi0 z₀.2))
    simp only [OneMemClass.coe_one, inv_one, one_mul, mul_one, Subgroup.coe_mul]
    rw [hx]
    rfl

theorem exists_cvMul_edge
    {y y' : CVert} (h : cgraph.Adj y y') :
    ∃ g : Shat, cvMul cv0 g = y ∧ cvMul cw0 g = y' := by
  obtain ⟨g₁, hg₁⟩ := cvMul_transitive cv0 y
  have hadj : cgraph.Adj cv0 (cvMul y' g₁⁻¹) := by
    rw [← cgraph_adj_cvMul _ _ g₁, ← cvMul_mul, inv_mul_cancel, cvMul_one, hg₁]
    exact h
  have horb := native_rank_five_exact_neighbor_matrix.2.1 cv0 1 cw0 cgraph_adj_cv0_cw0
  have hmem : cvMul y' g₁⁻¹ ∈ vStabOrbit cv0 cw0 := by
    rw [horb]
    exact hadj
  obtain ⟨h₁, hh₁, hh₁'⟩ := hmem
  refine ⟨h₁ * g₁, ?_, ?_⟩
  · rw [cvMul_mul, hh₁, hg₁]
  · rw [cvMul_mul, hh₁', ← cvMul_mul, inv_mul_cancel, cvMul_one]

theorem mem_cPi0_of_clabel_mul_eq_xhat
    {y y' : CVert} (h : cgraph.Adj y y')
    (hx : clabel y * clabel y' = xhat) : y ∈ cPi0 := by
  obtain ⟨g, hg0, hg1⟩ := exists_cvMul_edge h
  have e1 : clabel y = ((g : Dfull))⁻¹ * cQ * g := by rw [← hg0, clabel_cvMul, clabel_cv0]
  have e2 : clabel y' = ((g : Dfull))⁻¹ * (cQ * xhat) * g := by
    rw [← hg1, clabel_cvMul, clabel_cw0]
  have hyy : clabel y * clabel y' = ((g : Dfull))⁻¹ * xhat * g := by
    rw [e1, e2]
    calc ((g : Dfull))⁻¹ * cQ * g * (((g : Dfull))⁻¹ * (cQ * xhat) * g) =
        ((g : Dfull))⁻¹ * (cQ * cQ * xhat) * g := by group
      _ = ((g : Dfull))⁻¹ * xhat * g := by rw [cQ_mul_self, one_mul]
  have hgx : ((g : Dfull))⁻¹ * xhat * g = xhat := hyy.symm.trans hx
  have hgJ : (g : Dfull) ∈ Jhat := by
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    calc (g : Dfull) * xhat = (g : Dfull) * (((g : Dfull))⁻¹ * xhat * g) := by rw [hgx]
      _ = xhat * g := by group
  rw [← hg0]
  exact ⟨g, hgJ, by rw [cv0, cvMul_cvOf, one_mul, mul_one]⟩

theorem mem_Jhat_of_fix
    {s : Shat} (h0 : cvMul cv0 s = cv0) (h1 : cvMul cw0 s = cw0) :
    (s : Dfull) ∈ Jhat := by
  have e0 := clabel_cvMul cv0 s
  have e1 := clabel_cvMul cw0 s
  rw [h0, clabel_cv0] at e0
  rw [h1, clabel_cw0] at e1
  rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
  have hx : xhat = cQ * (cQ * xhat) := by rw [← mul_assoc, cQ_mul_self, one_mul]
  have key : ((s : Dfull))⁻¹ * xhat * s = xhat := by
    calc ((s : Dfull))⁻¹ * xhat * s = ((s : Dfull))⁻¹ * (cQ * (cQ * xhat)) * s := by rw [← hx]
      _ = (((s : Dfull))⁻¹ * cQ * s) * (((s : Dfull))⁻¹ * (cQ * xhat) * s) := by group
      _ = xhat := by rw [← e0, ← e1, ← hx]
  calc (s : Dfull) * xhat = (s : Dfull) * (((s : Dfull))⁻¹ * xhat * s) := by rw [key]
    _ = xhat * s := by group

theorem triType_cv0_cw0_of_cPi0
    {u : CVert} (hu : u ∈ cPi0) (h0 : cgraph.Adj cv0 u)
    (h1 : cgraph.Adj cw0 u) : triType cv0 cw0 u = 1782 := by
  classical
  obtain ⟨M, -⟩ := exists_rootModel cv0
  rcases triType_eq_or M ⟨cgraph_adj_cv0_cw0, h0, h1⟩ with h | h
  · exact h
  exfalso
  set X : Set CVert := {x | x ∈ cPi0 ∧ cgraph.Adj cv0 x ∧ cgraph.Adj cw0 x} with hX
  have hsub : pairStabOrbit cv0 cw0 u ⊆ X := by
    rintro x ⟨s, hs0, hs1, rfl⟩
    refine ⟨cvMul_mem_cPi0 hu (mem_Jhat_of_fix hs0 hs1), ?_, ?_⟩
    · rw [← hs0, cgraph_adj_cvMul]
      exact h0
    · rw [← hs1, cgraph_adj_cvMul]
      exact h1
  have hfix : ∀ x ∈ X, clabelS x ∈ cEdgeFix := fun x hx =>
    ⟨mem_vStab.2 (cvMul_clabelS_of_adj hx.2.1), mem_vStab.2 (cvMul_clabelS_of_adj hx.2.2)⟩
  let f : CVert → cEdgeFix := fun x => if hx : clabelS x ∈ cEdgeFix then ⟨_, hx⟩ else 1
  have hf : ∀ x (hx : x ∈ X), f x = ⟨clabelS x, hfix x hx⟩ := fun x hx => by
    simp only [f, hfix x hx, dite_true]
  have hXL : X.ncard ≤ edgeL.ncard := by
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · rw [hf x hx]
      refine ⟨clabel_mem_Ehat_of_cPi0 hx.1, ⟨x, rfl⟩, fun h => ?_, fun h => ?_⟩
      · have e : clabelS x = clabelS cv0 := congrArg Subtype.val h
        exact hx.2.1.ne (clabelS_injective e).symm
      · have e : clabelS x = clabelS cw0 := congrArg Subtype.val h
        exact hx.2.2.ne (clabelS_injective e).symm
    · rw [hf x hx, hf y hy] at hxy
      exact clabelS_injective (congrArg Subtype.val hxy)
  have hle : triType cv0 cw0 u ≤ 1782 :=
    (Set.ncard_le_ncard hsub (Set.toFinite X)).trans (hXL.trans ncard_edgeL.le)
  omega

theorem bW_eq_zero_of_adj_cPi0
    {u v : cPi0} (h : cgraph.Adj (u : CVert) v) :
    Unitary.bW (cpsi u : Wv v0) (cpsi v) = 0 := by
  have hne : u ≠ v := fun e => h.ne (congrArg Subtype.val e)
  rcases (cgraphPi_adj_iff hne).1 h with e | e
  · rw [e]
    exact Unitary.bW_self _
  · exact ((omegaGraph_adj_iff_bW _ _).1 e).2

theorem isType1782_of_cPi0
    {u v w : cPi0} (huv : cgraph.Adj (u : CVert) v)
    (huw : cgraph.Adj (u : CVert) w) (hvw : cgraph.Adj (v : CVert) w)
    (hsum : ((cpsi u : Wv v0) + cpsi v + cpsi w) ∈ Unitary.OmegaW) :
    IsType1782 (u : CVert) v w := by
  set eu : Ehat := ⟨clabel u, clabel_mem_Ehat_of_cPi0 u.2⟩ with heu
  set ev : Ehat := ⟨clabel v, clabel_mem_Ehat_of_cPi0 v.2⟩ with hev
  set ew : Ehat := ⟨clabel w, clabel_mem_Ehat_of_cPi0 w.2⟩ with hew
  have hpsi : psiW (eu * ev * ew) = (cpsi u : Wv v0) + cpsi v + cpsi w := by
    rw [psiW_mul, psiW_mul, heu, hev, hew, psiW_clabel_cPi0, psiW_clabel_cPi0, psiW_clabel_cPi0]
  obtain ⟨z, hz, hzl⟩ := exists_cPi0_clabel_eq (hpsi ▸ hsum)
  have hprod : clabel (u : CVert) * clabel z = clabel (v : CVert) * clabel w := by
    rw [hzl]
    show clabel (u : CVert) * (clabel (u : CVert) * clabel (v : CVert) * clabel (w : CVert)) =
      clabel (v : CVert) * clabel w
    rw [← mul_assoc, ← mul_assoc, clabel_mul_clabel, one_mul]
  have huz : cgraph.Adj (u : CVert) z := by
    have hne : u ≠ ⟨z, hz⟩ := by
      intro e
      have e2 : (u : CVert) = z := congrArg Subtype.val e
      have e' : clabel (v : CVert) * clabel w = 1 := by
        rw [← hprod, ← e2]
        exact clabel_mul_clabel _
      have hvw' : clabel (v : CVert) = clabel w :=
        (eq_inv_of_mul_eq_one_left e').trans (inv_eq_of_mul_eq_one_right (clabel_mul_clabel _))
      exact hvw.ne (native_global_label_bijection_and_full_vertex_centralizer.1 hvw')
    have hzψ : (cpsi ⟨z, hz⟩ : Wv v0) = (cpsi u : Wv v0) + cpsi v + cpsi w := by
      rw [← psiW_clabel_cPi0, ← hpsi]
      congr 1
      exact Subtype.ext hzl
    have hb : Unitary.bW (cpsi u : Wv v0) (cpsi ⟨z, hz⟩) = 0 := by
      rw [hzψ, map_add, map_add, Unitary.bW_self, bW_eq_zero_of_adj_cPi0 huv,
        bW_eq_zero_of_adj_cPi0 huw, add_zero, add_zero]
    refine (cgraphPi_adj_iff hne).2 ?_
    by_cases hc : cpsi u = cpsi ⟨z, hz⟩
    · exact Or.inl hc
    · exact Or.inr ((omegaGraph_adj_iff_bW _ _).2 ⟨hc, hb⟩)
  obtain ⟨g, hg0, hg1⟩ := exists_cvMul_edge hvw
  have hu' : cgraph.Adj (cvMul (u : CVert) g⁻¹) (cvMul z g⁻¹) :=
    (cgraph_adj_cvMul _ _ _).2 huz
  have hx : clabel (cvMul (u : CVert) g⁻¹) * clabel (cvMul z g⁻¹) = xhat := by
    have ev' : clabel (v : CVert) = ((g : Dfull))⁻¹ * cQ * g := by
      rw [← hg0, clabel_cvMul, clabel_cv0]
    have ew' : clabel (w : CVert) = ((g : Dfull))⁻¹ * (cQ * xhat) * g := by
      rw [← hg1, clabel_cvMul, clabel_cw0]
    rw [clabel_cvMul, clabel_cvMul]
    calc (((g⁻¹ : Shat) : Dfull))⁻¹ * clabel (u : CVert) * ((g⁻¹ : Shat) : Dfull) *
          ((((g⁻¹ : Shat) : Dfull))⁻¹ * clabel z * ((g⁻¹ : Shat) : Dfull)) =
          (g : Dfull) * (clabel (u : CVert) * clabel z) * ((g : Dfull))⁻¹ := by
            simp only [Subgroup.coe_inv, inv_inv]
            group
      _ = (g : Dfull) * (clabel (v : CVert) * clabel w) * ((g : Dfull))⁻¹ := by rw [hprod]
      _ = cQ * cQ * xhat := by rw [ev', ew']; group
      _ = xhat := by rw [cQ_mul_self, one_mul]
  have hPi := mem_cPi0_of_clabel_mul_eq_xhat hu' hx
  have hgu : cvMul (cvMul (u : CVert) g⁻¹) g = u := by
    rw [← cvMul_mul, inv_mul_cancel, cvMul_one]
  have h0 : cgraph.Adj cv0 (cvMul (u : CVert) g⁻¹) := by
    rw [← cgraph_adj_cvMul _ _ g, hg0, hgu]
    exact huv.symm
  have h1 : cgraph.Adj cw0 (cvMul (u : CVert) g⁻¹) := by
    rw [← cgraph_adj_cvMul _ _ g, hg1, hgu]
    exact huw.symm
  have ht := triType_cv0_cw0_of_cPi0 hPi h0 h1
  have ht' : triType (v : CVert) w u = 1782 := by
    rw [← triType_cvMul cv0 cw0 _ g, hg0, hg1, hgu] at ht
    exact ht
  refine ⟨⟨huv, huw, hvw⟩, ?_⟩
  obtain ⟨-, -, -, h4, -⟩ := triType_perm (show IsCTriangle (v : CVert) w u from
    ⟨hvw, huv.symm, huw.symm⟩)
  rw [h4]
  exact ht'

@[expose] noncomputable def piSec
    (a : Unitary.OmegaPt) : cPi0 := (cpsi_surjective a).choose

theorem cpsi_piSec
    (a : Unitary.OmegaPt) : cpsi (piSec a) = a :=
  (cpsi_surjective a).choose_spec

theorem adj_piSec_iff
    {a b : Unitary.OmegaPt} (hab : a ≠ b) :
    cgraph.Adj (piSec a : CVert) (piSec b) ↔ Unitary.omegaGraph.Adj a b := by
  have hne : piSec a ≠ piSec b := fun e => hab (by rw [← cpsi_piSec a, e, cpsi_piSec])
  have h := cgraphPi_adj_iff hne
  rw [cpsi_piSec, cpsi_piSec] at h
  refine h.trans ⟨fun h' => h'.resolve_left hab, Or.inr⟩

theorem isType1782_piSec
    {a b c : Unitary.OmegaPt} (hab : Unitary.omegaGraph.Adj a b)
    (hac : Unitary.omegaGraph.Adj a c) (hbc : Unitary.omegaGraph.Adj b c)
    (hsum : ((a : Wv v0) + b + c) ∈ Unitary.OmegaW) :
    IsType1782 (piSec a : CVert) (piSec b) (piSec c) := by
  refine isType1782_of_cPi0 ((adj_piSec_iff hab.ne).2 hab) ((adj_piSec_iff hac.ne).2 hac)
    ((adj_piSec_iff hbc.ne).2 hbc) ?_
  rw [cpsi_piSec, cpsi_piSec, cpsi_piSec]
  exact hsum

end CFSG.Monster.B.GSide

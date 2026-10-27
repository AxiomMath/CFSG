module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsLocal
public import CFSG.Monster.B.TwoA.Amalgam.OrderFour

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

theorem cvMul_mem_cPi
    {x : CVert} (hx : x ∈ cPi0) (s : Shat) : cvMul x s ∈ cPi s := by
  have h := (cvMul_mem_cPi_iff (s := 1) (t := s)).2 hx
  rwa [one_mul] at h

theorem cv0_mem_cPi0 :
    cv0 ∈ cPi0 := jhatS_mem_cPi0 1

theorem mem_Jhat_of_mem_cPi_cvMul
    {s s' : Shat} {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) (hv : cvMul cv0 s ∈ cPi s')
    (hw : cvMul (cvOf (jhatS k)) s ∈ cPi s') : ((s' * s⁻¹ : Shat) : Dfull) ∈ Jhat := by
  have hne : (⟨cv0, cv0_mem_cPi0⟩ : cPi0) ≠ piV k := fun e => hk0 (congrArg Subtype.val e).symm
  have hn : ¬ cgraphPi.Adj ⟨cv0, cv0_mem_cPi0⟩ (piV k) := hk
  refine mem_Jhat_of_mem_cPi hne hn ?_ ?_
  · rw [← cvMul_mem_cPi_iff (t := s), inv_mul_cancel_right]
    exact hv
  · rw [← cvMul_mem_cPi_iff (t := s), inv_mul_cancel_right]
    exact hw

theorem exists_base_presentation
    {v w : CVert} (hw : w ∈ sphereFour v) :
    ∃ (s : Shat) (k : Jhat), cvMul cv0 s = v ∧ cvMul (cvOf (jhatS k)) s = w ∧
      cvOf (jhatS k) ≠ cv0 ∧ ¬ cgraph.Adj cv0 (cvOf (jhatS k)) ∧ psiW (labE k) = Unitary.tauW := by
  obtain ⟨-, -, ⟨s₁, hv₁, hw₁⟩, -, -⟩ := native_coset_graph_order_four_common_neighbors.1 v w hw
  obtain ⟨hvw, hna, -⟩ := cgraph_dist_eq_two_iff.1 hw.1
  obtain ⟨j, hj⟩ := mem_cPi0.1 (mem_cPi_iff.1 hv₁)
  set s₂ := jhatS j * s₁
  have hv₂ : cvMul cv0 s₂ = v := by
    show cvOf (1 * (jhatS j * s₁)) = v
    rw [one_mul, ← cvMul_cvOf, ← hj, cvMul_inv_cancel']
  have hw₂ : w ∈ cPi s₂ := by
    rw [cPi_mul_left (k := jhatS j) j.2]
    exact hw₁
  obtain ⟨k, hk⟩ := mem_cPi0.1 (mem_cPi_iff.1 hw₂)
  have hkw : cvMul (cvOf (jhatS k)) s₂ = w := by rw [← hk, cvMul_inv_cancel']
  have hk0 : cvOf (jhatS k) ≠ cv0 := fun e => hvw (by rw [← hv₂, ← hkw, e])
  have hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)) := fun h =>
    hna (by rw [← hv₂, ← hkw]; exact (cgraph_adj_cvMul _ _ s₂).2 h)
  obtain ⟨p, hp, hτ⟩ := exists_P1_tauW hk0 hk
  have hpE : ((jhatS p)⁻¹ : Shat) ∈ vStab cv0 := by
    rw [mem_vStab_cv0, Subgroup.coe_inv]
    exact Eam.inv_mem (Pc_le_Eam 0 hp)
  refine ⟨(jhatS p)⁻¹ * s₂, k * p, ?_, ?_, ?_, ?_, hτ⟩
  · rw [cvMul_mul, mem_vStab.1 hpE, hv₂]
  · rw [← hkw, cvMul_cvOf, cvMul_cvOf, jhatS_mul, mul_assoc, mul_inv_cancel_left]
  · intro e
    apply hk0
    rw [← cvMul_jhatS, ← (cvMul_cv0_iff (jhatS p)).2 (Pc_le_Eam 0 hp)] at e
    exact cvMul_injective _ e
  · intro h
    apply hk
    rw [← cvMul_jhatS, ← (cvMul_cv0_iff (jhatS p)).2 (Pc_le_Eam 0 hp)] at h
    exact (cgraph_adj_cvMul _ _ _).1 h

theorem cv0_ne_partner :
    cv0 ≠ cvOf a0S :=
  (adj_cv0_elS a0_mem_Ehat a0_not_mem_N1).ne

theorem cpsi_partner :

    cpsi ⟨cv0, cv0_mem_cPi0⟩ = cpsi ⟨cvOf a0S, cvOf_a0S_mem_cPi0⟩ := by
  have h1 : cpsi ⟨cv0, cv0_mem_cPi0⟩ = piPt 1 := cpsi_piV 1
  have h2 : cpsi ⟨cvOf a0S, cvOf_a0S_mem_cPi0⟩ = piPt a0J := cpsi_piV a0J
  rw [h1, h2]
  exact piPt_eq_iff.2 (Or.inr (by rw [mul_one]))

theorem eq_partner_of_fibre
    {s s' : Shat} {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) (hv : cvMul cv0 s ∈ cPi s')
    (hw : cvMul (cvOf (jhatS k)) s ∈ cPi s') {u u' : cPi0} (huu : u ≠ u')
    (hψ : cpsi u = cpsi u') (hu : cvMul u s' = cvMul cv0 s) :
    cvMul u' s' = cvMul (cvOf a0S) s := by
  have hJ := mem_Jhat_of_mem_cPi_cvMul hk0 hk hv hw
  set j : Jhat := ⟨_, hJ⟩
  have hjs : jhatS j = s' * s⁻¹ := rfl
  have hu' : (u : CVert) = cvOf (jhatS j⁻¹) := by
    rw [← cvMul_inv_cancel (u : CVert) s', hu]
    show cvOf (1 * s * s'⁻¹) = cvOf (jhatS j⁻¹)
    congr 1
    apply Subtype.ext
    show ((1 * s * s'⁻¹ : Shat) : Dfull) = ((s' * s⁻¹ : Shat) : Dfull)⁻¹
    simp only [one_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  have hueq : u = piV j⁻¹ := Subtype.ext hu'
  have hmem : u' ∈ cpsi ⁻¹' {piPt j⁻¹} := by
    rw [Set.mem_preimage, ← hψ, hueq, cpsi_piV]
    exact Set.mem_singleton _
  rw [cpsi_preimage] at hmem
  rcases hmem with h | h
  · exact absurd (hueq.trans h.symm) huu
  · rw [Set.mem_singleton_iff.1 h]
    show cvOf (jhatS (a0J * j⁻¹) * s') = cvOf (a0S * s)
    congr 1
    rw [jhatS_mul, mul_assoc]
    congr 1
    apply Subtype.ext
    show ((j : Dfull))⁻¹ * s' = s
    rw [show (j : Dfull) = ((s' * s⁻¹ : Shat) : Dfull) from rfl]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem neighborSet_cv0_inter_cPi0 :
    cgraph.neighborSet cv0 ∩ cPi0 = {cvOf a0S} ∪ piDelta := by
  ext x
  constructor
  · rintro ⟨hadj, hx⟩
    rcases mem_cPi0_cases ⟨x, hx⟩ with h | h | h | h
    · exact absurd hadj (by rw [show x = cv0 from h]; exact cgraph.irrefl)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨k, rfl⟩ := mem_cPi0.1 hx
      exact not_adj_cv0_of_tauOrb ((mem_piTau_iff k).1 h) hadj
  · rintro (h | h)
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨adj_cv0_elS a0_mem_Ehat a0_not_mem_N1, cvOf_a0S_mem_cPi0⟩
    · have hx : x ∈ cPi0 := h.fst
      obtain ⟨k, rfl⟩ := mem_cPi0.1 hx
      exact ⟨adj_cv0_of_delta ((mem_piDelta_iff k).1 h), hx⟩

theorem neighborSet_inter_cPi
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    cgraph.neighborSet v ∩ cPi s = {cvMul (cvOf a0S) s} ∪ (fun x => cvMul x s) '' piDelta := by
  ext x
  have key : x ∈ cgraph.neighborSet v ∩ cPi s ↔ cvMul x s⁻¹ ∈ cgraph.neighborSet cv0 ∩ cPi0 := by
    rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_cPi_iff, SimpleGraph.mem_neighborSet,
      SimpleGraph.mem_neighborSet, ← hs, ← cgraph_adj_cvMul cv0 _ s, cvMul_inv_cancel']
  rw [key, neighborSet_cv0_inter_cPi0]
  constructor
  · rintro (h | h)
    · left
      rw [← cvMul_inv_cancel' x s, Set.mem_singleton_iff.1 h]
      exact Set.mem_singleton _
    · exact Or.inr ⟨_, h, cvMul_inv_cancel' x s⟩
  · rintro (h | ⟨y, hy, rfl⟩)
    · left
      rw [Set.mem_singleton_iff.1 h, cvMul_inv_cancel]
      exact Set.mem_singleton _
    · right
      rwa [cvMul_inv_cancel]

theorem image_piDelta_eq_cvOrbit
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) {δ : CVert}
    (hδ : δ ∈ piDelta) :
    (fun x => cvMul x s) '' piDelta =
      cvOrbit (vStab v ⊓ vStab (cvMul (cvOf a0S) s)) (cvMul δ s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← p1Orb_of_mem_piDelta hδ] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have hpE : (p : Dfull) ∈ Eam := Pc_le_Eam 0 hp
    refine ⟨s⁻¹ * p * s, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [mem_vStab, ← hs, cvMul_cvMul_eq_iff, show s * (s⁻¹ * p * s) * s⁻¹ = p by group]
      exact (cvMul_cv0_iff p).2 hpE
    · rw [mem_vStab, cvMul_cvMul_eq_iff, show s * (s⁻¹ * p * s) * s⁻¹ = p by group]
      exact fix_partner_of_mem_Pc_zero (e := ⟨p, hpE⟩) hp
    · show cvMul (cvMul δ s) (s⁻¹ * p * s) = cvMul (cvMul δ p) s
      rw [← cvMul_mul, ← cvMul_mul]
      congr 1
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyv, hyv'⟩ := Subgroup.mem_inf.1 hy
    have h1 : cvMul cv0 (s * y * s⁻¹) = cv0 := by
      rw [mem_vStab, ← hs, cvMul_cvMul_eq_iff] at hyv
      exact hyv
    have hE : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Eam := (cvMul_cv0_iff _).1 h1
    have h2 := (cvMul_cvMul_eq_iff (s := s) (cvOf a0S) y).1 hyv'
    have hP : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Pc 0 :=
      mem_Pc_zero_of_fix_partner (e := ⟨_, hE⟩) h2
    refine ⟨cvMul δ (s * y * s⁻¹), ?_, ?_⟩
    · rw [← p1Orb_of_mem_piDelta hδ]
      exact ⟨_, hP, rfl⟩
    · show cvMul (cvMul δ (s * y * s⁻¹)) s = cvMul (cvMul δ s) y
      rw [← cvMul_mul, ← cvMul_mul]
      congr 1
      group

theorem ncard_image_piDelta
    (s : Shat) : ((fun x => cvMul x s) '' piDelta).ncard = 1782 := by
  rw [Set.ncard_image_of_injective _ (cvMul_injective s), ncard_piDelta]

theorem mem_sphereFour_of_cPi
    {s : Shat} {x y : CVert} (hx : x ∈ cPi s) (hy : y ∈ cPi s)
    (hxy : x ≠ y) (hn : ¬ cgraph.Adj x y) : y ∈ sphereFour x := by
  have hx' := mem_cPi_iff.1 hx
  have hy' := mem_cPi_iff.1 hy
  have hne : (⟨_, hx'⟩ : cPi0) ≠ ⟨_, hy'⟩ := fun e =>
    hxy (cvMul_injective _ (congrArg Subtype.val e))
  have hna : ¬ cgraphPi.Adj ⟨_, hx'⟩ ⟨_, hy'⟩ := fun h =>
    hn ((cgraph_adj_cvMul x y s⁻¹).1 h)
  have hd := dist_eq_two_of_pi hne hna
  have ho := orderOf_clabel_of_not_adj hne hna
  refine ⟨?_, Or.inl ?_⟩
  · have h := dist_eq_two_cvMul hd s
    rwa [cvMul_inv_cancel', cvMul_inv_cancel'] at h
  · have h := lblOrd_cvMul (cvMul x s⁻¹) (cvMul y s⁻¹) s
    rw [cvMul_inv_cancel', cvMul_inv_cancel'] at h
    rw [h]
    exact ho

end CFSG.Monster.B.TwoA.Amalgam

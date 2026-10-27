module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraph
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

theorem bV_eq_one_of_not_adj
    {x y : Unitary.OmegaPt} (hxy : x ≠ y)
    (hn : ¬ Unitary.omegaGraph.Adj x y) : bV (x : Wv v0) y = 1 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Kstab v0) Unitary.sigmaPt x
  obtain ⟨y', rfl⟩ : ∃ y', g • y' = y := ⟨g⁻¹ • y, smul_inv_smul g y⟩
  rw [omegaGraph_adj_smul] at hn
  have hne : y' ≠ Unitary.sigmaPt := fun e => hxy (by rw [e])
  rcases (Set.ext_iff.1 Unitary.OmegaW_eq_union _).1 y'.2 with (h1 | h1) | h1
  · exact absurd (Subtype.ext (Set.mem_singleton_iff.1 h1)) hne
  · exact absurd ((Unitary.adj_sigmaPt_iff y').2 h1) hn
  · rw [Unitary.coe_smul_OmegaPt, Unitary.coe_smul_OmegaPt]
    exact (Unitary.bW_wAct g⁻¹ Unitary.sigmaW y').trans (bV_sigmaW_of_mem_tauOrb h1)

theorem labE_mul_self
    (k : Jhat) : (labE k : Dfull) * labE k = 1 := by
  show (k : Dfull)⁻¹ * cQ * k * ((k : Dfull)⁻¹ * cQ * k) = 1
  rw [show (k : Dfull)⁻¹ * cQ * k * ((k : Dfull)⁻¹ * cQ * k) = (k : Dfull)⁻¹ * (cQ * cQ) * k by
    group, cQ_mul_self, mul_one, inv_mul_cancel]

theorem labE_sq_of_bV
    {k k' : Jhat} (h : bV (psiW (labE k)) (psiW (labE k')) = 1) :
    ((labE k : Dfull) * labE k') ^ 2 = xhat := by
  have hc := Ehat_comm (labE k') (labE k)
  rw [bV_comm, h, ZMod.val_one, pow_one] at hc
  have hx : (labE k' : Dfull) * xhat = xhat * labE k' :=
    xhat_comm_of_mem_Jhat (Ehat_le_Jhat (labE k').2)
  calc ((labE k : Dfull) * labE k') ^ 2 = labE k * ((labE k' : Dfull) * labE k) * labE k' := by
        rw [sq]
        group
    _ = labE k * (labE k * labE k' * xhat) * labE k' := by rw [hc]
    _ = ((labE k : Dfull) * labE k) * ((labE k' : Dfull) * xhat) * labE k' := by group
    _ = xhat := by
        rw [labE_mul_self, hx, one_mul, mul_assoc, labE_mul_self, mul_one]

theorem clabel_sq_of_not_adj
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) :
    (clabel v * clabel w) ^ 2 = xhat := by
  obtain ⟨k, rfl⟩ := exists_piV v
  obtain ⟨k', rfl⟩ := exists_piV w
  have h := (cgraphPi_adj_iff hvw).not.1 hn
  push Not at h
  rw [cpsi_piV, cpsi_piV] at h
  have hb := bV_eq_one_of_not_adj h.1 h.2
  rw [piPt_eq_psiW, piPt_eq_psiW] at hb
  exact labE_sq_of_bV hb

theorem orderOf_clabel_of_not_adj
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) :
    orderOf (clabel v * clabel w) = 4 := by
  have h2 := clabel_sq_of_not_adj hvw hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, h2]
    exact xhat_ne_one
  · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h2, sq, xhat_mul_self]

theorem cvMul_mem_cPi0
    {v : CVert} (hv : v ∈ cPi0) {s : Shat} (hs : (s : Dfull) ∈ Jhat) :
    cvMul v s ∈ cPi0 := by
  obtain ⟨k, rfl⟩ := mem_cPi0.1 hv
  exact cvMul_jhatS k ⟨s, hs⟩ ▸ jhatS_mem_cPi0 (k * ⟨s, hs⟩)

theorem cvMul_eq_iff_of_mem_Jhat
    {v : CVert} (hv : v ∈ cPi0) {s : Shat} (hs : (s : Dfull) ∈ Jhat) :
    cvMul v s = v ↔ (s : Dfull) * clabel v = clabel v * s := by
  obtain ⟨k, rfl⟩ := mem_cPi0.1 hv
  rw [show cvMul (cvOf (jhatS k)) s = cvOf (jhatS (k * ⟨s, hs⟩)) from rfl, ← labE_eq_iff,
    clabel_jhatS, Subtype.ext_iff]
  show ((k * ⟨s, hs⟩ : Jhat) : Dfull)⁻¹ * cQ * (k * ⟨s, hs⟩ : Jhat) = labE k ↔ _
  rw [Subgroup.coe_mul]
  show ((k : Dfull) * s)⁻¹ * cQ * (k * s) = labE k ↔ (s : Dfull) * labE k = labE k * s
  rw [show ((k : Dfull) * s)⁻¹ * cQ * (k * s) = (s : Dfull)⁻¹ * labE k * s by
    show _ = (s : Dfull)⁻¹ * ((k : Dfull)⁻¹ * cQ * k) * s
    group]
  constructor
  · intro h
    calc (s : Dfull) * labE k = s * ((s : Dfull)⁻¹ * labE k * s) := by rw [h]
      _ = labE k * s := by group
  · intro h
    rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem pairStab_iff
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) (s : Shat) :
    (cvMul v s = v ∧ cvMul w s = w) ↔ (s : Dfull) ∈ Jhat ∧
      (s : Dfull) ∈ Subgroup.centralizer {clabel v} ∧
        (s : Dfull) ∈ Subgroup.centralizer {clabel w} := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc : ∀ u : CVert, cvMul u s = u → (s : Dfull) * clabel u = clabel u * s := by
      intro u hu
      have := clabel_cvMul u s
      rw [hu] at this
      calc (s : Dfull) * clabel u = s * ((s : Dfull)⁻¹ * clabel u * s) := by
            rw [← this]
        _ = clabel u * s := by group
    have hv := hc v h1
    have hw := hc w h2
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hv,
      Subgroup.mem_centralizer_singleton_iff.2 hw⟩
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff, ← clabel_sq_of_not_adj hvw hn]
    exact ((Commute.mul_right hv hw).pow_right 2).eq
  · rintro ⟨hJ, hv, hw⟩
    exact ⟨(cvMul_eq_iff_of_mem_Jhat v.2 hJ).2 (Subgroup.mem_centralizer_singleton_iff.1 hv),
      (cvMul_eq_iff_of_mem_Jhat w.2 hJ).2 (Subgroup.mem_centralizer_singleton_iff.1 hw)⟩

theorem mem_cPi_iff
    {v : CVert} {s : Shat} : v ∈ cPi s ↔ cvMul v s⁻¹ ∈ cPi0 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [cvMul_cvOf, mul_inv_cancel_right, mul_one]⟩
  · rintro ⟨k, hk, hv⟩
    refine ⟨k, hk, ?_⟩
    rw [mul_one] at hv
    rw [← cvMul_cvOf, ← hv, cvMul_inv_cancel']

theorem cvMul_mem_cPi_iff
    {v : CVert} {s t : Shat} : cvMul v t ∈ cPi (s * t) ↔ v ∈ cPi s := by
  constructor
  · rintro ⟨k, hk, hv⟩
    refine ⟨k, hk, ?_⟩
    rw [← cvMul_inv_cancel v t, hv, cvMul_cvOf, mul_assoc, mul_inv_cancel_right]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [cvMul_cvOf, mul_assoc]⟩

theorem cPi_mul_left
    {k : Shat} (hk : (k : Dfull) ∈ Jhat) (s : Shat) : cPi (k * s) = cPi s := by
  ext v
  constructor
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k' * k, Jhat.mul_mem hk' hk, by rw [mul_assoc]⟩
  · rintro ⟨k', hk', rfl⟩
    refine ⟨k' * k⁻¹, Jhat.mul_mem hk' (Jhat.inv_mem hk), ?_⟩
    rw [mul_assoc, inv_mul_cancel_left]

theorem mem_Jhat_of_mem_cPi
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) {s : Shat}
    (hv : v.1 ∈ cPi s) (hw : w.1 ∈ cPi s) : (s : Dfull) ∈ Jhat := by
  have hv' := mem_cPi_iff.1 hv
  have hw' := mem_cPi_iff.1 hw
  have hne : (⟨_, hv'⟩ : cPi0) ≠ ⟨_, hw'⟩ := fun e =>
    hvw (Subtype.ext (cvMul_injective _ (congrArg Subtype.val e)))
  have hna : ¬ cgraphPi.Adj ⟨_, hv'⟩ ⟨_, hw'⟩ := fun h =>
    hn ((cgraph_adj_cvMul v.1 w.1 s⁻¹).1 h)
  have h := clabel_sq_of_not_adj hne hna
  change (clabel (cvMul v.1 s⁻¹) * clabel (cvMul w.1 s⁻¹)) ^ 2 = xhat at h
  rw [clabel_cvMul, clabel_cvMul] at h
  have e : (((s⁻¹ : Shat) : Dfull))⁻¹ * clabel v.1 * (s⁻¹ : Shat) *
      ((((s⁻¹ : Shat) : Dfull))⁻¹ * clabel w.1 * (s⁻¹ : Shat)) =
        (s : Dfull) * (clabel v.1 * clabel w.1) * (s : Dfull)⁻¹ := by
    simp only [Subgroup.coe_inv, inv_inv]
    group
  rw [e, conj_pow, clabel_sq_of_not_adj hvw hn] at h
  rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
  calc (s : Dfull) * xhat = (s * xhat * (s : Dfull)⁻¹) * s := by group
    _ = xhat * s := by rw [h]

theorem exists_commonNeighbor_pi
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) :
    ∃ u : cPi0, cgraphPi.Adj v u ∧ cgraphPi.Adj w u := by
  have h := native_Co2_two_clique_fiber_graph.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v w hvw hn
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h]; norm_num)
  exact ⟨u, hu.1, hu.2⟩

theorem dist_eq_two_of_pi
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w) :
    cgraph.dist v.1 w.1 = 2 := by
  obtain ⟨u, hvu, hwu⟩ := exists_commonNeighbor_pi hvw hn
  exact cgraph_dist_eq_two_iff.2 ⟨fun e => hvw (Subtype.ext e), hn, u.1, hvu, hwu.symm⟩

theorem commonNeighbors_subset_cPi0
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w)
    (htrans : ∀ u ∈ cgraph.commonNeighbors v.1 w.1, ∀ u' ∈ cgraph.commonNeighbors v.1 w.1,
      ∃ s : Shat, cvMul v.1 s = v.1 ∧ cvMul w.1 s = w.1 ∧ cvMul u s = u') :
    cgraph.commonNeighbors v.1 w.1 ⊆ cPi0 := by
  intro u hu
  obtain ⟨u₀, hvu₀, hwu₀⟩ := exists_commonNeighbor_pi hvw hn
  obtain ⟨s, hsv, hsw, rfl⟩ := htrans u₀.1 ⟨hvu₀, hwu₀⟩ u hu
  exact cvMul_mem_cPi0 u₀.2 ((pairStab_iff hvw hn s).1 ⟨hsv, hsw⟩).1

theorem ncard_commonNeighbors_of_pi
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraphPi.Adj v w)
    (htrans : ∀ u ∈ cgraph.commonNeighbors v.1 w.1, ∀ u' ∈ cgraph.commonNeighbors v.1 w.1,
      ∃ s : Shat, cvMul v.1 s = v.1 ∧ cvMul w.1 s = w.1 ∧ cvMul u s = u') :
    (cgraph.commonNeighbors v.1 w.1).ncard = 648 := by
  have hsub := commonNeighbors_subset_cPi0 hvw hn htrans
  have e : cgraph.commonNeighbors v.1 w.1 = Subtype.val '' cgraphPi.commonNeighbors v w := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u, hsub hu⟩, hu, rfl⟩
    · rintro ⟨u', hu', rfl⟩
      exact hu'
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact native_Co2_two_clique_fiber_graph.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v w hvw hn

theorem exists_base_pair :
    ∃ w : cPi0, (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0) ≠ w ∧
    ¬ cgraphPi.Adj ⟨cv0, jhatS_mem_cPi0 1⟩ w := by
  obtain ⟨k, hk⟩ := piPt_surjective Unitary.tauPt
  have h1 : cpsi ⟨cv0, jhatS_mem_cPi0 1⟩ = Unitary.sigmaPt :=
    (cpsi_piV 1).trans (Subtype.ext coe_piPt_one)
  have h2 : cpsi (piV k) = Unitary.tauPt := (cpsi_piV k).trans hk
  have hne : (⟨cv0, jhatS_mem_cPi0 1⟩ : cPi0) ≠ piV k := fun e => Unitary.sigmaPt_ne_tauPt (by
    rw [← h1, ← h2, e])
  refine ⟨piV k, hne, fun h => ?_⟩
  rcases (cgraphPi_adj_iff hne).1 h with e | e
  · rw [h1, h2] at e
    exact Unitary.sigmaPt_ne_tauPt e
  · rw [h1, h2] at e
    exact Unitary.not_adj_sigmaPt_tauPt e

theorem order_four_common_neighbors_of
    (hpath : ∀ t t' : CVert × CVert × CVert, IsDistTwoPath t → IsDistTwoPath t' →
      (t' ∈ tripleOrbit t ↔ (LabelThree t.1 t.2.2 ↔ LabelThree t'.1 t'.2.2)))
    (hdisj : ∀ v : CVert, Disjoint (sphereThree v) (sphereFour v))
    (htrans : ∀ v w : CVert, cgraph.dist v w = 2 → ∀ u ∈ cgraph.commonNeighbors v w,
      ∀ u' ∈ cgraph.commonNeighbors v w, ∃ s : Shat, cvMul v s = v ∧ cvMul w s = w ∧ cvMul u s = u')
    (hcount : ∃ μ₄ : ℕ,
      (∀ v w : CVert, w ∈ sphereFour v → (cgraph.commonNeighbors v w).ncard = μ₄) ∧
      ∀ v : CVert, (sphereFour v).ncard * μ₄ = 3968055 * 1824768) :
    (∀ v w : CVert, w ∈ sphereFour v →
      orderOf (clabel v * clabel w) = 4 ∧ (cgraph.commonNeighbors v w).ncard = 648 ∧
      (∃ s : Shat, v ∈ cPi s ∧ w ∈ cPi s) ∧
      (∀ s s' : Shat, v ∈ cPi s → w ∈ cPi s → v ∈ cPi s' → w ∈ cPi s' → cPi s = cPi s') ∧
      ∀ s : Shat, v ∈ cPi s → w ∈ cPi s → cgraph.commonNeighbors v w ⊆ cPi s) ∧
    (∀ v : CVert, (sphereFour v).ncard = 11174042880) ∧
    ∀ v w : cPi0, v ≠ w → ¬ cgraphPi.Adj v w →
      (clabel v * clabel w) ^ 2 = xhat ∧
      ∀ s : Shat, (cvMul v s = v ∧ cvMul w s = w) ↔ (s : Dfull) ∈ Jhat ∧
        (s : Dfull) ∈ Subgroup.centralizer {clabel v} ∧
          (s : Dfull) ∈ Subgroup.centralizer {clabel w} := by
  obtain ⟨μ₄, hμ, hsph⟩ := hcount
  obtain ⟨w₀, hne₀, hn₀⟩ := exists_base_pair
  set v₀ : cPi0 := ⟨cv0, jhatS_mem_cPi0 1⟩ with hv₀
  have hd₀ := dist_eq_two_of_pi hne₀ hn₀
  have hord₀ := orderOf_clabel_of_not_adj hne₀ hn₀
  have hw₀ : w₀.1 ∈ sphereFour v₀.1 := ⟨hd₀, Or.inl hord₀⟩
  have h648 := ncard_commonNeighbors_of_pi hne₀ hn₀ (htrans _ _ hd₀)
  have hμ₄ : μ₄ = 648 := (hμ _ _ hw₀).symm.trans h648
  subst hμ₄
  obtain ⟨u₀, hvu₀, hwu₀⟩ := exists_commonNeighbor_pi hne₀ hn₀
  have hsub₀ := commonNeighbors_subset_cPi0 hne₀ hn₀ (htrans _ _ hd₀)
  have htransport : ∀ v w : CVert, w ∈ sphereFour v →
      ∃ s : Shat, cvMul v₀.1 s = v ∧ cvMul w₀.1 s = w := by
    intro v w hw
    obtain ⟨-, -, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
    have hn3 : ¬ LabelThree v w := fun h3 =>
      Set.disjoint_left.1 (hdisj v) ⟨hw.1, h3⟩ hw
    have hn3₀ : ¬ LabelThree v₀.1 w₀.1 := by
      rintro (h | h) <;> rw [show lblOrd v₀.1 w₀.1 = 4 from hord₀] at h <;> norm_num at h
    have ht : IsDistTwoPath (v₀.1, u₀.1, w₀.1) := ⟨hvu₀.symm, hwu₀.symm, hd₀⟩
    have ht' : IsDistTwoPath (v, u, w) := ⟨hvu.symm, huw, hw.1⟩
    obtain ⟨s, hs⟩ := (hpath _ _ ht ht').2 (iff_of_false hn3₀ hn3)
    simp only [Prod.mk.injEq] at hs
    exact ⟨s, hs.1.symm, hs.2.2.symm⟩
  have huniq : ∀ s s' : Shat, cvMul v₀.1 s ∈ cPi s' → cvMul w₀.1 s ∈ cPi s' → cPi s = cPi s' := by
    intro s s' hv hw
    have hv' : v₀.1 ∈ cPi (s' * s⁻¹) := by
      rw [← cvMul_mem_cPi_iff (t := s), inv_mul_cancel_right]
      exact hv
    have hw' : w₀.1 ∈ cPi (s' * s⁻¹) := by
      rw [← cvMul_mem_cPi_iff (t := s), inv_mul_cancel_right]
      exact hw
    have hJ := mem_Jhat_of_mem_cPi hne₀ hn₀ hv' hw'
    rw [← cPi_mul_left hJ s, inv_mul_cancel_right]
  have hmem : ∀ (u : CVert) (s : Shat), u ∈ cPi0 → cvMul u s ∈ cPi s := fun u s hu => by
    have h := (cvMul_mem_cPi_iff (s := 1) (t := s)).2 hu
    rwa [one_mul] at h
  refine ⟨fun v w hw => ?_, fun v => ?_, fun v w hvw hn =>
    ⟨clabel_sq_of_not_adj hvw hn, pairStab_iff hvw hn⟩⟩
  · obtain ⟨s, rfl, rfl⟩ := htransport v w hw
    refine ⟨?_, hμ _ _ hw, ⟨s, hmem _ s v₀.2, hmem _ s w₀.2⟩,
      fun t t' hv hw hv' hw' => (huniq s t hv hw).symm.trans (huniq s t' hv' hw'), ?_⟩
    · exact (lblOrd_cvMul v₀.1 w₀.1 s).trans hord₀
    · intro t hv hw
      rw [← huniq s t hv hw, commonNeighbors_cvMul]
      rintro _ ⟨u, hu, rfl⟩
      exact hmem u s (hsub₀ hu)
  · have := hsph v
    omega

end CFSG.Monster.B.TwoA.Amalgam

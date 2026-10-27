module

public import CFSG.Quasithin.Recognition.Stroth.PolygonRigidity

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

omit [Fintype V] [DecidableRel Γ.Adj] [FaithfulSMul D V] [GraphAction D Γ] in
theorem mem_pathRootGroup {p : GPath Γ n} {g : D} :
    g ∈ pathRootGroup D Γ p ↔
      ∀ i : ℕ, 1 ≤ i → i ≤ n - 1 → ∀ w : V, Γ.Adj (p i) w → g • w = w := by
  simp only [pathRootGroup, Subgroup.mem_iInf, mem_fixingSubgroup_iff, Set.mem_Icc,
    SimpleGraph.mem_neighborSet]
  exact ⟨fun h i h1 h2 => h i ⟨h1, h2⟩, fun h i hi => h i hi.1 hi.2⟩

theorem pathRootGroup_eq_one_of_fix (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {p : GPath Γ n} (hp : p.NoBack) {g : D}
    (hg : g ∈ pathRootGroup D Γ p) {w : V} (hw : Γ.Adj (p n) w) (hw' : w ≠ p (n - 1))
    (hgw : g • w = w) : g = 1 := by
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hT' : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hfix : ∀ v : V, g • v = v := by
    refine hgp.smul_eq_of_fix_root hn hT' p hp ?_ hw hw' hgw
    intro i hi1 hi2 u hu
    exact (mem_pathRootGroup.mp hg) i hi1 hi2 u hu
  refine eq_of_smul_eq_smul (m₁ := g) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  exact hfix v

theorem rootGroupRegular (n : ℕ) : RootGroupRegular n := by
  intro V _ Γ _ D _ _ _ _ hn hP hT hM p hp y y' hy hy' hne hne'
  obtain ⟨g, hgfix, hgy⟩ := hM p hp y y' hy hy' hne hne'
  have hg : g ∈ pathRootGroup D Γ p := mem_pathRootGroup.mpr hgfix
  refine ⟨⟨g, hg⟩, hgy, ?_⟩
  rintro ⟨g', hg'⟩ hgy'
  have hmem : g⁻¹ * g' ∈ pathRootGroup D Γ p :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg'
  have hfix : (g⁻¹ * g') • y = y := by
    rw [mul_smul, hgy', ← hgy, inv_smul_smul]
  have hone : g⁻¹ * g' = 1 := pathRootGroup_eq_one_of_fix hn hP hT hp hmem hy hne hfix
  refine Subtype.ext ?_
  have h : g' = g := by
    have h2 : g * (g⁻¹ * g') = g := by rw [hone, mul_one]
    rwa [mul_inv_cancel_left] at h2
  exact h

open CFSG.Geometry.GeneralizedPolygons in
theorem card_pathRootGroup_add_one (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (p : GPath Γ n) (hp : p.NoBack) :
    Nat.card (pathRootGroup D Γ p) + 1 = Γ.degree (p n) := by
  classical
  have hR₀ : RootGroupRegular n := rootGroupRegular n
  unfold RootGroupRegular at hR₀
  have hR := hR₀ V Γ D hn hP hT hM p hp
  have hv : Γ.Adj (p n) (p (n - 1)) := by
    have h := p.adj (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    exact h.symm
  have hmem : p (n - 1) ∈ Γ.neighborFinset (p n) := by
    rw [SimpleGraph.mem_neighborFinset]; exact hv
  have h2 : 2 ≤ ((Γ.neighborFinset (p n)).erase (p (n - 1))).card := by
    rw [Finset.card_erase_of_mem hmem, SimpleGraph.card_neighborFinset_eq_degree]
    have := hT (p n); omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega :
    0 < ((Γ.neighborFinset (p n)).erase (p (n - 1))).card)
  have ha_adj : Γ.Adj (p n) a := by
    have h : a ∈ Γ.neighborFinset (p n) := Finset.mem_of_mem_erase ha
    rwa [SimpleGraph.mem_neighborFinset] at h
  have ha_ne : a ≠ p (n - 1) := by
    intro h
    rw [h] at ha
    exact Finset.notMem_erase _ _ ha
  have hfixU : ∀ g ∈ pathRootGroup D Γ p, g • p (n - 1) = p (n - 1) := by
    intro g hg
    have h := p.adj (n - 2) (by omega)
    rw [show n - 2 + 1 = n - 1 by omega] at h
    exact (mem_pathRootGroup.mp hg) (n - 2) (by omega) (by omega) (p (n - 1)) h
  have hfixUn : ∀ g ∈ pathRootGroup D Γ p, g • p n = p n := by
    intro g hg
    exact (mem_pathRootGroup.mp hg) (n - 1) (by omega) le_rfl (p n) hv.symm
  let φ : ↥(pathRootGroup D Γ p) → {w : V // Γ.Adj (p n) w ∧ w ≠ p (n - 1)} := fun g =>
    ⟨g.1 • a, ⟨by
        have h := (GraphAction.adj_smul (Γ := Γ) g.1 (p n) a).mpr ha_adj
        rwa [hfixUn g.1 g.2] at h,
      by
        intro h
        have h' : g.1⁻¹ • (g.1 • a) = g.1⁻¹ • (p (n - 1)) := congrArg (g.1⁻¹ • ·) h
        rw [inv_smul_smul, hfixU g.1⁻¹ (Subgroup.inv_mem _ g.2)] at h'
        exact ha_ne h'⟩⟩
  have hφ_inj : Function.Injective φ := by
    intro g h hgh
    have heq : (g.1 • a) = (h.1 • a) := congrArg Subtype.val hgh
    have hmem' : h.1⁻¹ * g.1 ∈ pathRootGroup D Γ p :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ h.2) g.2
    have hfix : (h.1⁻¹ * g.1) • a = a := by
      rw [mul_smul, heq, inv_smul_smul]
    have hfix' : ((⟨h.1⁻¹ * g.1, hmem'⟩ : ↥(pathRootGroup D Γ p)) : D) • a = a := hfix
    have huniq := (hR a a ha_adj ha_adj ha_ne ha_ne).unique
      (show ((1 : ↥(pathRootGroup D Γ p)) : D) • a = a by simp) hfix'
    have hval : h.1⁻¹ * g.1 = 1 := (congrArg Subtype.val huniq).symm
    refine Subtype.ext ?_
    calc g.1 = h.1 * (h.1⁻¹ * g.1) := by group
      _ = h.1 := by rw [hval, mul_one]
  have hφ_surj : Function.Surjective φ := by
    intro w
    obtain ⟨g, hg⟩ := (hR a w.1 ha_adj w.2.1 ha_ne w.2.2).exists
    refine ⟨g, ?_⟩
    exact Subtype.ext hg
  have hcompl : Fintype.card {w : V // Γ.Adj (p n) w ∧ w ≠ p (n - 1)} =
      (Γ.neighborFinset (p n)).card - 1 := by
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun w : V => Γ.Adj (p n) w ∧ w ≠ p (n - 1))) =
        (Γ.neighborFinset (p n)).erase (p (n - 1)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset,
        Finset.mem_erase]
      exact and_comm
    rw [hfilter, Finset.card_erase_of_mem hmem, SimpleGraph.card_neighborFinset_eq_degree]
  have hcard : Nat.card ↥(pathRootGroup D Γ p) =
      (Γ.neighborFinset (p n)).card - 1 := by
    rw [Nat.card_congr (Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩), Nat.card_eq_fintype_card, hcompl]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have := hT (p n)
  omega

end CFSG.Quasithin.Stroth

module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphLocal

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

attribute [local instance] auxAction

theorem exists_auxI_adj_of_ne [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {x y : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (hxy : x ≠ y) :
    ∃ z, W.auxI.Adj x z := by
  have hreach : (auxGraph Γ (W.kernelAt 0)).Reachable (x : V) (y : V) :=
    SimpleGraph.ConnectedComponent.reachable_of_mem_supp
      ((auxGraph Γ (W.kernelAt 0)).connectedComponentMk (W.x 0)) x.2 y.2
  obtain ⟨w⟩ := hreach
  have hpos : 0 < w.length := by
    rcases Nat.eq_zero_or_pos w.length with h | h
    · exfalso
      apply hxy
      apply Subtype.ext
      have h1 : (x : V) = (y : V) := by
        rw [← SimpleGraph.Walk.getVert_zero (w := w)]
        exact w.getVert_of_length_le (i := 0) (le_of_eq h)
      exact h1
    · exact h
  have hadj : (auxGraph Γ (W.kernelAt 0)).Adj (x : V) (w.getVert 1) := by
    have h := w.adj_getVert_succ (i := 0) (by omega)
    rwa [SimpleGraph.Walk.getVert_zero] at h
  have hxsupp : (x : V) ∈ ((auxGraph Γ (W.kernelAt 0)).connectedComponentMk
      (W.x 0)).supp := x.2
  refine ⟨⟨w.getVert 1, SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hxsupp
    hadj⟩, ?_⟩
  exact SimpleGraph.induce_adj.mpr hadj

theorem eq_midOf_of_step_eq [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {v w : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (hvw : W.auxI.Adj v w)
    {z : V} (hz : Γ.Adj (v : V) z) (hstep : step hQ v z hz = (w : V)) :
    (⟨z, hz⟩ : {y : V // Γ.Adj (v : V) y}) =
      ⟨midOf hQ v w hvw, midOf_adj_left hQ v w hvw⟩ := by
  apply midFun_injective hQ v
  apply Subtype.ext
  apply Subtype.ext
  show step hQ v z hz = step hQ v (midOf hQ v w hvw) (midOf_adj_left hQ v w hvw)
  rw [hstep, step_midOf hQ v w hvw]

theorem step_eq_of_midOf_eq [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {x z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (hz : W.auxI.Adj x z)
    {v : V} (hv : Γ.Adj (x : V) v) (h : midOf hQ x z hz = v) :
    step hQ x v hv = (z : V) := by
  rw [step_congr hQ x hv (midOf_adj_left hQ x z hz) h.symm]
  exact step_midOf hQ x z hz

theorem exists_auxI_adj_ne [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {v w : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (hvw : W.auxI.Adj v w) :
    ∃ u, W.auxI.Adj v u ∧ u ≠ w := by
  have hm : Γ.Adj (v : V) (midOf hQ v w hvw) := midOf_adj_left hQ v w hvw
  obtain ⟨y, hy, -⟩ := hQ.ne (v : V) (midOf hQ v w hvw) hm
  obtain ⟨z, hz, hz1, -⟩ := hQ.three (v : V) (midOf hQ v w hvw) y hm hy
  refine ⟨⟨step hQ v z hz, step_mem hQ v z hz⟩, step_adjI hQ v z hz, ?_⟩
  intro heq
  have hstep : step hQ v z hz = (w : V) := by
    have h := congrArg
      (fun u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (u : V)) heq
    simpa using h
  exact hz1 (congrArg Subtype.val (eq_midOf_of_step_eq hQ hvw hz hstep))

theorem auxI_twinFree [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) :
    ∀ x y : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      (∀ z, W.auxI.Adj x z ↔ W.auxI.Adj y z) → x = y := by
  intro x y hxy
  by_contra hne
  obtain ⟨z1, hz1⟩ := exists_auxI_adj_of_ne hQ hne
  obtain ⟨z2, hz2, hz21⟩ := exists_auxI_adj_ne hQ hz1
  have hy1 : W.auxI.Adj y z1 := (hxy z1).mp hz1
  have hy2 : W.auxI.Adj y z2 := (hxy z2).mp hz2
  have haux : ∀ z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), (z : V) ∈ auxSet Γ (W.kernelAt 0) :=
    fun z => mem_auxSet_of_mem_auxComp (self_mem_auxSet W) z.2
  have hneV : ∀ {a b : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))}, W.auxI.Adj a b →
      (a : V) ≠ (b : V) := by
    intro a b hab heq
    have hd := (SimpleGraph.induce_adj.mp hab).2.2
    rw [heq, SimpleGraph.dist_self] at hd
    omega
  have hnexy : (x : V) ≠ (y : V) := fun h => hne (Subtype.ext h)
  have hxa1 : Γ.Adj (x : V) (midOf hQ x z1 hz1) := midOf_adj_left hQ x z1 hz1
  have ha1z1 : Γ.Adj (midOf hQ x z1 hz1) (z1 : V) := midOf_adj_right hQ x z1 hz1
  have hxa2 : Γ.Adj (x : V) (midOf hQ x z2 hz2) := midOf_adj_left hQ x z2 hz2
  have ha2z2 : Γ.Adj (midOf hQ x z2 hz2) (z2 : V) := midOf_adj_right hQ x z2 hz2
  have hyb1 : Γ.Adj (y : V) (midOf hQ y z1 hy1) := midOf_adj_left hQ y z1 hy1
  have hb1y : Γ.Adj (midOf hQ y z1 hy1) (y : V) := (midOf_adj_left hQ y z1 hy1).symm
  have hb1z1 : Γ.Adj (midOf hQ y z1 hy1) (z1 : V) := midOf_adj_right hQ y z1 hy1
  have hb2y : Γ.Adj (midOf hQ y z2 hy2) (y : V) := (midOf_adj_left hQ y z2 hy2).symm
  have hb2z2 : Γ.Adj (midOf hQ y z2 hy2) (z2 : V) := midOf_adj_right hQ y z2 hy2
  have hmid1 : midOf hQ x z1 hz1 ≠ midOf hQ y z1 hy1 := by
    intro heq
    have h1 : step hQ z1 (midOf hQ x z1 hz1) ha1z1.symm = (x : V) :=
      (step_unique hQ z1 ha1z1.symm hxa1.symm (hneV hz1) (haux x)).symm
    have h2 : step hQ z1 (midOf hQ x z1 hz1) ha1z1.symm = (y : V) := by
      have h3 : step hQ z1 (midOf hQ y z1 hy1) hb1z1.symm = (y : V) :=
        (step_unique hQ z1 hb1z1.symm hyb1.symm (hneV hy1) (haux y)).symm
      rwa [← step_congr hQ z1 ha1z1.symm hb1z1.symm heq] at h3
    exact hnexy (h1.symm.trans h2)
  have hmid2 : midOf hQ x z2 hz2 ≠ midOf hQ y z2 hy2 := by
    intro heq
    have h1 : step hQ z2 (midOf hQ x z2 hz2) ha2z2.symm = (x : V) :=
      (step_unique hQ z2 ha2z2.symm hxa2.symm (hneV hz2) (haux x)).symm
    have h2 : step hQ z2 (midOf hQ x z2 hz2) ha2z2.symm = (y : V) := by
      have h3 : step hQ z2 (midOf hQ y z2 hy2) hb2z2.symm = (y : V) :=
        (step_unique hQ z2 hb2z2.symm (midOf_adj_left hQ y z2 hy2).symm (hneV hy2) (haux y)).symm
      rwa [← step_congr hQ z2 ha2z2.symm hb2z2.symm heq] at h3
    exact hnexy (h1.symm.trans h2)
  by_cases hxyadj : Γ.Adj (x : V) (y : V)
  · have five : ∀ (z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (hz : W.auxI.Adj x z)
        (hyz : W.auxI.Adj y z), midOf hQ x z hz ≠ (y : V) → False := by
      intro z hz hyz hzy
      have hxz : (x : V) ≠ (z : V) := hneV hz
      have hxdy : (x : V) ≠ (midOf hQ y z hyz) := by
        intro h
        have hxz2 : Γ.Adj (x : V) (z : V) := by
          rw [h]
          exact midOf_adj_right hQ y z hyz
        have hd := (SimpleGraph.induce_adj.mp hz).2.2
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz2] at hd
        omega
      have hzy' : (z : V) ≠ (y : V) := (hneV hyz).symm
      have hbd : midOf hQ x z hz ≠ midOf hQ y z hyz := by
        intro heq
        have h1 : step hQ z (midOf hQ x z hz) (midOf_adj_right hQ x z hz).symm = (x : V) :=
          (step_unique hQ z (midOf_adj_right hQ x z hz).symm (midOf_adj_left hQ x z hz).symm
            (hneV hz) (haux x)).symm
        have h2 : step hQ z (midOf hQ x z hz) (midOf_adj_right hQ x z hz).symm = (y : V) := by
          have h3 : step hQ z (midOf hQ y z hyz) (midOf_adj_right hQ y z hyz).symm = (y : V) :=
            (step_unique hQ z (midOf_adj_right hQ y z hyz).symm
              (midOf_adj_left hQ y z hyz).symm (hneV hyz) (haux y)).symm
          rwa [← step_congr hQ z (midOf_adj_right hQ x z hz).symm
            (midOf_adj_right hQ y z hyz).symm heq] at h3
        exact hnexy (h1.symm.trans h2)
      exact no_five_cycle (five_lt_egirth hQ) (midOf_adj_left hQ x z hz)
        (midOf_adj_right hQ x z hz) (midOf_adj_right hQ y z hyz).symm
        (midOf_adj_left hQ y z hyz).symm hxyadj.symm hxz hxdy hbd hzy hzy'
    by_cases h1 : midOf hQ x z1 hz1 = (y : V)
    · by_cases h2 : midOf hQ x z2 hz2 = (y : V)
      · have e1 : step hQ x (y : V) hxyadj = (z1 : V) :=
          step_eq_of_midOf_eq hQ hz1 hxyadj h1
        have e2 : step hQ x (y : V) hxyadj = (z2 : V) :=
          step_eq_of_midOf_eq hQ hz2 hxyadj h2
        exact hz21 (Subtype.ext (e2.symm.trans e1))
      · exact five z2 hz2 hy2 h2
    · exact five z1 hz1 hy1 h1
  · have ha1y : midOf hQ x z1 hz1 ≠ (y : V) := by
      intro h
      exact hxyadj (by rw [← h]; exact hxa1)
    have ha2y : midOf hQ x z2 hz2 ≠ (y : V) := by
      intro h
      exact hxyadj (by rw [← h]; exact hxa2)
    have hb1x : midOf hQ y z1 hy1 ≠ (x : V) := by
      intro h
      have hxz2 : Γ.Adj (x : V) (z1 : V) := by
        rw [← h]
        exact hb1z1
      have hd := (SimpleGraph.induce_adj.mp hz1).2.2
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz2] at hd
      omega
    have hb2x : midOf hQ y z2 hy2 ≠ (x : V) := by
      intro h
      have hxz2 : Γ.Adj (x : V) (z2 : V) := by
        rw [← h]
        exact hb2z2
      have hd := (SimpleGraph.induce_adj.mp hz2).2.2
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz2] at hd
      omega
    have hW1 : (SimpleGraph.Walk.cons hxa1 (SimpleGraph.Walk.cons ha1z1
        (SimpleGraph.Walk.cons hb1z1.symm (SimpleGraph.Walk.cons hb1y
          SimpleGraph.Walk.nil)))).IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [hxa1.ne, hxa1.ne.symm, hneV hz1, (hneV hz1).symm, hb1x, hb1x.symm, hnexy,
        hnexy.symm, ha1z1.ne, ha1z1.ne.symm, hmid1, hmid1.symm, ha1y, ha1y.symm, hb1z1.ne,
        hb1z1.ne.symm, hneV hy1, (hneV hy1).symm, hb1y.ne, hb1y.ne.symm]
    have hW2 : (SimpleGraph.Walk.cons hxa2 (SimpleGraph.Walk.cons ha2z2
        (SimpleGraph.Walk.cons hb2z2.symm (SimpleGraph.Walk.cons hb2y
          SimpleGraph.Walk.nil)))).IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [hxa2.ne, hxa2.ne.symm, hneV hz2, (hneV hz2).symm, hb2x, hb2x.symm, hnexy,
        hnexy.symm, ha2z2.ne, ha2z2.ne.symm, hmid2, hmid2.symm, ha2y, ha2y.symm, hb2z2.ne,
        hb2z2.ne.symm, hneV hy2, (hneV hy2).symm, hb2y.ne, hb2y.ne.symm]
    have hW12 : (SimpleGraph.Walk.cons hxa1 (SimpleGraph.Walk.cons ha1z1
        (SimpleGraph.Walk.cons hb1z1.symm (SimpleGraph.Walk.cons hb1y
          SimpleGraph.Walk.nil)))) ≠
        (SimpleGraph.Walk.cons hxa2 (SimpleGraph.Walk.cons ha2z2
          (SimpleGraph.Walk.cons hb2z2.symm (SimpleGraph.Walk.cons hb2y
            SimpleGraph.Walk.nil)))) := by
      intro h
      have h2 := congrArg (fun p : Γ.Walk (x : V) (y : V) => p.getVert 2) h
      simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] at h2
      exact hz21 (Subtype.ext h2.symm)
    obtain ⟨_, -, -, c, hc, hclen⟩ :=
      SimpleGraph.Walk.IsPath.exists_isCycle_length_le_add_of_ne hW1 hW2 hW12
    have hlen : (SimpleGraph.Walk.cons hxa1 (SimpleGraph.Walk.cons ha1z1
        (SimpleGraph.Walk.cons hb1z1.symm (SimpleGraph.Walk.cons hb1y
          SimpleGraph.Walk.nil)))).length +
        (SimpleGraph.Walk.cons hxa2 (SimpleGraph.Walk.cons ha2z2
          (SimpleGraph.Walk.cons hb2z2.symm (SimpleGraph.Walk.cons hb2y
            SimpleGraph.Walk.nil)))).length = 8 := by simp
    rw [hlen] at hclen
    have h1 : Γ.egirth ≤ ((c.length : ℕ) : ℕ∞) := SimpleGraph.egirth_le_length hc
    have h2 : ((c.length : ℕ) : ℕ∞) ≤ (8 : ℕ∞) := by exact_mod_cast hclen
    have h3 : ((2 * 8 + 2 : ℕ) : ℕ∞) ≤ (8 : ℕ∞) := le_trans hQ.egirth.le (le_trans h1 h2)
    norm_num at h3

theorem auxI_adj_smul_iff [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (g : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0)))
    {a b : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} :
    W.auxI.Adj (g • a) (g • b) ↔ W.auxI.Adj a b := by
  have hnorm : (g : H) ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H) :=
    (Subgroup.mem_inf.mp g.2).1
  have hnorm' : ((g⁻¹ : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) : H) ∈
      Subgroup.normalizer ((W.kernelAt 0) : Set H) := (Subgroup.mem_inf.mp (g⁻¹).2).1
  constructor
  · intro h
    have h1 := auxGraph_adj_smul hnorm' (SimpleGraph.induce_adj.mp h)
    have h2 : ((g⁻¹ : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) : H) •
        (((g • a : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) : V)) = (a : V) := by
      show ((g⁻¹ : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) : H) • ((g : H) • (a : V)) = (a : V)
      rw [← mul_smul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, one_smul]
    have h3 : ((g⁻¹ : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) : H) •
        (((g • b : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) : V)) = (b : V) := by
      show ((g⁻¹ : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) : H) • ((g : H) • (b : V)) = (b : V)
      rw [← mul_smul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, one_smul]
    rw [h2, h3] at h1
    exact SimpleGraph.induce_adj.mpr h1
  · intro h
    exact SimpleGraph.induce_adj.mpr
      (auxGraph_adj_smul hnorm (SimpleGraph.induce_adj.mp h))

theorem mem_fixingSubgroup_of_fixes_auxI [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {g : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))}
    {u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))}
    (hfix : ∀ v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), W.auxI.Adj u v →
      (auxProj W g) • v = v) :
    (g : H) ∈ fixingSubgroup H (Γ.neighborSet (u : V)) := by
  have hmap : ∀ {a b : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))}, W.auxI.Adj a b →
      W.auxI.Adj (g • a) (g • b) := fun h => (auxI_adj_smul_iff g).mpr h
  have hgz : ∀ z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), W.auxI.Adj u z → g • z = z := by
    intro z hz
    have h := auxProj_smul W g z
    rw [hfix z hz] at h
    exact h.symm
  have hgu : g • u = u := by
    by_contra hne
    have htw : ∀ z, W.auxI.Adj u z ↔ W.auxI.Adj (g • u) z := by
      intro z
      constructor
      · intro hz
        have h1 := hmap hz
        rwa [hgz z hz] at h1
      · intro hz
        have h2 : W.auxI.Adj (g⁻¹ • (g • u)) (g⁻¹ • z) :=
          (auxI_adj_smul_iff (g := g⁻¹)).mpr hz
        have h3 : g⁻¹ • (g • u) = u := by
          rw [← mul_smul, inv_mul_cancel, one_smul]
        rw [h3] at h2
        have h4 : g • (g⁻¹ • z) = z := by
          rw [← mul_smul, mul_inv_cancel, one_smul]
        have h5 := hgz (g⁻¹ • z) h2
        have h6 : g⁻¹ • z = z := h5.symm.trans h4
        rwa [h6] at h2
    exact hne (auxI_twinFree hQ u (g • u) htw).symm
  rw [mem_fixingSubgroup_iff]
  intro y hy
  by_contra hne
  have hv : W.auxI.Adj u ⟨step hQ u y hy, step_mem hQ u y hy⟩ := step_adjI hQ u y hy
  have hgv : g • (⟨step hQ u y hy, step_mem hQ u y hy⟩ :
      ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) = ⟨step hQ u y hy, step_mem hQ u y hy⟩ := by
    have h := auxProj_smul W g ⟨step hQ u y hy, step_mem hQ u y hy⟩
    rw [hfix _ hv] at h
    exact h.symm
  have hgvV : (g : H) • step hQ u y hy = step hQ u y hy := by
    have h := congrArg (fun z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (z : V)) hgv
    exact h
  have hguV : (g : H) • (u : V) = (u : V) := congrArg
    (fun z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (z : V)) hgu
  have hgy_u : Γ.Adj ((g : H) • y) (u : V) := by
    have h := (GraphAction.adj_smul (g : H) (u : V) y).mpr hy
    rw [hguV] at h
    exact h.symm
  have hgy_v : Γ.Adj ((g : H) • y) (step hQ u y hy) := by
    have h := (GraphAction.adj_smul (g : H) y (step hQ u y hy)).mpr
      (step_spec hQ u y hy).1
    rwa [hgvV] at h
  exact no_four_cycle (four_lt_egirth hQ) hy (step_spec hQ u y hy).1 hgy_v.symm hgy_u
    (step_spec hQ u y hy).2.1.symm (fun h => hne h.symm)

theorem ClosedGoodPath.QuarterHyp.weissFree_aux [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) : WeissFree ↥W.auxS W.auxI 4 := by
  classical
  letI := auxAction Γ (W.kernelAt 0) (W.x 0)
  intro p hp h hfix h0 h1
  obtain ⟨P, hPnb, hP2, hPodd, hPfix⟩ := exists_lift hQ p hp
  have h34 : W.auxI.Adj (p 3) (p 4) := p.adj 3 (by omega)
  have haux : ∀ z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), (z : V) ∈ auxSet Γ (W.kernelAt 0) :=
    fun z => mem_auxSet_of_mem_auxComp (self_mem_auxSet W) z.2
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp h.2
  have hgeq : auxProj W g = h := Subtype.ext hg
  have hnorm : (g : H) ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H) :=
    (Subgroup.mem_inf.mp g.2).1
  have hgp : ∀ i : ℕ, i ≤ 4 → g • p i = p i := by
    intro i hi
    have h := auxProj_smul W g (p i)
    rw [hgeq, hfix i hi] at h
    exact h.symm
  have hgV : ∀ (i : ℕ), i ≤ 4 → (g : H) • (p i).1 = (p i).1 := by
    intro i hi
    exact congrArg (fun z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) => (z : V)) (hgp i hi)
  have hgmid : ∀ (j : ℕ) (hj : j ≤ 3),
      (g : H) • midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)) =
        midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)) := by
    intro j hj
    have hgu : (g : H) • (p j).1 = (p j).1 := hgV j (by omega)
    have hm : Γ.Adj ((p j) : V) (midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) :=
      midOf_adj_left hQ (p j) (p (j + 1)) (p.adj j (by omega))
    have hhy : Γ.Adj ((p j) : V)
        ((g : H) • midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) := by
      have h := (GraphAction.adj_smul (g : H)
        (midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) ((p j) : V)).mpr hm.symm
      rw [hgu] at h
      exact h.symm
    have hstep := step_smul hQ (p j) hm hnorm hgu hhy
    rw [step_midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))] at hstep
    have hgpj1 : (g : H) • (p (j + 1)).1 = (p (j + 1)).1 := hgV (j + 1) (by omega)
    rw [hgpj1] at hstep
    have hmidEq : (⟨(g : H) • midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)), hhy⟩ :
        {y : V // Γ.Adj ((p j) : V) y}) =
        ⟨midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)), hm⟩ := by
      apply midFun_injective hQ (p j)
      apply Subtype.ext
      apply Subtype.ext
      show step hQ (p j) ((g : H) • midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) hhy =
        step hQ (p j) (midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) hm
      rw [hstep, step_midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))]
    exact congrArg Subtype.val hmidEq
  have hgP : ∀ i : ℕ, i ≤ 8 → (g : H) • P i = P i := by
    intro i hi
    have hi9 : i < 9 := by omega
    interval_cases i
    · rw [hP2 0 (by omega)]; exact hgV 0 (by omega)
    · rw [show P 1 = midOf hQ (p 0) (p 1) (p.adj 0 (by omega)) from by
        have h := hPodd 0 (by omega); simpa using h]
      exact hgmid 0 (by omega)
    · rw [hP2 1 (by omega)]; exact hgV 1 (by omega)
    · rw [show P 3 = midOf hQ (p 1) (p 2) (p.adj 1 (by omega)) from by
        have h := hPodd 1 (by omega); simpa using h]
      exact hgmid 1 (by omega)
    · rw [hP2 2 (by omega)]; exact hgV 2 (by omega)
    · rw [show P 5 = midOf hQ (p 2) (p 3) (p.adj 2 (by omega)) from by
        have h := hPodd 2 (by omega); simpa using h]
      exact hgmid 2 (by omega)
    · rw [hP2 3 (by omega)]; exact hgV 3 (by omega)
    · rw [show P 7 = midOf hQ (p 3) (p 4) (p.adj 3 (by omega)) from by
        have h := hPodd 3 (by omega); simpa using h]
      exact hgmid 3 (by omega)
    · rw [hP2 4 (by omega)]; exact hgV 4 (by omega)
  have hP7 : P 7 = midOf hQ (p 3) (p 4) h34 := by
    have h := hPodd 3 (by omega); simpa using h
  obtain ⟨p9, hp9, hp97⟩ := hQ.ne ((p 4) : V) (midOf hQ (p 3) (p 4) h34)
    (midOf_adj_right hQ (p 3) (p 4) h34).symm
  have hp97' : p9 ≠ P 7 := by rw [hP7]; exact hp97
  have hP8p9 : Γ.Adj (P 8) p9 := by rw [hP2 4 le_rfl]; exact hp9
  have hKp9 : ∀ k ∈ W.kernelAt 0, k • p9 = p9 := by
    intro k hk
    exact (mem_fixingSubgroup_iff H).mp (haux (p 4) hk) p9 hp9
  let P9 : GPath Γ 9 := P.snoc p9 hP8p9
  have hP9le : ∀ j : ℕ, j ≤ 8 → P9 j = P j := fun j hj => GPath.snoc_of_le P p9 hP8p9 hj
  have hP9nine : P9 9 = p9 := GPath.snoc_last P p9 hP8p9
  have hP9nb : P9.NoBack := by
    intro i hi
    by_cases h8 : i + 2 ≤ 8
    · rw [hP9le i (by omega), hP9le (i + 2) h8]
      exact hPnb i (by omega)
    · have hi7 : i = 7 := by omega
      subst hi7
      rw [hP9le 7 (by omega), hP9nine]
      exact fun h => hp97' h.symm
  have hP9fix : ∀ j, j ≤ 9 → ∀ k ∈ W.kernelAt 0, k • P9 j = P9 j := by
    intro j hj k hk
    by_cases h9 : j = 9
    · subst h9; rw [hP9nine]; exact hKp9 k hk
    · have hj8 : j < 9 := Nat.lt_of_le_of_ne hj h9
      rw [hP9le j (Nat.lt_succ_iff.mp hj8)]
      exact hPfix j (by omega) k hk
  have hgP8 : (g : H) • P 8 = P 8 := hgP 8 (by omega)
  have hgy9 : Γ.Adj (P 8) ((g : H) • p9) := by
    have h := (GraphAction.adj_smul (g : H) p9 (P 8)).mpr hP8p9.symm
    rw [hgP8] at h
    exact h.symm
  have hgne9 : (g : H) • p9 ≠ P 7 := by
    intro h
    apply hp97'
    have h7 : (g : H) • P 7 = P 7 := hgP 7 (by omega)
    have h2 : (g : H) • P 7 = (g : H) • p9 := by rw [h7, h]
    rw [smul_left_cancel_iff] at h2
    exact h2.symm
  obtain ⟨u, hu_fix, hu_p9⟩ := hQ.moufang P hPnb p9 ((g : H) • p9) hP8p9 hgy9 hp97' hgne9
  have hU : u ∈ pathRootGroup H Γ P := mem_pathRootGroup.mpr hu_fix
  obtain ⟨W', hW'⟩ := ClosedGoodPath.exists_of_noBack (by norm_num : 3 ≤ 8) hQ.moufang
    hQ.weissFree hQ.ne hQ.localFacts hP9nb
  have hP9zero : P9 0 = ((p 0) : V) := by
    rw [hP9le 0 (by omega), hP2 0 (by omega)]
  have hW'stab : GPath.stabPath (H := H) P9 = W'.stab := by
    rw [← ClosedGoodPath.stabPath_window (H := H) (by norm_num : 3 ≤ 8) hQ.weissFree
      hQ.localFacts W' 0]
    congr 1
    apply GPath.ext'
    intro j hj
    rw [ClosedGoodPath.window_apply W' 0 hj, zero_add, hW' j (by omega)]
  have hW'ker : W'.kernelAt 0 = W.kernelAt 0 := by
    have h0 : W'.x (0 : ℤ) = ((p 0) : V) := by
      have := hW' 0 (by omega)
      simpa [hP9zero] using this
    have h := kernel_eq_of_fix (H := H) hQ (u := ((p 0) : V)) (p 0).2 hP9nb hP9zero hP9fix
    rw [ClosedGoodPath.kernelAt, h0, ← hW'stab]
    exact h
  have hP2mem : P 2 = ((p 1) : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) := by
    rw [hP2 1 (by omega)]
  have huinv : (u⁻¹ * (g : H) : H) ∈ W'.kernelAt 2 := by
    have hx2 : W'.x (2 : ℤ) = P 2 := by
      have h := hW' 2 (by omega)
      rw [hP9le 2 (by omega), hP2 1 (by omega)] at h
      rw [hP2 1 (by omega)]
      exact h
    have h2 : (u⁻¹ * (g : H) : H) ∈ fixingSubgroup H (Γ.neighborSet (W'.x 2)) := by
      rw [hx2]
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have hu2 : u ∈ fixingSubgroup H (Γ.neighborSet (P 2)) :=
        (mem_fixingSubgroup_iff H).mpr ((mem_pathRootGroup.mp hU) 2 (by omega) (by omega))
      have hg2 : (g : H) ∈ fixingSubgroup H (Γ.neighborSet (P 2)) := by
        have h := hP2mem
        rw [h] at *
        exact mem_fixingSubgroup_of_fixes_auxI hQ (g := g) (u := p 1)
          (fun v hv => by rw [hgeq]; exact h1 v hv)
      have huy : u • y = y := (mem_fixingSubgroup_iff H).mp hu2 y hy
      have hgy : (g : H) • y = y := (mem_fixingSubgroup_iff H).mp hg2 y hy
      calc (u⁻¹ * g : H) • y = u⁻¹ • ((g : H) • y) := mul_smul _ _ _
        _ = u⁻¹ • y := by rw [hgy]
        _ = y := by
          conv_lhs => rw [← huy]
          rw [inv_smul_smul]
    have h9 : (u⁻¹ * (g : H) : H) ∈ GPath.stabPath (H := H) P9 := by
      rw [GPath.mem_stabPath_iff]
      intro j hj
      by_cases h9 : j = 9
      · subst h9
        rw [hP9nine, mul_smul, ← hu_p9, inv_smul_smul]
      · have hj9 : j < 9 := Nat.lt_of_le_of_ne hj h9
        have hj8 : j ≤ 8 := Nat.lt_succ_iff.mp hj9
        rw [hP9le j hj8, mul_smul, hgP j (by omega)]
        have huPj : u • P j = P j := by
          interval_cases j
          · exact (mem_pathRootGroup.mp hU) 1 (by omega) (by omega) (P 0)
              (P.adj 0 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 2 (by omega) (by omega) (P 1)
              (P.adj 1 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 3 (by omega) (by omega) (P 2)
              (P.adj 2 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 4 (by omega) (by omega) (P 3)
              (P.adj 3 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 5 (by omega) (by omega) (P 4)
              (P.adj 4 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 6 (by omega) (by omega) (P 5)
              (P.adj 5 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 7 (by omega) (by omega) (P 6)
              (P.adj 6 (by omega)).symm
          · exact (mem_pathRootGroup.mp hU) 6 (by omega) (by omega) (P 7)
              (P.adj 6 (by omega))
          · exact (mem_pathRootGroup.mp hU) 7 (by omega) (by omega) (P 8)
              (P.adj 7 (by omega))
        calc u⁻¹ • P j = u⁻¹ • (u • P j) := by rw [huPj]
          _ = P j := inv_smul_smul u (P j)
    rw [ClosedGoodPath.kernelAt]
    exact Subgroup.mem_inf.mpr ⟨h2, hW'stab ▸ h9⟩
  have hW'ker2 : W'.kernelAt 2 = W'.kernelAt 0 := by
    refine ClosedGoodPath.kernelAt_eq_of_le (by norm_num : 3 ≤ 8) hQ.moufang hQ.weissFree
      hQ.ne hQ.localFacts hQ.loc W' 1 ?_
    have hx2 : W'.x (2 * (1 : ℤ)) = ((p 1) : V) := by
      have h2' : W'.x (2 : ℤ) = P9 2 := by simpa using hW' 2 (by omega)
      rw [show 2 * (1 : ℤ) = 2 by norm_num, h2', hP9le 2 (by omega), hP2 1 (by omega)]
    rw [hx2, hW'ker]
    exact haux (p 1)
  have hKer : (u⁻¹ * (g : H) : H) ∈ W.kernelAt 0 := by
    have hle : W'.kernelAt 2 ≤ W.kernelAt 0 := by rw [hW'ker2, hW'ker]
    exact hle huinv
  have hP0adj : P 0 = ((p 0) : V) := by simpa using hP2 0 (by omega)
  have huG : u ∈ fixingSubgroup H (Γ.neighborSet (P 0)) := by
    have hKle : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (P 0)) := by
      rw [hP0adj]
      exact haux (p 0)
    have hg0 : (g : H) ∈ fixingSubgroup H (Γ.neighborSet (P 0)) := by
      rw [hP0adj]
      exact mem_fixingSubgroup_of_fixes_auxI hQ (g := g) (u := p 0)
        (fun v hv => by rw [hgeq]; exact h0 v hv)
    have h1' : (u⁻¹ : H) ∈ fixingSubgroup H (Γ.neighborSet (P 0)) := by
      have h2' : ((u⁻¹ * (g : H)) * (g : H)⁻¹ : H) ∈
          fixingSubgroup H (Γ.neighborSet (P 0)) :=
        Subgroup.mul_mem _ (hKle hKer) (Subgroup.inv_mem _ hg0)
      simpa using h2'
    rwa [inv_mem_iff] at h1'
  have hu1 : u = 1 := by
    have hmem : u ∈ fixingSubgroup H (Γ.neighborSet (P 0)) ⊓ pathRootGroup H Γ P :=
      Subgroup.mem_inf.mpr ⟨huG, hU⟩
    rw [fixingSubgroup_inf_pathRootGroup_eq_bot (by norm_num : 2 ≤ 8) hQ.weissFree hPnb] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hgK : (g : H) ∈ W.kernelAt 0 := by
    have h : u⁻¹ * (g : H) = (g : H) := by rw [hu1, inv_one, one_mul]
    rwa [h] at hKer
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro v
  apply Subtype.ext
  have h1' : (g : H) • (v : V) = (v : V) := by
    exact MulAction.mem_stabilizer_iff.mp ((hQ.localFacts (v : V)).kernel_le (haux v hgK))
  calc ((h : Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) v : V)
      = ((auxProj W g : Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) v : V) := by
        rw [hgeq]
    _ = (g : H) • (v : V) := rfl
    _ = (v : V) := h1'
    _ = ((1 : Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) v : V) := rfl

private theorem exists_auxI_adj [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) : ∃ z, W.auxI.Adj u z := by
  by_cases hu : u = (⟨W.x 0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ :
      ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
  · subst hu
    have hx2aux : W.x 2 ∈ auxSet Γ (W.kernelAt 0) := (hQ.quarter 2).mpr (by norm_num)
    have hdist : Γ.dist (W.x 0) (W.x 2) = 2 := by
      have hwalk : Γ.Walk (W.x 0) (W.x 2) :=
        SimpleGraph.Walk.cons (W.adj 0) (SimpleGraph.Walk.cons (W.adj 1) SimpleGraph.Walk.nil)
      have hle : Γ.dist (W.x 0) (W.x 2) ≤ 2 := by
        have h := SimpleGraph.dist_le (SimpleGraph.Walk.cons (W.adj 0)
          (SimpleGraph.Walk.cons (W.adj 1) SimpleGraph.Walk.nil))
        simpa using h
      have hne0 : (W.x 0 : V) ≠ W.x 2 := W.ne_add_two 0
      have hreach : Γ.Reachable (W.x 0) (W.x 2) := ⟨hwalk⟩
      have hnadj : ¬ Γ.Adj (W.x 0) (W.x 2) := by
        intro hc
        exact no_triangle (four_lt_egirth hQ) (W.adj 0) (W.adj 1) hc.symm
      have h2 : 1 < Γ.dist (W.x 0) (W.x 2) :=
        SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj hreach hne0 hnadj
      exact le_antisymm hle (Nat.succ_le_of_lt h2)
    have hadj : (auxGraph Γ (W.kernelAt 0)).Adj (W.x 0) (W.x 2) :=
      ⟨self_mem_auxSet W, hx2aux, hdist⟩
    refine ⟨⟨W.x 2, SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem) hadj⟩, ?_⟩
    exact SimpleGraph.induce_adj.mpr hadj
  · exact exists_auxI_adj_of_ne hQ hu

theorem exists_auxI_path [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    ∃ p : GPath W.auxI 4, p 0 = u ∧ p.NoBack := by
  obtain ⟨z0, hz0⟩ := exists_auxI_adj hQ u
  obtain ⟨p2, h12, h21⟩ := exists_auxI_adj_ne hQ hz0.symm
  obtain ⟨p3, h23, h32⟩ := exists_auxI_adj_ne hQ h12.symm
  obtain ⟨p4, h34, h43⟩ := exists_auxI_adj_ne hQ h23.symm
  refine ⟨GPath.cons u (GPath.cons z0 (GPath.cons p2 (GPath.cons p3 (GPath.nil p4) h34) h23)
    h12) hz0, rfl, ?_⟩
  intro i hi
  have hi3 : i < 3 := by omega
  interval_cases i
  · show u ≠ p2
    exact fun h => h21 (Subtype.ext (by simpa using congrArg Subtype.val h.symm))
  · show z0 ≠ p3
    exact h32.symm
  · show p2 ≠ p4
    exact h43.symm

end CFSG.Quasithin.Stroth.WeissDelta

end

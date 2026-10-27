module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraph2

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

attribute [local instance] auxAction

theorem auxComp_eq_of_mem {K : Subgroup H} {u₀ v : V}
    (hv : v ∈ auxComp Γ K u₀) : auxComp Γ K v = auxComp Γ K u₀ := by
  have hv' := hv
  rw [auxComp, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv'
  rw [auxComp, auxComp, hv']

theorem mem_auxSet_of_mem_auxComp {K : Subgroup H} {u₀ : V} (h₀ : u₀ ∈ auxSet Γ K)
    {u : V} (hu : u ∈ auxComp Γ K u₀) : u ∈ auxSet Γ K := by
  have hreach : (auxGraph Γ K).Reachable u₀ u := by
    rw [auxComp, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm] at hu
    exact hu
  obtain ⟨w⟩ := hreach
  have key : ∀ {a b : V}, (auxGraph Γ K).Walk a b → a ∈ auxSet Γ K → b ∈ auxSet Γ K := by
    intro a b w
    induction w with
    | nil => exact id
    | cons h p ih => exact fun _ => ih h.2.1
  exact key w h₀

theorem no_triangle (hG : (4 : ℕ∞) < Γ.egirth)
    {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hca : Γ.Adj c a) : False := by
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    simp [hab.ne, hab.ne.symm, hbc.ne, hca.ne, hca.ne.symm]
  have hle : Γ.egirth ≤ (3 : ℕ∞) := by
    have h := SimpleGraph.egirth_le_length hcyc
    simpa using h
  have hlt : (4 : ℕ∞) < (3 : ℕ∞) := lt_of_lt_of_le hG hle
  norm_num at hlt

theorem no_four_cycle (hG : (4 : ℕ∞) < Γ.egirth)
    {a b c d : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hcd : Γ.Adj c d) (hda : Γ.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    simp [hab.ne, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hda.ne.symm, hac, hac.symm, hbd]
  have hle : Γ.egirth ≤ (4 : ℕ∞) := by
    have h := SimpleGraph.egirth_le_length hcyc
    simpa using h
  have hlt : (4 : ℕ∞) < (4 : ℕ∞) := lt_of_lt_of_le hG hle
  norm_num at hlt

theorem no_five_cycle (hG : (5 : ℕ∞) < Γ.egirth)
    {a b c d e : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hcd : Γ.Adj c d) (hde : Γ.Adj d e)
    (hea : Γ.Adj e a) (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e)
    (hce : c ≠ e) : False := by
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hde
        (SimpleGraph.Walk.cons hea SimpleGraph.Walk.nil))))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    simp [hab.ne, hab.ne.symm, hbc.ne, hcd.ne, hde.ne, hea.ne, hea.ne.symm, hac, hac.symm,
      had, had.symm, hbd, hbe, hbe.symm, hce, hce.symm]
  have hle : Γ.egirth ≤ (5 : ℕ∞) := by
    have h := SimpleGraph.egirth_le_length hcyc
    simpa using h
  have hlt : (5 : ℕ∞) < (5 : ℕ∞) := lt_of_lt_of_le hG hle
  norm_num at hlt

theorem four_lt_egirth {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) :
    (4 : ℕ∞) < Γ.egirth := by
  have h : ((2 * 8 + 2 : ℕ) : ℕ∞) < Γ.egirth := hQ.egirth
  have h' : ((4 : ℕ) : ℕ∞) < ((2 * 8 + 2 : ℕ) : ℕ∞) := by norm_num
  exact lt_trans h' h

theorem five_lt_egirth {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) :
    (5 : ℕ∞) < Γ.egirth := by
  have h : ((2 * 8 + 2 : ℕ) : ℕ∞) < Γ.egirth := hQ.egirth
  have h' : ((5 : ℕ) : ℕ∞) < ((2 * 8 + 2 : ℕ) : ℕ∞) := by norm_num
  exact lt_trans h' h

theorem mem_auxComp_smul {K : Subgroup H} {u₀ : V} {g : H}
    (hnorm : g ∈ Subgroup.normalizer (K : Set H)) (hfix : g • u₀ = u₀) {v : V}
    (hv : v ∈ auxComp Γ K u₀) : g • v ∈ auxComp Γ K u₀ := by
  rw [auxComp, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ⊢
  rw [SimpleGraph.ConnectedComponent.eq] at hv ⊢
  have hmap : (auxGraph Γ K).Reachable (g • v) (g • u₀) :=
    hv.map ⟨fun x => g • x, fun {x y} hxy => auxGraph_adj_smul hnorm hxy⟩
  rwa [hfix] at hmap

theorem mem_auxGroup_of_normalizes_of_fixes {K : Subgroup H} {u₀ : V} {g : H}
    (hnorm : g ∈ Subgroup.normalizer (K : Set H)) (hfix : g • u₀ = u₀) :
    g ∈ auxGroup Γ K u₀ := by
  refine Subgroup.mem_inf.mpr ⟨hnorm, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · intro v hv
    rw [Set.mem_smul_set] at hv
    obtain ⟨s, hs, rfl⟩ := hv
    exact mem_auxComp_smul hnorm hfix hs
  · intro v hv
    rw [Set.mem_smul_set]
    have hfix' : g⁻¹ • u₀ = u₀ := by
      calc g⁻¹ • u₀ = g⁻¹ • (g • u₀) := by rw [hfix]
        _ = u₀ := inv_smul_smul g u₀
    exact ⟨g⁻¹ • v, mem_auxComp_smul (Subgroup.inv_mem _ hnorm) hfix' hv, by simp⟩

theorem mem_auxGroup_of_normalizes_of_fixes_mem {K : Subgroup H} {u₀ : V} {g : H}
    (hnorm : g ∈ Subgroup.normalizer (K : Set H)) {v : V} (hv : v ∈ auxComp Γ K u₀)
    (hgv : g • v = v) : g ∈ auxGroup Γ K u₀ := by
  have hmem : g ∈ auxGroup Γ K v := mem_auxGroup_of_normalizes_of_fixes hnorm hgv
  have hcomp : auxComp Γ K v = auxComp Γ K u₀ := auxComp_eq_of_mem hv
  simpa [auxGroup, hcomp] using hmem

theorem self_mem_auxSet (W : ClosedGoodPath H Γ) :
    W.x 0 ∈ auxSet Γ (W.kernelAt 0) :=
  (inf_le_left : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x 0)))

@[expose] noncomputable def step [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (y : V) (hy : Γ.Adj (u : V) y) : V :=
  (hQ.existsUnique_auxSet_adj u.2 hy).exists.choose

theorem step_spec [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (y : V) (hy : Γ.Adj (u : V) y) :
    Γ.Adj y (step hQ u y hy) ∧ step hQ u y hy ≠ (u : V) ∧
      step hQ u y hy ∈ auxSet Γ (W.kernelAt 0) :=
  (hQ.existsUnique_auxSet_adj u.2 hy).exists.choose_spec

theorem step_unique [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {y : V} (hy : Γ.Adj (u : V) y) {v : V}
    (hv : Γ.Adj y v) (hne : v ≠ (u : V)) (haux : v ∈ auxSet Γ (W.kernelAt 0)) :
    v = step hQ u y hy :=
  ((hQ.existsUnique_auxSet_adj u.2 hy).unique (step_spec hQ u y hy)
    ⟨hv, hne, haux⟩).symm

theorem step_congr [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {y y' : V} (hy : Γ.Adj (u : V) y)
    (hy' : Γ.Adj (u : V) y') (h : y = y') : step hQ u y hy = step hQ u y' hy' := by
  subst h
  rfl

theorem step_dist [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (y : V) (hy : Γ.Adj (u : V) y) :
    Γ.dist (u : V) (step hQ u y hy) = 2 := by
  have hspec := step_spec hQ u y hy
  have hle : Γ.dist (u : V) (step hQ u y hy) ≤ 2 := by
    have h := SimpleGraph.dist_le (SimpleGraph.Walk.cons hy
      (SimpleGraph.Walk.cons hspec.1 SimpleGraph.Walk.nil))
    simpa using h
  have hreach : Γ.Reachable (u : V) (step hQ u y hy) :=
    ⟨SimpleGraph.Walk.cons hy (SimpleGraph.Walk.cons hspec.1 SimpleGraph.Walk.nil)⟩
  have hnadj : ¬ Γ.Adj (u : V) (step hQ u y hy) := by
    intro hc
    exact no_triangle (four_lt_egirth hQ) hy hspec.1 hc.symm
  have hgt : 1 < Γ.dist (u : V) (step hQ u y hy) :=
    SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj hreach
      (fun h => hspec.2.1 h.symm) hnadj
  exact le_antisymm hle (Nat.succ_le_of_lt hgt)

theorem step_mem [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (y : V) (hy : Γ.Adj (u : V) y) :
    step hQ u y hy ∈ auxComp Γ (W.kernelAt 0) (W.x 0) := by
  have hspec := step_spec hQ u y hy
  have hadj : (auxGraph Γ (W.kernelAt 0)).Adj (u : V) (step hQ u y hy) :=
    ⟨mem_auxSet_of_mem_auxComp (self_mem_auxSet W) u.2, hspec.2.2, step_dist hQ u y hy⟩
  exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp
    ((auxGraph Γ (W.kernelAt 0)).connectedComponentMk (W.x 0)) u.2 hadj

theorem step_adjI [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (y : V) (hy : Γ.Adj (u : V) y) :
    W.auxI.Adj u ⟨step hQ u y hy, step_mem hQ u y hy⟩ := by
  have hspec := step_spec hQ u y hy
  rw [show W.auxI.Adj u ⟨step hQ u y hy, step_mem hQ u y hy⟩ ↔
    (auxGraph Γ (W.kernelAt 0)).Adj (u : V) (step hQ u y hy) from
    SimpleGraph.induce_adj]
  exact ⟨mem_auxSet_of_mem_auxComp (self_mem_auxSet W) u.2, hspec.2.2, step_dist hQ u y hy⟩

@[expose] noncomputable def midFun [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
    (y : {y : V // Γ.Adj (u : V) y}) :
    {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v} :=
  ⟨⟨step hQ u y.1 y.2, step_mem hQ u y.1 y.2⟩, step_adjI hQ u y.1 y.2⟩

theorem midFun_injective [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    Function.Injective (midFun hQ u) := by
  intro y y' h
  have hval : step hQ u y.1 y.2 = step hQ u y'.1 y'.2 := by
    have h' := congrArg (fun z : {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) //
      W.auxI.Adj u v} => (z.1 : V)) h
    simpa [midFun] using h'
  by_contra hne
  refine no_four_cycle (four_lt_egirth hQ) y.2 (step_spec hQ u y.1 y.2).1 ?_
    (SimpleGraph.Adj.symm y'.2) (step_spec hQ u y.1 y.2).2.1.symm ?_
  · rw [hval]
    exact (step_spec hQ u y'.1 y'.2).1.symm
  · intro heq
    exact hne (Subtype.ext heq)

theorem midFun_surjective [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    Function.Surjective (midFun hQ u) := by
  rintro ⟨v, hv⟩
  have hdist : Γ.dist (u : V) (v : V) = 2 := (SimpleGraph.induce_adj.mp hv).2.2
  obtain ⟨y, hyu, hyv⟩ := exists_common_adj_of_dist_eq_two hdist
  have hne : (v : V) ≠ (u : V) := by
    intro heq
    rw [← heq] at hdist
    rw [SimpleGraph.dist_self] at hdist
    omega
  have haux : (v : V) ∈ auxSet Γ (W.kernelAt 0) :=
    mem_auxSet_of_mem_auxComp (self_mem_auxSet W) v.2
  have hstep : (v : V) = step hQ u y hyu := step_unique hQ u hyu hyv.symm hne haux
  refine ⟨⟨y, hyu⟩, ?_⟩
  exact Subtype.ext (Subtype.ext hstep.symm)

@[expose] noncomputable def midEquiv [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    {y : V // Γ.Adj (u : V) y} ≃ {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v} :=
  Equiv.ofBijective (midFun hQ u) ⟨midFun_injective hQ u, midFun_surjective hQ u⟩

@[expose] noncomputable def midOf [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (h : W.auxI.Adj u v) : V :=
  ((midEquiv hQ u).symm ⟨v, h⟩).1

theorem midOf_adj_left [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (h : W.auxI.Adj u v) :
    Γ.Adj (u : V) (midOf hQ u v h) :=
  ((midEquiv hQ u).symm ⟨v, h⟩).2

theorem midEquiv_midOf [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (h : W.auxI.Adj u v) :
    midEquiv hQ u ⟨midOf hQ u v h, midOf_adj_left hQ u v h⟩ = ⟨v, h⟩ := by
  have h1 := (midEquiv hQ u).apply_symm_apply ⟨v, h⟩
  exact h1

theorem step_midOf [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (h : W.auxI.Adj u v) :
    step hQ u (midOf hQ u v h) (midOf_adj_left hQ u v h) = (v : V) := by
  have h1 := midEquiv_midOf hQ u v h
  rw [show midEquiv hQ u ⟨midOf hQ u v h, midOf_adj_left hQ u v h⟩ =
    midFun hQ u ⟨midOf hQ u v h, midOf_adj_left hQ u v h⟩ from
    Equiv.ofBijective_apply _ _ _] at h1
  have h2 : ((midFun hQ u ⟨midOf hQ u v h, midOf_adj_left hQ u v h⟩ :
    {w : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u w}).1 : V) = (v : V) := by
    rw [h1]
  simpa [midFun] using h2

theorem midOf_adj_right [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) (h : W.auxI.Adj u v) :
    Γ.Adj (midOf hQ u v h) (v : V) := by
  have h1 := (step_spec hQ u (midOf hQ u v h) (midOf_adj_left hQ u v h)).1
  rwa [step_midOf hQ u v h] at h1

theorem step_smul [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) {y : V} (hy : Γ.Adj (u : V) y) {g : H}
    (hnorm : g ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H)) (hgu : g • (u : V) = (u : V))
    (hy' : Γ.Adj (u : V) (g • y)) :
    step hQ u (g • y) hy' = g • step hQ u y hy := by
  have hspec := step_spec hQ u y hy
  refine (step_unique hQ u hy' ?_ ?_ ?_).symm
  · exact (GraphAction.adj_smul g y (step hQ u y hy)).mpr hspec.1
  · intro heq
    have h2 : step hQ u y hy = g⁻¹ • (u : V) := by
      rw [← heq, inv_smul_smul]
    have h3 : g⁻¹ • (u : V) = (u : V) := by
      calc g⁻¹ • (u : V) = g⁻¹ • (g • (u : V)) := by rw [hgu]
        _ = (u : V) := inv_smul_smul g (u : V)
    exact hspec.2.1 (h2.trans h3)
  · exact mem_auxSet_smul hnorm hspec.2.2

theorem midEquiv_midOf_right [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))} (h : W.auxI.Adj u v) :
    midEquiv hQ v ⟨midOf hQ u v h, (midOf_adj_right hQ u v h).symm⟩ = ⟨u, h.symm⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  show step hQ v (midOf hQ u v h) (midOf_adj_right hQ u v h).symm = (u : V)
  have hne : (u : V) ≠ (v : V) := by
    intro heq
    have hd := (SimpleGraph.induce_adj.mp h).2.2
    rw [heq, SimpleGraph.dist_self] at hd
    omega
  exact (step_unique hQ v (midOf_adj_right hQ u v h).symm (midOf_adj_left hQ u v h).symm hne
    (mem_auxSet_of_mem_auxComp (self_mem_auxSet W) u.2)).symm

theorem step_midEquiv_symm [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) (u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)))
    (z : {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v}) :
    step hQ u ((midEquiv hQ u).symm z).1 ((midEquiv hQ u).symm z).2 = (z.1 : V) := by
  have h1 : midEquiv hQ u ((midEquiv hQ u).symm z) = z := (midEquiv hQ u).apply_symm_apply z
  rw [show midEquiv hQ u ((midEquiv hQ u).symm z) =
    midFun hQ u ((midEquiv hQ u).symm z) from Equiv.ofBijective_apply _ _ _] at h1
  have h2 : ((midFun hQ u ((midEquiv hQ u).symm z) :
    {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj u v}).1 : V) = (z.1 : V) := by
    rw [h1]
  simpa [midFun] using h2

theorem exists_lift [Finite V] [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    (p : GPath W.auxI 4) (hp : p.NoBack) :
    ∃ P : GPath Γ 8, P.NoBack ∧ (∀ j, j ≤ 4 → P (2 * j) = (p j).1) ∧
      (∀ (j : ℕ) (_ : j ≤ 3), P (2 * j + 1) =
        midOf hQ (p j) (p (j + 1)) (p.adj j (by omega))) ∧
      (∀ i, i ≤ 8 → ∀ h ∈ W.kernelAt 0, h • P i = P i) := by
  have h01 : W.auxI.Adj (p 0) (p 1) := p.adj 0 (by omega)
  have h12 : W.auxI.Adj (p 1) (p 2) := p.adj 1 (by omega)
  have h23 : W.auxI.Adj (p 2) (p 3) := p.adj 2 (by omega)
  have h34 : W.auxI.Adj (p 3) (p 4) := p.adj 3 (by omega)
  let P : GPath Γ 8 :=
    { toFun := fun i =>
        if i = 0 then (p 0).1 else if i = 1 then midOf hQ (p 0) (p 1) h01
        else if i = 2 then (p 1).1 else if i = 3 then midOf hQ (p 1) (p 2) h12
        else if i = 4 then (p 2).1 else if i = 5 then midOf hQ (p 2) (p 3) h23
        else if i = 6 then (p 3).1 else if i = 7 then midOf hQ (p 3) (p 4) h34
        else (p 4).1
      adj := by
        intro i hi
        interval_cases i
        · show Γ.Adj (p 0).1 (midOf hQ (p 0) (p 1) h01)
          exact midOf_adj_left hQ (p 0) (p 1) h01
        · show Γ.Adj (midOf hQ (p 0) (p 1) h01) (p 1).1
          exact midOf_adj_right hQ (p 0) (p 1) h01
        · show Γ.Adj (p 1).1 (midOf hQ (p 1) (p 2) h12)
          exact midOf_adj_left hQ (p 1) (p 2) h12
        · show Γ.Adj (midOf hQ (p 1) (p 2) h12) (p 2).1
          exact midOf_adj_right hQ (p 1) (p 2) h12
        · show Γ.Adj (p 2).1 (midOf hQ (p 2) (p 3) h23)
          exact midOf_adj_left hQ (p 2) (p 3) h23
        · show Γ.Adj (midOf hQ (p 2) (p 3) h23) (p 3).1
          exact midOf_adj_right hQ (p 2) (p 3) h23
        · show Γ.Adj (p 3).1 (midOf hQ (p 3) (p 4) h34)
          exact midOf_adj_left hQ (p 3) (p 4) h34
        · show Γ.Adj (midOf hQ (p 3) (p 4) h34) (p 4).1
          exact midOf_adj_right hQ (p 3) (p 4) h34
      tail := by
        intro i hi
        show (if i = 0 then (p 0).1 else if i = 1 then midOf hQ (p 0) (p 1) h01
          else if i = 2 then (p 1).1 else if i = 3 then midOf hQ (p 1) (p 2) h12
          else if i = 4 then (p 2).1 else if i = 5 then midOf hQ (p 2) (p 3) h23
          else if i = 6 then (p 3).1 else if i = 7 then midOf hQ (p 3) (p 4) h34
          else (p 4).1) = (p 4).1
        rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ i = 1),
          if_neg (by omega : ¬ i = 2), if_neg (by omega : ¬ i = 3),
          if_neg (by omega : ¬ i = 4), if_neg (by omega : ¬ i = 5),
          if_neg (by omega : ¬ i = 6), if_neg (by omega : ¬ i = 7)] }
  have hP0 : P 0 = (p 0).1 := rfl
  have hP1 : P 1 = midOf hQ (p 0) (p 1) h01 := rfl
  have hP2 : P 2 = (p 1).1 := rfl
  have hP3 : P 3 = midOf hQ (p 1) (p 2) h12 := rfl
  have hP4 : P 4 = (p 2).1 := rfl
  have hP5 : P 5 = midOf hQ (p 2) (p 3) h23 := rfl
  have hP6 : P 6 = (p 3).1 := rfl
  have hP7 : P 7 = midOf hQ (p 3) (p 4) h34 := rfl
  have hP8 : P 8 = (p 4).1 := rfl
  have haux : ∀ z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), (z : V) ∈ auxSet Γ (W.kernelAt 0) :=
    fun z => mem_auxSet_of_mem_auxComp (self_mem_auxSet W) z.2
  have hEven : ∀ (j : ℕ) (hj : j ≤ 4) (h : H), h ∈ W.kernelAt 0 → h • (p j).1 = (p j).1 := by
    intro j hj h hh
    exact MulAction.mem_stabilizer_iff.mp ((hQ.localFacts (p j).1).kernel_le (haux (p j) hh))
  have hOdd : ∀ (j : ℕ) (hj : j ≤ 3) (h : H), h ∈ W.kernelAt 0 →
      h • midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)) =
        midOf hQ (p j) (p (j + 1)) (p.adj j (by omega)) := by
    intro j hj h hh
    exact (mem_fixingSubgroup_iff H).mp (haux (p j) hh) _
      (midOf_adj_left hQ (p j) (p (j + 1)) (p.adj j (by omega)))
  have hdist_ne : ∀ {a b : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))}, W.auxI.Adj a b →
      (a : V) ≠ (b : V) := by
    intro a b hab heq
    have hd := (SimpleGraph.induce_adj.mp hab).2.2
    rw [heq, SimpleGraph.dist_self] at hd
    omega
  have hmid_ne : midOf hQ (p 0) (p 1) h01 ≠ midOf hQ (p 1) (p 2) h12 := by
    intro heq
    have h1 : step hQ (p 1) (midOf hQ (p 0) (p 1) h01)
        (midOf_adj_right hQ (p 0) (p 1) h01).symm = (p 0).1 := by
      refine (step_unique hQ (p 1) (midOf_adj_right hQ (p 0) (p 1) h01).symm
        (midOf_adj_left hQ (p 0) (p 1) h01).symm (hdist_ne h01) (haux (p 0))).symm
    have h2 : step hQ (p 1) (midOf hQ (p 1) (p 2) h12)
        (midOf_adj_left hQ (p 1) (p 2) h12) = (p 2).1 := step_midOf hQ (p 1) (p 2) h12
    have hstep := step_congr hQ (p 1) (midOf_adj_right hQ (p 0) (p 1) h01).symm
      (midOf_adj_left hQ (p 1) (p 2) h12) heq
    rw [hstep] at h1
    exact hp 0 (by omega) (Subtype.ext (h1.symm.trans h2))
  have hmid_ne2 : midOf hQ (p 1) (p 2) h12 ≠ midOf hQ (p 2) (p 3) h23 := by
    intro heq
    have h1 : step hQ (p 2) (midOf hQ (p 1) (p 2) h12)
        (midOf_adj_right hQ (p 1) (p 2) h12).symm = (p 1).1 := by
      refine (step_unique hQ (p 2) (midOf_adj_right hQ (p 1) (p 2) h12).symm
        (midOf_adj_left hQ (p 1) (p 2) h12).symm (hdist_ne h12) (haux (p 1))).symm
    have h2 : step hQ (p 2) (midOf hQ (p 2) (p 3) h23)
        (midOf_adj_left hQ (p 2) (p 3) h23) = (p 3).1 := step_midOf hQ (p 2) (p 3) h23
    have hstep := step_congr hQ (p 2) (midOf_adj_right hQ (p 1) (p 2) h12).symm
      (midOf_adj_left hQ (p 2) (p 3) h23) heq
    rw [hstep] at h1
    exact hp 1 (by omega) (Subtype.ext (h1.symm.trans h2))
  have hmid_ne3 : midOf hQ (p 2) (p 3) h23 ≠ midOf hQ (p 3) (p 4) h34 := by
    intro heq
    have h1 : step hQ (p 3) (midOf hQ (p 2) (p 3) h23)
        (midOf_adj_right hQ (p 2) (p 3) h23).symm = (p 2).1 := by
      refine (step_unique hQ (p 3) (midOf_adj_right hQ (p 2) (p 3) h23).symm
        (midOf_adj_left hQ (p 2) (p 3) h23).symm (hdist_ne h23) (haux (p 2))).symm
    have h2 : step hQ (p 3) (midOf hQ (p 3) (p 4) h34)
        (midOf_adj_left hQ (p 3) (p 4) h34) = (p 4).1 := step_midOf hQ (p 3) (p 4) h34
    have hstep := step_congr hQ (p 3) (midOf_adj_right hQ (p 2) (p 3) h23).symm
      (midOf_adj_left hQ (p 3) (p 4) h34) heq
    rw [hstep] at h1
    exact hp 2 (by omega) (Subtype.ext (h1.symm.trans h2))
  have hPnB : P.NoBack := by
    intro i hi
    have hi8 : i < 7 := by omega
    interval_cases i
    · rw [hP0, hP2]; exact hdist_ne h01
    · rw [hP1, hP3]; exact hmid_ne
    · rw [hP2, hP4]; exact hdist_ne h12
    · rw [hP3, hP5]; exact hmid_ne2
    · rw [hP4, hP6]; exact hdist_ne h23
    · rw [hP5, hP7]; exact hmid_ne3
    · rw [hP6, hP8]; exact hdist_ne h34
  refine ⟨P, hPnB, ?_, ?_, ?_⟩
  · intro j hj
    have hj5 : j < 5 := by omega
    interval_cases j
    · simpa using hP0
    · simpa using hP2
    · simpa using hP4
    · simpa using hP6
    · simpa using hP8
  · intro j hj
    have hj4 : j < 4 := by omega
    interval_cases j
    · simpa using hP1
    · simpa using hP3
    · simpa using hP5
    · simpa using hP7
  · intro i hi h hh
    interval_cases i
    · rw [hP0]; exact hEven 0 (by omega) h hh
    · rw [hP1]; exact hOdd 0 (by omega) h hh
    · rw [hP2]; exact hEven 1 (by omega) h hh
    · rw [hP3]; exact hOdd 1 (by omega) h hh
    · rw [hP4]; exact hEven 2 (by omega) h hh
    · rw [hP5]; exact hOdd 2 (by omega) h hh
    · rw [hP6]; exact hEven 3 (by omega) h hh
    · rw [hP7]; exact hOdd 3 (by omega) h hh
    · rw [hP8]; exact hEven 4 (by omega) h hh

@[expose] noncomputable def auxProj (W : ClosedGoodPath H Γ) :
    ↥(auxGroup Γ (W.kernelAt 0) (W.x 0)) →* ↥W.auxS :=
  letI := auxAction Γ (W.kernelAt 0) (W.x 0)
  (MulAction.toPermHom ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))
    ↥(auxComp Γ (W.kernelAt 0) (W.x 0))).rangeRestrict

theorem auxProj_smul (W : ClosedGoodPath H Γ)
    (g : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0)))
    (v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :
    (auxProj W g) • v = g • v := by
  letI := auxAction Γ (W.kernelAt 0) (W.x 0)
  rw [Subgroup.smul_def, Equiv.Perm.smul_def]
  show MulAction.toPerm (g : ↥(auxGroup Γ (W.kernelAt 0) (W.x 0))) v = g • v
  rw [MulAction.toPerm_apply]

theorem ClosedGoodPath.QuarterHyp.moufangCondition_aux [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) : MoufangCondition ↥W.auxS W.auxI 4 := by
  classical
  letI := auxAction Γ (W.kernelAt 0) (W.x 0)
  intro p hp y y' hy hy' hne hne'
  obtain ⟨P, hPnb, hP2, hPodd, hPfix⟩ := exists_lift hQ p hp
  have h34 : W.auxI.Adj (p 3) (p 4) := p.adj 3 (by omega)
  have haux : ∀ z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), (z : V) ∈ auxSet Γ (W.kernelAt 0) :=
    fun z => mem_auxSet_of_mem_auxComp (self_mem_auxSet W) z.2
  set y0 : {v : V // Γ.Adj ((p 4) : V) v} := (midEquiv hQ (p 4)).symm ⟨y, hy⟩ with hy0def
  set y1 : {v : V // Γ.Adj ((p 4) : V) v} := (midEquiv hQ (p 4)).symm ⟨y', hy'⟩ with hy1def
  have hm0 : midEquiv hQ (p 4) y0 = ⟨y, hy⟩ := (midEquiv hQ (p 4)).apply_symm_apply _
  have hm1 : midEquiv hQ (p 4) y1 = ⟨y', hy'⟩ := (midEquiv hQ (p 4)).apply_symm_apply _
  have hy0adj : Γ.Adj (P 8) y0.1 := by rw [hP2 4 le_rfl]; exact y0.2
  have hy1adj : Γ.Adj (P 8) y1.1 := by rw [hP2 4 le_rfl]; exact y1.2
  have hP7 : P 7 = midOf hQ (p 3) (p 4) h34 := by
    have h := hPodd 3 (by omega)
    simpa using h
  have hy0ne : y0.1 ≠ P 7 := by
    intro heq
    have hy0eq : y0 = ⟨midOf hQ (p 3) (p 4) h34,
        (midOf_adj_right hQ (p 3) (p 4) h34).symm⟩ := Subtype.ext (heq.trans hP7)
    have h2 : (⟨y, hy⟩ : {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj (p 4) v}) =
        ⟨p 3, h34.symm⟩ := by
      rw [← hm0, hy0eq]
      exact midEquiv_midOf_right hQ h34
    exact hne (congrArg (fun z => z.1) h2)
  have hy1ne : y1.1 ≠ P 7 := by
    intro heq
    have hy1eq : y1 = ⟨midOf hQ (p 3) (p 4) h34,
        (midOf_adj_right hQ (p 3) (p 4) h34).symm⟩ := Subtype.ext (heq.trans hP7)
    have h2 : (⟨y', hy'⟩ : {v : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) // W.auxI.Adj (p 4) v}) =
        ⟨p 3, h34.symm⟩ := by
      rw [← hm1, hy1eq]
      exact midEquiv_midOf_right hQ h34
    exact hne' (congrArg (fun z => z.1) h2)
  obtain ⟨g, hgfix, hgy⟩ := hQ.moufang P hPnb y0.1 y1.1 hy0adj hy1adj hy0ne hy1ne
  have hU : g ∈ pathRootGroup H Γ P := mem_pathRootGroup.mpr hgfix
  have hcomm : ∀ k ∈ W.kernelAt 0, g * k = k * g := by
    intro k hk
    have hgmem : k ∈ fixingSubgroup H (Γ.neighborSet (P 0)) ⊓ GPath.stabPath (H := H) P := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hP2 0 (by omega)]
        exact haux (p 0) hk
      · rw [GPath.mem_stabPath_iff]
        exact fun i hi => hPfix i hi k hk
    exact (commute_of_mem_fixingSubgroup_inf_stabPath (by norm_num : 2 ≤ 8) hQ.weissFree
      hPnb hgmem hU).symm
  have hnorm : g ∈ Subgroup.normalizer ((W.kernelAt 0) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hcomm k hk]
      simpa using hk
    · intro hk
      have h2 := hcomm (g * k * g⁻¹) hk
      have h3 : g * k * g⁻¹ = k := by
        have h4 : g * (g * k * g⁻¹) = g * k := by rw [h2]; group
        exact mul_left_cancel h4
      rw [← h3]
      exact hk
  have hgaux : g ∈ auxGroup Γ (W.kernelAt 0) (W.x 0) := by
    refine mem_auxGroup_of_normalizes_of_fixes_mem (v := P 0) hnorm ?_ ?_
    · rw [hP2 0 (by omega)]
      exact (p 0).2
    · exact hgfix 1 (by omega) (by omega) (P 0) (P.adj 0 (by omega)).symm
  refine ⟨auxProj W ⟨g, hgaux⟩, ?_, ?_⟩
  · intro i hi1 hi3 w hw
    have hi : i ≤ 3 := by omega
    apply Subtype.ext
    show g • (w : V) = (w : V)
    have hmid : Γ.Adj (p i).1 (midOf hQ (p i) w hw) := midOf_adj_left hQ (p i) w hw
    have hgmid : g • midOf hQ (p i) w hw = midOf hQ (p i) w hw := by
      apply hgfix (2 * i) (by omega) (by omega)
      rw [hP2 i (by omega)]
      exact hmid
    have hadjPi : Γ.Adj (P (2 * i - 1)) ((p i) : V) := by
      have h := P.adj (2 * i - 1) (by omega)
      rw [show 2 * i - 1 + 1 = 2 * i by omega, hP2 i (by omega)] at h
      exact h
    have hgpi : g • (p i).1 = (p i).1 :=
      hgfix (2 * i - 1) (by omega) (by omega) ((p i) : V) hadjPi
    have hy' : Γ.Adj ((p i) : V) (g • midOf hQ (p i) w hw) := by
      have h := (GraphAction.adj_smul g (midOf hQ (p i) w hw) ((p i) : V)).mpr hmid.symm
      rw [hgpi] at h
      exact h.symm
    have hsw : step hQ (p i) (g • midOf hQ (p i) w hw) hy' = g • (w : V) := by
      rw [step_smul hQ (p i) hmid hnorm hgpi hy', step_midOf hQ (p i) w hw]
    have heq : step hQ (p i) (g • midOf hQ (p i) w hw) hy' = (w : V) := by
      rw [step_congr hQ (p i) hy' hmid hgmid]
      exact step_midOf hQ (p i) w hw
    exact hsw.symm.trans heq
  · apply Subtype.ext
    show g • (y : V) = (y' : V)
    have hstep0 : step hQ (p 4) y0.1 y0.2 = (y : V) := by
      have h := step_midEquiv_symm hQ (p 4) ⟨y, hy⟩
      simpa [hy0def] using h
    have hstep1 : step hQ (p 4) y1.1 y1.2 = (y' : V) := by
      have h := step_midEquiv_symm hQ (p 4) ⟨y', hy'⟩
      simpa [hy1def] using h
    have hgp4 : g • ((p 4) : V) = ((p 4) : V) := by
      rw [← hP2 4 le_rfl]
      exact hgfix 7 (by omega) (by omega) (P 8) (P.adj 7 (by omega))
    have hy0' : Γ.Adj ((p 4) : V) (g • y0.1) := by
      have h := (GraphAction.adj_smul g y0.1 ((p 4) : V)).mpr y0.2.symm
      rw [hgp4] at h
      exact h.symm
    have h1 : g • (y : V) = step hQ (p 4) (g • y0.1) hy0' := by
      rw [← hstep0]
      exact (step_smul hQ (p 4) y0.2 hnorm hgp4 hy0').symm
    have hfin : step hQ (p 4) (g • y0.1) hy0' = step hQ (p 4) y1.1 y1.2 :=
      step_congr hQ (p 4) hy0' y1.2 hgy
    rw [h1, hfin]
    exact hstep1

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.ClosedGoodPath

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

variable (Γ) in
@[expose] def auxSet (K : Subgroup H) : Set V := {u | K ≤ fixingSubgroup H (Γ.neighborSet u)}

variable (Γ) in
@[expose] def auxGraph (K : Subgroup H) : SimpleGraph V where
  Adj u v := u ∈ auxSet Γ K ∧ v ∈ auxSet Γ K ∧ Γ.dist u v = 2
  symm := ⟨fun u v h => ⟨h.2.1, h.1, by rw [SimpleGraph.dist_comm]; exact h.2.2⟩⟩
  loopless := ⟨fun u h => by simp [SimpleGraph.dist_self] at h⟩

variable (Γ) in
@[expose] def auxComp (K : Subgroup H) (u₀ : V) : Set V :=
  ((auxGraph Γ K).connectedComponentMk u₀).supp

variable (Γ) in
@[expose] def auxGroup (K : Subgroup H) (u₀ : V) : Subgroup H :=
  Subgroup.normalizer (K : Set H) ⊓ MulAction.stabilizer H (auxComp Γ K u₀)

variable (Γ) in
@[expose, instance_reducible] def auxAction (K : Subgroup H) (u₀ : V) :
    MulAction ↥(auxGroup Γ K u₀) ↥(auxComp Γ K u₀) where
  smul g u := ⟨(g : H) • (u : V), by
    have hg : (g : H) • auxComp Γ K u₀ = auxComp Γ K u₀ := (Subgroup.mem_inf.mp g.2).2
    have h := Set.smul_mem_smul_set (a := (g : H)) u.2
    rwa [hg] at h⟩
  one_smul u := Subtype.ext (one_smul H (u : V))
  mul_smul g h u := Subtype.ext (mul_smul (g : H) (h : H) (u : V))

variable (Γ) in
@[expose] noncomputable def auxPerm (K : Subgroup H) (u₀ : V) :
    Subgroup (Equiv.Perm ↥(auxComp Γ K u₀)) :=
  letI := auxAction Γ K u₀
  (MulAction.toPermHom ↥(auxGroup Γ K u₀) ↥(auxComp Γ K u₀)).range

variable (Γ) in
@[expose] def auxGraphOn (K : Subgroup H) (u₀ : V) : SimpleGraph ↥(auxComp Γ K u₀) :=
  (auxGraph Γ K).induce (auxComp Γ K u₀)

private theorem dist_smul_eq (g : H) (a b : V) : Γ.dist (g • a) (g • b) = Γ.dist a b := by
  have key : ∀ (g : H) (a b : V), Γ.dist (g • a) (g • b) ≤ Γ.dist a b := by
    intro g a b
    by_cases h : Γ.Reachable a b
    · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
      let f : Γ →g Γ :=
        ⟨fun x => g • x, fun {x y} hxy => (GraphAction.adj_smul g x y).mpr hxy⟩
      have := SimpleGraph.dist_le (w.map f)
      rw [SimpleGraph.Walk.length_map, hw] at this
      exact this
    · have hnr : ¬ Γ.Reachable (g • a) (g • b) := by
        rintro ⟨w⟩
        apply h
        let f : Γ →g Γ :=
          ⟨fun x => g⁻¹ • x, fun {x y} hxy => (GraphAction.adj_smul g⁻¹ x y).mpr hxy⟩
        exact ⟨by simpa [f] using w.map f⟩
      rw [SimpleGraph.dist_eq_zero_of_not_reachable hnr,
        SimpleGraph.dist_eq_zero_of_not_reachable h]
  refine le_antisymm (key g a b) ?_
  have := key g⁻¹ (g • a) (g • b)
  simpa using this

theorem mem_auxSet_smul {K : Subgroup H} {g : H}
    (hnorm : g ∈ Subgroup.normalizer (K : Set H)) {u : V} (hu : u ∈ auxSet Γ K) :
    g • u ∈ auxSet Γ K := by
  rw [auxSet] at hu
  change K ≤ fixingSubgroup H (Γ.neighborSet (g • u))
  rw [fixingSubgroup_neighborSet_smul]
  rw [Subgroup.mem_normalizer_iff] at hnorm
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨g⁻¹ * k * g, ?_, ?_⟩
  · exact hu ((hnorm (g⁻¹ * k * g)).mpr (by simpa [mul_assoc] using hk))
  · simp [mul_assoc]

theorem auxGraph_adj_smul {K : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.normalizer (K : Set H)) {a b : V} (h : (auxGraph Γ K).Adj a b) :
    (auxGraph Γ K).Adj (g • a) (g • b) :=
  ⟨mem_auxSet_smul hg h.1, mem_auxSet_smul hg h.2.1, by
    rw [dist_smul_eq]; exact h.2.2⟩

noncomputable instance auxPerm.graphAction (K : Subgroup H) (u₀ : V) :
    GraphAction ↥(auxPerm Γ K u₀) (auxGraphOn Γ K u₀) where
  adj_smul g a b := by
    letI := auxAction Γ K u₀
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp g.2
    have hga : ((g • a : ↥(auxComp Γ K u₀)) : V) = (m : H) • (a : V) := by
      rw [Subgroup.smul_def, Equiv.Perm.smul_def, ← hm, MulAction.toPermHom_apply,
        MulAction.toPerm_apply]
      rfl
    have hgb : ((g • b : ↥(auxComp Γ K u₀)) : V) = (m : H) • (b : V) := by
      rw [Subgroup.smul_def, Equiv.Perm.smul_def, ← hm, MulAction.toPermHom_apply,
        MulAction.toPerm_apply]
      rfl
    rw [auxGraphOn, SimpleGraph.induce_adj, SimpleGraph.induce_adj, hga, hgb]
    constructor
    · intro h
      have h' := auxGraph_adj_smul (g := ((m⁻¹ : ↥(auxGroup Γ K u₀)) : H))
        (Subgroup.mem_inf.mp (m⁻¹).2).1 h
      simpa using h'
    · exact auxGraph_adj_smul (Subgroup.mem_inf.mp m.2).1

abbrev ClosedGoodPath.auxI (W : ClosedGoodPath H Γ) :
    SimpleGraph ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) :=
  auxGraphOn Γ (W.kernelAt 0) (W.x 0)

noncomputable abbrev ClosedGoodPath.auxS (W : ClosedGoodPath H Γ) :
    Subgroup (Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) :=
  auxPerm Γ (W.kernelAt 0) (W.x 0)

structure ClosedGoodPath.QuarterHyp (W : ClosedGoodPath H Γ) : Prop where
  egirth : ((2 * 8 + 2 : ℕ) : ℕ∞) < Γ.egirth
  moufang : MoufangCondition H Γ 8
  weissFree : WeissFree H Γ 8
  ne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w
  three : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w'
  val : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e
  loc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v
  localFacts : ∀ z, LocalFacts H Γ z
  zassenhaus : ∀ z, ZassenhausFacts H Γ z
  rootFacts : ∀ z, RootFacts H Γ 8 z
  notTwo : ¬ IsPGroup 2 ↥(W.kernelAt 0)
  quarter : ∀ i : ℤ, W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x i)) ↔ (2 : ℤ) ∣ i

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.RootOps.Cert.D4Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.D4Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Tab

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk
open CFSG.LieType.Ree (vecBEq vecBEq_iff)

@[expose] def d4ToG2 (β : Fin Tag.D4.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  (![β ⟨2, by decide⟩, β ⟨0, by decide⟩ + β ⟨1, by decide⟩ + β ⟨3, by decide⟩] : Fin 2 → ℤ)

@[expose] def g2IndexOrbit : Fin Tag.G2.rank → List (Fin Tag.D4.rank) :=
  (![[⟨2, by decide⟩], [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩]] :
    Fin 2 → List (Fin Tag.D4.rank))

@[expose] def d4IndexToG2 : Fin Tag.D4.rank → Fin Tag.G2.rank :=
  (![⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] : Fin 4 → Fin Tag.G2.rank)

@[expose] def g2IndexRep : Fin Tag.G2.rank → Fin Tag.D4.rank :=
  (![⟨2, by decide⟩, ⟨0, by decide⟩] : Fin 2 → Fin Tag.D4.rank)

@[expose] def rhoD4 : Equiv.Perm (Fin Tag.D4.rank) :=
  TwistTag.D4.perm

@[expose] def d4LabelPerm : Label Tag.D4 ≃ Label Tag.D4 :=
  labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm

@[expose] def d4DiagramEnd (K : Type*) [Field K] : Module.End K (RootModule Tag.D4 K) :=
  (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K))

theorem d4DiagramEnd_apply {K : Type*} [Field K] (v : RootModule Tag.D4 K) (b : Label Tag.D4) :
    d4DiagramEnd K v b = v (d4LabelPerm.symm b) :=
  Finsupp.equivMapDomain_apply _ _ _

theorem mem_g2IndexOrbit_iff (i : Fin Tag.D4.rank) (j : Fin Tag.G2.rank) :
    i ∈ g2IndexOrbit j ↔ d4IndexToG2 i = j := by
  revert i j
  decide

theorem nodup_g2IndexOrbit (j : Fin Tag.G2.rank) : (g2IndexOrbit j).Nodup := by
  revert j
  decide

theorem d4IndexToG2_g2IndexRep (j : Fin Tag.G2.rank) : d4IndexToG2 (g2IndexRep j) = j := by
  revert j
  decide

theorem g2IndexRep_d4IndexToG2 (i : Fin Tag.D4.rank) :
    g2IndexRep (d4IndexToG2 i) = i ∨ g2IndexRep (d4IndexToG2 i) = rhoD4 i ∨
      g2IndexRep (d4IndexToG2 i) = rhoD4 (rhoD4 i) := by
  revert i
  decide

theorem d4IndexToG2_rhoD4 (i : Fin Tag.D4.rank) : d4IndexToG2 (rhoD4 i) = d4IndexToG2 i := by
  revert i
  decide

theorem d4ToG2_permLattice (β : Fin Tag.D4.rank → ℤ) :
    d4ToG2 (permLattice rhoD4 β) = d4ToG2 β := by
  have h0 : rhoD4.symm ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
  have h1 : rhoD4.symm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
  have h2 : rhoD4.symm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have h3 : rhoD4.symm ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
  funext j
  fin_cases j
  · show β (rhoD4.symm ⟨2, by decide⟩) = β ⟨2, by decide⟩
    rw [h2]
  · show β (rhoD4.symm ⟨0, by decide⟩) + β (rhoD4.symm ⟨1, by decide⟩) +
        β (rhoD4.symm ⟨3, by decide⟩) = β ⟨0, by decide⟩ + β ⟨1, by decide⟩ + β ⟨3, by decide⟩
    rw [h0, h1, h3]
    ring

theorem permLattice_rhoD4_three (β : Fin Tag.D4.rank → ℤ) :
    permLattice rhoD4 (permLattice rhoD4 (permLattice rhoD4 β)) = β := by
  have h : ∀ i, rhoD4.symm (rhoD4.symm (rhoD4.symm i)) = i := by decide
  funext i
  show β (rhoD4.symm (rhoD4.symm (rhoD4.symm i))) = β i
  rw [h]

@[expose] def d4ToG2Check : Bool :=
  (List.range Tag.D4.rootCertificate.roots.length).all fun k =>
    (List.range Tag.G2.rootCertificate.roots.length).any fun m =>
      vecBEq (Tag.G2.rootCertificate.root m) (d4ToG2 (Tag.D4.rootCertificate.root k))

theorem d4ToG2Check_eq_true : d4ToG2Check = true := by decide +kernel

@[expose] def d4ToG2FibreCheck : Bool :=
  (List.range Tag.G2.rootCertificate.roots.length).all fun m =>
    (List.range Tag.D4.rootCertificate.roots.length).any fun k =>
      vecBEq (d4ToG2 (Tag.D4.rootCertificate.root k)) (Tag.G2.rootCertificate.root m) &&
        (List.range Tag.D4.rootCertificate.roots.length).all fun k' =>
          vecBEq (d4ToG2 (Tag.D4.rootCertificate.root k')) (Tag.G2.rootCertificate.root m) ==
            (vecBEq (Tag.D4.rootCertificate.root k') (Tag.D4.rootCertificate.root k) ||
              vecBEq (Tag.D4.rootCertificate.root k')
                (permLattice rhoD4 (Tag.D4.rootCertificate.root k)) ||
              vecBEq (Tag.D4.rootCertificate.root k')
                (permLattice rhoD4 (permLattice rhoD4 (Tag.D4.rootCertificate.root k))))

theorem d4ToG2FibreCheck_eq_true : d4ToG2FibreCheck = true := by decide +kernel

theorem isRoot_d4ToG2 {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    IsRoot Tag.G2 (d4ToG2 β) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  have h := d4ToG2Check_eq_true
  simp only [d4ToG2Check, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨m, hm, hmk⟩ := h k hk
  rw [← vecBEq_iff.1 hmk]
  exact isRoot_rootCertificate_root hm

theorem exists_d4ToG2_fibre {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) :
    ∃ β, IsRoot Tag.D4 β ∧ d4ToG2 β = α ∧ ∀ β', IsRoot Tag.D4 β' →
      (d4ToG2 β' = α ↔ β' = β ∨ β' = permLattice rhoD4 β ∨
        β' = permLattice rhoD4 (permLattice rhoD4 β)) := by
  obtain ⟨m, hm, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h := d4ToG2FibreCheck_eq_true
  simp only [d4ToG2FibreCheck, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨k, hk, hkm, hall⟩ := h m hm
  refine ⟨_, isRoot_rootCertificate_root hk, vecBEq_iff.1 hkm, fun β' hβ' => ?_⟩
  obtain ⟨k', hk', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ'
  have h' := beq_iff_eq.1 (hall k' hk')
  rw [← vecBEq_iff (u := d4ToG2 (Tag.D4.rootCertificate.root k')),
    ← vecBEq_iff (u := Tag.D4.rootCertificate.root k') (v := Tag.D4.rootCertificate.root k),
    ← vecBEq_iff (u := Tag.D4.rootCertificate.root k'),
    ← vecBEq_iff (u := Tag.D4.rootCertificate.root k'), h', Bool.or_eq_true, Bool.or_eq_true,
    or_assoc]

variable (K : Type*) [CommRing K]

@[expose] def g2ToD4Module : RootModule Tag.G2 K →ₗ[K] RootModule Tag.D4 K :=
  Finsupp.linearCombination K fun b => match b with
    | .inl j => ((g2IndexOrbit j).map fun i => hVec Tag.D4 K i).sum
    | .inr α => ∑ β ∈ (rootFinset Tag.D4).filter (fun β => d4ToG2 β = α.1), rootVec Tag.D4 K β

@[expose] def g2OrbitX (j : Fin Tag.G2.rank) (c : K) : Module.End K (RootModule Tag.D4 K) :=
  ((g2IndexOrbit j).map fun i => xOp Tag.D4 K i c).prod

@[expose] def g2OrbitY (j : Fin Tag.G2.rank) (c : K) : Module.End K (RootModule Tag.D4 K) :=
  ((g2IndexOrbit j).map fun i => yOp Tag.D4 K i c).prod

@[expose] def d4LabelToG2 : Label Tag.D4 → Label Tag.G2
  | .inl i => .inl (d4IndexToG2 i)
  | .inr β => .inr ⟨d4ToG2 β.1, isRoot_d4ToG2 β.2⟩

@[expose] def g2LabelRep : Label Tag.G2 → Label Tag.D4
  | .inl j => .inl (g2IndexRep j)
  | .inr α => .inr ⟨(exists_d4ToG2_fibre α.2).choose, (exists_d4ToG2_fibre α.2).choose_spec.1⟩

theorem d4LabelToG2_g2LabelRep (a : Label Tag.G2) : d4LabelToG2 (g2LabelRep a) = a := by
  rcases a with j | α
  · exact congrArg Sum.inl (d4IndexToG2_g2IndexRep j)
  · exact congrArg Sum.inr (Subtype.ext (exists_d4ToG2_fibre α.2).choose_spec.2.1)

theorem d4LabelToG2_d4LabelPerm (b : Label Tag.D4) :
    d4LabelToG2 (d4LabelPerm b) = d4LabelToG2 b := by
  rcases b with i | β
  · exact congrArg Sum.inl (d4IndexToG2_rhoD4 i)
  · exact congrArg Sum.inr (Subtype.ext (d4ToG2_permLattice β.1))

theorem g2LabelRep_d4LabelToG2 (b : Label Tag.D4) :
    g2LabelRep (d4LabelToG2 b) = b ∨ g2LabelRep (d4LabelToG2 b) = d4LabelPerm b ∨
      g2LabelRep (d4LabelToG2 b) = d4LabelPerm (d4LabelPerm b) := by
  rcases b with i | ⟨β, hβ⟩
  · rcases g2IndexRep_d4IndexToG2 i with h | h | h
    · exact Or.inl (congrArg Sum.inl h)
    · exact Or.inr (Or.inl (congrArg Sum.inl h))
    · exact Or.inr (Or.inr (congrArg Sum.inl h))
  · have hspec := (exists_d4ToG2_fibre (isRoot_d4ToG2 hβ)).choose_spec
    rcases (hspec.2.2 β hβ).1 rfl with h | h | h
    · exact Or.inl (congrArg Sum.inr (Subtype.ext h.symm))
    ·
      refine Or.inr (Or.inr (congrArg Sum.inr (Subtype.ext ?_)))
      change _ = permLattice rhoD4 (permLattice rhoD4 β)
      exact (permLattice_rhoD4_three _).symm.trans
        (congrArg (fun v => permLattice rhoD4 (permLattice rhoD4 v)) h.symm)
    ·
      refine Or.inr (Or.inl (congrArg Sum.inr (Subtype.ext ?_)))
      change _ = permLattice rhoD4 β
      exact (permLattice_rhoD4_three _).symm.trans (congrArg (permLattice rhoD4) h.symm)

theorem g2ToD4Module_single (a : Label Tag.G2) (b : Label Tag.D4) :
    g2ToD4Module K (Finsupp.single a 1) b = if d4LabelToG2 b = a then 1 else 0 := by
  rw [g2ToD4Module, Finsupp.linearCombination_single, one_smul]
  rcases a with j | ⟨α, hα⟩
  · simp only
    rw [← List.sum_toFinset _ (nodup_g2IndexOrbit j), Finsupp.finsetSum_apply]
    simp only [hVec_apply_eq]
    rcases b with i | β
    · simp only [Sum.inl.injEq, Finset.sum_ite_eq, List.mem_toFinset, mem_g2IndexOrbit_iff,
        d4LabelToG2]
    · simp [d4LabelToG2]
  · simp only
    rw [Finsupp.finsetSum_apply]
    rcases b with i | ⟨β, hβ⟩
    · simp [rootVec_apply_inl, d4LabelToG2]
    · simp only [rootVec_apply_inr, Finset.sum_ite_eq, Finset.mem_filter, mem_rootFinset.2 hβ,
        true_and, d4LabelToG2, Sum.inr.injEq, Subtype.mk.injEq]

theorem g2ToD4Module_apply (w : RootModule Tag.G2 K) (b : Label Tag.D4) :
    g2ToD4Module K w b = w (d4LabelToG2 b) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w w' hw hw' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hw, hw']
  | single a r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
      g2ToD4Module_single, Finsupp.smul_apply, Finsupp.single_apply]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, eq_comm]

theorem g2ToD4Module_injective : Function.Injective (g2ToD4Module K) := by
  intro w w' h
  ext a
  have := congrArg (fun v => v (g2LabelRep a)) h
  simp only [g2ToD4Module_apply, d4LabelToG2_g2LabelRep] at this
  exact this

@[expose] def d4GraphFixedModule (K : Type*) [Field K] : Submodule K (RootModule Tag.D4 K) :=
  LinearMap.eqLocus (d4DiagramEnd K) LinearMap.id

theorem mem_d4GraphFixedModule {K : Type*} [Field K] {v : RootModule Tag.D4 K} :
    v ∈ d4GraphFixedModule K ↔ d4DiagramEnd K v = v :=
  LinearMap.mem_eqLocus

theorem apply_d4LabelPerm_of_mem {K : Type*} [Field K] {v : RootModule Tag.D4 K}
    (hv : v ∈ d4GraphFixedModule K) (b : Label Tag.D4) : v (d4LabelPerm b) = v b := by
  have h := congrArg (fun u : RootModule Tag.D4 K => u (d4LabelPerm b))
    (mem_d4GraphFixedModule.1 hv)
  simp only [d4DiagramEnd_apply, Equiv.symm_apply_apply] at h
  exact h.symm

theorem range_g2ToD4Module (K : Type*) [Field K] :
    LinearMap.range (g2ToD4Module K) = d4GraphFixedModule K := by
  ext v
  rw [LinearMap.mem_range, mem_d4GraphFixedModule]
  constructor
  · rintro ⟨w, rfl⟩
    ext b
    rw [d4DiagramEnd_apply, g2ToD4Module_apply, g2ToD4Module_apply]
    have h := d4LabelToG2_d4LabelPerm (d4LabelPerm.symm b)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
  · intro hv
    have hv' := apply_d4LabelPerm_of_mem (mem_d4GraphFixedModule.2 hv)
    refine ⟨Finsupp.equivFunOnFinite.symm fun a => v (g2LabelRep a), ?_⟩
    ext b
    rw [g2ToD4Module_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rcases g2LabelRep_d4LabelToG2 b with h | h | h
    · rw [h]
    · rw [h, hv']
    · rw [h, hv', hv']

@[expose] def g2ToD4Pos (p : ℕ) : List (ℕ × ℤ) :=
  if h : p < Tag.G2.rank then (g2IndexOrbit ⟨p, h⟩).map fun i : Fin Tag.D4.rank => (i.val, 1)
  else ((List.range Tag.D4.rootCertificate.roots.length).filter fun k =>
      vecBEq (d4ToG2 (Tag.D4.rootCertificate.root k))
        (Tag.G2.rootCertificate.root (p - Tag.G2.rank))).map fun k => (Tag.D4.rank + k, 1)

theorem validVec_g2ToD4Pos (p : ℕ) : ValidVec Tag.D4 (g2ToD4Pos p) := by
  intro x hx
  unfold g2ToD4Pos at hx
  split_ifs at hx with h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have := i.2
    simp only [dim]
    omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 (List.mem_filter.1 hk).1
    simp only [dim]
    omega

theorem g2ToD4Module_posVec {p : ℕ} (hp : p < dim Tag.G2) :
    g2ToD4Module K (posVec Tag.G2 K p) = vecOf Tag.D4 K (g2ToD4Pos p) := by
  unfold posVec g2ToD4Pos
  split_ifs with h
  · rw [hVec, g2ToD4Module, Finsupp.linearCombination_single, one_smul]
    simp only [vecOf, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [posVec, i.2]
  · have hm : p - Tag.G2.rank < Tag.G2.rootCertificate.roots.length := by
      simp only [dim] at hp
      omega
    rw [CFSG.LieType.Ree.rootVec_eq_single K (isRoot_rootCertificate_root hm), g2ToD4Module,
      Finsupp.linearCombination_single, one_smul]
    simp only [vecOf, List.map_map]
    have hnd : ((List.range Tag.D4.rootCertificate.roots.length).map
        Tag.D4.rootCertificate.root).Nodup :=
      (List.nodup_range).map_on fun x hx y hy hxy =>
        rootCertificate_root_injOn (List.mem_range.1 hx) (List.mem_range.1 hy) hxy
    rw [list_sum_map_filter, Finset.sum_filter, rootFinset, List.sum_toFinset _ hnd, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    by_cases hk : d4ToG2 (Tag.D4.rootCertificate.root k) =
        Tag.G2.rootCertificate.root (p - Tag.G2.rank)
    · rw [ite_eq_left hk, ite_eq_left (vecBEq_iff.2 hk)]
      simp [posVec]
    · rw [ite_eq_right hk, ite_eq_right fun h => hk (vecBEq_iff.1 h)]

@[expose] def g2ToD4Vec (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (g2ToD4Pos x.1).map fun y => (y.1, x.2 * y.2)

theorem g2ToD4Module_vecOf {v : List (ℕ × ℤ)} (hv : ValidVec Tag.G2 v) :
    g2ToD4Module K (vecOf Tag.G2 K v) = vecOf Tag.D4 K (g2ToD4Vec v) := by
  induction v with
  | nil => simp [g2ToD4Vec]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, g2ToD4Module_posVec K (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [g2ToD4Vec, List.flatMap_cons, vecOf_append, vecOf_map_mul]

theorem validVec_g2ToD4Vec (v : List (ℕ × ℤ)) : ValidVec Tag.D4 (g2ToD4Vec v) := by
  intro x hx
  obtain ⟨y, -, hy⟩ := List.mem_flatMap.1 hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  exact validVec_g2ToD4Pos _ z hz

theorem simpleRow_D4_all (j : Fin Tag.D4.rank) : simpleRow .D4 j = true := by
  fin_cases j
  exacts [d4_simpleRow_0, d4_simpleRow_1, d4_simpleRow_2, d4_simpleRow_3]

theorem simpleRow_G2_all (j : Fin Tag.G2.rank) : simpleRow .G2 j = true := by
  fin_cases j
  exacts [g2_simpleRow_0, g2_simpleRow_1]

@[expose] def d4OrbitLhs (y : Bool) (I : List (Fin Tag.D4.rank)) (n p : ℕ) : List (ℕ × ℤ) :=
  match I with
  | [i] => if n < 4 then coeffVec .D4 y i n (g2ToD4Pos p) else []
  | [i, i', i''] => (List.range 3).flatMap fun k => (List.range 3).flatMap fun l =>
      if k + l ≤ n ∧ n - (k + l) < 3 then
        coeffVec .D4 y i k (coeffVec .D4 y i' l (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p)))
      else []
  | _ => []

@[expose] def d4OrbitRhs (y : Bool) (j : Fin Tag.G2.rank) (n p : ℕ) : List (ℕ × ℤ) :=
  if n < 4 then g2ToD4Vec (coeffVec .G2 y j n [(p, 1)]) else []

@[expose] def d4IntertwinerCheck (y : Bool) (I : List (Fin Tag.D4.rank)) (j : Fin Tag.G2.rank) :
    Bool :=
  (List.range (dim Tag.G2)).all fun p => (List.range 7).all fun n =>
    normalizeTwo (d4OrbitLhs y I n p) == normalizeTwo (d4OrbitRhs y j n p)

theorem d4IntertwinerCheck_x0 :
    d4IntertwinerCheck false [⟨2, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem d4IntertwinerCheck_x1 :
    d4IntertwinerCheck false [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] ⟨1, by decide⟩ =
      true := by
  decide +kernel

theorem d4IntertwinerCheck_y0 :
    d4IntertwinerCheck true [⟨2, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem d4IntertwinerCheck_y1 :
    d4IntertwinerCheck true [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] ⟨1, by decide⟩ =
      true := by
  decide +kernel

theorem ext_posVec_G2 {f g : RootModule Tag.G2 K →ₗ[K] RootModule Tag.D4 K}
    (h : ∀ p, p < dim Tag.G2 → f (posVec Tag.G2 K p) = g (posVec Tag.G2 K p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  simpa [posVec_eq_single hp] using h p hp

theorem g2ToD4Module_coeffOp (K : Type) [CommRing K] (y : Bool) (j : Fin Tag.G2.rank) {n p : ℕ}
    (hn : n < 4) (hp : p < dim Tag.G2) :
    g2ToD4Module K (coeffOp Tag.G2 K y j n (posVec Tag.G2 K p)) =
      vecOf Tag.D4 K (g2ToD4Vec (coeffVec .G2 y j n [(p, 1)])) := by
  obtain ⟨e, hv⟩ := coeffOp_vecOf simpleRow_G2_all g2_allValid K y j hn (validVec_single hp)
  rw [posVec_eq_vecOf_single, e, g2ToD4Module_vecOf K hv]

theorem d4_coeffOp_comp_of_check_single (K : Type) [CommRing K] (h2 : (2 : K) = 0) {y : Bool}
    {i : Fin Tag.D4.rank} {j : Fin Tag.G2.rank} (h : d4IntertwinerCheck y [i] j = true) {n : ℕ}
    (hn : n < 4) :
    coeffOp Tag.D4 K y i n ∘ₗ g2ToD4Module K = g2ToD4Module K ∘ₗ coeffOp Tag.G2 K y j n := by
  simp only [d4IntertwinerCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_G2 K fun p hp => ?_
  have e := vecOf_eq_of_normalizeTwo_eq (τ := Tag.D4) (R := K) h2 (h p hp n (by omega))
  simp only [d4OrbitLhs, d4OrbitRhs, hn, ↓reduceIte] at e
  rw [LinearMap.comp_apply, LinearMap.comp_apply, g2ToD4Module_posVec K hp,
    (coeffOp_vecOf simpleRow_D4_all d4_allValid K y i hn (validVec_g2ToD4Pos p)).1, e,
    g2ToD4Module_coeffOp K y j hn hp]

theorem d4_coeffOp_comp_of_check_triple (K : Type) [CommRing K] (h2 : (2 : K) = 0) {y : Bool}
    {i i' i'' : Fin Tag.D4.rank} {j : Fin Tag.G2.rank}
    (h : d4IntertwinerCheck y [i, i', i''] j = true) {n : ℕ} (hn : n < 7) :
    ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, (if k + l ≤ n ∧ n - (k + l) < 3 then
      (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l * coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ
        g2ToD4Module K else 0) =
      if n < 4 then g2ToD4Module K ∘ₗ coeffOp Tag.G2 K y j n else 0 := by
  simp only [d4IntertwinerCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_G2 K fun p hp => ?_
  have e := vecOf_eq_of_normalizeTwo_eq (τ := Tag.D4) (R := K) h2 (h p hp n hn)
  simp only [d4OrbitLhs, d4OrbitRhs] at e
  have hflat : vecOf Tag.D4 K ((List.range 3).flatMap fun k => (List.range 3).flatMap fun l =>
      if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
        (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) =
      ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, vecOf Tag.D4 K
        (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
          (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    rw [vecOf_flatMap_range]
    exact Finset.sum_congr rfl fun k _ => vecOf_flatMap_range 3 _
  rw [hflat] at e
  rw [LinearMap.sum_apply]
  have hL : ∀ k ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
      (if k + l ≤ n ∧ n - (k + l) < 3 then (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l *
        coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ g2ToD4Module K else 0) (posVec Tag.G2 K p) =
      vecOf Tag.D4 K (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k
        (coeffVec .D4 y i' l (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    intro k hk l hl
    by_cases hc : k + l ≤ n ∧ n - (k + l) < 3
    · rw [ite_eq_left hc, ite_eq_left hc]
      have hk4 : k < 4 := by have := Finset.mem_range.1 hk; omega
      have hl4 : l < 4 := by have := Finset.mem_range.1 hl; omega
      obtain ⟨e1, hv1⟩ := coeffOp_vecOf (k := n - (k + l)) simpleRow_D4_all d4_allValid K y i''
        (by omega) (validVec_g2ToD4Pos p)
      obtain ⟨e2, hv2⟩ := coeffOp_vecOf simpleRow_D4_all d4_allValid K y i' hl4 hv1
      rw [LinearMap.comp_apply, Module.End.mul_apply, Module.End.mul_apply,
        g2ToD4Module_posVec K hp, e1, e2,
        (coeffOp_vecOf simpleRow_D4_all d4_allValid K y i hk4 hv2).1]
    · rw [ite_eq_right hc, ite_eq_right hc]
      simp
  have hsum : ∑ k ∈ Finset.range 3, (∑ l ∈ Finset.range 3,
      (if k + l ≤ n ∧ n - (k + l) < 3 then (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l *
        coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ g2ToD4Module K else 0)) (posVec Tag.G2 K p) =
      ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, vecOf Tag.D4 K
        (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
          (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun l hl => hL k hk l hl
  rw [hsum, e]
  split_ifs with hn4
  · rw [LinearMap.comp_apply, g2ToD4Module_coeffOp K y j hn4 hp]
  · simp

theorem triple_poly_comp {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (A B C : ℕ → Module.End K W) (D : ℕ → Module.End K V) (T : V →ₗ[K] W)
    (h : ∀ n < 7, ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      (if k + l ≤ n ∧ n - (k + l) < 3 then (A k * B l * C (n - (k + l))) ∘ₗ T else 0) =
        if n < 4 then T ∘ₗ D n else 0) (c : K) :
    ((∑ k ∈ Finset.range 3, c ^ k • A k) * (∑ l ∈ Finset.range 3, c ^ l • B l) *
      (∑ m ∈ Finset.range 3, c ^ m • C m)) ∘ₗ T = T ∘ₗ ∑ m ∈ Finset.range 4, c ^ m • D m := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h0 h1 h2 h3 h4 h5 h6 ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, LinearMap.add_comp,
    LinearMap.smul_comp, LinearMap.comp_add, LinearMap.comp_smul]
  linear_combination (norm := module) h0 + c • h1 + c ^ 2 • h2 + c ^ 3 • h3 + c ^ 4 • h4 +
    c ^ 5 • h5 + c ^ 6 • h6

theorem xOp_D4_eq_sum (R : Type*) [CommRing R] (i : Fin Tag.D4.rank) (c : R) :
    xOp Tag.D4 R i c = ∑ k ∈ Finset.range 3, c ^ k • xCoeff Tag.D4 R i k :=
  xOp_eq_sum_xCoeff_entryDegreeBound Tag.D4 i c

theorem yOp_D4_eq_sum (R : Type*) [CommRing R] (i : Fin Tag.D4.rank) (c : R) :
    yOp Tag.D4 R i c = ∑ k ∈ Finset.range 3, c ^ k • yCoeff Tag.D4 R i k :=
  yOp_eq_sum_yCoeff_entryDegreeBound Tag.D4 i c

theorem g2OrbitX_comp_g2ToD4Module (R : Type) [CommRing R] (h2 : (2 : R) = 0)
    (j : Fin Tag.G2.rank) (c : R) :
    g2OrbitX R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ xOp Tag.G2 R j c := by
  fin_cases j
  · show [xOp Tag.D4 R ⟨2, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => d4_coeffOp_comp_of_check_single R h2 d4IntertwinerCheck_x0 hn) c
  · show [xOp Tag.D4 R ⟨0, by decide⟩ c, xOp Tag.D4 R ⟨1, by decide⟩ c,
      xOp Tag.D4 R ⟨3, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_cons, List.prod_cons, List.prod_singleton, ← mul_assoc, xOp_D4_eq_sum,
      xOp_D4_eq_sum, xOp_D4_eq_sum, xOp_eq_sum_xCoeff]
    exact triple_poly_comp R _ _ _ _ _
      (fun n hn => d4_coeffOp_comp_of_check_triple R h2 d4IntertwinerCheck_x1 hn) c

theorem g2OrbitY_comp_g2ToD4Module (R : Type) [CommRing R] (h2 : (2 : R) = 0)
    (j : Fin Tag.G2.rank) (c : R) :
    g2OrbitY R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ yOp Tag.G2 R j c := by
  fin_cases j
  · show [yOp Tag.D4 R ⟨2, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => d4_coeffOp_comp_of_check_single R h2 d4IntertwinerCheck_y0 hn) c
  · show [yOp Tag.D4 R ⟨0, by decide⟩ c, yOp Tag.D4 R ⟨1, by decide⟩ c,
      yOp Tag.D4 R ⟨3, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_cons, List.prod_cons, List.prod_singleton, ← mul_assoc, yOp_D4_eq_sum,
      yOp_D4_eq_sum, yOp_D4_eq_sum, yOp_eq_sum_yCoeff]
    exact triple_poly_comp R _ _ _ _ _
      (fun n hn => d4_coeffOp_comp_of_check_triple R h2 d4IntertwinerCheck_y1 hn) c

theorem even_D4_graph_fixed_module_G2_intertwiner (K : Type) [Field K] (hK : ringChar K = 2) :
    (∀ β, IsRoot Tag.D4 β → IsRoot Tag.G2 (d4ToG2 β)) ∧
    (∀ α, IsRoot Tag.G2 α → ∃ β, IsRoot Tag.D4 β ∧ d4ToG2 β = α ∧ ∀ β', IsRoot Tag.D4 β' →
      (d4ToG2 β' = α ↔ β' = β ∨ β' = permLattice TwistTag.D4.perm β ∨
        β' = permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm β))) ∧
    (∀ j, g2ToD4Module K (hVec Tag.G2 K j) =
      ((g2IndexOrbit j).map fun i => hVec Tag.D4 K i).sum) ∧
    (∀ α, IsRoot Tag.G2 α → g2ToD4Module K (rootVec Tag.G2 K α) =
      ∑ β ∈ (rootFinset Tag.D4).filter (fun β => d4ToG2 β = α), rootVec Tag.D4 K β) ∧
    (∀ v, v ∈ d4GraphFixedModule K ↔
      (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K)) v = v) ∧
    Function.Injective (g2ToD4Module K) ∧
    LinearMap.range (g2ToD4Module K) = d4GraphFixedModule K ∧
    (∀ j (c : K), g2OrbitX K j c ∘ₗ g2ToD4Module K = g2ToD4Module K ∘ₗ xOp Tag.G2 K j c) ∧
    (∀ j (c : K), g2OrbitY K j c ∘ₗ g2ToD4Module K = g2ToD4Module K ∘ₗ yOp Tag.G2 K j c) ∧
    ∀ (R : Type) [CommRing R], (2 : R) = 0 → ∀ j (c : R),
      g2OrbitX R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ xOp Tag.G2 R j c ∧
      g2OrbitY R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ yOp Tag.G2 R j c := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  refine ⟨fun β hβ => isRoot_d4ToG2 hβ, fun α hα => exists_d4ToG2_fibre hα, fun j => ?_,
    fun α hα => ?_, fun v => mem_d4GraphFixedModule, g2ToD4Module_injective K,
    range_g2ToD4Module K, g2OrbitX_comp_g2ToD4Module K h2, g2OrbitY_comp_g2ToD4Module K h2,
    fun R _ hR j c => ⟨g2OrbitX_comp_g2ToD4Module R hR j c, g2OrbitY_comp_g2ToD4Module R hR j c⟩⟩
  · rw [hVec, g2ToD4Module, Finsupp.linearCombination_single, one_smul]
  · rw [CFSG.LieType.Ree.rootVec_eq_single K hα, g2ToD4Module, Finsupp.linearCombination_single,
      one_smul]

end CFSG.RankThree.PartTwo.KFacts

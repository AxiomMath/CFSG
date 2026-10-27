module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroups

public section

open scoped Pointwise

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private def edgeX (Γ : SimpleGraph V) (v : V) : Subgroup H :=
  ⨆ w ∈ Γ.neighborSet v, edgeKernel (H := H) Γ w v

theorem edgeKernel_map_conj (g : H) (w v : V) :
    (edgeKernel (H := H) Γ w v).map (MulAut.conj g).toMonoidHom =
      edgeKernel (H := H) Γ (g • w) (g • v) := by
  have hsmul : ∀ x : V, g • Γ.neighborSet x = Γ.neighborSet (g • x) := by
    intro x
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, SimpleGraph.mem_neighborSet,
      SimpleGraph.mem_neighborSet]
    constructor
    · intro hy
      simpa using (GraphAction.adj_smul g x (g⁻¹ • y)).mpr hy
    · intro hy
      exact (GraphAction.adj_smul g x (g⁻¹ • y)).mp (by simpa using hy)
  unfold edgeKernel
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
        (g := g) (s := Γ.neighborSet w),
      ← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
        (g := g) (s := Γ.neighborSet v)]
  rw [hsmul w, hsmul v]

private theorem edgeX_map_conj (g : H) (v : V) :
    (edgeX (H := H) Γ v).map (MulAut.conj g).toMonoidHom =
      edgeX (H := H) Γ (g • v) := by
  have hbij : Set.BijOn (fun w => g • w) (Γ.neighborSet v) (Γ.neighborSet (g • v)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      exact (GraphAction.adj_smul g v w).mpr hw
    · intro w₁ _ w₂ _ h
      exact MulAction.injective g h
    · intro y hy
      refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
      simpa using (GraphAction.adj_smul g⁻¹ (g • v) y).mpr hy
  unfold edgeX
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]
  simp_rw [edgeKernel_map_conj]
  exact hbij.iSup_comp (fun y => edgeKernel (H := H) Γ y (g • v))

private theorem stabilizer_le_normalizer_edgeX (v : V) :
    MulAction.stabilizer H v ≤ Subgroup.normalizer (edgeX (H := H) Γ v : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj g).toMonoidHom (edgeX (H := H) Γ v) =
    edgeX (H := H) Γ v
  rw [edgeX_map_conj, MulAction.mem_stabilizer_iff.mp hg]

private theorem edgeX_isPGroup [Finite H] {n : ℕ} (hn : 1 ≤ n) (hW : WeissFree H Γ n)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) (v : V) :
    IsPGroup 2 (edgeX (H := H) Γ v) := by
  let Gv1 : Subgroup H := fixingSubgroup H (Γ.neighborSet v)
  have hnormal : ∀ w ∈ Γ.neighborSet v,
      ((edgeKernel (H := H) Γ w v).subgroupOf Gv1).Normal := by
    intro w hw
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro g hg
    have hgv : g • v = v := MulAction.mem_stabilizer_iff.mp (hK v hg)
    have hgw : g • w = w := (mem_fixingSubgroup_iff H).mp hg w hw
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj g).toMonoidHom (edgeKernel (H := H) Γ w v) =
      edgeKernel (H := H) Γ w v
    rw [edgeKernel_map_conj, hgw, hgv]
  have hpgroup : ∀ w ∈ Γ.neighborSet v,
      IsPGroup 2 ((edgeKernel (H := H) Γ w v).subgroupOf Gv1) := by
    intro w hw
    have hle : edgeKernel (H := H) Γ w v ≤ Gv1 := inf_le_right
    have hwv : Γ.Adj w v := ((SimpleGraph.mem_neighborSet Γ v w).mp hw).symm
    exact (edgeKernel_isPGroup_of_weissFree (H := H) hn hW hval hwv).of_equiv
      (Subgroup.subgroupOfEquivOfLe hle).symm
  let M : Subgroup H := (CFSG.pCore 2 Gv1).map Gv1.subtype
  have hM : IsPGroup 2 M :=
    (CFSG.pCore_isPGroup (p := 2) (G := Gv1)).map Gv1.subtype
  have hle : edgeX (H := H) Γ v ≤ M := by
    rw [edgeX]
    refine iSup_le fun w => iSup_le fun hw => ?_
    have hcore : (edgeKernel (H := H) Γ w v).subgroupOf Gv1 ≤ CFSG.pCore 2 Gv1 := by
      rw [show CFSG.pCore 2 Gv1 =
          sSup {K : Subgroup Gv1 | K.Normal ∧ IsPGroup 2 K} from rfl]
      exact le_sSup ⟨hnormal w hw, hpgroup w hw⟩
    calc edgeKernel (H := H) Γ w v
        = ((edgeKernel (H := H) Γ w v).subgroupOf Gv1).map Gv1.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (show edgeKernel (H := H) Γ w v ≤ Gv1 from
            inf_le_right)).symm
      _ ≤ (CFSG.pCore 2 Gv1).map Gv1.subtype := Subgroup.map_mono hcore
  exact hM.to_le hle

variable (H) in
@[expose] def edgeUnion (Γ : SimpleGraph V) (x y : V) : Subgroup H :=
  (⨆ w ∈ Γ.neighborSet x,
      fixingSubgroup H (Γ.neighborSet w) ⊓ fixingSubgroup H (Γ.neighborSet x)) ⊔
    ⨆ z ∈ Γ.neighborSet y,
      fixingSubgroup H (Γ.neighborSet y) ⊓ fixingSubgroup H (Γ.neighborSet z)

private theorem edgeUnion_eq_edgeX_sup (x y : V) :
    edgeUnion H Γ x y = edgeX (H := H) Γ x ⊔ edgeX (H := H) Γ y := by
  have hsecond : (⨆ z ∈ Γ.neighborSet y,
      fixingSubgroup H (Γ.neighborSet y) ⊓ fixingSubgroup H (Γ.neighborSet z)) =
      edgeX (H := H) Γ y := by
    rw [edgeX]
    apply iSup_congr
    intro z
    apply iSup_congr
    intro hz
    exact inf_comm (a := fixingSubgroup H (Γ.neighborSet y))
      (b := fixingSubgroup H (Γ.neighborSet z))
  rw [edgeUnion, hsecond]
  rfl

theorem edgeUnion_map_conj_eq (g : H) {x y : V} (hgx : g • x = x) (hgy : g • y = y) :
    (edgeUnion H Γ x y).map (MulAut.conj g).toMonoidHom = edgeUnion H Γ x y := by
  rw [edgeUnion_eq_edgeX_sup, Subgroup.map_sup, edgeX_map_conj g x, edgeX_map_conj g y,
    hgx, hgy]

theorem edgeUnion_le_stabilizer
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {x y : V}
    (hxy : Γ.Adj x y) :
    edgeUnion H Γ x y ≤ MulAction.stabilizer H x ⊓ MulAction.stabilizer H y := by
  rw [edgeUnion]
  refine sup_le ?_ ?_
  · refine iSup_le fun w => iSup_le fun hw => ?_
    intro g hg
    obtain ⟨-, hgx⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨hK x hgx, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_fixingSubgroup_iff H).mp hgx y hxy
  · refine iSup_le fun z => iSup_le fun hz => ?_
    intro g hg
    obtain ⟨hgy, -⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨?_, hK y hgy⟩
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_fixingSubgroup_iff H).mp hgy x hxy.symm

theorem edgeUnion_isPGroup [Finite H] {n : ℕ} (hn : 1 ≤ n) (hW : WeissFree H Γ n)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) {x y : V}
    (hxy : Γ.Adj x y) :
    IsPGroup 2 ↥(edgeUnion H Γ x y) := by
  have hxP : IsPGroup 2 (edgeX (H := H) Γ x) := edgeX_isPGroup hn hW hval hK x
  have hyP : IsPGroup 2 (edgeX (H := H) Γ y) := edgeX_isPGroup hn hW hval hK y
  have hy_stab_x : edgeX (H := H) Γ y ≤ MulAction.stabilizer H x := by
    rw [edgeX]
    refine iSup_le fun w => iSup_le fun hw => ?_
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_fixingSubgroup_iff H).mp hg.2 x hxy.symm
  have hy_norm : edgeX (H := H) Γ y ≤
      Subgroup.normalizer (edgeX (H := H) Γ x : Set H) :=
    hy_stab_x.trans (stabilizer_le_normalizer_edgeX x)
  have hsecond : (⨆ z ∈ Γ.neighborSet y,
      fixingSubgroup H (Γ.neighborSet y) ⊓ fixingSubgroup H (Γ.neighborSet z)) =
      edgeX (H := H) Γ y := by
    rw [edgeX]
    apply iSup_congr
    intro z
    apply iSup_congr
    intro hz
    exact inf_comm (a := fixingSubgroup H (Γ.neighborSet y))
      (b := fixingSubgroup H (Γ.neighborSet z))
  have h := IsPGroup.to_sup_of_normal_left' hxP hyP hy_norm
  rw [edgeUnion, hsecond]
  exact h

end CFSG.Quasithin.Stroth.WeissDelta

end

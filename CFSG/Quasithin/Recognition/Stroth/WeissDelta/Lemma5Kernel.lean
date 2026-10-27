module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.EdgeUnion
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootFacts

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

@[expose] def path3 (a b c : V) (hab : Γ.Adj a b) (hbc : Γ.Adj b c) : GPath Γ 2 where
  toFun i := if i = 0 then a else if i = 1 then b else c
  adj i hi := by
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> simp [hab, hbc]
  tail i hi := by
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    simp [h0, h1]

theorem path3_noBack {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : a ≠ c) :
    (path3 a b c hab hbc).NoBack := by
  intro i hi
  have hi' : i = 0 := by omega
  subst hi'
  simpa [path3] using hac

private theorem secondKernel_normal {z : V}
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) :
    ((secondKernel H Γ z).subgroupOf (MulAction.stabilizer H z)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (h := inf_le_left.trans hK)).mpr ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have hgz : g • z = z := MulAction.mem_stabilizer_iff.mp hg
  have hginv : g⁻¹ • z = z := by
    calc g⁻¹ • z = g⁻¹ • (g • z) := by rw [hgz]
      _ = z := by simp
  intro x
  constructor
  · intro hx
    have h := conj_mem_secondKernel g hx
    rwa [hgz] at h
  · intro hx
    have h := conj_mem_secondKernel (g := g⁻¹) hx
    have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rwa [hginv, heq] at h

private theorem secondKernel_le_edgeUnion {x y : V} (hxy : Γ.Adj x y) :
    secondKernel H Γ x ≤ edgeUnion H Γ x y := by
  have hx : secondKernel H Γ x ≤ fixingSubgroup H (Γ.neighborSet x) := by
    intro g hg
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_secondKernel_iff.mp hg).1 w hw
  have hy : secondKernel H Γ x ≤ fixingSubgroup H (Γ.neighborSet y) := by
    intro g hg
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact (mem_secondKernel_iff.mp hg).2 y hxy w hw
  intro g hg
  refine Subgroup.mem_sup_left ?_
  refine Subgroup.mem_iSup_of_mem y ?_
  refine Subgroup.mem_iSup_of_mem (by simpa using hxy) ?_
  exact ⟨hy hg, hx hg⟩

private theorem secondKernel_subgroupOf_edgeUnion_normal (hL : ∀ z, LocalFacts H Γ z)
    {x y : V} (hxy : Γ.Adj x y) :
    ((secondKernel H Γ x).subgroupOf (edgeUnion H Γ x y)).Normal := by
  haveI := secondKernel_normal (hL x).kernel_le
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    ((edgeUnion_le_stabilizer (fun z => (hL z).kernel_le) hxy).trans inf_le_left |>.trans
      (Subgroup.le_normalizer_of_normal_subgroupOf (inf_le_left.trans (hL x).kernel_le)))

def kernelCenter (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (x₀ y : V) : Subgroup H :=
  secondKernel H Γ x₀ ⊓
    (Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) ⊓ edgeUnion H Γ x₀ y)

private theorem mem_kernelCenter {x₀ y : V} {x : H} :
    x ∈ kernelCenter H Γ x₀ y ↔ x ∈ secondKernel H Γ x₀ ∧
      x ∈ Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) ∧
        x ∈ edgeUnion H Γ x₀ y := by
  simp only [kernelCenter, Subgroup.mem_inf]

theorem kernelCenter_le_secondKernel {x₀ y : V} :
    kernelCenter H Γ x₀ y ≤ secondKernel H Γ x₀ := inf_le_left

theorem kernelCenter_centralizes {x₀ y : V} :
    kernelCenter H Γ x₀ y ≤
      Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) :=
  inf_le_right.trans inf_le_left

theorem kernelCenter_le_edgeUnion {x₀ y : V} :
    kernelCenter H Γ x₀ y ≤ edgeUnion H Γ x₀ y :=
  inf_le_right.trans inf_le_right

theorem kernelCenter_conj_mem {x₀ y : V} {a x : H} (ha₀ : a • x₀ = x₀)
    (hay : a • y = y) (hx : x ∈ kernelCenter H Γ x₀ y) :
    a * x * a⁻¹ ∈ kernelCenter H Γ x₀ y := by
  obtain ⟨hxQ, hxcent, hxU⟩ := mem_kernelCenter.mp hx
  have hainv₀ : a⁻¹ • x₀ = x₀ := by
    calc a⁻¹ • x₀ = a⁻¹ • (a • x₀) := by rw [ha₀]
      _ = x₀ := by simp
  have hainvy : a⁻¹ • y = y := by
    calc a⁻¹ • y = a⁻¹ • (a • y) := by rw [hay]
      _ = y := by simp
  have hUmap : (edgeUnion H Γ x₀ y).map (MulAut.conj a).toMonoidHom =
      edgeUnion H Γ x₀ y := edgeUnion_map_conj_eq a ha₀ hay
  have hUmapinv : (edgeUnion H Γ x₀ y).map (MulAut.conj a⁻¹).toMonoidHom =
      edgeUnion H Γ x₀ y := edgeUnion_map_conj_eq a⁻¹ hainv₀ hainvy
  have hxQ' : a * x * a⁻¹ ∈ secondKernel H Γ x₀ :=
    by simpa [ha₀] using conj_mem_secondKernel a hxQ
  have hxU' : a * x * a⁻¹ ∈ edgeUnion H Γ x₀ y := by
    have h : (MulAut.conj a) x ∈ (edgeUnion H Γ x₀ y).map
        (MulAut.conj a).toMonoidHom := Subgroup.mem_map_of_mem _ hxU
    rw [hUmap] at h
    simpa [MulAut.conj_apply] using h
  have hxcent' : a * x * a⁻¹ ∈
      Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    have huinv : a⁻¹ * u * a ∈ edgeUnion H Γ x₀ y := by
      have h : (MulAut.conj a⁻¹) u ∈ (edgeUnion H Γ x₀ y).map
          (MulAut.conj a⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hu
      rw [hUmapinv] at h
      simpa [MulAut.conj_apply] using h
    have hcomm : (a⁻¹ * u * a) * x = x * (a⁻¹ * u * a) :=
      (Subgroup.mem_centralizer_iff.mp hxcent) _ huinv
    calc u * (a * x * a⁻¹) = a * ((a⁻¹ * u * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * u * a)) * a⁻¹ := by rw [hcomm]
      _ = (a * x * a⁻¹) * u := by group
  exact mem_kernelCenter.mpr ⟨hxQ', hxcent', hxU'⟩

theorem secondKernel_inf_fixingSubgroup_eq_bot (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {x₀ y y₂ : V} (hxy : Γ.Adj x₀ y) (hyy₂ : Γ.Adj y y₂) (hy₂x₀ : y₂ ≠ x₀) :
    secondKernel H Γ x₀ ⊓ fixingSubgroup H (Γ.neighborSet y₂) = ⊥ := by
  obtain ⟨w, hx₀w, hwy⟩ := hne x₀ y hxy
  obtain ⟨v, hwv, hvx₀⟩ := hne w x₀ hx₀w.symm
  let p : GPath Γ 4 := path5 y₂ y x₀ w v hyy₂.symm hxy.symm hx₀w hwv
  have hpnb : p.NoBack :=
    path5_noBack hyy₂.symm hxy.symm hx₀w hwv hy₂x₀ hwy.symm hvx₀.symm
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgQ, hgF⟩ := Subgroup.mem_inf.mp hg
  have hQ := mem_secondKernel_iff.mp hgQ
  have hfix : ∀ i, i ≤ 4 → g • p i = p i := by
    intro i hi
    interval_cases i
    · simpa [p, path5] using hQ.2 y hxy y₂ hyy₂
    · simpa [p, path5] using hQ.1 y hxy
    · simpa [p, path5] using hQ.2 y hxy x₀ hxy.symm
    · simpa [p, path5] using hQ.1 w hx₀w
    · simpa [p, path5] using hQ.2 w hx₀w v hwv
  have h0 : ∀ u, Γ.Adj (p 0) u → g • u = u := by
    intro u hu
    have hu' : Γ.Adj y₂ u := by simpa [p, path5] using hu
    exact (mem_fixingSubgroup_iff H).mp hgF u hu'
  have h1 : ∀ u, Γ.Adj (p 1) u → g • u = u := by
    intro u hu
    have hu' : Γ.Adj y u := by simpa [p, path5] using hu
    exact hQ.2 y hxy u hu'
  exact hW p hpnb g hfix h0 h1

theorem kernelCenter_ne_bot [Finite H] (hW : WeissFree H Γ 4)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) {x₀ y : V} (hxy : Γ.Adj x₀ y)
    (h2 : secondKernel H Γ x₀ ≠ ⊥) : kernelCenter H Γ x₀ y ≠ ⊥ := by
  classical
  let Q := secondKernel H Γ x₀
  let U := edgeUnion H Γ x₀ y
  have hQU : Q ≤ U := secondKernel_le_edgeUnion hxy
  haveI : (Q.subgroupOf U).Normal :=
    secondKernel_subgroupOf_edgeUnion_normal hL hxy
  have hU2 : IsPGroup 2 ↥U :=
    edgeUnion_isPGroup (n := 4) (by norm_num) hW hval
      (fun z => (hL z).kernel_le) hxy
  haveI : Group.IsNilpotent ↥U := IsPGroup.isNilpotent hU2
  have hQne : Q.subgroupOf U ≠ ⊥ := by
    intro hbot
    apply h2
    have hmap := congrArg (Subgroup.map (U.subtype)) hbot
    rw [Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hQU] at hmap
    exact hmap
  have hcenter : (Q.subgroupOf U) ⊓ Subgroup.center U ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hQne
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  let z : H := (c : H)
  have hcQ : z ∈ Q := by
    have h := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp c.2).1
    simpa [z] using h
  have hcCenter : (c : ↥U) ∈ Subgroup.center U := (Subgroup.mem_inf.mp c.2).2
  have hcCentral : z ∈ Subgroup.centralizer (U : Set H) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    have h := (Subgroup.mem_center_iff.mp hcCenter) (⟨u, hu⟩ : ↥U)
    have h' := congrArg (fun x : ↥U => (x : H)) h
    simpa [z] using h'
  have hcU : z ∈ U := by
    simpa [z] using c.1.2
  have hzP : z ∈ kernelCenter H Γ x₀ y :=
    mem_kernelCenter.mpr ⟨hcQ, hcCentral, hcU⟩
  have hzne : z ≠ 1 := by
    intro hz1
    apply hcne
    ext
    exact hz1
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨z, hzP⟩, ?_⟩
  intro h
  exact hzne (congrArg (fun x : ↥(kernelCenter H Γ x₀ y) => (x : H)) h)

private theorem kernelCenter_not_le_fixing [Finite H] (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) {x₀ y y₂ : V} (hxy : Γ.Adj x₀ y)
    (hyy₂ : Γ.Adj y y₂) (hy₂x₀ : y₂ ≠ x₀) (h2 : secondKernel H Γ x₀ ≠ ⊥) :
    ¬ kernelCenter H Γ x₀ y ≤ fixingSubgroup H (Γ.neighborSet y₂) := by
  intro hle
  refine kernelCenter_ne_bot hW hval hL hxy h2 ?_
  rw [eq_bot_iff]
  intro x hx
  have hxQ : x ∈ secondKernel H Γ x₀ := (mem_kernelCenter.mp hx).1
  have hxF : x ∈ fixingSubgroup H (Γ.neighborSet y₂) := hle hx
  have hmem : x ∈ secondKernel H Γ x₀ ⊓ fixingSubgroup H (Γ.neighborSet y₂) :=
    Subgroup.mem_inf.mpr ⟨hxQ, hxF⟩
  rw [secondKernel_inf_fixingSubgroup_eq_bot hW hne hxy hyy₂ hy₂x₀] at hmem
  simpa using hmem

theorem pathRootGroup_le_edgeUnion_one_two {p : GPath Γ 4} {x y : V}
    (hp1 : p 1 = y) (hp2 : p 2 = x) :
    pathRootGroup H Γ p ≤ edgeUnion H Γ x y := by
  intro g hg
  have hfix := mem_pathRootGroup.mp hg
  have hgy : g ∈ fixingSubgroup H (Γ.neighborSet y) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 1 (by norm_num) (by norm_num) w (by rwa [hp1])
  have hgx : g ∈ fixingSubgroup H (Γ.neighborSet x) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 2 (by norm_num) (by norm_num) w (by rwa [hp2])
  refine Subgroup.mem_sup_left ?_
  refine Subgroup.mem_iSup_of_mem y ?_
  refine Subgroup.mem_iSup_of_mem ?_ ?_
  · rw [SimpleGraph.mem_neighborSet, ← hp2, ← hp1]
    exact (p.adj 1 (by norm_num)).symm
  · exact ⟨hgy, hgx⟩

theorem pathRootGroup_le_edgeUnion_two_three {p : GPath Γ 4} {x y : V}
    (hp2 : p 2 = x) (hp3 : p 3 = y) :
    pathRootGroup H Γ p ≤ edgeUnion H Γ x y := by
  intro g hg
  have hfix := mem_pathRootGroup.mp hg
  have hgy : g ∈ fixingSubgroup H (Γ.neighborSet y) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 3 (by norm_num) (by norm_num) w (by rwa [hp3])
  have hgx : g ∈ fixingSubgroup H (Γ.neighborSet x) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 2 (by norm_num) (by norm_num) w (by rwa [hp2])
  refine Subgroup.mem_sup_left ?_
  refine Subgroup.mem_iSup_of_mem y ?_
  refine Subgroup.mem_iSup_of_mem ?_ ?_
  · rw [SimpleGraph.mem_neighborSet, ← hp3, ← hp2]
    exact (p.adj 2 (by norm_num))
  · exact ⟨hgy, hgx⟩

theorem pathRootGroup_le_edgeUnion_penultimate {p : GPath Γ 4} {x y : V}
    (hp3 : p 3 = x) :
    pathRootGroup H Γ p ≤ edgeUnion H Γ y x := by
  intro g hg
  have hfix := mem_pathRootGroup.mp hg
  have hgx : g ∈ fixingSubgroup H (Γ.neighborSet x) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 3 (by norm_num) (by norm_num) w (by rwa [hp3])
  have hgp2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    exact hfix 2 (by norm_num) (by norm_num) w hw
  have hp2 : p 2 ∈ Γ.neighborSet x := by
    rw [SimpleGraph.mem_neighborSet, ← hp3]
    exact (p.adj 2 (by norm_num)).symm
  refine Subgroup.mem_sup_right ?_
  refine Subgroup.mem_iSup_of_mem (p 2) ?_
  refine Subgroup.mem_iSup_of_mem hp2 ?_
  exact ⟨hgx, hgp2⟩

theorem isTorusNormalAt_of_stabPath_conj (hM : MoufangCondition H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hK : ∀ z : V, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    {p : GPath Γ 4} (hp : p.NoBack) {Z : Subgroup H}
    (hZstab : Z ≤ MulAction.stabilizer H (p 3))
    (hZconj : ∀ a ∈ GPath.stabPath (H := H) p, ∀ x ∈ Z, a * x * a⁻¹ ∈ Z) :
    IsTorusNormalAt H Γ (p 3) (p 2) Z := by
  refine ⟨p 4, p.adj 3 (by norm_num), (hp 2 (by norm_num)).symm, ?_⟩
  intro t ht x hx
  have hgood := (isGoodPath_of_noBack (n := 4) (by norm_num) hM hne hK
    (s := 4) (by norm_num) hp).2 3 (by norm_num) (by norm_num)
  have ht' : t ∈ (GPath.stabPath (H := H) p ⊓ socleAt H Γ (p 3)) ⊔
      fixingSubgroup H (Γ.neighborSet (p 3)) := by
    simpa using hgood ht
  have hAnorm : (GPath.stabPath (H := H) p ⊓ socleAt H Γ (p 3)) ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p 3)) : Set H) :=
    inf_le_right.trans ((socleAt_le_stabilizer (hK (p 3))).trans
      stabilizer_le_normalizer_fixingSubgroup)
  have ht'' : t ∈ (↑((GPath.stabPath (H := H) p ⊓ socleAt H Γ (p 3)) ⊔
      fixingSubgroup H (Γ.neighborSet (p 3))) : Set H) := ht'
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAnorm] at ht''
  rcases ht'' with ⟨a, ha, k, hk, hak⟩
  have haz : a • p 3 = p 3 := (GPath.mem_stabPath_iff.mp ha.1) 3 (by norm_num)
  have hzNormG : Z ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p 3)) : Set H) :=
    hZstab.trans stabilizer_le_normalizer_fixingSubgroup
  have hxNorm : x ∈
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p 3)) : Set H) :=
    stabilizer_le_normalizer_fixingSubgroup (hZstab hx)
  have hkx : k * x * k⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet (p 3)) := by
    have hxinv : x⁻¹ ∈
        Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (p 3)) : Set H) :=
      Subgroup.inv_mem _ hxNorm
    have hxinvkx : x⁻¹ * k * x ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
      simpa using (Subgroup.mem_normalizer_iff.mp hxinv k).mp hk
    have h1 : x * (x⁻¹ * k * x) ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet (p 3)) :=
      Subgroup.mul_mem_sup hx hxinvkx
    have h2 : k⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet (p 3)) :=
      Subgroup.mem_sup_right (Subgroup.inv_mem _ hk)
    have hEq : k * x * k⁻¹ = x * (x⁻¹ * k * x) * k⁻¹ := by group
    rw [hEq]
    exact Subgroup.mul_mem _ h1 h2
  have hmain : a * (k * x * k⁻¹) * a⁻¹ ∈ Z ⊔
      fixingSubgroup H (Γ.neighborSet (p 3)) := by
    have hprod := Subgroup.coe_mul_of_left_le_normalizer_right Z
      (fixingSubgroup H (Γ.neighborSet (p 3))) hzNormG
    have hkx' : k * x * k⁻¹ ∈
        (↑(Z ⊔ fixingSubgroup H (Γ.neighborSet (p 3))) : Set H) := hkx
    rw [hprod] at hkx'
    rcases hkx' with ⟨z₁, hz₁, z₂, hz₂, hz₁₂⟩
    have haz₁ : a * z₁ * a⁻¹ ∈ Z := hZconj a ha.1 z₁ hz₁
    have haz₂ : a * z₂ * a⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) :=
      (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_fixingSubgroup
          (MulAction.mem_stabilizer_iff.mpr haz)) z₂).mp hz₂
    have heq : a * (k * x * k⁻¹) * a⁻¹ = (a * z₁ * a⁻¹) * (a * z₂ * a⁻¹) := by
      rw [← hz₁₂]
      group
    rw [heq]
    exact Subgroup.mul_mem_sup haz₁ haz₂
  have htxy : t * x * t⁻¹ = a * (k * x * k⁻¹) * a⁻¹ := by
    rw [← hak]
    group
  rw [htxy]
  exact hmain

theorem kernelCenter_le_kernelCenter_of_ne [Finite H]
    (hM : MoufangCondition H Γ 4) (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) {e : ℕ} {x₀ : V}
    (hC : ∀ g : H, CenterFacts H Γ (g • x₀) e)
    {x₁ y : V} (h1 : Γ.Adj x₀ x₁) (hxy : Γ.Adj x₀ y) (hne_xy : x₁ ≠ y)
    (h2 : secondKernel H Γ x₀ ≠ ⊥) :
    kernelCenter H Γ x₀ x₁ ≤ kernelCenter H Γ x₀ y := by
  classical
  obtain ⟨x₂', hx₁x₂', hx₂'x₀⟩ := hne x₁ x₀ h1.symm
  obtain ⟨y₂, hyy₂, hy₂x₀⟩ := hne y x₀ hxy.symm
  obtain ⟨w, hy₂w, hwy⟩ := hne y₂ y hyy₂.symm
  let q : GPath Γ 4 := path5 x₂' x₁ x₀ y y₂ hx₁x₂'.symm h1.symm hxy hyy₂
  have hqnb : q.NoBack :=
    path5_noBack hx₁x₂'.symm h1.symm hxy hyy₂ hx₂'x₀ hne_xy hy₂x₀.symm
  have hq1 : q 1 = x₁ := by simp [q, path5]
  have hq2 : q 2 = x₀ := by simp [q, path5]
  have hq3 : q 3 = y := by simp [q, path5]
  have hq4 : q 4 = y₂ := by simp [q, path5]
  have hRroot : IsRootAt H Γ y₂ y (pathRootGroup H Γ q) := by
    have h := isRootAt_pathRootGroup (n := 4) (by norm_num) hM hW hne hval
      (fun z => (hL z).kernel_le) hqnb
    rw [hq4, hq3] at h
    exact h
  let p : GPath Γ 4 := path5 x₁ x₀ y y₂ w h1.symm hxy hyy₂ hy₂w
  have hpnb : p.NoBack :=
    path5_noBack h1.symm hxy hyy₂ hy₂w hne_xy hy₂x₀.symm hwy.symm
  have hp3 : p 3 = y₂ := by simp [p, path5]
  have hp2 : p 2 = y := by simp [p, path5]
  have hZle : kernelCenter H Γ x₀ x₁ ≤
      MulAction.stabilizer H y₂ ⊓ MulAction.stabilizer H y := by
    intro z hz
    have hzQ := mem_secondKernel_iff.mp (kernelCenter_le_secondKernel (H := H) (Γ := Γ) hz)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.2 y hxy y₂ hyy₂
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.1 y hxy
  have hZ'le : kernelCenter H Γ x₀ y ≤
      MulAction.stabilizer H y₂ ⊓ MulAction.stabilizer H y := by
    intro z hz
    have hzQ := mem_secondKernel_iff.mp (kernelCenter_le_secondKernel (H := H) (Γ := Γ) hz)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.2 y hxy y₂ hyy₂
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.1 y hxy
  have hZconj₁ : ∀ a ∈ GPath.stabPath (H := H) p, ∀ z ∈ kernelCenter H Γ x₀ x₁,
      a * z * a⁻¹ ∈ kernelCenter H Γ x₀ x₁ := by
    intro a ha z hz
    have ha0 : a • x₀ = x₀ := by
      have h := (GPath.mem_stabPath_iff.mp ha) 1 (by norm_num)
      simpa [p, path5] using h
    have ha1 : a • x₁ = x₁ := by
      have h := (GPath.mem_stabPath_iff.mp ha) 0 (by norm_num)
      simpa [p, path5] using h
    exact kernelCenter_conj_mem ha0 ha1 hz
  have hZconj₂ : ∀ a ∈ GPath.stabPath (H := H) p, ∀ z ∈ kernelCenter H Γ x₀ y,
      a * z * a⁻¹ ∈ kernelCenter H Γ x₀ y := by
    intro a ha z hz
    have ha0 : a • x₀ = x₀ := by
      have h := (GPath.mem_stabPath_iff.mp ha) 1 (by norm_num)
      simpa [p, path5] using h
    have hay : a • y = y := by
      have h := (GPath.mem_stabPath_iff.mp ha) 2 (by norm_num)
      simpa [p, path5] using h
    exact kernelCenter_conj_mem ha0 hay hz
  have hTN₁ : IsTorusNormalAt H Γ y₂ y (kernelCenter H Γ x₀ x₁) := by
    have h := isTorusNormalAt_of_stabPath_conj hM hne (fun z => (hL z).kernel_le)
      (Z := kernelCenter H Γ x₀ x₁) hpnb ?_ hZconj₁
    · simpa [hp3, hp2] using h
    · simpa [hp3] using hZle.trans inf_le_left
  have hTN₂ : IsTorusNormalAt H Γ y₂ y (kernelCenter H Γ x₀ y) := by
    have h := isTorusNormalAt_of_stabPath_conj hM hne (fun z => (hL z).kernel_le)
      (Z := kernelCenter H Γ x₀ y) hpnb ?_ hZconj₂
    · simpa [hp3, hp2] using h
    · simpa [hp3] using hZ'le.trans inf_le_left
  have hcomm₁ : ⁅pathRootGroup H Γ q, kernelCenter H Γ x₀ x₁⁆ ≤
      fixingSubgroup H (Γ.neighborSet y₂) := by
    rw [Subgroup.commutator_le]
    intro r hr z hz
    have hzU : z ∈ edgeUnion H Γ x₀ x₁ := kernelCenter_le_edgeUnion hz
    have hzC : z ∈ Subgroup.centralizer (edgeUnion H Γ x₀ x₁ : Set H) :=
      kernelCenter_centralizes hz
    have hrU : r ∈ edgeUnion H Γ x₀ x₁ :=
      pathRootGroup_le_edgeUnion_one_two hq1 hq2 hr
    have hcomm : r * z = z * r := (Subgroup.mem_centralizer_iff.mp hzC) r hrU
    have hone : ⁅r, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [hone]
    exact Subgroup.one_mem _
  have hcomm₂ : ⁅pathRootGroup H Γ q, kernelCenter H Γ x₀ y⁆ ≤
      fixingSubgroup H (Γ.neighborSet y₂) := by
    rw [Subgroup.commutator_le]
    intro r hr z hz
    have hzU : z ∈ edgeUnion H Γ x₀ y := kernelCenter_le_edgeUnion hz
    have hzC : z ∈ Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) :=
      kernelCenter_centralizes hz
    have hrU : r ∈ edgeUnion H Γ x₀ y :=
      pathRootGroup_le_edgeUnion_two_three hq2 hq3 hr
    have hcomm : r * z = z * r := (Subgroup.mem_centralizer_iff.mp hzC) r hrU
    have hone : ⁅r, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [hone]
    exact Subgroup.one_mem _
  have hnot : ¬ kernelCenter H Γ x₀ y ≤ fixingSubgroup H (Γ.neighborSet y₂) :=
    kernelCenter_not_le_fixing hW hne hval hL hxy hyy₂ hy₂x₀ h2
  obtain ⟨g, -, hgx⟩ := hloc y x₀ y₂ hxy.symm hyy₂
  have hCy : CenterFacts H Γ y₂ e := by
    have h := hC g
    rwa [hgx] at h
  have hle := hCy.le_of_ne_bot y hyy₂.symm (pathRootGroup H Γ q)
    (kernelCenter H Γ x₀ x₁) (kernelCenter H Γ x₀ y) hRroot hZle hZ'le
    hTN₁ hTN₂ hcomm₁ hcomm₂ hnot
  intro x hx
  have hxsup : x ∈ kernelCenter H Γ x₀ y ⊔ fixingSubgroup H (Γ.neighborSet y₂) := hle hx
  have hnorm : kernelCenter H Γ x₀ y ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet y₂) : Set H) :=
    (hZ'le.trans inf_le_left).trans stabilizer_le_normalizer_fixingSubgroup
  have hx' : x ∈ (↑(kernelCenter H Γ x₀ y ⊔
      fixingSubgroup H (Γ.neighborSet y₂)) : Set H) := hxsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hx'
  rcases hx' with ⟨p, hp, k, hk, hpk⟩
  have hxQ : x ∈ secondKernel H Γ x₀ := kernelCenter_le_secondKernel hx
  have hpQ : p ∈ secondKernel H Γ x₀ := kernelCenter_le_secondKernel hp
  have hkQ : k ∈ secondKernel H Γ x₀ := by
    have hk_eq : k = p⁻¹ * x := by
      rw [← hpk]
      group
    rw [hk_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpQ) hxQ
  have hkbot : k ∈ secondKernel H Γ x₀ ⊓ fixingSubgroup H (Γ.neighborSet y₂) :=
    Subgroup.mem_inf.mpr ⟨hkQ, hk⟩
  rw [secondKernel_inf_fixingSubgroup_eq_bot hW hne hxy hyy₂ hy₂x₀] at hkbot
  have hk1 : k = 1 := by simpa using hkbot
  rw [← hpk]
  simpa [hk1] using hp

end CFSG.Quasithin.Stroth.WeissDelta

end

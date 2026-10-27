module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.EdgeUnion
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPath
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

private def edgeCenter (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (x y : V) : Subgroup H :=
  Subgroup.centralizer (edgeUnion H Γ x y : Set H) ⊓ edgeUnion H Γ x y

private theorem edgeCenter_le_edgeUnion (x y : V) :
    edgeCenter H Γ x y ≤ edgeUnion H Γ x y := inf_le_right

private theorem edgeCenter_le_centralizer (x y : V) :
    edgeCenter H Γ x y ≤ Subgroup.centralizer (edgeUnion H Γ x y : Set H) := inf_le_left

private theorem edgeCenter_comm (x y : V) {z u : H} (hz : z ∈ edgeCenter H Γ x y)
    (hu : u ∈ edgeUnion H Γ x y) : z * u = u * z := by
  have hc : z ∈ Subgroup.centralizer (edgeUnion H Γ x y : Set H) :=
    edgeCenter_le_centralizer x y hz
  exact ((Subgroup.mem_centralizer_iff.mp hc) u hu).symm

private theorem tripleKernel_map_conj (g : H) (x v u : V) :
    (((fixingSubgroup H (Γ.neighborSet x) ⊓ fixingSubgroup H (Γ.neighborSet v)) ⊓
      fixingSubgroup H (Γ.neighborSet u)).map (MulAut.conj g).toMonoidHom) =
      (fixingSubgroup H (Γ.neighborSet (g • x)) ⊓
        fixingSubgroup H (Γ.neighborSet (g • v))) ⊓
        fixingSubgroup H (Γ.neighborSet (g • u)) := by
  rw [Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    ← fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g x,
    ← fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g v,
    ← fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g u]

private theorem edgeCenter_conj_mem {x y : V} {g z : H}
    (hgx : g • x = x) (hgy : g • y = y) (hz : z ∈ edgeCenter H Γ x y) :
    g * z * g⁻¹ ∈ edgeCenter H Γ x y := by
  obtain ⟨hzcent, hzU⟩ := Subgroup.mem_inf.mp hz
  have hUmap := edgeUnion_map_conj_eq (H := H) (Γ := Γ) g hgx hgy
  have hzU' : g * z * g⁻¹ ∈ edgeUnion H Γ x y := by
    have : g * z * g⁻¹ ∈ (edgeUnion H Γ x y).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzU
    rwa [hUmap] at this
  refine Subgroup.mem_inf.mpr ⟨?_, hzU'⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro u hu
  have hginvx : g⁻¹ • x = x := by
    calc g⁻¹ • x = g⁻¹ • (g • x) := by rw [hgx]
      _ = x := by simp
  have hginy : g⁻¹ • y = y := by
    calc g⁻¹ • y = g⁻¹ • (g • y) := by rw [hgy]
      _ = y := by simp
  have hUmapinv := edgeUnion_map_conj_eq (H := H) (Γ := Γ) g⁻¹ hginvx hginy
  have huinv : g⁻¹ * u * g ∈ edgeUnion H Γ x y := by
    have hmem : (MulAut.conj g⁻¹) u ∈ (edgeUnion H Γ x y).map
        (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hu
    rw [hUmapinv] at hmem
    simpa [MulAut.conj_apply, mul_assoc] using hmem
  have hcomm : z * (g⁻¹ * u * g) = (g⁻¹ * u * g) * z :=
    ((Subgroup.mem_centralizer_iff.mp hzcent) (g⁻¹ * u * g) huinv).symm
  calc u * (g * z * g⁻¹) = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by rw [← hcomm]
    _ = (g * z * g⁻¹) * u := by group

private theorem edgeKernel_le_edgeUnion_left {x y w : V} (hw : Γ.Adj x w) :
    edgeKernel (H := H) Γ x w ≤ edgeUnion H Γ x y := by
  unfold edgeUnion
  refine le_sup_of_le_left ?_
  refine le_iSup_of_le w (le_iSup_of_le ?_ ?_)
  · simpa [SimpleGraph.mem_neighborSet] using hw
  · rw [edgeKernel, inf_comm]

private theorem edgeKernel_ne_bot_of_edge (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    {x y : V} (hxy : Γ.Adj x y) : edgeKernel (H := H) Γ x y ≠ ⊥ := by
  obtain ⟨a, hxa, hay⟩ := hne x y hxy
  obtain ⟨b, hyb, hbx⟩ := hne y x hxy.symm
  obtain ⟨c, hbc, hcy⟩ := hne b y hyb.symm
  let p : GPath Γ 4 := path5 a x y b c hxa.symm hxy hyb hbc
  have hpnb : p.NoBack := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · simpa [p, path5] using hay
    · simpa [p, path5] using hbx.symm
    · simpa [p, path5] using hcy.symm
  have hp1 : p 1 = x := by simp [p, path5]
  have hp2 : p 2 = y := by simp [p, path5]
  have hp3 : p 3 = b := by simp [p, path5]
  have hp4 : p 4 = c := by simp [p, path5]
  obtain ⟨s, hcs, hsb, -⟩ := h3 c b b hbc.symm hbc.symm
  obtain ⟨s', hcs', hs'b, hs's⟩ := h3 c b s hbc.symm hcs
  have hsne : s ≠ b := hsb
  have hs'ne : s' ≠ b := hs'b
  have hs's' : s' ≠ s := hs's
  obtain ⟨r, hr, -⟩ := pathRootGroup_regular_of_weissFree (n := 4) (by norm_num) hM hW hpnb
    (by simpa [hp4] using hcs) (by simpa [hp4] using hcs')
    (by simpa [hp3] using hsne) (by simpa [hp3] using hs'ne)
  have hUle : pathRootGroup H Γ p ≤ edgeKernel (H := H) Γ x y := by
    intro g hg
    rw [mem_edgeKernel]
    constructor
    · intro w hw
      have h := mem_pathRootGroup.mp hg 1 (by norm_num) (by norm_num) w
      rw [hp1] at h
      exact h hw
    · intro w hw
      have h := mem_pathRootGroup.mp hg 2 (by norm_num) (by norm_num) w
      rw [hp2] at h
      exact h hw
  intro hbot
  have hrmem : (r : H) ∈ edgeKernel (H := H) Γ x y := hUle r.2
  have hrbot : (r : H) ∈ (⊥ : Subgroup H) := by rwa [hbot] at hrmem
  have hrone : (r : H) = 1 := by simpa using hrbot
  have hr1 : r = 1 := Subtype.ext hrone
  have hst : s = s' := by
    have := hr
    rw [hr1] at this
    simpa using this
  exact hs's' hst.symm

private theorem edgeCenter_ne_bot [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) {x y : V} (hxy : Γ.Adj x y) :
    edgeCenter H Γ x y ≠ ⊥ := by
  have hK : edgeKernel (H := H) Γ x y ≠ ⊥ :=
    edgeKernel_ne_bot_of_edge hM hW hne h3 hxy
  have hUle : edgeKernel (H := H) Γ x y ≤ edgeUnion H Γ x y :=
    edgeKernel_le_edgeUnion_left hxy
  have hU : edgeUnion H Γ x y ≠ ⊥ := fun h => hK (le_bot_iff.mp (hUle.trans (le_of_eq h)))
  have hU2 : IsPGroup 2 ↥(edgeUnion H Γ x y) :=
    edgeUnion_isPGroup (n := 4) (by norm_num) hW hval (fun z => (hL z).kernel_le) hxy
  haveI : Nontrivial ↥(edgeUnion H Γ x y) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hU
  have hcenter : Subgroup.center ↥(edgeUnion H Γ x y) ≠ ⊥ :=
    ne_of_gt (IsPGroup.bot_lt_center hU2)
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  let z : H := (c.1 : H)
  have hcU : z ∈ edgeUnion H Γ x y := c.1.2
  have hccent : z ∈ Subgroup.centralizer (edgeUnion H Γ x y : Set H) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    have h := (Subgroup.mem_center_iff.mp c.2) (⟨u, hu⟩ : ↥(edgeUnion H Γ x y))
    have h' := congrArg (fun x : ↥(edgeUnion H Γ x y) => (x : H)) h
    simpa [z, mul_comm] using h'
  have hcZ : z ∈ edgeCenter H Γ x y := Subgroup.mem_inf.mpr ⟨hccent, hcU⟩
  intro hbot
  have hzbot : z ∈ (⊥ : Subgroup H) := by rwa [hbot] at hcZ
  have hz1 : z = 1 := by simpa using hzbot
  have hc1 : c = 1 := by
    ext
    exact hz1
  exact hcne hc1

private theorem edgeUnion_comm (x y : V) :
    edgeUnion H Γ x y = edgeUnion H Γ y x := by
  unfold edgeUnion
  simp_rw [inf_comm]
  rw [sup_comm]

private theorem edgeCenter_swap (x y : V) :
    edgeCenter H Γ y x = edgeCenter H Γ x y := by
  unfold edgeCenter
  rw [edgeUnion_comm x y]

private theorem edgeCenter_le_fixing_left [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) (hT : ∀ z, TransitiveFacts H Γ z)
    (h2 : ∀ z, secondKernel H Γ z = ⊥) {x y : V} (hxy : Γ.Adj x y) :
    edgeCenter H Γ x y ≤ fixingSubgroup H (Γ.neighborSet x) := by
  by_contra hnot
  have hK : ∀ z, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z :=
    fun z => (hL z).kernel_le
  have hU2 : IsPGroup 2 ↥(edgeUnion H Γ x y) :=
    edgeUnion_isPGroup (n := 4) (by norm_num) hW hval hK hxy
  have hZ2 : IsPGroup 2 ↥(edgeCenter H Γ x y) :=
    IsPGroup.to_le hU2 (edgeCenter_le_edgeUnion x y)
  have hZstab : edgeCenter H Γ x y ≤
      MulAction.stabilizer H x ⊓ MulAction.stabilizer H y :=
    (edgeCenter_le_edgeUnion x y).trans (edgeUnion_le_stabilizer (fun z => (hL z).kernel_le) hxy)
  obtain ⟨w', hxw', hyw', -⟩ := h3 x y y hxy hxy
  have hZnorm : ∀ t ∈ socTorus H Γ x y w', ∀ z ∈ edgeCenter H Γ x y,
      t * z * t⁻¹ ∈ edgeCenter H Γ x y ⊔ fixingSubgroup H (Γ.neighborSet x) := by
    intro t ht z hz
    have htsoc : t ∈ socleAt H Γ x := (Subgroup.mem_inf.mp ht).1.1
    have hty : t ∈ MulAction.stabilizer H y := (Subgroup.mem_inf.mp ht).1.2
    have htx : t ∈ MulAction.stabilizer H x :=
      socleAt_le_stabilizer (hL x).kernel_le htsoc
    have htx' : t • x = x := MulAction.mem_stabilizer_iff.mp htx
    have hty' : t • y = y := MulAction.mem_stabilizer_iff.mp hty
    exact Subgroup.mem_sup_left (edgeCenter_conj_mem htx' hty' hz)
  have htrans := (hT x).transitive y w' hxy hxw' hyw'.symm
    (edgeCenter H Γ x y) hZstab hZ2 hnot hZnorm
  have hfam : ∀ w1 w2 : V, Γ.Adj x w1 → Γ.Adj x w2 → w1 ≠ y → w2 ≠ y →
      edgeKernel (H := H) Γ x w1 = edgeKernel (H := H) Γ x w2 := by
    intro w1 w2 hxw1 hxw2 h1 h2
    obtain ⟨z, hzZ, hzw⟩ := htrans w1 w2 hxw1 hxw2 h1 h2
    have hzU : z ∈ edgeUnion H Γ x y := edgeCenter_le_edgeUnion x y hzZ
    have hzx : z • x = x := by
      have h := edgeUnion_le_stabilizer (fun z => (hL z).kernel_le) hxy hzU
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).1
    have hcent : ∀ e ∈ edgeKernel (H := H) Γ x w1, z * e = e * z := by
      intro e he
      exact edgeCenter_comm x y hzZ (edgeKernel_le_edgeUnion_left hxw1 he)
    have hmap : (edgeKernel (H := H) Γ x w1).map (MulAut.conj z).toMonoidHom =
        edgeKernel (H := H) Γ x w1 := by
      refine le_antisymm ?_ ?_
      · intro e he
        rw [Subgroup.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        have := hcent e0 he0
        simpa [MulAut.conj_apply, this] using he0
      · intro e he
        refine Subgroup.mem_map.mpr ⟨e, he, ?_⟩
        have := hcent e he
        simp [MulAut.conj_apply, this]
    have hEq : edgeKernel (H := H) Γ x (z • w1) = edgeKernel (H := H) Γ x w1 := by
      rw [← hzx, ← edgeKernel_map_conj z x w1, hmap, hzx]
    rw [hzw] at hEq
    exact hEq.symm
  have hfam' : ∀ e : V, Γ.Adj x e → ∀ w1 w2 : V, Γ.Adj x w1 → Γ.Adj x w2 →
      w1 ≠ e → w2 ≠ e → edgeKernel (H := H) Γ x w1 = edgeKernel (H := H) Γ x w2 := by
    intro e hxe w1 w2 hxw1 hxw2 h1 h2
    obtain ⟨g, hgx, hgye⟩ := hloc x y e hxy hxe
    have hgx' : g⁻¹ • x = x := by
      calc g⁻¹ • x = g⁻¹ • (g • x) := by rw [hgx]
        _ = x := by simp
    have hw1 : g⁻¹ • w1 ≠ y := by
      intro h
      apply h1
      rw [← hgye, ← h]
      simp
    have hw2 : g⁻¹ • w2 ≠ y := by
      intro h
      apply h2
      rw [← hgye, ← h]
      simp
    have hxw1' : Γ.Adj x (g⁻¹ • w1) := by
      have h := (GraphAction.adj_smul g⁻¹ x w1).mpr hxw1
      simpa [hgx'] using h
    have hxw2' : Γ.Adj x (g⁻¹ • w2) := by
      have h := (GraphAction.adj_smul g⁻¹ x w2).mpr hxw2
      simpa [hgx'] using h
    have hmap1 : (edgeKernel (H := H) Γ x (g⁻¹ • w1)).map (MulAut.conj g).toMonoidHom =
        edgeKernel (H := H) Γ x w1 := by
      rw [edgeKernel_map_conj g x (g⁻¹ • w1), hgx]
      simp
    have hmap2 : (edgeKernel (H := H) Γ x (g⁻¹ • w2)).map (MulAut.conj g).toMonoidHom =
        edgeKernel (H := H) Γ x w2 := by
      rw [edgeKernel_map_conj g x (g⁻¹ • w2), hgx]
      simp
    rw [← hmap1, ← hmap2, hfam (g⁻¹ • w1) (g⁻¹ • w2) hxw1' hxw2' hw1 hw2]
  have hall : ∀ w : V, Γ.Adj x w → edgeKernel (H := H) Γ x w = edgeKernel (H := H) Γ x y := by
    intro w hxw
    by_cases hwy : w = y
    · subst hwy
      rfl
    · obtain ⟨u, hxu, huy, huw⟩ := h3 x y w hxy hxw
      have h1 : edgeKernel (H := H) Γ x u = edgeKernel (H := H) Γ x w :=
        hfam u w hxu hxw huy hwy
      have h2' : edgeKernel (H := H) Γ x u = edgeKernel (H := H) Γ x y :=
        hfam' w hxw u y hxu hxy huw (fun h => hwy h.symm)
      exact h1.symm.trans h2'
  have hKle : edgeKernel (H := H) Γ x y ≤ secondKernel H Γ x := by
    unfold secondKernel
    refine le_inf inf_le_left ?_
    refine le_iInf fun w => le_iInf fun hw => ?_
    rw [← hall w (by simpa [SimpleGraph.mem_neighborSet] using hw)]
    exact inf_le_right
  have hbotK : edgeKernel (H := H) Γ x y = ⊥ := by
    have := h2 x
    rw [this] at hKle
    exact le_bot_iff.mp hKle
  exact edgeKernel_ne_bot_of_edge hM hW hne h3 hxy hbotK


private theorem edgeCenter_le_fixing_right [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) (hT : ∀ z, TransitiveFacts H Γ z)
    (h2 : ∀ z, secondKernel H Γ z = ⊥) {x y : V} (hxy : Γ.Adj x y) :
    edgeCenter H Γ x y ≤ fixingSubgroup H (Γ.neighborSet y) := by
  rw [← edgeCenter_swap x y]
  exact edgeCenter_le_fixing_left hM hW hne h3 hval hloc hL hT h2 hxy.symm


private theorem edgeCenter_le_fixing_third [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hL : ∀ z, LocalFacts H Γ z) (hT : ∀ z, TransitiveFacts H Γ z)
    (h2 : ∀ z, secondKernel H Γ z = ⊥) {x y v : V}
    (hxy : Γ.Adj x y) (hxv : Γ.Adj x v) (hvy : v ≠ y)
    (hZx : edgeCenter H Γ x y ≤ fixingSubgroup H (Γ.neighborSet x)) :
    edgeCenter H Γ x y ≤ fixingSubgroup H (Γ.neighborSet v) := by
  by_contra hnot
  let Z : Subgroup H := edgeCenter H Γ x y
  have hK : ∀ z, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z :=
    fun z => (hL z).kernel_le
  have hZ2 : IsPGroup 2 ↥Z :=
    IsPGroup.to_le (edgeUnion_isPGroup (n := 4) (by norm_num) hW hval hK hxy)
      (edgeCenter_le_edgeUnion x y)
  obtain ⟨ω', hvω', hω'x⟩ := hne v x hxv.symm
  let r2 : GPath Γ 2 := GPath.cons v (GPath.ofAdj hxy) hxv.symm
  let p3 : GPath Γ 3 := GPath.cons ω' r2 hvω'.symm
  have hr2 : r2.NoBack := by
    refine GPath.noBack_cons v (GPath.ofAdj hxy) hxv.symm (by intro i hi; omega) ?_
    simpa using hvy
  have hr2_1 : r2 1 = x := by
    have h := GPath.cons_succ v (GPath.ofAdj hxy) hxv.symm 0
    simpa [r2, show (0 : ℕ) + 1 = 1 by norm_num] using h
  have hp3nb : p3.NoBack := by
    refine GPath.noBack_cons ω' r2 hvω'.symm hr2 ?_
    simpa [hr2_1] using hω'x
  have hp30 : p3 0 = ω' := GPath.cons_zero ω' r2 hvω'.symm
  have hp31 : p3 1 = v := by
    have h1 := GPath.cons_succ ω' r2 hvω'.symm 0
    rw [show (0 : ℕ) + 1 = 1 by norm_num] at h1
    exact h1.trans (GPath.cons_zero v (GPath.ofAdj hxy) hxv.symm)
  have hp32 : p3 2 = x := by
    have h1 := GPath.cons_succ ω' r2 hvω'.symm 1
    have h2 := GPath.cons_succ v (GPath.ofAdj hxy) hxv.symm 0
    have h := h1.trans (h2.trans (GPath.ofAdj_zero hxy))
    simpa [show (1 : ℕ) + 1 = 2 by norm_num, show (0 : ℕ) + 1 = 1 by norm_num] using h
  have hp33 : p3 3 = y := by
    have h1 := GPath.cons_succ ω' r2 hvω'.symm 2
    have h2 := GPath.cons_succ v (GPath.ofAdj hxy) hxv.symm 1
    have h := h1.trans (h2.trans (GPath.ofAdj_one hxy))
    simpa [show (2 : ℕ) + 1 = 3 by norm_num, show (1 : ℕ) + 1 = 2 by norm_num] using h
  have hgood := (isGoodPath_of_noBack (n := 4) (by norm_num) hM hne hK (s := 3)
    (by norm_num) hp3nb).2 1 (by norm_num) (by norm_num)
  simp only [hp31, hp30, hp32] at hgood
  have hTnorm : ∀ t ∈ socTorus H Γ v x ω', ∀ z ∈ Z,
      t * z * t⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet v) := by
    intro t ht z hz
    have ht' : t ∈ socTorus H Γ v ω' x := by
      simpa [socTorus_comm v x ω'] using ht
    have htR : t ∈ (p3.stabPath ⊓ socleAt H Γ v) ⊔
        fixingSubgroup H (Γ.neighborSet v) := hgood ht'
    have hAnorm : (p3.stabPath ⊓ socleAt H Γ v) ≤
        Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet v) : Set H) :=
      inf_le_right.trans ((socleAt_le_stabilizer (hK v)).trans
        (stabilizer_le_normalizer_fixingSubgroup (z := v)))
    have htA : t ∈ (↑((p3.stabPath ⊓ socleAt H Γ v) ⊔
        fixingSubgroup H (Γ.neighborSet v)) : Set H) := htR
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAnorm] at htA
    rcases htA with ⟨a, ha, k, hk, hakt⟩
    have hax : a • x = x := by
      have := (GPath.mem_stabPath_iff.mp ha.1) 2 (by omega)
      simpa [hp32] using this
    have hay : a • y = y := by
      have := (GPath.mem_stabPath_iff.mp ha.1) 3 (by omega)
      simpa [hp33] using this
    have haNormZ : a ∈ Subgroup.normalizer (Z : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        exact edgeCenter_conj_mem hax hay hw
      · intro hw
        have hainvx : a⁻¹ • x = x := by
          calc a⁻¹ • x = a⁻¹ • (a • x) := by rw [hax]
            _ = x := by simp
        have hainvy : a⁻¹ • y = y := by
          calc a⁻¹ • y = a⁻¹ • (a • y) := by rw [hay]
            _ = y := by simp
        have hmem := edgeCenter_conj_mem (g := a⁻¹) hainvx hainvy hw
        convert hmem using 1 <;> group
    have haNormB : a ∈ Subgroup.normalizer
        (fixingSubgroup H (Γ.neighborSet v) : Set H) :=
      ((socleAt_le_stabilizer (hK v)).trans
        (stabilizer_le_normalizer_fixingSubgroup (z := v))) ha.2
    have hmapZ : (Z.map (MulAut.conj a).toMonoidHom) = Z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haNormZ
    have hmapB : ((fixingSubgroup H (Γ.neighborSet v)).map
        (MulAut.conj a).toMonoidHom) = fixingSubgroup H (Γ.neighborSet v) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haNormB
    have hzGv : z ∈ MulAction.stabilizer H v := by
      rw [MulAction.mem_stabilizer_iff]
      exact (mem_fixingSubgroup_iff H).mp (hZx hz) v hxv
    have hzNormB : z ∈ Subgroup.normalizer
        (fixingSubgroup H (Γ.neighborSet v) : Set H) :=
      stabilizer_le_normalizer_fixingSubgroup (z := v) hzGv
    have hzK : z * k⁻¹ * z⁻¹ ∈ fixingSubgroup H (Γ.neighborSet v) := by
      exact ((Subgroup.mem_normalizer_iff.mp hzNormB) k⁻¹).mp (Subgroup.inv_mem _ hk)
    have hcomm : k * z * k⁻¹ * z⁻¹ ∈ fixingSubgroup H (Γ.neighborSet v) := by
      have := Subgroup.mul_mem _ hk hzK
      simpa [mul_assoc] using this
    have hkz : k * z * k⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet v) := by
      have heq : k * z * k⁻¹ = (k * z * k⁻¹ * z⁻¹) * z := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hz)
    have hmem : a * (k * z * k⁻¹) * a⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet v) := by
      have hm : (MulAut.conj a) (k * z * k⁻¹) ∈
          (Z ⊔ fixingSubgroup H (Γ.neighborSet v)).map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hkz
      rw [Subgroup.map_sup, hmapZ, hmapB] at hm
      simpa [MulAut.conj_apply] using hm
    have htconj : t * z * t⁻¹ = a * (k * z * k⁻¹) * a⁻¹ := by
      rw [← hakt]
      group
    rw [htconj]
    exact hmem
  have hZstabv : Z ≤ MulAction.stabilizer H v ⊓ MulAction.stabilizer H x := by
    refine le_inf ?_ ?_
    · intro z hz
      rw [MulAction.mem_stabilizer_iff]
      exact (mem_fixingSubgroup_iff H).mp (hZx hz) v hxv
    · exact hZx.trans ((hL x).kernel_le)
  have htrans := (hT v).transitive x ω' hxv.symm hvω' (fun h => hω'x h.symm)
    Z hZstabv hZ2 hnot hTnorm
  let K : V → Subgroup H := fun u =>
    (fixingSubgroup H (Γ.neighborSet x) ⊓ fixingSubgroup H (Γ.neighborSet v)) ⊓
      fixingSubgroup H (Γ.neighborSet u)
  have hKleU : ∀ u, Γ.Adj v u → K u ≤ edgeUnion H Γ x y := by
    intro u hu
    exact (show K u ≤ edgeKernel (H := H) Γ x v from inf_le_left).trans
      (edgeKernel_le_edgeUnion_left hxv)
  have hKcenter : ∀ z ∈ Z, ∀ u, Γ.Adj v u → ∀ e ∈ K u, z * e = e * z := by
    intro z hz u hu e he
    exact edgeCenter_comm x y hz (hKleU u hu he)
  have hKconj : ∀ z ∈ Z, ∀ u, Γ.Adj v u → K (z • u) = K u := by
    intro z hz u hu
    have hzx : z • x = x := by
      have := hZx hz
      exact MulAction.mem_stabilizer_iff.mp ((hL x).kernel_le this)
    have hzv : z • v = v := (mem_fixingSubgroup_iff H).mp (hZx hz) v hxv
    have hmapid : (K u).map (MulAut.conj z).toMonoidHom = K u := by
      refine le_antisymm ?_ ?_
      · intro e he
        rw [Subgroup.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        have := hKcenter z hz u hu e0 he0
        simpa [MulAut.conj_apply, this] using he0
      · intro e he
        refine Subgroup.mem_map.mpr ⟨e, he, ?_⟩
        have := hKcenter z hz u hu e he
        simp [MulAut.conj_apply, this]
    have htriple : K (z • u) = (K u).map (MulAut.conj z).toMonoidHom := by
      simpa [K, hzx, hzv] using (tripleKernel_map_conj z x v u).symm
    rw [htriple, hmapid]
  have hallK : ∀ u u', Γ.Adj v u → Γ.Adj v u' → u ≠ x → u' ≠ x → K u = K u' := by
    intro u u' hvu hvu' hux hu'x
    obtain ⟨z, hzZ, hzu⟩ := htrans u u' hvu hvu' hux hu'x
    have h := hKconj z hzZ u hvu
    rw [hzu] at h
    exact h.symm
  obtain ⟨x₁, hvx₁, hx₁x⟩ := hne v x hxv.symm
  have hKne : K x₁ ≠ ⊥ := by
    obtain ⟨x₀, hx₁x₀, hx₀v⟩ := hne x₁ v hvx₁.symm
    let p : GPath Γ 4 := path5 x₀ x₁ v x y hx₁x₀.symm hvx₁.symm hxv.symm hxy
    have hpnb : p.NoBack := by
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · simpa [p, path5] using hx₀v
      · simpa [p, path5] using hx₁x
      · simpa [p, path5] using hvy
    have hp1 : p 1 = x₁ := by simp [p, path5]
    have hp2 : p 2 = v := by simp [p, path5]
    have hp3 : p 3 = x := by simp [p, path5]
    have hp4 : p 4 = y := by simp [p, path5]
    obtain ⟨s, hys, hsx, -⟩ := h3 y x x hxy.symm hxy.symm
    obtain ⟨s', hys', hs'x, hs's⟩ := h3 y x s hxy.symm hys
    have hsne : s ≠ x := hsx
    have hs'ne : s' ≠ x := hs'x
    have hs's' : s' ≠ s := hs's
    obtain ⟨r, hr, -⟩ := pathRootGroup_regular_of_weissFree (n := 4) (by norm_num) hM hW hpnb
      (by simpa [hp4] using hys) (by simpa [hp4] using hys')
      (by simpa [hp3] using hsne) (by simpa [hp3] using hs'ne)
    have hUle : pathRootGroup H Γ p ≤ K x₁ := by
      intro g hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h := mem_pathRootGroup.mp hg 3 (by norm_num) (by norm_num)
          exact (mem_fixingSubgroup_iff H).mpr (fun w hw => h w (by rwa [← hp3] at hw))
        · have h := mem_pathRootGroup.mp hg 2 (by norm_num) (by norm_num)
          exact (mem_fixingSubgroup_iff H).mpr (fun w hw => h w (by rwa [← hp2] at hw))
      · have h := mem_pathRootGroup.mp hg 1 (by norm_num) (by norm_num)
        exact (mem_fixingSubgroup_iff H).mpr (fun w hw => h w (by rwa [← hp1] at hw))
    intro hbot
    have hrmem : (r : H) ∈ K x₁ := hUle r.2
    have hrbot : (r : H) ∈ (⊥ : Subgroup H) := by rwa [hbot] at hrmem
    have hrone : (r : H) = 1 := by simpa using hrbot
    have hr1 : r = 1 := Subtype.ext hrone
    have hst : s = s' := by
      have := hr
      rw [hr1] at this
      simpa using this
    exact hs's' hst.symm
  have hKle2 : K x₁ ≤ secondKernel H Γ v := by
    unfold secondKernel
    refine le_inf ?_ ?_
    · exact inf_le_left.trans inf_le_right
    · refine le_iInf fun w => le_iInf fun hw => ?_
      by_cases hwx : w = x
      · subst hwx
        exact inf_le_left.trans inf_le_left
      · rw [hallK x₁ w hvx₁ (by simpa [SimpleGraph.mem_neighborSet] using hw) hx₁x hwx]
        exact inf_le_right
  have hKbot : K x₁ = ⊥ := by
    have := h2 v
    rw [this] at hKle2
    exact le_bot_iff.mp hKle2
  exact hKne hKbot

theorem exists_secondKernel_ne_bot_of_transitive [Finite H]
    (hM : MoufangCondition H Γ 4) (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) (hT : ∀ z, TransitiveFacts H Γ z) {x y : V}
    (hxy : Γ.Adj x y) :
    ∃ z, secondKernel H Γ z ≠ ⊥ := by
  by_contra h
  push Not at h
  have hZx : edgeCenter H Γ x y ≤ fixingSubgroup H (Γ.neighborSet x) :=
    edgeCenter_le_fixing_left hM hW hne h3 hval hloc hL hT h hxy
  have hZ2 : edgeCenter H Γ x y ≤ secondKernel H Γ x := by
    unfold secondKernel
    refine le_inf hZx ?_
    refine le_iInf fun v => le_iInf fun hv => ?_
    have hxv : Γ.Adj x v := by simpa [SimpleGraph.mem_neighborSet] using hv
    by_cases hvy : v = y
    · subst hvy
      exact edgeCenter_le_fixing_right hM hW hne h3 hval hloc hL hT h hxy
    · exact edgeCenter_le_fixing_third hM hW hne h3 hval hL hT h hxy hxv hvy hZx
  have hbot : edgeCenter H Γ x y = ⊥ := by
    have := h x
    rw [this] at hZ2
    exact le_bot_iff.mp hZ2
  exact edgeCenter_ne_bot hM hW hne h3 hval hL hxy hbot


end CFSG.Quasithin.Stroth.WeissDelta

end

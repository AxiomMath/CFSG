module
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.MoufangApartment
public import CFSG.Quasithin.Recognition.F4Paths
public import CFSG.Quasithin.Background.F3PathCons
public section
namespace CFSG.Quasithin.Stroth
open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons
variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]
private def consPathPred (v : V) (p : GPath Γ (n - 1)) (h : Γ.Adj v (p 0)) (hn : 1 ≤ n) :
    GPath Γ n where
  toFun i := if i = 0 then v else p (i - 1)
  adj i hi := by
    by_cases hi0 : i = 0
    · subst i
      simp [h]
    · have hi1 : i - 1 < n - 1 := by
        have hi' : 0 < i := Nat.pos_of_ne_zero hi0
        omega
      have h2 : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp only [hi0, if_false, h2]
      have e : i + 1 - 1 = (i - 1) + 1 := by omega
      rw [e]
      exact p.adj (i - 1) hi1
  tail i hi := by
    by_cases hi0 : i = 0
    · subst i
      have hn0 : n = 0 := by omega
      subst n
      simp
    · have hn0 : n ≠ 0 := by omega
      simp only [hi0, if_false, hn0]
      rw [p.tail (i - 1) (Nat.sub_le_sub_right hi 1)]

@[simp] private theorem consPathPred_zero (v : V) (p : GPath Γ (n - 1)) (h : Γ.Adj v (p 0))
    (hn : 1 ≤ n) : consPathPred v p h hn 0 = v := by simp [consPathPred]

@[simp] private theorem consPathPred_succ (v : V) (p : GPath Γ (n - 1)) (h : Γ.Adj v (p 0))
    (hn : 1 ≤ n) (i : ℕ) : consPathPred v p h hn (i + 1) = p i := by
  simp [consPathPred]

private theorem consPathPred_noBack (v : V) (p : GPath Γ (n - 1)) (h : Γ.Adj v (p 0)) (hn : 1 ≤ n)
    (hp : p.NoBack) (hv0 : v ≠ consPathPred v p h hn 2) :
    (consPathPred v p h hn).NoBack := by
  intro i hi heq
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    exact hv0 (by simpa using heq)
  · have hleft : consPathPred v p h hn i = p (i - 1) := by
      simp [consPathPred, show i ≠ 0 by omega]
    have hright : consPathPred v p h hn (i + 2) = p (i + 1) := by
      simp [consPathPred, show i + 2 ≠ 0 by omega]
    rw [hleft, hright] at heq
    exact hp (i - 1) (by omega)
      (by simpa [show i - 1 + 2 = i + 1 by omega] using heq)

theorem pathRootGroup_rev (p : GPath Γ n) :
    pathRootGroup D Γ p.rev = pathRootGroup D Γ p := by
  ext g
  rw [mem_pathRootGroup, mem_pathRootGroup]
  constructor
  · intro h i hi1 hi2 w hw
    have hrev : p.rev (n - i) = p i := by
      rw [GPath.rev_apply p (by omega)]
      rw [show n - (n - i) = i by omega]
    exact h (n - i) (by omega) (by omega) w (by rwa [hrev])
  · intro h i hi1 hi2 w hw
    have hrev : p.rev i = p (n - i) := GPath.rev_apply p (by omega)
    exact h (n - i) (by omega) (by omega) w (by rwa [← hrev])
theorem conj_mem_pathRootGroup_iff {p : GPath Γ n} (g x : D) :
    g⁻¹ * x * g ∈ pathRootGroup D Γ p ↔ x ∈ pathRootGroup D Γ (g • p) := by
  rw [mem_pathRootGroup, mem_pathRootGroup]
  constructor
  · intro h i hi1 hi2 w hw
    rw [GPath.smul_apply] at hw
    have hAdj : Γ.Adj (p i) (g⁻¹ • w) := by
      have := (GraphAction.adj_smul g (p i) (g⁻¹ • w)).mp (by rwa [smul_inv_smul])
      exact this
    have hfix := h i hi1 hi2 (g⁻¹ • w) hAdj
    have hconv : (g⁻¹ * x * g) • (g⁻¹ • w) = g⁻¹ • (x • (g • (g⁻¹ • w))) := by
      rw [mul_smul, mul_smul]
    rw [hconv, smul_inv_smul] at hfix
    have := congrArg (fun v => g • v) hfix
    simpa using this
  · intro h i hi1 hi2 w hw
    have hAdj : Γ.Adj ((g • p) i) (g • w) := by
      rw [GPath.smul_apply]
      exact (GraphAction.adj_smul g (p i) w).mpr hw
    have hfix := h i hi1 hi2 (g • w) hAdj
    have hconv : (g⁻¹ * x * g) • w = g⁻¹ • (x • (g • w)) := by
      rw [mul_smul, mul_smul]
    rw [hconv, hfix, inv_smul_smul]
theorem pathRootGroup_map_conj (p : GPath Γ n) (g : D) :
    (pathRootGroup D Γ p).map (MulAut.conj g).toMonoidHom =
      pathRootGroup D Γ (g • p) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (MulAut.conj g y) * g = y := by
      rw [MulAut.conj_apply]
      group
    exact (conj_mem_pathRootGroup_iff (p := p) g (MulAut.conj g y)).mp (by rwa [e])
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact (conj_mem_pathRootGroup_iff (p := p) g x).mpr hx
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
omit [Fintype V] [DecidableRel Γ.Adj] [FaithfulSMul D V] [GraphAction D Γ] in
theorem pathRootGroup_le_littleGroup {p : GPath Γ n} (hp : p.NoBack) :
    pathRootGroup D Γ p ≤ littleGroup D Γ n := by
  rw [littleGroup]
  exact (le_iSup (fun _ : p.NoBack => pathRootGroup D Γ p) hp).trans
    (le_iSup (fun q : GPath Γ n => ⨆ (_ : q.NoBack), pathRootGroup D Γ q) p)
theorem littleGroup_normal : (littleGroup D Γ n).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  apply le_antisymm
  · rw [littleGroup, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hp => ?_
    change (pathRootGroup D Γ p).map (MulAut.conj g).toMonoidHom ≤
      littleGroup D Γ n
    rw [pathRootGroup_map_conj]
    exact pathRootGroup_le_littleGroup (GPath.smul_noBack hp)
  · rw [littleGroup]
    refine iSup_le fun p => ?_
    refine iSup_le fun hp => ?_
    have hle : pathRootGroup D Γ (g⁻¹ • p) ≤ littleGroup D Γ n :=
      pathRootGroup_le_littleGroup (GPath.smul_noBack hp)
    have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
    change (pathRootGroup D Γ (g⁻¹ • p)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.map (MulAut.conj g).toMonoidHom (littleGroup D Γ n) at hmap
    rw [pathRootGroup_map_conj] at hmap
    have heq : g • (g⁻¹ • p) = p := by
      calc g • (g⁻¹ • p) = (g * g⁻¹) • p := (GPath.mul_smul' g g⁻¹ p).symm
        _ = (1 : D) • p := by rw [mul_inv_cancel]
        _ = p := GPath.one_smul' p
    rwa [heq] at hmap
private theorem exists_path_end_penult (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {w z1 : V} (h : Γ.Adj w z1) :
    ∃ p : GPath Γ n, p.NoBack ∧ p n = w ∧ p (n - 1) = z1 := by
  obtain ⟨y, hwy, hzy⟩ := hP.exists_dist_eq hT h n (by omega) (by omega)
  have hzy' : Γ.dist z1 y = n - 1 := by omega
  obtain ⟨r, hr0, hrn, hrnb⟩ := GPath.exists_geodesic' hP.connected z1 y hzy'
  have hr1_ne : r 1 ≠ w := by
    intro h1
    have hle := GPath.dist_le_sub hP.connected r (show 1 ≤ n - 1 by omega) le_rfl
    rw [h1, hrn] at hle
    omega
  let p : GPath Γ n :=
    { toFun := fun i => if n ≤ i then w else r (n - 1 - i)
      adj := by
        intro i hi
        by_cases hlast : i = n - 1
        · subst i
          have hif0 : ¬ n ≤ n - 1 := by omega
          have hif1 : n ≤ n - 1 + 1 := by omega
          have h0 : n - 1 - (n - 1) = 0 := by omega
          show Γ.Adj (if n ≤ n - 1 then w else r (n - 1 - (n - 1)))
            (if n ≤ n - 1 + 1 then w else r (n - 1 - (n - 1 + 1)))
          rw [if_neg hif0, if_pos hif1, h0, hr0]
          exact h.symm
        · have hin : i < n := by omega
          have hi1n : ¬ n ≤ i := by omega
          have h2 : ¬ n ≤ i + 1 := by omega
          have hk : n - 1 - i = (n - 1 - (i + 1)) + 1 := by omega
          show Γ.Adj (if n ≤ i then w else r (n - 1 - i))
            (if n ≤ i + 1 then w else r (n - 1 - (i + 1)))
          rw [if_neg hi1n, if_neg h2, hk]
          exact (r.adj (n - 1 - (i + 1)) (by omega)).symm
      tail := by
        intro i hi
        have h1 : n ≤ i := by omega
        show (if n ≤ i then w else r (n - 1 - i)) =
          (if n ≤ n then w else r (n - 1 - n))
        rw [if_pos h1, if_pos le_rfl] }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i hi
    have hin : i < n := by omega
    have hi1n : ¬ n ≤ i := by omega
    by_cases hlast : i + 2 = n
    · have e1 : n - 1 - i = 1 := by omega
      show (if n ≤ i then w else r (n - 1 - i)) ≠
        (if n ≤ i + 2 then w else r (n - 1 - (i + 2)))
      rw [if_neg hi1n, if_pos (by omega : n ≤ i + 2), e1]
      exact hr1_ne
    · have h2 : ¬ n ≤ i + 2 := by omega
      have hk : n - 1 - i = (n - 1 - (i + 2)) + 2 := by omega
      show (if n ≤ i then w else r (n - 1 - i)) ≠
        (if n ≤ i + 2 then w else r (n - 1 - (i + 2)))
      rw [if_neg hi1n, if_neg h2, hk]
      exact (hrnb (n - 1 - (i + 2)) (by omega)).symm
  · show (if n ≤ n then w else r (n - 1 - n)) = w
    rw [if_pos le_rfl]
  · have hlt : ¬ n ≤ n - 1 := by omega
    show (if n ≤ n - 1 then w else r (n - 1 - (n - 1))) = z1
    rw [if_neg hlt, show n - 1 - (n - 1) = 0 by omega, hr0]
private theorem littleGroup_inf_stabilizer_transitive (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {w y1 y2 : V} (hy1 : Γ.Adj w y1) (hy2 : Γ.Adj w y2) (hne : y1 ≠ y2) :
    ∃ g : D, g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D w ∧ g • y1 = y2 := by
  classical
  have hdeg : 3 ≤ (Γ.neighborFinset w).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hT w
  have hcard : ({y1, y2} : Finset V).card < (Γ.neighborFinset w).card := by
    have h2 : ({y1, y2} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨z1, hz1mem, hz1not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hz1adj : Γ.Adj w z1 := by
    rwa [SimpleGraph.mem_neighborFinset] at hz1mem
  have hz1y1 : z1 ≠ y1 := by
    intro h
    exact hz1not (by simp [h])
  have hz1y2 : z1 ≠ y2 := by
    intro h
    exact hz1not (by simp [h])
  obtain ⟨p, hpnb, hpn, hpnm⟩ := exists_path_end_penult hn hP hT hz1adj
  have hR0 : RootGroupRegular n := rootGroupRegular n
  unfold RootGroupRegular at hR0
  have hy1' : Γ.Adj (p n) y1 := by rwa [hpn]
  have hy2' : Γ.Adj (p n) y2 := by rwa [hpn]
  have h1 : y1 ≠ p (n - 1) := by rw [hpnm]; exact hz1y1.symm
  have h2 : y2 ≠ p (n - 1) := by rw [hpnm]; exact hz1y2.symm
  have hR : ∃! g : ↥(pathRootGroup D Γ p), (g : D) • y1 = y2 :=
    hR0 V Γ D hn hP hT hM p hpnb y1 y2 hy1' hy2' h1 h2
  obtain ⟨g, hgy, -⟩ := hR
  refine ⟨(g : D), ⟨pathRootGroup_le_littleGroup hpnb g.2, ?_⟩, hgy⟩
  refine MulAction.mem_stabilizer_iff.mpr ?_
  have hadj : Γ.Adj (p (n - 1)) (p n) := by
    simpa [show n - 1 + 1 = n by omega] using p.adj (n - 1) (by omega)
  have hadj' : Γ.Adj (p (n - 1)) w := by rwa [hpn] at hadj
  exact (mem_pathRootGroup.mp g.2) (n - 1) (by omega) le_rfl w hadj'
private theorem exists_mem_littleGroup_inf_stabilizer_smul_ne (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {w y : V} (hy : Γ.Adj w y) :
    ∃ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D w, g • y ≠ y := by
  classical
  have hdeg : 3 ≤ (Γ.neighborFinset w).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hT w
  have hcard : ({y} : Finset V).card < (Γ.neighborFinset w).card := by
    have h1 : ({y} : Finset V).card = 1 := Finset.card_singleton y
    omega
  obtain ⟨y2, hy2mem, hy2not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hy2adj : Γ.Adj w y2 := by
    rwa [SimpleGraph.mem_neighborFinset] at hy2mem
  have hne : y ≠ y2 := by
    intro h
    exact hy2not (by simp [h])
  obtain ⟨g, hg, hgy⟩ := littleGroup_inf_stabilizer_transitive hn hP hT hM hy hy2adj hne
  refine ⟨g, hg, ?_⟩
  rw [hgy]
  exact fun h => hne h.symm
private theorem littleGroup_inf_stabilizer_fixes_eq (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {w w' : V} (hfix : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D w,
      g • w' = w') : w' = w := by
  classical
  by_contra hne
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hle : Γ.dist w w' ≤ n := hP.dist_le (by omega) w w'
  have hpos : 0 < Γ.dist w w' := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hne ((SimpleGraph.Connected.dist_eq_zero_iff hP.connected).mp h0).symm
  by_cases hlt : Γ.dist w w' < n
  · obtain ⟨p0, hp00, hp0d, hp0nb⟩ := GPath.exists_geodesic' hP.connected w w' rfl
    have hgeo : p0.IsGeodesic := by
      show Γ.dist (p0 0) (p0 (Γ.dist w w')) = Γ.dist w w'
      rw [hp00, hp0d]
    have hy : Γ.Adj w (p0 1) := by
      have := p0.adj 0 hpos
      rwa [hp00] at this
    obtain ⟨g, hg, hgmove⟩ :=
      exists_mem_littleGroup_inf_stabilizer_smul_ne hn hP hT hM hy
    have hgw : g • w = w := MulAction.mem_stabilizer_iff.mp hg.2
    have hgw' : g • w' = w' := hfix g hg
    have hgeosm : (g • p0).IsGeodesic := by
      show Γ.dist ((g • p0) 0) ((g • p0) (Γ.dist w w')) = Γ.dist w w'
      rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul hP.connected, hp00, hp0d]
    have heq : g • p0 = p0 :=
      hgp.uniqueGeod (Γ.dist w w') (g • p0) p0 hgeosm hgeo
        (by rw [GPath.smul_apply, hp00, hgw])
        (by rw [GPath.smul_apply, hp0d, hgw']) hlt
    have hfixy : g • (p0 1) = p0 1 := by
      have := congrArg (fun q : GPath Γ (Γ.dist w w') => q 1) heq
      rwa [GPath.smul_apply] at this
    exact hgmove hfixy
  · have hd : Γ.dist w w' = n := by omega
    obtain ⟨p0, hp00, hp0d, hp0nb⟩ := GPath.exists_geodesic' hP.connected w w' hd
    have hgeo : p0.IsGeodesic := by
      show Γ.dist (p0 0) (p0 n) = n
      rw [hp00, hp0d]
      exact hd
    have hy1 : Γ.Adj w (p0 1) := by
      have := p0.adj 0 (by omega)
      rwa [hp00] at this
    have hdeg : 3 ≤ (Γ.neighborFinset w).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hT w
    have hcard1 : ({p0 1} : Finset V).card < (Γ.neighborFinset w).card := by
      have h1 : ({p0 1} : Finset V).card = 1 := Finset.card_singleton (p0 1)
      omega
    obtain ⟨z1, hz1mem, hz1not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard1
    have hz1adj : Γ.Adj w z1 := by
      rwa [SimpleGraph.mem_neighborFinset] at hz1mem
    have hz1ne : z1 ≠ p0 1 := by
      intro h
      exact hz1not (by simp [h])
    let q : GPath Γ (n - 1) := p0.take (n - 1) (by omega)
    have hq0 : q 0 = w := by
      rw [show q 0 = p0 (min 0 (n - 1)) from rfl, min_eq_left (by omega), hp00]
    have hq1 : q 1 = p0 1 := by
      rw [show q 1 = p0 (min 1 (n - 1)) from rfl, min_eq_left (by omega)]
    have hqnb : q.NoBack := GPath.NoBack.take hp0nb (n - 1) (by omega)
    have hzq : Γ.Adj z1 (q 0) := by rw [hq0]; exact hz1adj.symm
    let γ : GPath Γ n := consPathPred z1 q hzq (by omega)
    have hγ1 : γ 1 = w := by
      rw [show γ 1 = q 0 by simp [γ, consPathPred]]
      exact hq0
    have hγ2 : γ 2 = p0 1 := by
      rw [show γ 2 = q 1 by simp [γ, consPathPred]]
      exact hq1
    have hγnb : γ.NoBack := by
      refine consPathPred_noBack z1 q hzq (by omega) hqnb ?_
      intro hv
      have h2 : consPathPred z1 q hzq (by omega) 2 = q 1 := by
        rw [show 2 = 1 + 1 by omega, consPathPred_succ]
      rw [h2, hq1] at hv
      exact hz1ne hv
    have hγn : γ n = p0 (n - 1) := by
      rw [show γ n = q (n - 1) by
        simp [γ, consPathPred, show n ≠ 0 by omega]]
      rw [show q (n - 1) = p0 (min (n - 1) (n - 1)) from rfl, min_self]
    have hγnm : γ (n - 1) = p0 (n - 2) := by
      rw [show γ (n - 1) = q (n - 1 - 1) by
        simp [γ, consPathPred, show n - 1 ≠ 0 by omega]]
      rw [show n - 1 - 1 = n - 2 by omega]
      rw [show q (n - 2) = p0 (min (n - 2) (n - 1)) from rfl,
        min_eq_left (by omega)]
    have hUL : pathRootGroup D Γ γ ≤ littleGroup D Γ n :=
      pathRootGroup_le_littleGroup hγnb
    have hUstab : pathRootGroup D Γ γ ≤ MulAction.stabilizer D w := by
      intro u hu
      rw [MulAction.mem_stabilizer_iff]
      have hadj : Γ.Adj (γ 2) (γ 1) := (γ.adj 1 (by omega)).symm
      have hadj' : Γ.Adj (γ 2) w := by rwa [hγ1] at hadj
      exact (mem_pathRootGroup.mp hu) 2 (by omega) (by omega) w hadj'
    have hw'adj : Γ.Adj (p0 (n - 1)) w' := by
      have := p0.adj (n - 1) (by omega)
      rwa [show n - 1 + 1 = n by omega, hp0d] at this
    have hγw' : Γ.Adj (γ n) w' := by rwa [hγn]
    have hpne : p0 (n - 2) ≠ w' := by
      intro h
      have h1 := GPath.dist_prefix hP.connected p0 hgeo (show n - 2 ≤ n by omega)
      rw [h, hp00] at h1
      have h2 : n - 2 = n := h1.symm.trans hd
      have h3 : n - 2 ≠ n := by omega
      exact h3 h2
    have hw'm : w' ≠ γ (n - 1) := by
      rw [hγnm]
      exact hpne.symm
    have hdegp : 3 ≤ (Γ.neighborFinset (p0 (n - 1))).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hT (p0 (n - 1))
    have hcard2 : ({p0 (n - 2), w'} : Finset V).card <
        (Γ.neighborFinset (p0 (n - 1))).card := by
      have h2 : ({p0 (n - 2), w'} : Finset V).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨y2, hy2mem, hy2not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
    have hy2adj : Γ.Adj (p0 (n - 1)) y2 := by
      rwa [SimpleGraph.mem_neighborFinset] at hy2mem
    have hy2ne1 : y2 ≠ p0 (n - 2) := by
      intro h
      exact hy2not (by simp [h])
    have hy2ne2 : y2 ≠ w' := by
      intro h
      exact hy2not (by simp [h])
    have hγy2 : Γ.Adj (γ n) y2 := by rwa [hγn]
    have hy2m : y2 ≠ γ (n - 1) := by
      rw [hγnm]
      exact hy2ne1
    have hR0 : RootGroupRegular n := rootGroupRegular n
    unfold RootGroupRegular at hR0
    have hR : ∃! g : ↥(pathRootGroup D Γ γ), (g : D) • w' = y2 :=
      hR0 V Γ D hn hP hT hM γ hγnb w' y2 hγw' hγy2 hw'm hy2m
    obtain ⟨g, hgy, -⟩ := hR
    have hmemg : (g : D) ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D w :=
      ⟨hUL g.2, hUstab g.2⟩
    have hfixg := hfix (g : D) hmemg
    exact hy2ne2 (hgy.symm.trans hfixg)
private theorem littleGroup_inf_stabilizer_inj (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {z z' : V} (h : littleGroup D Γ n ⊓ MulAction.stabilizer D z =
      littleGroup D Γ n ⊓ MulAction.stabilizer D z') : z = z' := by
  by_contra hne
  have hfix : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z', g • z = z := by
    intro g hg
    have hg' : g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z := by rwa [← h] at hg
    exact MulAction.mem_stabilizer_iff.mp hg'.2
  exact hne (littleGroup_inf_stabilizer_fixes_eq hn hP hT hM hfix)
private theorem conjSub_stabilizer (g : D) (z : V) :
    conjSub g (MulAction.stabilizer D z) = MulAction.stabilizer D (g • z) := by
  rw [conjSub, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
private theorem conjSub_littleGroup_inf_stabilizer (g : D) (z : V) :
    conjSub g (littleGroup D Γ n ⊓ MulAction.stabilizer D z) =
      littleGroup D Γ n ⊓ MulAction.stabilizer D (g • z) := by
  rw [conjSub_inf]
  have hL : conjSub g (littleGroup D Γ n) = littleGroup D Γ n := by
    haveI : (littleGroup D Γ n).Normal := littleGroup_normal
    exact Subgroup.Normal.map_conj_eq (H := littleGroup D Γ n) g
  rw [hL, conjSub_stabilizer]
theorem centralizer_littleGroup_eq_bot (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    Subgroup.centralizer (littleGroup D Γ n : Set D) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro d hd
  rw [Subgroup.mem_bot]
  have hcomm : ∀ y ∈ littleGroup D Γ n, d⁻¹ * y * d = y := by
    intro y hy
    have h := (Subgroup.mem_centralizer_iff.mp hd) y hy
    calc d⁻¹ * y * d = d⁻¹ * (y * d) := by group
      _ = d⁻¹ * (d * y) := by rw [h]
      _ = y := by group
  have hfixall : ∀ z : V, d • z = z := by
    intro z
    have hH : conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z) =
        littleGroup D Γ n ⊓ MulAction.stabilizer D z := by
      refine le_antisymm ?_ ?_
      · intro x hx
        rw [mem_conjSub] at hx
        have hy : d⁻¹ * x * d ∈ littleGroup D Γ n := hx.1
        have hcommute := (Subgroup.mem_centralizer_iff.mp hd) (d⁻¹ * x * d) hy
        have hdy : d * (d⁻¹ * x * d) * d⁻¹ = d⁻¹ * x * d := by
          calc d * (d⁻¹ * x * d) * d⁻¹ = (d⁻¹ * x * d) * d * d⁻¹ := by
                rw [← hcommute]
            _ = d⁻¹ * x * d := by group
        have hx' : x = d⁻¹ * x * d := by
          calc x = d * (d⁻¹ * x * d) * d⁻¹ := by group
            _ = d⁻¹ * x * d := hdy
        rwa [← hx'] at hx
      · intro x hx
        rw [mem_conjSub]
        have hx' : d⁻¹ * x * d = x := hcomm x hx.1
        rw [hx']
        exact hx
    have hEq : littleGroup D Γ n ⊓ MulAction.stabilizer D (d • z) =
        littleGroup D Γ n ⊓ MulAction.stabilizer D z := by
      rw [← conjSub_littleGroup_inf_stabilizer d z, hH]
    exact littleGroup_inf_stabilizer_inj hn hP hT hM hEq
  exact eq_of_smul_eq_smul (m₁ := d) (m₂ := 1) (fun z : V => by
    rw [one_smul]
    exact hfixall z)
theorem normalizer_littleGroup_inf_stabilizer (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (z : V) :
    Subgroup.normalizer
        ((littleGroup D Γ n ⊓ MulAction.stabilizer D z : Subgroup D) : Set D) =
      MulAction.stabilizer D z := by
  apply le_antisymm
  · intro d hd
    have hd' : conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z) =
        littleGroup D Γ n ⊓ MulAction.stabilizer D z := by
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at hd
    have hEq : littleGroup D Γ n ⊓ MulAction.stabilizer D (d • z) =
        littleGroup D Γ n ⊓ MulAction.stabilizer D z := by
      rw [← conjSub_littleGroup_inf_stabilizer d z, hd']
    exact MulAction.mem_stabilizer_iff.mpr (littleGroup_inf_stabilizer_inj hn hP hT hM hEq)
  · intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z) =
      littleGroup D Γ n ⊓ MulAction.stabilizer D z
    rw [conjSub_littleGroup_inf_stabilizer d z, MulAction.mem_stabilizer_iff.mp hd]
private theorem edgeStabilizer_transitive (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {a b y1 y2 : V} (hab : Γ.Adj a b) (hy1 : Γ.Adj a y1) (hy2 : Γ.Adj a y2)
    (h1 : y1 ≠ b) (h2 : y2 ≠ b) :
    ∃ g : D, g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
      MulAction.stabilizer D b ∧ g • y1 = y2 := by
  classical
  obtain ⟨p, hpnb, hpn, hpnm⟩ := exists_path_end_penult hn hP hT hab
  have hy1' : Γ.Adj (p n) y1 := by rwa [hpn]
  have hy2' : Γ.Adj (p n) y2 := by rwa [hpn]
  have h1' : y1 ≠ p (n - 1) := by rwa [hpnm]
  have h2' : y2 ≠ p (n - 1) := by rwa [hpnm]
  have hR0 : RootGroupRegular n := rootGroupRegular n
  unfold RootGroupRegular at hR0
  obtain ⟨g, hgy, -⟩ := hR0 V Γ D hn hP hT hM p hpnb y1 y2 hy1' hy2' h1' h2'
  have hL : pathRootGroup D Γ p ≤ littleGroup D Γ n := pathRootGroup_le_littleGroup hpnb
  have ha : pathRootGroup D Γ p ≤ MulAction.stabilizer D a := by
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    have hadj : Γ.Adj (p (n - 1)) (p n) := by
      simpa [show n - 1 + 1 = n by omega] using p.adj (n - 1) (by omega)
    have hadj' : Γ.Adj (p (n - 1)) a := by rwa [hpn] at hadj
    exact (mem_pathRootGroup.mp hu) (n - 1) (by omega) le_rfl a hadj'
  have hb : pathRootGroup D Γ p ≤ MulAction.stabilizer D b := by
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    have hadj : Γ.Adj (p (n - 2)) (p (n - 1)) := by
      simpa [show n - 2 + 1 = n - 1 by omega] using p.adj (n - 2) (by omega)
    have hadj' : Γ.Adj (p (n - 2)) b := by rwa [hpnm] at hadj
    exact (mem_pathRootGroup.mp hu) (n - 2) (by omega) (by omega) b hadj'
  exact ⟨(g : D), ⟨⟨hL g.2, ha g.2⟩, hb g.2⟩, hgy⟩
private theorem edgeStabilizer_not_fix_neighbor (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {a b y : V} (hab : Γ.Adj a b) (hy : Γ.Adj a y) (hne : y ≠ b) :
    ∃ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓ MulAction.stabilizer D b,
      g • y ≠ y := by
  classical
  have hdeg : 3 ≤ (Γ.neighborFinset a).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hT a
  have hcard : ({b, y} : Finset V).card < (Γ.neighborFinset a).card := by
    have h2 : ({b, y} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨y2, hy2mem, hy2not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hy2 : Γ.Adj a y2 := by
    rwa [SimpleGraph.mem_neighborFinset] at hy2mem
  have hy2ne : y2 ≠ y := by
    intro h
    exact hy2not (by simp [h])
  have hy2b : y2 ≠ b := by
    intro h
    exact hy2not (by simp [h])
  obtain ⟨g, hg, hgy⟩ := edgeStabilizer_transitive hn hP hT hM hab hy hy2 hne hy2b
  exact ⟨g, hg, by rw [hgy]; exact hy2ne⟩
private theorem eq_endpoint_of_fixed_of_dist_lt (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {a b w : V} (hab : Γ.Adj a b)
    (hfix : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓ MulAction.stabilizer D b,
      g • w = w)
    (hlt : Γ.dist a w < n) (hwa : w ≠ a) : w = b := by
  classical
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hdpos : 0 < Γ.dist a w := hP.connected.pos_dist_of_ne (fun h => hwa h.symm)
  obtain ⟨p0, hp00, hp0d, hp0nb⟩ := GPath.exists_geodesic' hP.connected a w rfl
  have hgeo : p0.IsGeodesic := by
    show Γ.dist (p0 0) (p0 (Γ.dist a w)) = Γ.dist a w
    rw [hp00, hp0d]
  have hfix_geod : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
      MulAction.stabilizer D b, g • p0 = p0 := by
    intro g hg
    have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg.1.2
    have hgw : g • w = w := hfix g hg
    have hgeosm : (g • p0).IsGeodesic := by
      show Γ.dist ((g • p0) 0) ((g • p0) (Γ.dist a w)) = Γ.dist a w
      rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul hP.connected, hp00, hp0d]
    exact hgp.uniqueGeod (Γ.dist a w) (g • p0) p0 hgeosm hgeo
      (by rw [GPath.smul_apply, hp00, hga])
      (by rw [GPath.smul_apply, hp0d, hgw]) hlt
  have hy1 : Γ.Adj a (p0 1) := by
    have := p0.adj 0 hdpos
    rwa [hp00] at this
  have hfix1 : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
      MulAction.stabilizer D b, g • (p0 1) = p0 1 := by
    intro g hg
    have := congrArg (fun q : GPath Γ (Γ.dist a w) => q 1) (hfix_geod g hg)
    rwa [GPath.smul_apply] at this
  have hp1 : p0 1 = b := by
    by_contra hne
    obtain ⟨g, hg, hgm⟩ := edgeStabilizer_not_fix_neighbor hn hP hT hM hab hy1 hne
    exact hgm (hfix1 g hg)
  have hd1 : Γ.dist a w = 1 := by
    by_contra hne
    have hd2 : 2 ≤ Γ.dist a w := by omega
    have hfix2 : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
        MulAction.stabilizer D b, g • (p0 2) = p0 2 := by
      intro g hg
      have := congrArg (fun q : GPath Γ (Γ.dist a w) => q 2) (hfix_geod g hg)
      rwa [GPath.smul_apply] at this
    have hp2ne : p0 2 ≠ a := by
      have hdist2 := GPath.dist_prefix hP.connected p0 hgeo (show 2 ≤ Γ.dist a w by omega)
      rw [hp00] at hdist2
      intro h
      rw [h] at hdist2
      simp at hdist2
    have hy2 : Γ.Adj b (p0 2) := by
      have := p0.adj 1 (by omega)
      rwa [hp1] at this
    obtain ⟨g, hg, hgm⟩ := edgeStabilizer_not_fix_neighbor hn hP hT hM hab.symm hy2 hp2ne
    have hg' : g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
        MulAction.stabilizer D b := by
      have hEq : littleGroup D Γ n ⊓ MulAction.stabilizer D b ⊓
          MulAction.stabilizer D a =
        littleGroup D Γ n ⊓ MulAction.stabilizer D a ⊓
          MulAction.stabilizer D b := by ac_rfl
      rwa [hEq] at hg
    exact hgm (hfix2 g hg')
  have hw : w = p0 (Γ.dist a w) := hp0d.symm
  rw [hw]
  simpa [hd1] using hp1
private theorem edgeStabilizer_fixes_mem (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {z z' w : V} (hadj : Γ.Adj z z')
    (hfix : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
      MulAction.stabilizer D z', g • w = w) : w = z ∨ w = z' := by
  classical
  by_contra hnot
  have hwz : w ≠ z := fun h => hnot (Or.inl h)
  have hwz' : w ≠ z' := fun h => hnot (Or.inr h)
  have hle : Γ.dist z w ≤ n := hP.dist_le (by omega) z w
  by_cases hlt : Γ.dist z w < n
  · exact hnot (Or.inr (eq_endpoint_of_fixed_of_dist_lt hn hP hT hM hadj hfix hlt hwz))
  · have hd : Γ.dist z w = n := by omega
    have hfix' : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z' ⊓
        MulAction.stabilizer D z, g • w = w := by
      intro g hg
      exact hfix g (by
        have hEq : littleGroup D Γ n ⊓ MulAction.stabilizer D z' ⊓
            MulAction.stabilizer D z =
          littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
            MulAction.stabilizer D z' := by ac_rfl
        rwa [hEq] at hg)
    have hdist : Γ.dist z' w = n - 1 := by
      rcases hP.dist_adj hadj w with h | h
      · have h1 : Γ.dist w z' ≤ n := hP.dist_le (by omega) w z'
        rw [h] at h1
        have h2 : Γ.dist w z = Γ.dist z w := SimpleGraph.dist_comm
        rw [h2, hd] at h1
        omega
      · have h2 : Γ.dist w z = Γ.dist z w := SimpleGraph.dist_comm
        rw [h2, hd] at h
        have h3 : Γ.dist w z' = n - 1 := by omega
        rwa [SimpleGraph.dist_comm]
    exact hnot (Or.inl (eq_endpoint_of_fixed_of_dist_lt hn hP hT hM hadj.symm hfix'
      (by omega) hwz'))
theorem normalizer_edge_fixes_or_swaps (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {z z' : V} (hadj : Γ.Adj z z') {d : D}
    (hd : d ∈ Subgroup.normalizer
      ((littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z' : Subgroup D) : Set D)) :
    (d • z = z ∧ d • z' = z') ∨ (d • z = z' ∧ d • z' = z) := by
  classical
  have hd' : conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
      MulAction.stabilizer D z') =
      littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z' := by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at hd
  have hfixz : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
      MulAction.stabilizer D z', g • (d • z) = d • z := by
    intro g hg
    have hgH : g ∈ conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z') := by rwa [hd']
    have hconj : d⁻¹ * g * d ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z' := mem_conjSub.mp hgH
    have hgz : (d⁻¹ * g * d) • z = z := MulAction.mem_stabilizer_iff.mp hconj.1.2
    calc g • (d • z) = (g * d) • z := by rw [mul_smul]
      _ = (d * (d⁻¹ * g * d)) • z := by rw [show g * d = d * (d⁻¹ * g * d) by group]
      _ = d • ((d⁻¹ * g * d) • z) := by rw [mul_smul]
      _ = d • z := by rw [hgz]
  have hfixz' : ∀ g ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
      MulAction.stabilizer D z', g • (d • z') = d • z' := by
    intro g hg
    have hgH : g ∈ conjSub d (littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z') := by rwa [hd']
    have hconj : d⁻¹ * g * d ∈ littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓
        MulAction.stabilizer D z' := mem_conjSub.mp hgH
    have hgz : (d⁻¹ * g * d) • z' = z' := MulAction.mem_stabilizer_iff.mp hconj.2
    calc g • (d • z') = (g * d) • z' := by rw [mul_smul]
      _ = (d * (d⁻¹ * g * d)) • z' := by rw [show g * d = d * (d⁻¹ * g * d) by group]
      _ = d • ((d⁻¹ * g * d) • z') := by rw [mul_smul]
      _ = d • z' := by rw [hgz]
  have hz : d • z = z ∨ d • z = z' := edgeStabilizer_fixes_mem hn hP hT hM hadj hfixz
  have hz' : d • z' = z ∨ d • z' = z' := edgeStabilizer_fixes_mem hn hP hT hM hadj hfixz'
  have hinj : Function.Injective (fun v : V => d • v) := by
    intro a b h
    simpa using congrArg (fun v => d⁻¹ • v) h
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact absurd (hinj (hz.trans hz'.symm)) hadj.ne
  · exact Or.inl ⟨hz, hz'⟩
  · exact Or.inr ⟨hz, hz'⟩
  · exact absurd (hinj (hz.trans hz'.symm)) hadj.ne
theorem moufangLittleNormal (n : ℕ) : MoufangLittleNormal n := by
  intro V _ Γ _ D _ _ _ _ hn hP hT hM
  refine ⟨littleGroup_normal, centralizer_littleGroup_eq_bot hn hP hT hM, ?_, ?_⟩
  · intro z
    exact normalizer_littleGroup_inf_stabilizer hn hP hT hM z
  · intro z z' hadj d hd
    exact normalizer_edge_fixes_or_swaps hn hP hT hM hadj hd
end CFSG.Quasithin.Stroth

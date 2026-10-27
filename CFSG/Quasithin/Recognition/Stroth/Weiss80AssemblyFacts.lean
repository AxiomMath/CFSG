module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardU
public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleNormal

public section

namespace CFSG.Quasithin.Stroth

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.Geometry.GeneralizedPolygons CFSG.GH74.BNPair
  CFSG.GH74.GLS.SP

section Apartment

variable {V : Type}

theorem polyHyp_of_thick_of_isGeneralizedPolygon {Γ : SimpleGraph V} [Fintype V]
    [DecidableRel Γ.Adj] {n : ℕ}
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) : PolyHyp Γ n :=
  (isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT).polyHyp hn
    (three_le_encard_of_isThick hT)

private theorem exists_gPath_through_edge {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
    {n : ℕ} (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {v y u : V} (hvy : Γ.dist v y = n) (hvu : Γ.Adj v u) :
    ∃ p : GPath Γ n, p.NoBack ∧ p 0 = v ∧ p 1 = u ∧ p n = y := by
  obtain ⟨l, hl, hhead, hlast, hlen, hl1⟩ :=
    (polyHyp_of_thick_of_isGeneralizedPolygon hn hP hT).exists_path_through hvy hvu
  have hne : l ≠ [] := by rintro rfl; simp at hhead
  obtain ⟨p0, hpnb, hpmap⟩ := exists_gPath_of_isGLSPath (Γ := Γ) hl hne
  have hlen' : l.length - 1 = n := by omega
  let p : GPath Γ n :=
    { toFun := p0.toFun
      adj := fun i hi => p0.adj i (by omega)
      tail := fun i hi => by
        have h := p0.tail i (by omega)
        show p0.toFun i = p0.toFun n
        rw [← hlen']
        exact h }
  have hp0 : p 0 = v := by
    have h := congrArg (fun l : List V => l[0]?) hpmap
    rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
    rw [← List.head?_eq_getElem?, hhead] at h
    exact Option.some.inj h
  have hp1 : p 1 = u := by
    have h := congrArg (fun l : List V => l[1]?) hpmap
    rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
    rw [hl1] at h
    exact Option.some.inj h
  have hpn : p n = y := by
    have hlast' : l[n]? = some y := by
      rw [← hlast, getLast?_eq_getElem?_of_length (l := l) (m := n) (by omega)]
    have h := congrArg (fun l : List V => l[n]?) hpmap
    rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
    rw [hlast'] at h
    exact Option.some.inj h
  have hpnb' : p.NoBack := by
    intro i hi
    exact hpnb i (by omega)
  exact ⟨p, hpnb', hp0, hp1, hpn⟩

theorem exists_polygonApartment_through_edge {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
    {n : ℕ} (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {v u : V} (hvu : Γ.Adj v u) :
    ∃ t : ZMod (2 * n) → V, IsPolygonApartment Γ n t ∧ t n = v ∧ t (n + 1) = u := by
  classical
  obtain ⟨y, hvy, huy⟩ := hP.exists_dist_eq hT hvu n (by omega) le_rfl
  obtain ⟨v', hvv', hv'u⟩ : ∃ v' : V, Γ.Adj v v' ∧ v' ≠ u := by
    have h3 : 3 ≤ (Γ.neighborFinset v).card := hT v
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < (Γ.neighborFinset v).card by omega)
    rw [SimpleGraph.mem_neighborFinset] at ha hb
    by_cases hau : a = u
    · exact ⟨b, hb, by rintro rfl; exact hab hau⟩
    · exact ⟨a, ha, hau⟩
  obtain ⟨r, hrnb, hr0, hr1, hrn⟩ := exists_gPath_through_edge hn hP hT hvy hvu
  obtain ⟨s, hsnb, hs0, hs1, hsn⟩ := exists_gPath_through_edge hn hP hT hvy hvv'
  let q : GPath Γ n := r.rev
  let p : GPath Γ n := s.rev
  have hpnb : p.NoBack := by
    change s.rev.NoBack
    exact GPath.NoBack.rev hsnb
  have hqnb : q.NoBack := by
    change r.rev.NoBack
    exact GPath.NoBack.rev hrnb
  have hq0 : q 0 = y := by
    change r.rev 0 = y
    rw [GPath.rev_apply _ (by omega), show n - 0 = n by omega, hrn]
  have hq_n : q n = v := by
    change r.rev n = v
    rw [GPath.rev_apply _ le_rfl, show n - n = 0 by omega, hr0]
  have hp0 : p 0 = y := by
    change s.rev 0 = y
    rw [GPath.rev_apply _ (by omega), show n - 0 = n by omega, hsn]
  have hp_n : p n = v := by
    change s.rev n = v
    rw [GPath.rev_apply _ le_rfl, show n - n = 0 by omega, hs0]
  have hq_pen : q (n - 1) = u := by
    change r.rev (n - 1) = u
    rw [GPath.rev_apply _ (by omega), show n - (n - 1) = 1 by omega, hr1]
  have hp_pen : p (n - 1) = v' := by
    change s.rev (n - 1) = v'
    rw [GPath.rev_apply _ (by omega), show n - (n - 1) = 1 by omega, hs1]
  have hpq : p ≠ q := by
    intro h
    have := congrArg (fun t : GPath Γ n => t (n - 1)) h
    rw [hp_pen, hq_pen] at this
    exact hv'u this
  have hconn : Γ.Connected := hP.connected
  obtain ⟨c⟩ := hP.isBipartite
  let col : Γ.Coloring Bool := Γ.recolorOfEquiv finTwoEquiv c
  have hcol : ∀ a b, Γ.Adj a b → col a ≠ col b := fun _ _ h => col.valid h
  have hU : UniqueGeod Γ n :=
    (isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT).uniqueGeod
  have hpgeo : p.IsGeodesic := by
    have : Γ.dist (p 0) (p n) = n := by rw [hp0, hp_n, SimpleGraph.dist_comm]; exact hvy
    exact this
  have hqgeo : q.IsGeodesic := by
    have : Γ.dist (q 0) (q n) = n := by rw [hq0, hq_n, SimpleGraph.dist_comm]; exact hvy
    exact this
  obtain ⟨hfirst, hlastne⟩ :=
    GPath.geod_first_last_ne hconn hU (by omega) hpgeo hqgeo (by rw [hp0, hq0])
      (by rw [hp_n, hq_n]) hpq
  have hnb : ∀ i, GPath.cycSeq p q i ≠ GPath.cycSeq p q (i + 2) :=
    GPath.cycSeq_nb p q (by omega) hpnb hqnb (by rw [hp0, hq0]) (by rw [hp_n, hq_n])
      hfirst hlastne
  have hper : ∀ i, GPath.cycSeq p q (i + 2 * n) = GPath.cycSeq p q i :=
    GPath.cycSeq_per p q
  have hadj : ∀ i, Γ.Adj (GPath.cycSeq p q i) (GPath.cycSeq p q (i + 1)) :=
    GPath.cycSeq_adj p q (by omega) (by rw [hp0, hq0]) (by rw [hp_n, hq_n])
  let z : ℕ → V := GPath.cycSeq p q
  have hz_eq : ∀ i j, z i = z j ↔ i % (2 * n) = j % (2 * n) :=
    GPath.periodic_eq_iff hconn hcol (by omega) hU z hadj hnb hper
  haveI : NeZero (2 * n) := ⟨by omega⟩
  haveI : Fact (1 < 2 * n) := ⟨by omega⟩
  let t : ZMod (2 * n) → V := fun k => z k.val
  have ht_inj : Function.Injective t := by
    intro a b hab
    have hmod := (hz_eq a.val b.val).mp hab
    rw [Nat.mod_eq_of_lt a.val_lt, Nat.mod_eq_of_lt b.val_lt] at hmod
    exact ZMod.val_injective (2 * n) hmod
  have ht_adj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1)) := by
    intro k
    have hval : (k + 1).val = (k.val + 1) % (2 * n) := by
      rw [ZMod.val_add, ZMod.val_one]
    have hmod : z ((k.val + 1) % (2 * n)) = z (k.val + 1) :=
      (hz_eq _ _).mpr (by rw [Nat.mod_mod])
    have h := hadj k.val
    change Γ.Adj (z k.val) (z (k + 1).val)
    rw [hval]
    exact hmod ▸ h
  refine ⟨t, ⟨ht_inj, ht_adj⟩, ?_, ?_⟩
  · change z ((n : ZMod (2 * n)).val) = v
    rw [ZMod.val_natCast_of_lt (by omega)]
    change GPath.cycSeq p q n = v
    rw [GPath.cycSeq_of_le p q (by omega) le_rfl]
    exact hp_n
  · have hval : ((n : ZMod (2 * n)) + 1).val = n + 1 := by
      rw [ZMod.val_add, ZMod.val_natCast_of_lt (by omega), ZMod.val_one,
        Nat.mod_eq_of_lt (by omega)]
    change z ((n : ZMod (2 * n)) + 1).val = u
    rw [hval]
    change GPath.cycSeq p q (n + 1) = u
    have hcyc : GPath.cycSeq p q (n + 1) = q (2 * n - (n + 1)) :=
      GPath.cycSeq_of_ge p q (by omega) (by rw [hp0, hq0]) (by rw [hp_n, hq_n])
        (by omega) (by omega)
    rw [hcyc, show 2 * n - (n + 1) = n - 1 by omega, hq_pen]

end Apartment

section Subconst

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [GraphAction D Γ]
  {X : Type} [Group X]
 {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [GraphAction D Γ]
  {X : Type} [Group X]

abbrev nbrs (u : V) : Type := {w : V // Γ.Adj u w}

private def p1Smul {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (g : ↥P1)
    (w : nbrs (Γ := Γ) u) : nbrs (Γ := Γ) u :=
  ⟨ψ1 g • w.1, by
    have hgu : ψ1 g • u = u := hψ1u (show ψ1 g ∈ ψ1.range from ⟨g, rfl⟩)
    have h := (GraphAction.adj_smul (Γ := Γ) (ψ1 g) u w.1).mpr w.2
    rwa [hgu] at h⟩

@[simp] private theorem p1Smul_apply {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (g : ↥P1)
    (w : nbrs (Γ := Γ) u) : (p1Smul hψ1u g w).1 = ψ1 g • w.1 := rfl

@[instance_reducible]
private def p1Action {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) : MulAction ↥P1 (nbrs (Γ := Γ) u) where
  smul := p1Smul hψ1u
  one_smul w := by
    show p1Smul hψ1u 1 w = w
    apply Subtype.ext
    rw [p1Smul_apply, map_one, one_smul]
  mul_smul g h w := by
    show p1Smul hψ1u (g * h) w = p1Smul hψ1u g (p1Smul hψ1u h w)
    apply Subtype.ext
    rw [p1Smul_apply, p1Smul_apply, p1Smul_apply, map_mul, mul_smul]

private noncomputable abbrev p1PermHom {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u) :=
  letI := p1Action (Γ := Γ) hψ1u
  MulAction.toPermHom ↥P1 (nbrs (Γ := Γ) u)

@[simp] private theorem p1PermHom_apply {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (g : ↥P1)
    (w : nbrs (Γ := Γ) u) : (p1PermHom (Γ := Γ) hψ1u g) w = p1Smul hψ1u g w := rfl

private theorem core_smul_eq {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hv : Γ.Adj u v) (n : ↥P1)
    (hn : n ∈ ((P1 ⊓ P2).subgroupOf P1).normalCore) (w : nbrs (Γ := Γ) u) :
    p1Smul hψ1u n w = w := by
  apply Subtype.ext
  rw [p1Smul_apply]
  change ψ1 n • w.1 = w.1
  obtain ⟨g, hg⟩ := htrans w.1 w.2
  have hfix : ∀ x ∈ ((P1 ⊓ P2).subgroupOf P1).normalCore, ψ1 x • v = v := by
    intro x hx
    have hxB : x ∈ (P1 ⊓ P2).subgroupOf P1 := Subgroup.normalCore_le _ hx
    have hmem : ψ1 x ∈ (psiB P2 ψ1).range := ⟨⟨x, hxB⟩, rfl⟩
    rw [← hψ1v] at hmem
    exact hmem.2
  calc ψ1 n • w.1 = ψ1 n • (ψ1 g • v) := by rw [hg]
    _ = ψ1 (n * g) • v := by simp [mul_smul]
    _ = ψ1 (g * (g⁻¹ * n * g)) • v := by group
    _ = ψ1 g • (ψ1 (g⁻¹ * n * g) • v) := by rw [map_mul, mul_smul]
    _ = ψ1 g • v := by
          have hmem : g⁻¹ * n * g ∈ ((P1 ⊓ P2).subgroupOf P1).normalCore := by
            simpa using (Subgroup.normalCore_normal _).conj_mem n hn g⁻¹
          rw [hfix _ hmem]
    _ = w.1 := hg

private theorem p1PermHom_ker {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hv : Γ.Adj u v) :
    MonoidHom.ker (p1PermHom (Γ := Γ) hψ1u : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)) =
      ((P1 ⊓ P2).subgroupOf P1).normalCore := by
  have hkerB : (p1PermHom (Γ := Γ) hψ1u : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)).ker ≤
      (P1 ⊓ P2).subgroupOf P1 := by
    intro x hx
    have hxfix : ∀ w : nbrs (Γ := Γ) u, p1Smul hψ1u x w = w := by
      intro w
      have h := congrArg (fun φ : Equiv.Perm (nbrs (Γ := Γ) u) => φ w)
        (MonoidHom.mem_ker.mp hx)
      rw [p1PermHom_apply] at h
      simpa using h
    have hfixv : ψ1 x • v = v := by
      have := congrArg Subtype.val (hxfix ⟨v, hv⟩)
      simpa [p1Smul] using this
    have hmem : ψ1 x ∈ (psiB P2 ψ1).range := by
      rw [← hψ1v]
      exact ⟨⟨x, rfl⟩, hfixv⟩
    obtain ⟨⟨b, hbB⟩, hb⟩ := hmem
    have hthis : b = (x : X) := congrArg Subtype.val (hψ1 hb)
    show (x : X) ∈ P1 ⊓ P2
    rw [← hthis]
    exact hbB
  refine le_antisymm ?_ ?_
  · intro g hg
    exact (Subgroup.normal_le_normalCore (H := (P1 ⊓ P2).subgroupOf P1)
      (N := (p1PermHom (Γ := Γ) hψ1u : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)).ker)).mpr hkerB hg
  · intro n hn
    rw [MonoidHom.mem_ker]
    ext w
    rw [p1PermHom_apply]
    simpa using congrArg Subtype.val (core_smul_eq hψ1u hψ1v htrans hv n hn w)

private noncomputable def subconstEquivRange {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hv : Γ.Adj u v) :
    Subconst P1 P2 ≃* (p1PermHom (Γ := Γ) hψ1u : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)).range :=
  (QuotientGroup.quotientMulEquivOfEq (p1PermHom_ker hψ1 hψ1u hψ1v htrans hv).symm).trans
    (QuotientGroup.quotientKerEquivRange (p1PermHom (Γ := Γ) hψ1u))

@[reducible] noncomputable def rangeGroup {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) :
    Subgroup (Equiv.Perm (nbrs (Γ := Γ) u)) :=
  (p1PermHom (Γ := Γ) hψ1u : ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)).range

@[instance_reducible]
noncomputable def rangeAction {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) :
    MulAction (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) :=
  MulAction.compHom (nbrs (Γ := Γ) u) (Subgroup.subtype (rangeGroup (Γ := Γ) hψ1u))

theorem rangeAction_smul_eq {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (σ : rangeGroup (Γ := Γ) hψ1u)
    (w : nbrs (Γ := Γ) u) :
    (letI := rangeAction (Γ := Γ) hψ1u; σ • w) = (σ : Equiv.Perm (nbrs (Γ := Γ) u)) w := by
  unfold rangeAction
  rfl

theorem mem_rangeGroup_iff {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (σ : Equiv.Perm (nbrs (Γ := Γ) u)) :
    σ ∈ rangeGroup (Γ := Γ) hψ1u ↔ ∃ g : ↥P1, ∀ w : nbrs (Γ := Γ) u, (σ w).1 = ψ1 g • w.1 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun w => rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Equiv.ext fun w => Subtype.ext (hg w).symm⟩

private noncomputable def rangeHom {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) :
    ↥P1 →* rangeGroup (Γ := Γ) hψ1u :=
  (p1PermHom (Γ := Γ) hψ1u).codRestrict _ fun g => ⟨g, rfl⟩

@[simp] private theorem rangeHom_apply {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (g : ↥P1)
    (w : nbrs (Γ := Γ) u) :
    (((rangeHom hψ1u g : rangeGroup (Γ := Γ) hψ1u) : Equiv.Perm (nbrs (Γ := Γ) u)) w).1 =
      ψ1 g • w.1 := by
  change ((p1PermHom (Γ := Γ) hψ1u g) w).1 = ψ1 g • w.1
  rw [p1PermHom_apply, p1Smul_apply]

@[simp] private theorem rangeAction_rangeHom {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) (g : ↥P1)
    (w : nbrs (Γ := Γ) u) :
    (letI := rangeAction (Γ := Γ) hψ1u; (rangeHom (Γ := Γ) hψ1u g) • w) =
      (((rangeHom (Γ := Γ) hψ1u g : rangeGroup (Γ := Γ) hψ1u) : Equiv.Perm
        (nbrs (Γ := Γ) u)) w) := by
  change (p1PermHom (Γ := Γ) hψ1u g) w =
    ((rangeHom (Γ := Γ) hψ1u g : Equiv.Perm (nbrs (Γ := Γ) u)) w)
  rfl

private theorem range_faithful {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u) :
    letI := rangeAction (Γ := Γ) hψ1u
    FaithfulSMul (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) := by
  letI := rangeAction (Γ := Γ) hψ1u
  rw [faithfulSMul_iff]
  intro y hy
  apply Subtype.ext
  ext w
  exact congrArg Subtype.val (hy w)

private theorem range_pretransitive {P1 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hv : Γ.Adj u v) :
    letI := rangeAction (Γ := Γ) hψ1u
    MulAction.IsPretransitive (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) := by
  letI := rangeAction (Γ := Γ) hψ1u
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := htrans a.1 a.2
  obtain ⟨h, hh⟩ := htrans b.1 b.2
  have hg' : (p1PermHom (Γ := Γ) hψ1u g) ⟨v, hv⟩ = a := by
    apply Subtype.ext
    rw [p1PermHom_apply, p1Smul_apply]
    exact hg
  have hh' : (p1PermHom (Γ := Γ) hψ1u h) ⟨v, hv⟩ = b := by
    apply Subtype.ext
    rw [p1PermHom_apply, p1Smul_apply]
    exact hh
  refine ⟨⟨(p1PermHom (Γ := Γ) hψ1u (h * g⁻¹) : Equiv.Perm (nbrs (Γ := Γ) u)),
    ⟨_, rfl⟩⟩, ?_⟩
  change (p1PermHom (Γ := Γ) hψ1u (h * g⁻¹)) a = b
  rw [map_mul]
  change (p1PermHom (Γ := Γ) hψ1u h)
    (((p1PermHom (Γ := Γ) hψ1u g) : Equiv.Perm (nbrs (Γ := Γ) u))⁻¹ a) = b
  have hinv : ((p1PermHom (Γ := Γ) hψ1u g) : Equiv.Perm (nbrs (Γ := Γ) u))⁻¹ a =
      ⟨v, hv⟩ := by
    rw [← hg']
    simp
  rw [hinv, hh']

private theorem range_stabilizer_of_v {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v) {a b : nbrs (Γ := Γ) u}
    (ha : a ≠ ⟨v, hv⟩) (hb : b ≠ ⟨v, hv⟩) :
    letI := rangeAction (Γ := Γ) hψ1u
    ∃ y : rangeGroup (Γ := Γ) hψ1u,
      y • (⟨v, hv⟩ : nbrs (Γ := Γ) u) = ⟨v, hv⟩ ∧ y • a = b := by
  letI := rangeAction (Γ := Γ) hψ1u
  have ha' : a.1 ≠ v := fun h => ha (Subtype.ext h)
  have hb' : b.1 ≠ v := fun h => hb (Subtype.ext h)
  obtain ⟨g, hg, -⟩ := hreg a.1 b.1 a.2 b.2 ha' hb'
  have hgv : (g : D) • v = v := by
    have hmem : (g : D) ∈ (psiB P2 ψ1).range := hroot_le g.2
    rw [← hψ1v] at hmem
    exact hmem.2
  obtain ⟨⟨b0, hb0B⟩, hb0⟩ := hroot_le g.2
  let b0' : ↥P1 := ⟨b0, hb0B.1⟩
  have hb0' : ψ1 b0' = (g : D) := by
    have h := hb0
    change ψ1 (Subgroup.inclusion inf_le_left ⟨b0, hb0B⟩) = (g : D) at h
    rwa [show Subgroup.inclusion inf_le_left ⟨b0, hb0B⟩ = b0' from Subtype.ext rfl] at h
  let yperm : Equiv.Perm (nbrs (Γ := Γ) u) := p1PermHom (Γ := Γ) hψ1u b0'
  let y : rangeGroup (Γ := Γ) hψ1u := ⟨yperm, ⟨b0', rfl⟩⟩
  have hyval : ∀ w, y • w = yperm w := fun w => rfl
  refine ⟨y, ?_, ?_⟩
  · rw [hyval]
    apply Subtype.ext
    change (yperm ⟨v, hv⟩).1 = v
    rw [show yperm ⟨v, hv⟩ = p1Smul hψ1u b0' ⟨v, hv⟩ from p1PermHom_apply _ _ _,
      p1Smul_apply, hb0']
    exact hgv
  · rw [hyval]
    apply Subtype.ext
    change (yperm a).1 = b.1
    rw [show yperm a = p1Smul hψ1u b0' a from p1PermHom_apply _ _ _,
      p1Smul_apply, hb0']
    exact hg

private theorem range_stabilizer_transitive {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v) (c a b : nbrs (Γ := Γ) u)
    (ha : a ≠ c) (hb : b ≠ c) :
    letI := rangeAction (Γ := Γ) hψ1u
    ∃ y : rangeGroup (Γ := Γ) hψ1u, y • c = c ∧ y • a = b := by
  letI := rangeAction (Γ := Γ) hψ1u
  obtain ⟨g, hg⟩ := (range_pretransitive (Γ := Γ) hψ1u htrans hv).exists_smul_eq
    (⟨v, hv⟩ : nbrs (Γ := Γ) u) c
  let gp : Equiv.Perm (nbrs (Γ := Γ) u) := g
  let a' : nbrs (Γ := Γ) u := gp⁻¹ a
  let b' : nbrs (Γ := Γ) u := gp⁻¹ b
  have hg_perm : gp ⟨v, hv⟩ = c := by
    change (g : Equiv.Perm (nbrs (Γ := Γ) u)) ⟨v, hv⟩ = c
    exact hg
  have ha' : a' ≠ ⟨v, hv⟩ := by
    intro h
    apply ha
    have := congrArg gp h
    simpa [a', gp] using this.trans hg_perm
  have hb' : b' ≠ ⟨v, hv⟩ := by
    intro h
    apply hb
    have := congrArg gp h
    simpa [b', gp] using this.trans hg_perm
  obtain ⟨y0, hy0fix, hy0ab⟩ :=
    range_stabilizer_of_v (Γ := Γ) hψ1u hψ1v hroot hroot_le hreg hv ha' hb'
  have hginv : (g⁻¹ : rangeGroup (Γ := Γ) hψ1u) • c = ⟨v, hv⟩ := by
    rw [← hg]
    simp
  have hginv_a : (g⁻¹ : rangeGroup (Γ := Γ) hψ1u) • a = a' := rfl
  refine ⟨g * y0 * g⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hginv, hy0fix, hg]
  · rw [mul_smul, mul_smul, hginv_a, hy0ab]
    show (g : Equiv.Perm (nbrs (Γ := Γ) u)) ((g : Equiv.Perm (nbrs (Γ := Γ) u)).symm b) = b
    exact Equiv.apply_symm_apply _ _

private theorem range_twoTransitive {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v) :
    letI := rangeAction (Γ := Γ) hψ1u
    MulAction.IsMultiplyPretransitive (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) 2 := by
  letI := rangeAction (Γ := Γ) hψ1u
  haveI : MulAction.IsPretransitive (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) :=
    range_pretransitive (Γ := Γ) hψ1u htrans hv
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hg⟩ := (range_pretransitive (Γ := Γ) hψ1u htrans hv).exists_smul_eq a c
  have hgb_ne : (g : Equiv.Perm (nbrs (Γ := Γ) u)) b ≠ c := by
    intro h
    apply hab
    have hga : (g : Equiv.Perm (nbrs (Γ := Γ) u)) a = c := hg
    exact (g : Equiv.Perm (nbrs (Γ := Γ) u)).injective (by rw [hga, h])
  obtain ⟨h, hhfix, hhab⟩ :=
    range_stabilizer_transitive (Γ := Γ) hψ1u hψ1v htrans hroot hroot_le hreg hv c
      ((g : Equiv.Perm (nbrs (Γ := Γ) u)) b) d hgb_ne hcd.symm
  refine ⟨h * g, ?_, ?_⟩
  · rw [mul_smul, hg, hhfix]
  · rw [mul_smul]
    exact hhab

theorem hasNormalCopy_of_mulEquiv {G H K : Type} [Group G] [Group H] [Group K]
    (e : G ≃* H) (h : HasNormalCopy G K) : HasNormalCopy H K := by
  obtain ⟨N, hN, ⟨φ⟩⟩ := h
  refine ⟨N.map e.toMonoidHom, hN.map e.toMonoidHom e.surjective, ?_⟩
  exact ⟨(MulEquiv.subgroupMap e N).symm.trans φ⟩

theorem subconstNatural_data {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v) {K : Type} [Group K]
    (hN : HasNormalCopy (Subconst P1 P2) K) :
    HasNormalCopy (rangeGroup (Γ := Γ) hψ1u) K ∧
      (letI := rangeAction (Γ := Γ) hψ1u
       FaithfulSMul (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) ∧
       MulAction.IsMultiplyPretransitive (rangeGroup (Γ := Γ) hψ1u)
         (nbrs (Γ := Γ) u) 2) := by
  have e : Subconst P1 P2 ≃* rangeGroup (Γ := Γ) hψ1u := by
    show Subconst P1 P2 ≃* (p1PermHom (Γ := Γ) hψ1u :
      ↥P1 →* Equiv.Perm (nbrs (Γ := Γ) u)).range
    exact subconstEquivRange hψ1 hψ1u hψ1v htrans hv
  refine ⟨hasNormalCopy_of_mulEquiv e hN, ?_⟩
  exact ⟨range_faithful (Γ := Γ) hψ1u,
    range_twoTransitive (Γ := Γ) hψ1u hψ1v htrans hroot hroot_le hreg hv⟩

theorem card_nbrs_eq_one_add_card_root {u v : V} (hT : IsThick Γ) {hroot : Subgroup D}
    (hroot_u : hroot ≤ MulAction.stabilizer D u)
    (hroot_v : hroot ≤ MulAction.stabilizer D v)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v) :
    Fintype.card (nbrs (Γ := Γ) u) = 1 + Nat.card hroot := by
  classical
  obtain ⟨a, hav⟩ : ∃ a : nbrs (Γ := Γ) u, a ≠ ⟨v, hv⟩ := by
    have h3 : 3 ≤ (Γ.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hT u
    have hv_mem : v ∈ Γ.neighborFinset u := by simpa using hv
    have h2 : 2 ≤ ((Γ.neighborFinset u).erase v).card := by
      rw [Finset.card_erase_of_mem hv_mem]; omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < ((Γ.neighborFinset u).erase v).card)
    refine ⟨⟨a, by simpa using (Finset.mem_of_mem_erase ha)⟩, ?_⟩
    intro h
    exact Finset.ne_of_mem_erase ha (congrArg Subtype.val h)
  have ha' : a.1 ≠ v := fun h => hav (Subtype.ext h)
  let φ : ↥hroot → {w : nbrs (Γ := Γ) u // w ≠ ⟨v, hv⟩} := fun g =>
    ⟨⟨(g : D) • a.1, by
        have hgu : (g : D) • u = u := hroot_u g.2
        have h := (GraphAction.adj_smul (Γ := Γ) (g : D) u a.1).mpr a.2
        rwa [hgu] at h⟩,
      by
        intro h
        have hgv : (g : D)⁻¹ • v = v := by
          have hgv' := congrArg ((g : D)⁻¹ • ·) (hroot_v g.2)
          rw [inv_smul_smul] at hgv'
          exact hgv'.symm
        have h' : (g : D)⁻¹ • ((g : D) • a.1) = (g : D)⁻¹ • v :=
          congrArg ((g : D)⁻¹ • ·) (congrArg Subtype.val h)
        rw [inv_smul_smul, hgv] at h'
        exact ha' h'⟩
  have hφ_inj : Function.Injective φ := by
    intro g h hgh
    have hw : (φ g).1.1 ≠ v := fun hh => (φ g).2 (Subtype.ext hh)
    have hg' : (g : D) • a.1 = (φ g).1.1 := rfl
    have hh' : (h : D) • a.1 = (φ g).1.1 := by
      have := congrArg (fun x : {w : nbrs (Γ := Γ) u // w ≠ ⟨v, hv⟩} => x.1.1) hgh
      simpa using this.symm
    exact (hreg a.1 (φ g).1.1 a.2 (φ g).1.2 ha' hw).unique hg' hh' 
  have hφ_surj : Function.Surjective φ := by
    intro w
    have hw : w.1.1 ≠ v := fun h => w.2 (Subtype.ext h)
    let g := (hreg a.1 w.1.1 a.2 w.1.2 ha' hw).choose
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (hreg a.1 w.1.1 a.2 w.1.2 ha' hw).choose_spec.1
  let e : ↥hroot ≃ {w : nbrs (Γ := Γ) u // w ≠ ⟨v, hv⟩} :=
    Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hcard : Nat.card hroot = Fintype.card {w : nbrs (Γ := Γ) u // w ≠ ⟨v, hv⟩} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  have hcompl : Fintype.card {w : nbrs (Γ := Γ) u // w ≠ ⟨v, hv⟩} =
      Fintype.card (nbrs (Γ := Γ) u) - 1 := by
    have h := Fintype.card_subtype_compl (α := nbrs (Γ := Γ) u)
      (p := fun w => w = ⟨v, hv⟩)
    simpa using h
  have hpos : 1 ≤ Fintype.card (nbrs (Γ := Γ) u) :=
    Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  omega

theorem range_psiB_comm {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {ψ2 : ↥P2 →* D}
    (h : ∀ g : ↥(P1 ⊓ P2),
      ψ1 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
        ψ2 (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g)) :
    (psiB P1 ψ2).range = (psiB P2 ψ1).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y.1, y.2.2, y.2.1⟩, ?_⟩
    have hz := h ⟨y.1, y.2.2, y.2.1⟩
    simpa [Subgroup.inclusion] using hz
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y.1, y.2.2, y.2.1⟩, ?_⟩
    have hz := h y
    simpa [Subgroup.inclusion] using hz.symm

theorem card_nbrs_eq_degree (u : V) : Fintype.card (nbrs (Γ := Γ) u) = Γ.degree u := by
  change Fintype.card {w : V // Γ.Adj u w} = Γ.degree u
  rw [Fintype.card_subtype]
  simp [SimpleGraph.degree, SimpleGraph.neighborFinset]

theorem subconstNatural_psu3 {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hSub : SubconstNatural) (k : ℕ) (F : Type) [Field F] [Finite F] (hk : 2 ≤ k)
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v)
    (hpow : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card (nbrs (Γ := Γ) u) = 1 + 2 ^ e)
    (hN : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F))) :
    Fintype.card (nbrs (Γ := Γ) u) = 2 ^ (3 * k) + 1 := by
  letI := rangeAction (Γ := Γ) hψ1u
  haveI : Finite (rangeGroup (Γ := Γ) hψ1u) := by infer_instance
  haveI : FaithfulSMul (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) :=
    range_faithful (Γ := Γ) hψ1u
  have h2t : MulAction.IsMultiplyPretransitive (rangeGroup (Γ := Γ) hψ1u)
      (nbrs (Γ := Γ) u) 2 :=
    range_twoTransitive (Γ := Γ) hψ1u hψ1v htrans hroot hroot_le hreg hv
  have hN' : HasNormalCopy (rangeGroup (Γ := Γ) hψ1u)
      (StatedProj (StatedSU 3 (2 ^ k) F)) :=
    hasNormalCopy_of_mulEquiv (subconstEquivRange hψ1 hψ1u hψ1v htrans hv) hN
  exact hSub.2.2 (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) k F hk hF h2t hpow hN'

theorem subconstNatural_sz {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hSub : SubconstNatural) (a : ℕ) (ha : 1 ≤ a)
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v)
    (hpow : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card (nbrs (Γ := Γ) u) = 1 + 2 ^ e)
    (hN : HasNormalCopy (Subconst P1 P2) ↥(Sz a)) :
    Fintype.card (nbrs (Γ := Γ) u) = 2 ^ (2 * (2 * a + 1)) + 1 := by
  letI := rangeAction (Γ := Γ) hψ1u
  haveI : Finite (rangeGroup (Γ := Γ) hψ1u) := by infer_instance
  haveI : FaithfulSMul (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) :=
    range_faithful (Γ := Γ) hψ1u
  have h2t : MulAction.IsMultiplyPretransitive (rangeGroup (Γ := Γ) hψ1u)
      (nbrs (Γ := Γ) u) 2 :=
    range_twoTransitive (Γ := Γ) hψ1u hψ1v htrans hroot hroot_le hreg hv
  have hN' : HasNormalCopy (rangeGroup (Γ := Γ) hψ1u) ↥(Sz a) :=
    hasNormalCopy_of_mulEquiv (subconstEquivRange hψ1 hψ1u hψ1v htrans hv) hN
  exact hSub.1 (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) a ha h2t hpow hN'

theorem subconstNatural_l2 {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D} {u v : V}
    (hSub : SubconstNatural) (m : ℕ) (hm : 2 ≤ m)
    (hψ1 : Function.Injective ψ1)
    (hψ1u : ψ1.range ≤ MulAction.stabilizer D u)
    (hψ1v : ψ1.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ1).range)
    (htrans : ∀ w : V, Γ.Adj u w → ∃ g : ↥P1, ψ1 g • v = w)
    (hroot : Subgroup D) (hroot_le : hroot ≤ (psiB P2 ψ1).range)
    (hreg : ∀ y y' : V, Γ.Adj u y → Γ.Adj u y' → y ≠ v → y' ≠ v →
      ∃! g : ↥hroot, (g : D) • y = y')
    (hv : Γ.Adj u v)
    (hpow : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card (nbrs (Γ := Γ) u) = 1 + 2 ^ e)
    (hN : HasNormalCopy (Subconst P1 P2)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))) :
    Fintype.card (nbrs (Γ := Γ) u) = 2 ^ m + 1 := by
  letI := rangeAction (Γ := Γ) hψ1u
  haveI : Finite (rangeGroup (Γ := Γ) hψ1u) := by infer_instance
  haveI : FaithfulSMul (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) :=
    range_faithful (Γ := Γ) hψ1u
  have h2t : MulAction.IsMultiplyPretransitive (rangeGroup (Γ := Γ) hψ1u)
      (nbrs (Γ := Γ) u) 2 :=
    range_twoTransitive (Γ := Γ) hψ1u hψ1v htrans hroot hroot_le hreg hv
  have hN' : HasNormalCopy (rangeGroup (Γ := Γ) hψ1u)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
    hasNormalCopy_of_mulEquiv (subconstEquivRange hψ1 hψ1u hψ1v htrans hv) hN
  exact hSub.2.1 (rangeGroup (Γ := Γ) hψ1u) (nbrs (Γ := Γ) u) m hm h2t hpow hN'

end Subconst

section Normalizer

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [GraphAction D Γ]

theorem degree_smul (d : D) (u : V) : Γ.degree (d • u) = Γ.degree u := by
  rw [← SimpleGraph.ncard_neighborSet, ← SimpleGraph.ncard_neighborSet]
  refine Nat.card_congr ?_
  refine
    { toFun := fun w => ⟨d⁻¹ • w.1, ?_⟩
      invFun := fun w => ⟨d • w.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ((GraphAction.adj_smul (Γ := Γ) d (d⁻¹ • w.1) u).mp (by simpa using w.2.symm)).symm
  · exact (GraphAction.adj_smul (Γ := Γ) d u w.1).mpr w.2
  · intro w; ext; simp
  · intro w; ext; simp

theorem degree_eq_degree_u_or_degree_v_of_adj_orbit {u v : V}
    (hconn : Γ.Connected)
    (hu : ∀ w, Γ.Adj u w → ∃ g : D, g • v = w)
    (hv : ∀ w, Γ.Adj v w → ∃ g : D, g • u = w) (w : V) :
    Γ.degree w = Γ.degree u ∨ Γ.degree w = Γ.degree v := by
  classical
  let O : V → Prop := fun x => (∃ g : D, g • u = x) ∨ (∃ g : D, g • v = x)
  have hOu : O u := Or.inl ⟨1, by simp⟩
  have hclosed : ∀ {a b : V}, O a → Γ.Adj a b → O b := by
    rintro a b (⟨g, rfl⟩ | ⟨g, rfl⟩) hab
    · have h : Γ.Adj u (g⁻¹ • b) := by
        have h' : Γ.Adj (g • u) (g • (g⁻¹ • b)) := by simpa using hab
        exact (GraphAction.adj_smul (Γ := Γ) g u (g⁻¹ • b)).mp h'
      obtain ⟨h, hh⟩ := hu (g⁻¹ • b) h
      refine Or.inr ⟨g * h, ?_⟩
      rw [mul_smul, hh]
      simp
    · have h : Γ.Adj v (g⁻¹ • b) := by
        have h' : Γ.Adj (g • v) (g • (g⁻¹ • b)) := by simpa using hab
        exact (GraphAction.adj_smul (Γ := Γ) g v (g⁻¹ • b)).mp h'
      obtain ⟨h, hh⟩ := hv (g⁻¹ • b) h
      refine Or.inl ⟨g * h, ?_⟩
      rw [mul_smul, hh]
      simp
  have hwalk : ∀ {a b : V}, Γ.Walk a b → O a → O b := by
    intro a b p
    induction p with
    | nil => intro h; exact h
    | cons hab pbc ih =>
        intro ha
        exact ih (hclosed ha hab)
  have hO : O w := by
    exact hwalk ((hconn u w).some) hOu
  rcases hO with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · left
    rw [degree_smul]
  · right
    rw [degree_smul]

theorem normalizer_chamber_le_left {L Du Dv : Subgroup D} {u v : V}
    (hDu : ∀ d : D, d ∈ Du ↔ d • u = u)
    (hswap : ∀ d ∈ Subgroup.normalizer ((L ⊓ Du ⊓ Dv : Subgroup D) : Set D),
      (d • u = u ∧ d • v = v) ∨ (d • u = v ∧ d • v = u))
    (hdeg : Γ.degree u ≠ Γ.degree v) :
    Subgroup.normalizer ((L ⊓ Du ⊓ Dv : Subgroup D) : Set D) ≤ Du := by
  intro d hd
  rcases hswap d hd with ⟨hu, -⟩ | ⟨hu, -⟩
  · exact (hDu d).mpr hu
  · exfalso
    apply hdeg
    calc Γ.degree u = Γ.degree (d • u) := (degree_smul d u).symm
      _ = Γ.degree v := by rw [hu]

end Normalizer

section RootConj

variable {X : Type} [Group X] {n : ℕ}

theorem rankTwoSystem_card_conjBy (R : RankTwoSystem X n) (m : R.N) (i : ℤ) :
    Nat.card (CFSG.GH74.BNPair.conjBy (m : X) (R.root i)) = Nat.card (R.root i) := by
  change Nat.card ((R.root i).map (MulAut.conj ((m : X)⁻¹)).toMonoidHom) =
    Nat.card (R.root i)
  rw [Subgroup.card_map_of_injective (MulAut.conj ((m : X)⁻¹)).injective]

theorem rankTwoSystem_card_root_three_eq_card_root_one (R : RankTwoSystem X 4) :
    Nat.card (R.root 3) = Nat.card (R.root 1) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective R.w₂
  have h := (R.roots.action₂ m hm).2.2 1 (by norm_num) (by norm_num)
  have hc := congrArg (fun A : Subgroup X => Nat.card A) h.1
  rw [rankTwoSystem_card_conjBy] at hc
  simpa using hc.symm

theorem rankTwoSystem_card_root_two_eq_card_root_four (R : RankTwoSystem X 4) :
    Nat.card (R.root 2) = Nat.card (R.root 4) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective R.w₁
  have h := (R.roots.action₁ m hm).2.2 2 (by norm_num) (by norm_num)
  have hc := congrArg (fun A : Subgroup X => Nat.card A) h.1
  rw [rankTwoSystem_card_conjBy] at hc
  simpa using hc

end RootConj

section RootProduct

variable {X : Type} [Group X] {n : ℕ}

theorem rankTwoSystem_card_U (R : RankTwoSystem X n) :
    Nat.card R.U = ((intList 1 (n : ℤ)).map fun k => Nat.card (R.root k)).prod := by
  rw [← cardU_card_chainProd R.root (intList 1 (n : ℤ)) (chain_intList_nodup 1 n) R.roots.unique,
    ← R.roots.carrier_eq]
  rfl

theorem pathRootGroup_le_stabilizer_last {V : Type} {Γ : SimpleGraph V} {n : ℕ}
    {D : Type} [Group D] [MulAction D V] {p : GPath Γ n} (hn : 2 ≤ n) :
    pathRootGroup D Γ p ≤ MulAction.stabilizer D (p n) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have e : n - 1 + 1 = n := by omega
  have h := (mem_pathRootGroup.mp hg) (n - 1) (by omega) (by omega) (p n) (by
    have := p.adj (n - 1) (by omega)
    rwa [e] at this)
  exact h

theorem pathRootGroup_le_stabilizer_penultimate {V : Type} {Γ : SimpleGraph V} {n : ℕ}
    {D : Type} [Group D] [MulAction D V] {p : GPath Γ n} (hn : 3 ≤ n) :
    pathRootGroup D Γ p ≤ MulAction.stabilizer D (p (n - 1)) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have h := (mem_pathRootGroup.mp hg) (n - 2) (by omega) (by omega) (p (n - 1)) (by
    have := p.adj (n - 2) (by omega)
    rwa [show n - 2 + 1 = n - 1 by omega] at this)
  exact h

end RootProduct

section ApartmentRoots

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]
  {L : Subgroup D} {R : RankTwoSystem ↥L n} {t : ZMod (2 * n) → V}

theorem map_root_le_of_pathRootGroup_le (hn : 3 ≤ n) (ht : IsPolygonApartment Γ n t)
    {B : Subgroup D}
    (hRoot : ∀ i : ℤ, 1 ≤ i → i ≤ n → (R.root i).map L.subtype = aptRoot D Γ n t i)
    (hrootLe : ∀ p : GPath Γ n, p.NoBack → ∀ j : ℕ, j + 1 ≤ n →
      ((p j = t n ∧ p (j + 1) = t (n + 1)) ∨
        (p j = t (n + 1) ∧ p (j + 1) = t n)) → pathRootGroup D Γ p ≤ B)
    {i : ℤ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (R.root i).map L.subtype ≤ B := by
  rw [hRoot i hi1 hin, aptRoot_eq_pathRootGroup ht i]
  have hnonneg : 0 ≤ (n : ℤ) - i := by omega
  let j : ℕ := ((n : ℤ) - i).toNat
  have hj : (j : ℤ) = (n : ℤ) - i := Int.toNat_of_nonneg hnonneg
  have hj1 : j + 1 ≤ n := by omega
  refine hrootLe (aptPath ht.2 i) (aptPath_noBack (by omega) ht i) j hj1 ?_
  left
  constructor
  · rw [aptPath_apply ht.2 i (by omega)]
    rw [show i + (j : ℤ) = (n : ℤ) by omega]
    simp [apt]
  · rw [aptPath_apply ht.2 i (by omega)]
    rw [show i + ((j + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega]
    simp [apt]

theorem map_U_le_of_pathRootGroup_le (hn : 3 ≤ n) (ht : IsPolygonApartment Γ n t)
    {B : Subgroup D}
    (hRoot : ∀ i : ℤ, 1 ≤ i → i ≤ n → (R.root i).map L.subtype = aptRoot D Γ n t i)
    (hrootLe : ∀ p : GPath Γ n, p.NoBack → ∀ j : ℕ, j + 1 ≤ n →
      ((p j = t n ∧ p (j + 1) = t (n + 1)) ∨
        (p j = t (n + 1) ∧ p (j + 1) = t n)) → pathRootGroup D Γ p ≤ B) :
    R.U.map L.subtype ≤ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hy' : y ∈ chainProd R.root (intList 1 ((n : ℕ) : ℤ)) := by
    rw [← R.roots.carrier_eq]
    exact hy
  exact chainProd_subset R.root (B.comap L.subtype) (intList 1 ((n : ℕ) : ℤ))
    (fun k hk => by
      intro z hz
      exact map_root_le_of_pathRootGroup_le hn ht hRoot hrootLe
        (mem_intList_iff.mp hk).1 (mem_intList_iff.mp hk).2
        (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)) hy'

theorem card_nbrs_succ_eq_one_add_card_root_one (hn : 3 ≤ n)
    (ht : IsPolygonApartment Γ n t) (hGP : IsGeneralizedPolygon Γ n)
    (hThick : IsThick Γ) (hMouf : MoufangCondition D Γ n)
    (hRoot : ∀ i : ℤ, 1 ≤ i → i ≤ n → (R.root i).map L.subtype = aptRoot D Γ n t i)
    (huv : Γ.Adj (t n) (t (n + 1))) :
    Fintype.card {w : V // Γ.Adj (t (n + 1)) w} = 1 + Nat.card (R.root 1) := by
  classical
  let p : GPath Γ n := aptPath ht.2 1
  have hp : p.NoBack := aptPath_noBack (by omega) ht 1
  have hpn : p n = t (n + 1) := by
    rw [aptPath_apply ht.2 1 (by omega)]
    rw [show 1 + (n : ℤ) = (n : ℤ) + 1 by ring]
    simp [apt]
  have hp1 : p (n - 1) = t n := by
    rw [aptPath_apply ht.2 1 (by omega)]
    rw [show 1 + ((n - 1 : ℕ) : ℤ) = (n : ℤ) by omega]
    simp [apt]
  have hroot_u : pathRootGroup D Γ p ≤ MulAction.stabilizer D (t (n + 1)) := by
    have h := pathRootGroup_le_stabilizer_last (Γ := Γ) (D := D) (p := p) (by omega)
    simpa [hpn] using h
  have hroot_v : pathRootGroup D Γ p ≤ MulAction.stabilizer D (t n) := by
    have h := pathRootGroup_le_stabilizer_penultimate (Γ := Γ) (D := D) (p := p) (by omega)
    simpa [hp1] using h
  have hreg : ∀ y y' : V, Γ.Adj (t (n + 1)) y → Γ.Adj (t (n + 1)) y' →
      y ≠ t n → y' ≠ t n → ∃! g : ↥(pathRootGroup D Γ p), (g : D) • y = y' := by
    intro y y' hy hy' hne hne'
    exact rootGroupRegular (n := n) (V := V) (Γ := Γ) (D := D) (by omega)
      hGP hThick hMouf p hp y y' (by simpa [hpn] using hy) (by simpa [hpn] using hy')
      (by simpa [hp1] using hne) (by simpa [hp1] using hne')
  have hcard := card_nbrs_eq_one_add_card_root (Γ := Γ) (D := D) (u := t (n + 1))
    (v := t n) (hroot := pathRootGroup D Γ p) hThick hroot_u hroot_v hreg huv.symm
  have hroot_eq : pathRootGroup D Γ p = (R.root 1).map L.subtype := by
    rw [show pathRootGroup D Γ p = aptRoot D Γ n t 1 from (aptRoot_eq_pathRootGroup ht 1).symm]
    rw [← hRoot 1 (by norm_num) (by omega)]
  rw [hroot_eq, Subgroup.card_map_of_injective L.subtype_injective] at hcard
  exact hcard

theorem card_nbrs_eq_one_add_card_root_last (hn : 3 ≤ n)
    (ht : IsPolygonApartment Γ n t) (hGP : IsGeneralizedPolygon Γ n)
    (hThick : IsThick Γ) (hMouf : MoufangCondition D Γ n)
    (hRoot : ∀ i : ℤ, 1 ≤ i → i ≤ n → (R.root i).map L.subtype = aptRoot D Γ n t i)
    (huv : Γ.Adj (t n) (t (n + 1))) :
    Fintype.card {w : V // Γ.Adj (t n) w} = 1 + Nat.card (R.root n) := by
  classical
  let p : GPath Γ n := aptPathRev ht.2 n
  have hp : p.NoBack := aptPathRev_noBack (by omega) ht n
  have hpn : p n = t n := by
    rw [aptPathRev_apply ht.2 n (by omega)]
    rw [show (n : ℤ) + (n : ℤ) - ((n : ℕ) : ℤ) = (n : ℤ) by omega]
    simp [apt]
  have hp1 : p (n - 1) = t (n + 1) := by
    rw [aptPathRev_apply ht.2 n (by omega)]
    rw [show (n : ℤ) + (n : ℤ) - ((n - 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by omega]
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega]
    simp [apt]
  have hroot_u : pathRootGroup D Γ p ≤ MulAction.stabilizer D (t n) := by
    have h := pathRootGroup_le_stabilizer_last (Γ := Γ) (D := D) (p := p) (by omega)
    simpa [hpn] using h
  have hroot_v : pathRootGroup D Γ p ≤ MulAction.stabilizer D (t (n + 1)) := by
    have h := pathRootGroup_le_stabilizer_penultimate (Γ := Γ) (D := D) (p := p) (by omega)
    simpa [hp1] using h
  have hreg : ∀ y y' : V, Γ.Adj (t n) y → Γ.Adj (t n) y' →
      y ≠ t (n + 1) → y' ≠ t (n + 1) →
      ∃! g : ↥(pathRootGroup D Γ p), (g : D) • y = y' := by
    intro y y' hy hy' hne hne'
    exact rootGroupRegular (n := n) (V := V) (Γ := Γ) (D := D) (by omega)
      hGP hThick hMouf p hp y y' (by simpa [hpn] using hy) (by simpa [hpn] using hy')
      (by simpa [hp1] using hne) (by simpa [hp1] using hne')
  have hcard := card_nbrs_eq_one_add_card_root (Γ := Γ) (D := D) (u := t n)
    (v := t (n + 1)) (hroot := pathRootGroup D Γ p) hThick hroot_u hroot_v hreg huv
  have hroot_eq : pathRootGroup D Γ p = (R.root n).map L.subtype := by
    rw [show pathRootGroup D Γ p = aptRoot D Γ n t n from
      (aptRoot_eq_pathRootGroupRev (by omega) ht n).symm]
    rw [← hRoot n (by omega) (by omega)]
  rw [hroot_eq, Subgroup.card_map_of_injective L.subtype_injective] at hcard
  exact hcard

end ApartmentRoots

section UnitaryLemmaN

variable {V : Type} [Fintype V] {Δ : SimpleGraph V} [DecidableRel Δ.Adj]
  {D : Type} [Group D] [Finite D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Δ]
  {X : Type} [Group X] {P1 P2 : Subgroup X} {ψ1 : ↥P1 →* D}
  {k : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_noncommuting_pathRootGroup_of_subconstUnitary
  (t : ZMod (2 * 4) → V) (ht : IsPolygonApartment Δ 4 t)
  (hGP : IsGeneralizedPolygon Δ 4) (hThick : IsThick Δ) (hMouf : MoufangCondition D Δ 4)
  (hψ1 : Function.Injective ψ1)
  (hψ1u : ψ1.range ≤ MulAction.stabilizer D (t 5))
  (hinter1 : ψ1.range ⊓ MulAction.stabilizer D (t 4) = (psiB P2 ψ1).range)
  (htrans1 : ∀ w : V, Δ.Adj (t 5) w → ∃ g : ↥P1, ψ1 g • t 4 = w)
  (hrootLe : ∀ p : GPath Δ 4, p.NoBack → ∀ j : ℕ, j + 1 ≤ 4 →
    ((p j = t 4 ∧ p (j + 1) = t 5) ∨ (p j = t 5 ∧ p (j + 1) = t 4)) →
    pathRootGroup D Δ p ≤ (psiB P2 ψ1).range)
  (hcardU : Nat.card {w : V // Δ.Adj (t 5) w} = 2 ^ (3 * k) + 1)
  (hU3N : HasNormalCopy (Subconst P1 P2)
    (StatedProj (StatedSU 3 (2 ^ k) F)))
  (hNonab : SubconstUnitaryNonabelian) (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
  (huv : Δ.Adj (t 4) (t 5)) :
  ∃ p : GPath Δ 4, p.NoBack ∧ Δ.degree (p 0) = 2 ^ (3 * k) + 1 ∧
    ∃ a ∈ pathRootGroup D Δ p, ∃ b ∈ pathRootGroup D Δ p, a * b ≠ b * a := by
  classical
  let q : GPath Δ 4 := aptPath ht.2 1
  let p : GPath Δ 4 := q.rev
  let Rroot : Subgroup D := pathRootGroup D Δ q
  have hq : q.NoBack := aptPath_noBack (by norm_num) ht 1
  have hq4 : q 4 = t 5 := by
    change apt t (1 + (4 : ℤ)) = t 5
    norm_num
    rfl
  have hq3 : q 3 = t 4 := by
    change apt t (1 + (3 : ℤ)) = t 4
    norm_num
    rfl
  have hp : p.NoBack := hq.rev
  have hp0 : p 0 = t 5 := by
    change q (4 - 0) = t 5
    rw [show 4 - 0 = 4 by omega, hq4]
  have hp1 : p 1 = t 4 := by
    change q (4 - 1) = t 4
    rw [show 4 - 1 = 3 by omega, hq3]
  have hdeg : Δ.degree (p 0) = 2 ^ (3 * k) + 1 := by
    rw [hp0, ← card_nbrs_eq_degree (Γ := Δ) (t 5)]
    simpa [nbrs, Nat.card_eq_fintype_card] using hcardU
  have hrootLeR : Rroot ≤ (psiB P2 ψ1).range := by
    refine hrootLe q hq 3 (by norm_num) ?_
    left
    exact ⟨hq3, hq4⟩
  have hreg : ∀ y y' : V, Δ.Adj (t 5) y → Δ.Adj (t 5) y' → y ≠ t 4 → y' ≠ t 4 →
      ∃! g : ↥Rroot, (g : D) • y = y' := by
    intro y y' hy hy' hne hne'
    exact rootGroupRegular (n := 4) (V := V) (Γ := Δ) (D := D) (by norm_num)
      hGP hThick hMouf q hq y y' (by simpa [hq4] using hy) (by simpa [hq4] using hy')
      (by simpa [hq3] using hne) (by simpa [hq3] using hne')
  letI := rangeAction (Γ := Δ) hψ1u
  haveI : FaithfulSMul ↥(rangeGroup (Γ := Δ) hψ1u) (nbrs (Γ := Δ) (t 5)) :=
    range_faithful (Γ := Δ) hψ1u
  let Y := ↥(rangeGroup (Γ := Δ) hψ1u)
  let Ω := nbrs (Γ := Δ) (t 5)
  let ω : Ω := ⟨t 4, huv.symm⟩
  let R1 : Subgroup ↥P1 := Rroot.comap ψ1
  let Rrange : Subgroup Y := by
    change Subgroup (rangeGroup (Γ := Δ) hψ1u)
    exact Subgroup.map (rangeHom (Γ := Δ) (u := t 5) hψ1u) R1
  have hB_le_psi : (psiB P2 ψ1).range ≤ ψ1.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion _ y, rfl⟩
  have hRroot_le_psi : Rroot ≤ ψ1.range := hrootLeR.trans hB_le_psi
  have hfixv : ∀ g : ↥Rroot, (g : D) • t 4 = t 4 := by
    intro g
    have hmem : (g : D) ∈ pathRootGroup D Δ q := g.2
    have h := (mem_pathRootGroup.mp hmem) 2 (by norm_num) (by norm_num) (t 4) (by
      simpa [hq3] using q.adj 2 (by norm_num))
    exact h
  have hRle : Rrange ≤ MulAction.stabilizer Y ω := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hr
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [rangeAction_rangeHom]
    rw [rangeHom_apply]
    exact hfixv ⟨ψ1 g, hg⟩
  have hRreg : ∀ ω₁ ω₂ : Ω, ω₁ ≠ ω → ω₂ ≠ ω →
      ∃! r : ↥Rrange, (r : Y) • ω₁ = ω₂ := by
    intro ω₁ ω₂ h₁ h₂
    have h₁' : ω₁.1 ≠ t 4 := fun h => h₁ (Subtype.ext h)
    have h₂' : ω₂.1 ≠ t 4 := fun h => h₂ (Subtype.ext h)
    obtain ⟨g, hg, huniq⟩ := hreg ω₁.1 ω₂.1 ω₁.2 ω₂.2 h₁' h₂'
    obtain ⟨g1, hg1⟩ := hRroot_le_psi g.2
    have hg1R : g1 ∈ R1 := by
      show ψ1 g1 ∈ Rroot
      rw [hg1]
      exact g.2
    let r : ↥Rrange := ⟨rangeHom hψ1u g1, ⟨g1, hg1R, rfl⟩⟩
    refine ⟨r, ?_, ?_⟩
    · apply Subtype.ext
      rw [rangeAction_rangeHom]
      rw [rangeHom_apply]
      simpa [hg1] using hg
    · intro r' hr'
      obtain ⟨g1', hg1', hg1'eq⟩ := Subgroup.mem_map.mp r'.2
      have hg' : (⟨ψ1 g1', hg1'⟩ : ↥Rroot) = g := by
        apply huniq
        have := hr'
        rw [← hg1'eq] at this
        rw [rangeAction_rangeHom] at this
        have hthis := congrArg Subtype.val this
        rw [rangeHom_apply (Γ := Δ) (u := t 5) (g := g1') (w := ω₁)] at hthis
        simpa using hthis
      have hg1'' : g1' = g1 := hψ1 (by
        have := congrArg Subtype.val hg'
        simpa [← hg1] using this)
      apply Subtype.ext
      rw [← hg1'eq, hg1'']
  have h2t : MulAction.IsMultiplyPretransitive Y Ω 2 :=
    range_twoTransitive (Γ := Δ) hψ1u hinter1 htrans1 Rroot hrootLeR hreg huv.symm
  have hNormalCopyY : HasNormalCopy Y (StatedProj (StatedSU 3 (2 ^ k) F)) :=
    hasNormalCopy_of_mulEquiv (subconstEquivRange hψ1 hψ1u hinter1 htrans1 huv.symm) hU3N
  have hpow : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e := by
    refine ⟨3 * k, by omega, ?_⟩
    rw [show Fintype.card Ω = Nat.card {w : V // Δ.Adj (t 5) w} from by
      rw [Nat.card_eq_fintype_card]]
    rw [hcardU]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    hNonab Y Ω k F hk hF h2t hpow hNormalCopyY ω Rrange hRle hRreg
  obtain ⟨a1, ha1, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b1, hb1, rfl⟩ := Subgroup.mem_map.mp hb
  have haR : ψ1 a1 ∈ Rroot := ha1
  have hbR : ψ1 b1 ∈ Rroot := hb1
  have hcomm : ψ1 a1 * ψ1 b1 ≠ ψ1 b1 * ψ1 a1 := by
    intro h
    have hP1 : a1 * b1 = b1 * a1 := hψ1 (by rw [map_mul, map_mul, h])
    apply hab
    rw [← map_mul, ← map_mul, hP1]
  have hrev : pathRootGroup D Δ p = Rroot := by
    change pathRootGroup D Δ q.rev = pathRootGroup D Δ q
    exact pathRootGroup_rev (p := q)
  refine ⟨p, hp, hdeg, ψ1 a1, ?_, ψ1 b1, ?_, hcomm⟩
  · simpa [hrev] using haR
  · simpa [hrev] using hbR

end UnitaryLemmaN

end CFSG.Quasithin.Stroth

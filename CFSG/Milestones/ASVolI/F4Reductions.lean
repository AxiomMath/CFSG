module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Main
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_hval {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : Facts46 c m) : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval F.faithful F.thick1 F.thick2

open CFSG.ASVolI.ChF in
def burnsideF4b_Parabolics : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
      IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)

open CFSG.ASVolI.ChF in
theorem burnsideF4b_parabolics_of_compat (hcompat : NativeChartCompatibilityGoal) :
    burnsideF4b_Parabolics := by
  intro κ p f E _ Gp M₁ M₂ hyp
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4b_thick (hP : burnsideF4b_Parabolics) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    2 ≤ (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne ∧ 2 ≤ (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo := by
  haveI := hyp.finite
  exact burnsideF4a_thick (burnsideF4a_prime_of_isGenLie hyp.model) (hP κ p f E Gp M₁ M₂ hyp)

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_facts46 (hF : F_4_6) (hP : burnsideF4b_Parabolics) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) {Y : Type}
    [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) : β.Facts46 κ.m :=
  burnsideF4a_facts46 hF hyp (burnsideF4b_thick hP hyp) β hβ

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_Facts46All : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      β.Facts46 κ.m

open CFSG.ASVolI.ChF in
theorem burnsideF4b_Facts46All_of_F46 (hF : F_4_6) (hP : burnsideF4b_Parabolics) :
    burnsideF4b_Facts46All :=
  fun κ p f E _ Gp M₁ M₂ hyp Y _ β hβ => burnsideF4b_facts46 hF hP hyp β hβ

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_TransExt : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → IsLieExtAmalgam M₁ M₂ →
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
        ∀ a : β.Γ, β.PathTrans a (κ.m + 1)

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_TransExt_of_F46 (hF : F_4_6) : burnsideF4b_TransExt :=
  fun κ p f E _ Gp M₁ M₂ hyp hext Y _ β hβ a =>
    ((hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).1 a).1 hext

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_lemma_F412 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : Facts46 c m) (hs : c.IsSmall m) (a b : c.Γ) (hab : c.graph.dist a b = m) :
    ∃ t₁ t₂ : GPath c.graph m, t₁ ∈ c.geods m a b ∧ t₂ ∈ c.geods m a b ∧ t₁ ≠ t₂ := by
  cases hv : CosetGeom.vtype a
  · exact F.two_geods_point hs hv hab
  · have hm := F.hm
    obtain ⟨r, hr, hrb⟩ := Facts46.exists_geod_path hab
    have hy1 : CosetGeom.vtype (r 1) = false := by
      have hne01 : CosetGeom.vtype (r 0) ≠ CosetGeom.vtype (r 1) :=
        CosetGeom.vtype_ne_of_adj (r.adj 0 (by omega))
      rw [hr.1, hv] at hne01
      cases h1 : CosetGeom.vtype (r 1)
      · rfl
      · rw [h1] at hne01
        exact absurd rfl hne01
    obtain ⟨y, hy, hyne, -⟩ := burnsideF4b_hval F b (r (m - 1)) (r (m - 1))
    have hadj : c.graph.Adj (r m) y := by rw [hrb]; exact hy
    let t : GPath c.graph m := GPath.shiftSnoc r y hadj
    have ht0 : t 0 = r 1 := GPath.shiftSnoc_apply_lt r y hadj (by omega)
    have htm : t m = y := GPath.shiftSnoc_last r y hadj
    have htnb : t ∈ GPath.nbPaths c.graph (r 1) m := ⟨ht0, hr.2.shiftSnoc hadj hyne⟩
    have hdist : c.graph.dist (r 1) y = m := by
      have := F.dist_m (r 1) t htnb
      rwa [htm] at this
    obtain ⟨t₁, t₂, ht₁, ht₂, hne12⟩ := F.two_geods_point hs hy1 hdist
    rcases F.alt (r 1) t htnb with hi | hbij
    · exfalso
      apply hne12
      rw [hi t₁ ht₁.1 (by rw [ht₁.2.1, htm]) ht₁.2.2,
        hi t₂ ht₂.1 (by rw [ht₂.2.1, htm]) ht₂.2.2]
    · have ha1 : a ∈ CosetGeom.nbrs (r 1) := by
        show c.graph.Adj (r 1) a
        have := (r.adj 0 (by omega)).symm
        rwa [hr.1] at this
      obtain ⟨s, hs', hsa⟩ := hbij.2.2 ha1
      have hs'' := (F.mem_geods_iff).mp hs'
      have hsm : s m = y := by rw [hs''.2, htm]
      have hadj2 : c.graph.Adj (s m) b := by rw [hsm]; exact hy.symm
      have hst : s ≠ t := by
        intro h
        have h1 := congrArg (fun r : GPath c.graph m => r 1) h
        have e1 : t 1 = r 2 := GPath.shiftSnoc_apply_lt r y hadj (by omega)
        have : r 0 = r 2 := by rw [← hr.1] at hsa; rw [← e1, ← h1]; exact hsa.symm
        exact hr.2 0 (by omega) this
      have hsg : s.IsGeodesic := hs'.2.2
      have htg : t.IsGeodesic := by
        show c.graph.dist (t 0) (t m) = m
        rw [ht0, htm]; exact hdist
      obtain ⟨-, hlast⟩ := GPath.geod_first_last_ne (connected_graph c) F.uniqueGeod
        (by omega) hsg htg (by rw [hs''.1.1, ht0]) (by rw [hs''.2, htm]) hst
      have htlast : t (m - 1) = b := by
        rw [GPath.shiftSnoc_apply_lt r y hadj (by omega), show m - 1 + 1 = m by omega, hrb]
      have hbne : b ≠ s (m - 1) := fun h => hlast (by rw [htlast]; exact h.symm)
      let α₂ : GPath c.graph m := GPath.shiftSnoc s b hadj2
      have hα0 : α₂ 0 = a := by
        rw [GPath.shiftSnoc_apply_lt s b hadj2 (by omega)]
        exact hsa
      have hαm : α₂ m = b := GPath.shiftSnoc_last s b hadj2
      have hαnb : α₂ ∈ GPath.nbPaths c.graph a m := ⟨hα0, hs''.1.2.shiftSnoc hadj2 hbne⟩
      refine ⟨r, α₂, (F.mem_geods_iff).mpr ⟨hr, hrb⟩, (F.mem_geods_iff).mpr ⟨hαnb, hαm⟩, ?_⟩
      intro h
      have h1 := congrArg (fun r : GPath c.graph m => r 1) h
      have e1 : α₂ 1 = s 2 := GPath.shiftSnoc_apply_lt s b hadj2 (by omega)
      have e2 : r 1 = s 0 := by rw [hs''.1.1]
      have : s 0 = s 2 := by rw [← e2, ← e1]; exact h1
      exact hs''.1.2 0 (by omega) this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_allBij {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : Facts46 c m) (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m) :
    BijFirst c m a b := by
  obtain ⟨P, hP, hPb⟩ := Facts46.exists_geod_path hab
  rcases F.alt a P hP with h | h
  · exfalso
    obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := burnsideF4b_lemma_F412 F hs a b hab
    apply hne
    rw [h t₁ ht₁.1 (by rw [ht₁.2.1, hPb]) ht₁.2.2, h t₂ ht₂.1 (by rw [ht₂.2.1, hPb]) ht₂.2.2]
  · rwa [hPb] at h

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_diam_le {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (F : Facts46 c m) (hs : c.IsSmall m) (u v : c.Γ) : c.graph.dist u v ≤ m := by
  have hm := F.hm
  by_contra hlt
  have hlt' : m < c.graph.dist u v := not_le.mp hlt
  obtain ⟨P, hP0, hPv, -⟩ := GPath.exists_geodesic (connected_graph c) u v
  have hgeo : c.graph.dist (P 0) (P (c.graph.dist u v)) = c.graph.dist u v := by
    rw [hP0, hPv]
  have hw : c.graph.dist u (P m) = m := by
    have := GPath.dist_prefix (connected_graph c) P hgeo (show m ≤ c.graph.dist u v by omega)
    rwa [hP0] at this
  have hz : c.graph.dist u (P (m + 1)) = m + 1 := by
    have := GPath.dist_prefix (connected_graph c) P hgeo (show m + 1 ≤ c.graph.dist u v by omega)
    rwa [hP0] at this
  have hadj : c.graph.Adj (P m) (P (m + 1)) := P.adj m (by omega)
  have hbij := burnsideF4b_allBij F hs (a := P m) (b := u) (by rw [SimpleGraph.dist_comm]; exact hw)
  obtain ⟨s, hs', hs1⟩ := hbij.2.2 (show P (m + 1) ∈ CosetGeom.nbrs (P m) from hadj)
  have hs1' : s 1 = P (m + 1) := hs1
  have hsg : s.IsGeodesic := hs'.2.2
  have hd := (hsg.drop (connected_graph c) 1 (by omega : 1 ≤ m))
  have hd' : c.graph.dist (s 1) (s m) = m - 1 := by
    have := hd
    unfold GPath.IsGeodesic at this
    rwa [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl,
      show 1 + (m - 1) = m by omega, add_zero] at this
  rw [hs1', hs'.2.1, SimpleGraph.dist_comm, hz] at hd'
  omega

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_nbrs_finite {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} (hc : c.IsFaithful) (u : c.Γ) :
    (CosetGeom.nbrs u).Finite := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hcard : Nat.card (CosetGeom.nbrs u) =
      Nat.card (CosetGeom.nbrs (c.baseVert (CosetGeom.vtype u))) :=
    calc Nat.card (CosetGeom.nbrs u)
        = Nat.card (CosetGeom.nbrs (g • c.baseVert (CosetGeom.vtype u))) := by rw [hg]
      _ = _ := card_nbrs_smul g _
  refine Set.finite_of_ncard_pos ?_
  rw [← Nat.card_coe_set_eq, hcard]
  generalize CosetGeom.vtype u = b
  cases b
  · have h1 : Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := nbrs_xv_card hc
    show 0 < Nat.card (CosetGeom.nbrs c.xv)
    rw [h1]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  · have h1 : Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := nbrs_lv_card hc
    show 0 < Nat.card (CosetGeom.nbrs c.lv)
    rw [h1]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_ball_finite {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} (hc : c.IsFaithful) (x : c.Γ) (k : ℕ) :
    {v : c.Γ | c.graph.dist x v ≤ k}.Finite := by
  induction k with
  | zero =>
    refine (Set.finite_singleton x).subset fun v hv => ?_
    have : c.graph.dist x v = 0 := Nat.le_zero.mp hv
    exact ((connected_graph c).dist_eq_zero_iff.mp this).symm
  | succ k ih =>
    refine (ih.union (ih.biUnion fun u _ => burnsideF4b_nbrs_finite hc u)).subset fun v hv => ?_
    by_cases hle : c.graph.dist x v ≤ k
    · exact Or.inl hle
    · right
      have hd : c.graph.dist x v = k + 1 := by
        have : c.graph.dist x v ≤ k + 1 := hv
        omega
      obtain ⟨P, hP0, hPv, -⟩ := GPath.exists_geodesic' (connected_graph c) x v hd
      have hgeo : c.graph.dist (P 0) (P (k + 1)) = k + 1 := by rw [hP0, hPv]; exact hd
      have hk : c.graph.dist x (P k) = k := by
        have := GPath.dist_prefix (connected_graph c) P hgeo (show k ≤ k + 1 by omega)
        rwa [hP0] at this
      refine Set.mem_iUnion₂.mpr ⟨P k, le_of_eq hk, ?_⟩
      show c.graph.Adj (P k) v
      have := P.adj k (by omega)
      rwa [hPv] at this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_finite_of_small {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite α.G1]
    [Finite α.G2] {c : α.Completion Y} {m : ℕ} (F : Facts46 c m) (hs : c.IsSmall m) : Finite Y := by
  have hΓ : Finite c.Γ := by
    refine Set.finite_univ_iff.mp ?_
    refine (burnsideF4b_ball_finite F.faithful c.xv m).subset fun v _ => ?_
    exact burnsideF4b_diam_le F hs c.xv v
  have h1 : Finite (MulAction.orbit c.G0 c.xv) := inferInstance
  have h2 : Finite (c.G0 ⧸ stv c c.xv) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer c.G0 c.xv)
  have h3 : Finite (stv c c.xv) := by
    rw [stv_xv_eq_range]
    exact Finite.of_surjective (f1 (c := c)).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have h4 : Finite c.G0 :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := stv c c.xv)).symm
  refine Finite.of_surjective (fun g : c.G0 => (g : Y)) fun y => ?_
  have hy : y ∈ c.φ1.range ⊔ c.φ2.range := by rw [c.gen]; exact Subgroup.mem_top y
  exact ⟨⟨y, hy⟩, rfl⟩

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F412 (hF : burnsideF4b_Facts46All) : F_4_12 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ hs a b hb
  have F := hF κ p f E Gp M₁ M₂ hyp Y β hβ
  obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := burnsideF4b_lemma_F412 F hs a b hb
  exact ⟨t₁, ht₁, t₂, ht₂, hne⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4b_finite_G1 {E : Type} [Group E] [Finite E] (M₁ M₂ : Subgroup E) :
    Finite (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 :=
  inferInstanceAs (Finite ↥M₁)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4b_finite_G2 {E : Type} [Group E] [Finite E] (M₁ M₂ : Subgroup E) :
    Finite (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 :=
  inferInstanceAs (Finite ↥M₂)

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_IotaSmall : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → (incl M₁ M₂).IsSmall κ.m

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F413 (hF : burnsideF4b_Facts46All)
    (hι : burnsideF4b_IotaSmall) : F_4_13 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ hs
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := hF κ p f E Gp M₁ M₂ hyp Y β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  refine ⟨F.isGenPolygon hs, ?_⟩
  have Fι := hF κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂)
  have h1 : Nat.card Y = Nat.card ↥(M₁ ⊔ M₂) :=
    card_Y_eq_of_small F Fι hs (hι κ p f E Gp M₁ M₂ hyp)
  have h2 : Nat.card β.G0 = Nat.card Y := card_G0 β
  have h3 : Nat.card ↥(M₁ ⊔ M₂) = Nat.card E := by
    rw [hyp.gen]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [h2, h1, h3]

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F414 (hF : burnsideF4b_Facts46All) : F_4_14 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ hs
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := hF κ p f E Gp M₁ M₂ hyp Y β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  refine ⟨fun a b hb => ?_, fun s t hs' ht' => F.lemma_F414_4 hs hs' ht'⟩
  have hab : β.graph.dist a b = κ.m := hb
  refine ⟨fun S => ?_, fun c hc => F.lemma_F414_2 hs hab hc, ?_⟩
  · have key := F.lemma_F414_1 hab S
    have hm := F.hm
    constructor
    · rintro ⟨ha, hb', hS⟩
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := key.mp ⟨hS, ha, hb'⟩
      refine ⟨p, hp, q, hq, hpq, ?_⟩
      exact GPath.range_cycSeq (by omega) (hp.1.trans hq.1.symm) (hp.2.1.trans hq.2.1.symm)
    · rintro ⟨p, hp, q, hq, hpq, rfl⟩
      have h1 : pathVerts p ∪ pathVerts q = Set.range (GPath.cycSeq p q) :=
        (GPath.range_cycSeq (by omega) (hp.1.trans hq.1.symm) (hp.2.1.trans hq.2.1.symm)).symm
      obtain ⟨hS, ha, hb'⟩ := key.mpr ⟨p, q, hp, hq, hpq, h1⟩
      exact ⟨ha, hb', hS⟩
  · have h := F.lemma_F414_3 hs hab
    have hset : {S : Set β.Γ | a ∈ S ∧ b ∈ S ∧ β.IsApartment κ.m S} =
        {S | β.IsApartment κ.m S ∧ a ∈ S ∧ b ∈ S} := by
      ext S
      simp only [Set.mem_setOf_eq]
      tauto
    rw [hset, Nat.card_coe_set_eq, h]
    rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_mem_stv_xv {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (g : c.G0) : g ∈ stv c c.xv ↔ (g : Y) ∈ c.φ1.range := by
  rw [stv_xv_eq_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_mem_stv_lv {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (g : c.G0) : g ∈ stv c c.lv ↔ (g : Y) ∈ c.φ2.range := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := stv_lv_le_range_f2 c hg
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    have : g = f2 (c := c) a := Subtype.ext ha.symm
    rw [this]
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F426 (hF : burnsideF4b_Facts46All) (h8 : F_4_8) :
    F_4_26 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ s₁ s₂ hs₁ hs₂ hs₁x hs₁xl hs₂l hs₂xl
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := hF κ p f E Gp M₁ M₂ hyp Y β hβ
  have hm := F.hm
  have h1 : (s₁ : Y) ∈ β.φ1.range := (burnsideF4b_mem_stv_xv β s₁).mp hs₁x
  have h2 : (s₂ : Y) ∈ β.φ2.range := (burnsideF4b_mem_stv_lv β s₂).mp hs₂l
  have h12₁ : (s₁ : Y) ∉ β.φ1.range ⊓ β.φ2.range := fun h =>
    hs₁xl ⟨hs₁x, (burnsideF4b_mem_stv_lv β s₁).mpr h.2⟩
  have h12₂ : (s₂ : Y) ∉ β.φ1.range ⊓ β.φ2.range := fun h =>
    hs₂xl ⟨(burnsideF4b_mem_stv_xv β s₂).mpr h.1, hs₂l⟩
  have key : ∀ n : ℕ, 0 < n → n ≤ κ.m → (s₁ * s₂) ^ n = 1 → n = κ.m ∧ β.IsSmall κ.m := by
    intro n hn hnm hpow
    have hst : (((s₁ * s₂) ^ n : β.G0) : Y) ∈ β.φ1.range ⊓ β.φ2.range := by
      rw [hpow]
      exact Subgroup.one_mem _
    obtain ⟨hnm', hpoly, -⟩ := CosetGeom.lemma_F36 (G₁ := β.φ1.range) (G₂ := β.φ2.range)
      (by omega) F.uniqueGeod hs₁ hs₂ h1 h12₁ h2 h12₂ hn hnm hst
    exact ⟨hnm', F.isSmall_of_polygon hpoly⟩
  refine ⟨fun n hn hnm hpow => ?_, fun hord => ?_⟩
  · have := (key n hn hnm.le hpow).1
    omega
  · have hpow : (s₁ * s₂) ^ κ.m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hs := (key κ.m (by omega) le_rfl hpow).2
    haveI : Finite Y := burnsideF4b_finite_of_small F hs
    obtain ⟨Ġ, hĠ, β', -, hext, hiso⟩ := (h8 κ p f E Gp M₁ M₂ hyp).1 Y β hβ hs
    exact ⟨β'.G0, inferInstance, hext, hiso⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_ptsCard_lt_of_large_odd {α : RankTwoAmalgam.{0}} {Y Y' : Type} [Group Y]
    [Finite Y] [Group Y'] [Finite Y'] {c : α.Completion Y} {d : α.Completion Y'} {m : ℕ}
    (F : Facts46 c m) (Fd : Facts46 d m) (hodd : ¬ Even m) (hl : c.IsLarge m)
    (hsd : d.IsSmall m) (hfar : ∃ w, m < c.graph.dist c.xv w) : d.ptsCard < c.ptsCard := by
  have hm := F.hm
  have hq1 := F.thick1
  have hidx : 3 ≤ α.α1.range.index := by
    unfold RankTwoAmalgam.qOne at hq1
    omega
  have hsph_lt : ∀ k, k < m →
      Nat.card ↥(CosetGeom.sphere k c.xv) = Nat.card ↥(CosetGeom.sphere k d.xv) := by
    intro k hk
    rw [F.card_sphere_lt hk, Fd.card_sphere_lt hk]
    exact card_nbPaths_eq c d F.faithful Fd.faithful k
  have hdpts := Facts46.card_pts (c := d) (burnsideF4b_diam_le Fd hsd)
  have hcle := Facts46.card_ptsLe (c := c) m
  have heq : (∑ k ∈ Finset.range (m + 1),
        if Even k then Nat.card ↥(CosetGeom.sphere k c.xv) else 0) =
      ∑ k ∈ Finset.range (m + 1),
        if Even k then Nat.card ↥(CosetGeom.sphere k d.xv) else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.lt_or_ge k m with h | h
    · rw [hsph_lt k h]
    · have hk' : k = m := le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h
      subst hk'
      simp only [hodd, ite_false]
  obtain ⟨w, hw⟩ := hfar
  have hex : ∃ v : c.Γ, CosetGeom.vtype v = false ∧ m < c.graph.dist c.xv v := by
    obtain ⟨P, hP0, hPw, -⟩ := GPath.exists_geodesic (connected_graph c) c.xv w
    have hgeo : c.graph.dist (P 0) (P (c.graph.dist c.xv w)) = c.graph.dist c.xv w := by
      rw [hP0, hPw]
    have hz : c.graph.dist c.xv (P (m + 1)) = m + 1 := by
      have := GPath.dist_prefix (connected_graph c) P hgeo
        (show m + 1 ≤ c.graph.dist c.xv w by omega)
      rwa [hP0] at this
    refine ⟨P (m + 1), ?_, by rw [hz]; omega⟩
    have hpar := GPath.dist_even_iff (connected_graph c)
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.xv (P (m + 1))
    have hev' : Even (c.graph.dist c.xv (P (m + 1))) := by
      rw [hz]
      exact (Nat.not_even_iff_odd.mp hodd).add_one
    have := hpar.mpr hev'
    exact this.symm
  have hlt := Facts46.ptsLe_lt (c := c) m hex
  omega

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F424 (hF : burnsideF4b_Facts46All) (hT : burnsideF4b_TransExt)
    (hι : burnsideF4b_IotaSmall) (h8 : F_4_8) : F_4_24 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ hfin hle
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  haveI : Finite Y := by
    refine Finite.of_surjective (fun g : β.G0 => (g : Y)) fun y => ?_
    have hy : y ∈ β.φ1.range ⊔ β.φ2.range := by rw [β.gen]; exact Subgroup.mem_top y
    exact ⟨⟨y, hy⟩, rfl⟩
  have F := hF κ p f E Gp M₁ M₂ hyp Y β hβ
  have Fι := hF κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂)
  have hιs := hι κ p f E Gp M₁ M₂ hyp
  have hcardι : Nat.card ↥(M₁ ⊔ M₂) = Nat.card E := by
    rw [hyp.gen]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hG0 : Nat.card β.G0 = Nat.card Y := card_G0 β
  have hs : β.IsSmall κ.m := by
    by_contra hns
    have hl : β.IsLarge κ.m := not_not.mp hns
    have hlt : (incl M₁ M₂).ptsCard < β.ptsCard := by
      by_cases hev : Even κ.m
      · exact Facts46.ptsCard_lt_of_large_even F Fι hev hl hιs
      · have hκ : ¬ (κ = .G2d ∨ κ = .Tits) := by
          rintro (rfl | rfl) <;> exact hev (by decide)
        have hext : IsLieExtAmalgam M₁ M₂ := ⟨κ, p, f, Gp, not_or.mp hκ, hyp⟩
        have hT' : ∀ a : β.Γ, β.PathTrans a (κ.m + 1) :=
          hT κ p f E Gp M₁ M₂ hyp hext Y β hβ
        have T : β.TransComp κ.m := ⟨hβ, F.thick1, F.thick2, hT', by have := F.hm; omega⟩
        exact burnsideF4b_ptsCard_lt_of_large_odd F Fι hev hl hιs
          (T.large_far_vertex hl β.xv)
    have e1 := card_Y_eq β hβ
    have e2 := card_Y_eq (incl M₁ M₂) (incl_faithful M₁ M₂)
    have hp : 0 < Nat.card (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := Nat.card_pos
    have : (incl M₁ M₂).ptsCard * Nat.card (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 <
        β.ptsCard * Nat.card (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 :=
      Nat.mul_lt_mul_of_pos_right hlt hp
    omega
  have hcard : Nat.card Y = Nat.card ↥(M₁ ⊔ M₂) := card_Y_eq_of_small F Fι hs hιs
  refine ⟨by rw [hG0, hcard, hcardι], ?_⟩
  obtain ⟨Ġ, hĠ, β', -, hext, hiso⟩ := (h8 κ p f E Gp M₁ M₂ hyp).1 Y β hβ hs
  exact ⟨β'.G0, inferInstance, hext, hiso⟩

section TransCompPort

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)

structure burnsideF4b_TC (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  trans : ∀ a : c.Γ, c.PathTrans a (m + 1)
  hm : 1 ≤ m

namespace burnsideF4b_TC

variable {c} {m : ℕ} (T : burnsideF4b_TC c m)

include T

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2

theorem f35 {a : c.Γ} {p : GPath c.graph (m + 1)} (hp : p ∈ GPath.nbPaths c.graph a (m + 1)) :
    GPath.F35Conclusion c.graph c.G0 a m p :=
  GPath.lemma_F35 T.hval (T.trans a) (CosetGeom.connected rfl)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) T.hm hp

theorem dist_nbPath {n : ℕ} (hn : n ≤ m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) : c.graph.dist a (p n) = n := by
  obtain ⟨r, hr, -⟩ := GPath.exists_extend_to T.hval (Nat.le_succ_of_le hn) hp
  exact (T.f35 hr).2.1 n hn p hp

theorem unique_geod {n : ℕ} (hn : n < m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) {q : GPath c.graph n} (hq0 : q 0 = a)
    (hqn : q n = p n) (hqg : q.IsGeodesic) : q = p := by
  obtain ⟨r, hr, hrp⟩ := GPath.exists_extend_to T.hval (Nat.le_succ_of_le hn.le) hp
  have h := (T.f35 hr).2.2.2.1 n hn q hq0 (by
    rw [hqn, ← hrp, GPath.take_apply_of_le _ _ _ le_rfl]) hqg
  rw [h, hrp]

theorem trans_sphere {n : ℕ} (hn : n ≤ m) (a : c.Γ) {v w : c.Γ} (hv : c.graph.dist a v = n)
    (hw : c.graph.dist a w = n) : ∃ g : c.G0, g • a = a ∧ g • v = w := by
  obtain ⟨p, hp⟩ := GPath.exists_nbPaths T.hval a (m + 1)
  exact (T.f35 hp).2.2.1 n hn v w hv hw

theorem mem_stabPath_iff_fix {n : ℕ} (hn : n < m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) {g : c.G0} (hga : g • a = a) :
    g ∈ p.stabPath ↔ g • p n = p n := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h
    have hpg : g • p ∈ GPath.nbPaths c.graph a n := by
      refine ⟨?_, GPath.smul_noBack hp.2⟩
      show g • p 0 = a
      rw [hp.1, hga]
    have hgeo : (g • p).IsGeodesic := by
      show c.graph.dist ((g • p) 0) ((g • p) n) = n
      rw [hpg.1]
      exact T.dist_nbPath hn.le hpg
    have := T.unique_geod hn hp (q := g • p) hpg.1 (by simpa using h) hgeo
    intro i hi
    have := congrArg (fun r : GPath c.graph n => r i) this
    simpa using this

end burnsideF4b_TC

def burnsideF4b_PhiII (m : ℕ) (a b : c.Γ) : Prop :=
  (∀ y, c.graph.Adj b y → ∃! t : GPath c.graph m,
      t 0 = a ∧ t m = b ∧ t.IsGeodesic ∧ t (m - 1) = y) ∧
  (∀ t₁ t₂ t₃ t₄ : GPath c.graph m, t₁ ∈ c.geods m a b → t₂ ∈ c.geods m a b →
      t₃ ∈ c.geods m a b → t₄ ∈ c.geods m a b → t₁ ≠ t₂ → t₃ ≠ t₄ →
      ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • t₁ = t₃ ∧ g • t₂ = t₄) ∧
  (∀ y₁ y₂ z₁ z₂ : c.Γ, c.graph.Adj b y₁ → c.graph.Adj b y₂ → c.graph.Adj b z₁ →
      c.graph.Adj b z₂ → y₁ ≠ y₂ → z₁ ≠ z₂ →
      ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • y₁ = z₁ ∧ g • y₂ = z₂)

namespace burnsideF4b_TC

variable {c} {m : ℕ} (T : burnsideF4b_TC c m)

include T

theorem alt {a : c.Γ} {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    ((∃ v, m < c.graph.dist a v) ∧
      ∀ t : GPath c.graph m, t 0 = a → t m = p m → t.IsGeodesic → t = p) ∨
    ((∀ v, c.graph.dist a v ≤ m) ∧ burnsideF4b_PhiII c m a (p m)) := by
  obtain ⟨r, hr, hrp⟩ := GPath.exists_extend_to T.hval (Nat.le_succ m) hp
  have hrm : r m = p m := by rw [← hrp, GPath.take_apply_of_le _ _ _ le_rfl]
  rcases (T.f35 hr).2.2.2.2.2.1 with h | h
  · left
    refine ⟨⟨r (m + 1), by rw [(h r hr).1]; omega⟩, ?_⟩
    intro t ht0 htm htg
    have := (h r hr).2 t ht0 htg (by rw [htm, hrm])
    rw [this, hrp]
  · right
    obtain ⟨hd, -, huniq, hnbtrans, hgtrans⟩ := h
    rw [hrm] at huniq hnbtrans hgtrans
    exact ⟨hd, huniq, fun t₁ t₂ t₃ t₄ h1 h2 h3 h4 hne hne' =>
      hgtrans t₁ t₂ t₃ t₄ h1 h2 h3 h4 hne hne', fun y₁ y₂ z₁ z₂ h1 h2 h3 h4 hne hne' =>
      hnbtrans y₁ y₂ z₁ z₂ h1 h2 h3 h4 hne hne'⟩

theorem exists_two_nbrs (v : c.Γ) : ∃ y₁ y₂, c.graph.Adj v y₁ ∧ c.graph.Adj v y₂ ∧ y₁ ≠ y₂ := by
  obtain ⟨y₁, h1⟩ := CosetGeom.exists_adj v
  obtain ⟨y₂, h2, hne, -⟩ := T.hval v y₁ y₁
  exact ⟨y₁, y₂, h1, h2, hne.symm⟩

theorem phiII_symm {a b : c.Γ} (h : burnsideF4b_PhiII c m a b) : burnsideF4b_PhiII c m b a := by
  have hm := T.hm
  obtain ⟨y₁, y₂, h1, h2, hne⟩ := T.exists_two_nbrs b
  obtain ⟨t₁, ⟨ht10, ht1m, ht1g, ht1y⟩, -⟩ := h.1 y₁ h1
  obtain ⟨t₂, ⟨ht20, ht2m, ht2g, ht2y⟩, -⟩ := h.1 y₂ h2
  have hnb : t₁ ∈ GPath.nbPaths c.graph a m :=
    ⟨ht10, GPath.noBack_of_dist_eq (CosetGeom.connected rfl) t₁ ht1g⟩
  have hrev : t₁.rev ∈ GPath.nbPaths c.graph b m := by
    refine ⟨?_, hnb.2.rev⟩
    rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht1m]
  have hrm : t₁.rev m = a := by
    rw [GPath.rev_apply _ le_rfl, Nat.sub_self, ht10]
  rcases T.alt hrev with ⟨-, hi⟩ | ⟨-, hii⟩
  · exfalso
    have e1 := hi t₁.rev (by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht1m]) rfl ht1g.rev
    have e2 := hi t₂.rev (by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, ht2m])
      (by rw [hrm, GPath.rev_apply _ le_rfl, Nat.sub_self, ht20]) ht2g.rev
    have e3 : t₁ = t₂ := by
      rw [← GPath.rev_rev t₁, e1, ← e2, GPath.rev_rev]
    apply hne
    rw [← ht1y, ← ht2y, e3]
  · rwa [hrm] at hii

theorem geods_bij {a b : c.Γ} (h : burnsideF4b_PhiII c m a b) :
    Set.BijOn (fun t : GPath c.graph m => t 1) (c.geods m a b) (CosetGeom.nbrs a) := by
  have hm := T.hm
  have hs := T.phiII_symm h
  refine ⟨fun t ht => ?_, fun t₁ h₁ t₂ h₂ he => ?_, fun y hy => ?_⟩
  · show c.graph.Adj a (t 1)
    rw [← ht.1]
    exact t.adj 0 (by omega)
  · have e1 : t₁.rev (m - 1) = t₁ 1 := by
      rw [GPath.rev_apply _ (by omega)]; congr 1; omega
    have e2 : t₂.rev (m - 1) = t₂ 1 := by
      rw [GPath.rev_apply _ (by omega)]; congr 1; omega
    have hu := (hs.1 (t₁ 1) (by
      show c.graph.Adj a (t₁ 1)
      rw [← h₁.1]
      exact t₁.adj 0 (by omega))).unique
      (y₁ := t₁.rev) (y₂ := t₂.rev)
      ⟨by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, h₁.2.1], by
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, h₁.1], h₁.2.2.rev, e1⟩
      ⟨by rw [GPath.rev_apply _ (by omega), Nat.sub_zero, h₂.2.1], by
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, h₂.1], h₂.2.2.rev, by rw [e2]; exact he.symm⟩
    rw [← GPath.rev_rev t₁, hu, GPath.rev_rev]
  · obtain ⟨t, ⟨ht0, htm, htg, hty⟩, -⟩ := hs.1 y hy
    refine ⟨t.rev, ⟨?_, ?_, htg.rev⟩, ?_⟩
    · rw [GPath.rev_apply _ (by omega), Nat.sub_zero, htm]
    · rw [GPath.rev_apply _ le_rfl, Nat.sub_self, ht0]
    · show t.rev 1 = y
      rw [GPath.rev_apply _ (by omega), ← hty]

theorem trans_nbrs {a b : c.Γ} (h : burnsideF4b_PhiII c m a b) {y z : c.Γ} (hy : c.graph.Adj a y)
    (hz : c.graph.Adj a z) : ∃ g : c.G0, g • a = a ∧ g • b = b ∧ g • y = z := by
  have hs := T.phiII_symm h
  obtain ⟨y', hy', hne⟩ : ∃ y', c.graph.Adj a y' ∧ y' ≠ y := by
    obtain ⟨w, hw, hwy, -⟩ := T.hval a y y
    exact ⟨w, hw, hwy⟩
  obtain ⟨z', hz', hne'⟩ : ∃ z', c.graph.Adj a z' ∧ z' ≠ z := by
    obtain ⟨w, hw, hwz, -⟩ := T.hval a z z
    exact ⟨w, hw, hwz⟩
  obtain ⟨g, hg1, hg2, hg3, -⟩ := hs.2.2 y y' z z' hy hy' hz hz' hne.symm hne'.symm
  exact ⟨g, hg2, hg1, hg3⟩

theorem lemma_F46_7 {n : ℕ} (hn : n < m) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) :
    (CosetGeom.sphere n a).ncard = (p.stabPath : Subgroup c.G0).relIndex (stv c a) := by
  have hv : p n ∈ CosetGeom.sphere n a := T.dist_nbPath hn.le hp
  have horb : MulAction.orbit (stv c a) (p n) = CosetGeom.sphere n a := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
      show c.graph.dist a ((g : c.G0) • p n) = n
      have := GPath.dist_smul (CosetGeom.connected (G₀ := c.φ1.range ⊔ c.φ2.range) rfl)
        (g : c.G0) a (p n)
      rw [hg] at this
      rw [this]
      exact hv
    · intro hw
      obtain ⟨g, hga, hgv⟩ := T.trans_sphere hn.le a hv hw
      exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩, hgv⟩
  have hstab : MulAction.stabilizer (stv c a) (p n) = p.stabPath.subgroupOf (stv c a) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
    rw [T.mem_stabPath_iff_fix hn hp hg]
    rfl
  rw [← Nat.card_coe_set_eq, ← horb,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (stv c a) (p n)), hstab]
  rfl

theorem stabPath_eq {a : c.Γ} {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    (p.stabPath : Subgroup c.G0) = stv c a ⊓ stv c (p 1) ⊓ stv c (p m) := by
  have hm := T.hm
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hp.1]; exact h 0 (Nat.zero_le m)
    · exact h 1 hm
    · exact h m le_rfl
  · rintro ⟨⟨hga, hg1⟩, hgm⟩
    let t : GPath c.graph (m - 1) := p.drop 1 hm
    have ht0 : t ∈ GPath.nbPaths c.graph (p 1) (m - 1) :=
      ⟨by show p (1 + min 0 (m - 1)) = p 1; simp, hp.2.drop 1 hm⟩
    have htm : t (m - 1) = p m := by
      rw [GPath.drop_apply _ _ _ le_rfl]; congr 1; omega
    have hgt : g • t ∈ GPath.nbPaths c.graph (p 1) (m - 1) := by
      refine ⟨?_, GPath.smul_noBack ht0.2⟩
      show g • t 0 = p 1
      rw [ht0.1, hg1]
    have hgeo : (g • t).IsGeodesic := by
      show c.graph.dist ((g • t) 0) ((g • t) (m - 1)) = m - 1
      rw [hgt.1]
      exact T.dist_nbPath (by omega) hgt
    have heq := T.unique_geod (n := m - 1) (by omega) ht0 (q := g • t) hgt.1
      (by show g • t (m - 1) = t (m - 1); rw [htm, hgm]) hgeo
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [hp.1]; exact hga
    · have := congrArg (fun r : GPath c.graph (m - 1) => r (i - 1)) heq
      simp only [GPath.smul_apply] at this
      have e : t (i - 1) = p i := by
        rw [GPath.drop_apply _ _ _ (by omega)]; congr 1; omega
      rwa [e] at this

end burnsideF4b_TC

end TransCompPort

section QGroup

open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.ASVolI.ChF

theorem burnsideF4b_le_normalizer_pCoreOf {E : Type} [Group E] (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) (M : Subgroup E) : M ≤ Subgroup.normalizer (pCoreOf p (Gp ⊓ M) : Set E) := by
  have hchar : (CFSG.pCore p ↥(Gp ⊓ M)).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic p
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := Gp ⊓ M) (CFSG.pCore p ↥(Gp ⊓ M))
  have h2 : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hN.conj_mem x hx1 a, M.mul_mem (M.mul_mem ha hx2) (M.inv_mem ha)⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have := hN.conj_mem _ hx1 a⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem ha) hx2) ha
        simpa [mul_assoc] using this
  exact fun a ha => h1 (h2 ha)

theorem burnsideF4b_Qbar_normal {E : Type} [Group E] (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) (M : Subgroup E) : ((pCoreOf p (Gp ⊓ M)).subgroupOf M).Normal := by
  have hle : pCoreOf p (Gp ⊓ M) ≤ M :=
    (CFSG.LieType.BorelTits.pCoreOf_le p (Gp ⊓ M)).trans inf_le_right
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (burnsideF4b_le_normalizer_pCoreOf p hN M)

theorem burnsideF4b_pCoreOf_le_sylow {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H P S : Subgroup E} (hS : IsSylowOf p S H) (hSP : S ≤ P) (hPH : P ≤ H) :
    pCoreOf p P ≤ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  have h1 : IsPGroup p (S.subgroupOf P) := hSp.comap_subtype
  have hdvd : S.relIndex P ∣ S.relIndex H :=
    ⟨P.relIndex H, (Subgroup.relIndex_mul_relIndex S P H hSP hPH).symm⟩
  have h2 : ¬ p ∣ (S.subgroupOf P).index := fun h => hSidx (h.trans hdvd)
  let T : Sylow p ↥P := h1.toSylow h2
  have hcore : CFSG.pCore p ↥P ≤ (T : Subgroup ↥P) := by
    haveI : (CFSG.pCore p ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal p
    exact (CFSG.LieType.BorelTits.pCore_isPGroup p).le_sylow_of_normal T
  have h3 : (T : Subgroup ↥P) = S.subgroupOf P := rfl
  rw [h3] at hcore
  have := Subgroup.map_mono (f := P.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this

theorem burnsideF4b_pCoreOf_le {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {Gp M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    pCoreOf p (Gp ⊓ M₁) ≤ M₂ ∧ pCoreOf p (Gp ⊓ M₂) ≤ M₁ := by
  obtain ⟨S, hS, hB⟩ := hP.1
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB]; exact le_inf hS.1 Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · have hSP : S ≤ Gp ⊓ M₁ := hSB.trans (inf_le_inf_left _ inf_le_left)
    exact (burnsideF4b_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_right))
  · have hSP : S ≤ Gp ⊓ M₂ := hSB.trans (inf_le_inf_left _ inf_le_right)
    exact (burnsideF4b_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_left))

end QGroup

section QCompletion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7 CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF4b_Qb1_normal (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (M₁ M₂ : Subgroup E) :
    (((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁ : Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)).Normal :=
  burnsideF4b_Qbar_normal p hN M₁

theorem burnsideF4b_Qb2_normal (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (M₁ M₂ : Subgroup E) :
    (((pCoreOf p (Gp ⊓ M₂)).subgroupOf M₂ : Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G2)).Normal :=
  burnsideF4b_Qbar_normal p hN M₂

theorem burnsideF4b_conjSub_f1 {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {Q : Subgroup α.G1}
    (hQ : Q.Normal) (a : α.G1) :
    conjSub (f1 (c := c) a) (Q.map (f1 (c := c))) = Q.map (f1 (c := c)) := by
  rw [LieSetting.conjSub_map, LieSetting.conjSub_normal hQ]

theorem burnsideF4b_conjSub_f2 {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {Q : Subgroup α.G2}
    (hQ : Q.Normal) (a : α.G2) :
    conjSub (f2 (c := c) a) (Q.map (f2 (c := c))) = Q.map (f2 (c := c)) := by
  rw [LieSetting.conjSub_map, LieSetting.conjSub_normal hQ]

theorem burnsideF4b_QNormalized (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal) (c : Cpl M₁ M₂ Y) :
    QNormalized (Qx p Gp c) (Ql p Gp c) := by
  intro b h hh
  cases b
  · have hh' : h ∈ stv c c.xv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_xv_le_range_f1 c hh'
    exact burnsideF4b_conjSub_f1 c (burnsideF4b_Qb1_normal p hN M₁ M₂) a0
  · have hh' : h ∈ stv c c.lv := MulAction.mem_stabilizer_iff.mpr hh
    obtain ⟨a0, rfl⟩ := stv_lv_le_range_f2 c hh'
    exact burnsideF4b_conjSub_f2 c (burnsideF4b_Qb2_normal p hN M₁ M₂) a0

theorem burnsideF4b_f1_mem_stv_lv {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {y : α.G1}
    (hy : y ∈ α.α1.range) : f1 (c := c) y ∈ stv c c.lv := by
  obtain ⟨g, rfl⟩ := hy
  refine (burnsideF4b_mem_stv_lv c _).mpr ?_
  show c.φ1 (α.α1 g) ∈ c.φ2.range
  rw [c.comm1, ← c.comm2 g]
  exact ⟨_, rfl⟩

theorem burnsideF4b_f2_mem_stv_xv {α : RankTwoAmalgam.{0}} (c : α.Completion Y) {y : α.G2}
    (hy : y ∈ α.α2.range) : f2 (c := c) y ∈ stv c c.xv := by
  obtain ⟨g, rfl⟩ := hy
  refine (burnsideF4b_mem_stv_xv c _).mpr ?_
  show c.φ2 (α.α2 g) ∈ c.φ1.range
  rw [c.comm2, ← c.comm1 g]
  exact ⟨_, rfl⟩

theorem burnsideF4b_Qx_le_stv (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal)
    (hQ : pCoreOf p (Gp ⊓ M₁) ≤ M₂) (c : Cpl M₁ M₂ Y) {w : c.Γ} (hw : w ∈ CosetGeom.nbrs c.xv) :
    Qx p Gp c ≤ stv c w := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show c.lv ∈ CosetGeom.nbrs c.xv from CosetGeom.adj_γ₀_γ₁) hw
  rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_left] at hg1
  obtain ⟨a, ha⟩ := hg1
  have hga : g = f1 (c := c) a := Subtype.ext ha.symm
  rw [← hg2, stv_smul]
  rintro x ⟨b, hb, rfl⟩
  rw [mem_conjSub, hga, ← map_inv, ← map_mul, ← map_mul]
  have hb' : a⁻¹ * b * a ∈ (pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁ := by
    exact (burnsideF4b_Qbar_normal p hN M₁).conj_mem' _ hb _
  refine burnsideF4b_f1_mem_stv_lv c ?_
  have h1 := hQ (Subgroup.mem_subgroupOf.mp hb')
  rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range = (M₁ ⊓ M₂).subgroupOf M₁ from
    Subgroup.inclusion_range (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
  exact Subgroup.mem_subgroupOf.mpr ⟨(show ↥M₁ from a⁻¹ * b * a).2, h1⟩

theorem burnsideF4b_Ql_le_stv (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal)
    (hQ : pCoreOf p (Gp ⊓ M₂) ≤ M₁) (c : Cpl M₁ M₂ Y) {w : c.Γ} (hw : w ∈ CosetGeom.nbrs c.lv) :
    Ql p Gp c ≤ stv c w := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show c.xv ∈ CosetGeom.nbrs c.lv from CosetGeom.adj_γ₀_γ₁.symm) hw
  rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at hg1
  obtain ⟨a, ha⟩ := hg1
  have hga : g = f2 (c := c) a := Subtype.ext ha.symm
  rw [← hg2, stv_smul]
  rintro x ⟨b, hb, rfl⟩
  rw [mem_conjSub, hga, ← map_inv, ← map_mul, ← map_mul]
  have hb' : a⁻¹ * b * a ∈ (pCoreOf p (Gp ⊓ M₂)).subgroupOf M₂ := by
    exact (burnsideF4b_Qbar_normal p hN M₂).conj_mem' _ hb _
  refine burnsideF4b_f2_mem_stv_xv c ?_
  have h1 := hQ (Subgroup.mem_subgroupOf.mp hb')
  rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range = (M₁ ⊓ M₂).subgroupOf M₂ from
    Subgroup.inclusion_range (inf_le_right : M₁ ⊓ M₂ ≤ M₂)]
  exact Subgroup.mem_subgroupOf.mpr ⟨h1, (show ↥M₂ from a⁻¹ * b * a).2⟩

end QCompletion

section ComplementGeneral

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7

theorem burnsideF4b_complement_of_base {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (hQ : QNormalized Qx Ql) {m : ℕ}
    (hbase : ∀ (b : Bool) (q : GPath c.graph m),
      q ∈ GPath.nbPaths c.graph (c.baseVert b) m →
      IsComplementIn q.stabPath (cond b Ql Qx) (stv c (c.baseVert b) ⊓ stv c (q 1)))
    (a : c.Γ) {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    IsComplementIn p.stabPath (c.Qvert Qx Ql a) (stv c a ⊓ stv c (p 1)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
  have hq : g⁻¹ • p ∈ GPath.nbPaths c.graph (c.baseVert (CosetGeom.vtype a)) m := by
    refine ⟨?_, GPath.smul_noBack hp.2⟩
    show g⁻¹ • p 0 = _
    rw [hp.1]
    exact inv_smul_eq_iff.mpr hg.symm
  have h2 := (IsComplementIn.conjSub_iff g).mpr (hbase _ _ hq)
  have e1 : conjSub g (g⁻¹ • p).stabPath = p.stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : conjSub g (stv c (c.baseVert (CosetGeom.vtype a)) ⊓ stv c ((g⁻¹ • p) 1)) =
      stv c a ⊓ stv c (p 1) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg, GPath.smul_apply, smul_inv_smul]
  rw [e1, e3, ← Qvert_eq_conjSub hQ hg] at h2
  exact h2

theorem burnsideF4b_complement_end {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (hQ : QNormalized Qx Ql) {m : ℕ} (hm : 1 ≤ m)
    (hbase : ∀ (b : Bool) (q : GPath c.graph m),
      q ∈ GPath.nbPaths c.graph (c.baseVert b) m →
      IsComplementIn q.stabPath (cond b Ql Qx) (stv c (c.baseVert b) ⊓ stv c (q 1)))
    (a : c.Γ) {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    IsComplementIn p.stabPath (c.Qvert Qx Ql (p m)) (stv c (p (m - 1)) ⊓ stv c (p m)) := by
  have hrev : p.rev ∈ GPath.nbPaths c.graph (p m) m := by
    refine ⟨?_, hp.2.rev⟩
    rw [GPath.rev_apply _ (by omega), Nat.sub_zero]
  have h := burnsideF4b_complement_of_base hQ hbase (p m) hrev
  rw [GPath.stabPath_rev, GPath.rev_apply _ (by omega), inf_comm] at h
  exact h

theorem burnsideF4b_transfer_x {α : RankTwoAmalgam.{0}} {Y Yb : Type} [Group Y] [Group Yb]
    {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful) {m : ℕ}
    (hm : 1 ≤ m) (Qb : Subgroup α.G1)
    (hi : ∀ q : GPath ι.graph m, q ∈ GPath.nbPaths ι.graph ι.xv m →
      IsComplementIn q.stabPath (Qb.map (f1 (c := ι))) (stv ι ι.xv ⊓ stv ι (q 1)))
    {p : GPath β.graph m} (hp : p ∈ GPath.nbPaths β.graph β.xv m) :
    IsComplementIn p.stabPath (Qb.map (f1 (c := β))) (stv β β.xv ⊓ stv β (p 1)) := by
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := (β.graphCovering hβ).lift_path xhat m p
    (by rw [hp.1]; exact (Θ_xhat β hβ).symm)
  have hpb0 : (ι.graphCovering hι).pathMap ph ∈ GPath.nbPaths ι.graph ι.xv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (ph 0) = ι.xv
      rw [hph0]; exact Θ_xhat ι hι
    · rw [(ι.graphCovering hι).noBack_pathMap_iff,
        ← (β.graphCovering hβ).noBack_pathMap_iff, hphp]
      exact hp.2
  have h1 := hi _ hpb0
  have rg : stv ι ι.xv ≤ (f1 (c := ι)).range := stv_xv_le_range_f1 ι
  have h2 := (IsComplementIn.comap_iff (f1 (c := ι)) (f1_injective ι hι)
    ((GPath.stabPath_le_stabilizer _ hpb0.1).trans rg) (Subgroup.map_le_range _ _)
    (inf_le_left.trans rg)).mp h1
  have e1 : ((ι.graphCovering hι).pathMap ph).stabPath.comap (f1 (c := ι)) =
      α.gam1 ph := comap_f1_stabPath ι hι ph hph0
  have e3 := comap_f1_stv_inf ι hι ph hph0 (by omega : 1 ≤ m)
  have e2 : (Qb.map (f1 (c := ι))).comap (f1 (c := ι)) = Qb :=
    Subgroup.comap_map_eq_self_of_injective (f1_injective ι hι) _
  rw [e1, e2, e3] at h2
  have rgβ : stv β β.xv ≤ (f1 (c := β)).range := stv_xv_le_range_f1 β
  have hp1 : p.stabPath ≤ stv β β.xv := GPath.stabPath_le_stabilizer p hp.1
  have e1β : p.stabPath.comap (f1 (c := β)) = α.gam1 ph := by
    rw [← hphp]; exact comap_f1_stabPath β hβ ph hph0
  have e2β : (Qb.map (f1 (c := β))).comap (f1 (c := β)) = Qb :=
    Subgroup.comap_map_eq_self_of_injective (f1_injective β hβ) _
  have e3β : (stv β β.xv ⊓ stv β (p 1)).comap (f1 (c := β)) =
      α.gam1 (ph.take 1 (by omega)) := by
    rw [← hphp]; exact comap_f1_stv_inf β hβ ph hph0 (by omega : 1 ≤ m)
  have hQβ : Qb.map (f1 (c := β)) ≤ (f1 (c := β)).range := Subgroup.map_le_range _ _
  rw [IsComplementIn.comap_iff (f1 (c := β)) (f1_injective β hβ) (hp1.trans rgβ)
    hQβ (inf_le_left.trans rgβ), e1β, e2β, e3β]
  exact h2

theorem burnsideF4b_transfer_l {α : RankTwoAmalgam.{0}} {Y Yb : Type} [Group Y] [Group Yb]
    {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful) {m : ℕ}
    (hm : 1 ≤ m) (Qb : Subgroup α.G2)
    (hi : ∀ q : GPath ι.graph m, q ∈ GPath.nbPaths ι.graph ι.lv m →
      IsComplementIn q.stabPath (Qb.map (f2 (c := ι))) (stv ι ι.lv ⊓ stv ι (q 1)))
    {p : GPath β.graph m} (hp : p ∈ GPath.nbPaths β.graph β.lv m) :
    IsComplementIn p.stabPath (Qb.map (f2 (c := β))) (stv β β.lv ⊓ stv β (p 1)) := by
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := (β.graphCovering hβ).lift_path lhat m p
    (by rw [hp.1]; exact (Θ_lhat β hβ).symm)
  have hpb0 : (ι.graphCovering hι).pathMap ph ∈ GPath.nbPaths ι.graph ι.lv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (ph 0) = ι.lv
      rw [hph0]; exact Θ_lhat ι hι
    · rw [(ι.graphCovering hι).noBack_pathMap_iff,
        ← (β.graphCovering hβ).noBack_pathMap_iff, hphp]
      exact hp.2
  have h1 := hi _ hpb0
  have rg : stv ι ι.lv ≤ (f2 (c := ι)).range := stv_lv_le_range_f2 ι
  have h2 := (IsComplementIn.comap_iff (f2 (c := ι)) (f2_injective ι hι)
    ((GPath.stabPath_le_stabilizer _ hpb0.1).trans rg) (Subgroup.map_le_range _ _)
    (inf_le_left.trans rg)).mp h1
  have e1 : ((ι.graphCovering hι).pathMap ph).stabPath.comap (f2 (c := ι)) =
      α.gam2 ph := comap_f2_stabPath ι hι ph hph0
  have e3 := comap_f2_stv_inf ι hι ph hph0 (by omega : 1 ≤ m)
  have e2 : (Qb.map (f2 (c := ι))).comap (f2 (c := ι)) = Qb :=
    Subgroup.comap_map_eq_self_of_injective (f2_injective ι hι) _
  rw [e1, e2, e3] at h2
  have rgβ : stv β β.lv ≤ (f2 (c := β)).range := stv_lv_le_range_f2 β
  have hp1 : p.stabPath ≤ stv β β.lv := GPath.stabPath_le_stabilizer p hp.1
  have e1β : p.stabPath.comap (f2 (c := β)) = α.gam2 ph := by
    rw [← hphp]; exact comap_f2_stabPath β hβ ph hph0
  have e2β : (Qb.map (f2 (c := β))).comap (f2 (c := β)) = Qb :=
    Subgroup.comap_map_eq_self_of_injective (f2_injective β hβ) _
  have e3β : (stv β β.lv ⊓ stv β (p 1)).comap (f2 (c := β)) =
      α.gam2 (ph.take 1 (by omega)) := by
    rw [← hphp]; exact comap_f2_stv_inf β hβ ph hph0 (by omega : 1 ≤ m)
  have hQβ : Qb.map (f2 (c := β)) ≤ (f2 (c := β)).range := Subgroup.map_le_range _ _
  rw [IsComplementIn.comap_iff (f2 (c := β)) (f2_injective β hβ) (hp1.trans rgβ)
    hQβ (inf_le_left.trans rgβ), e1β, e2β, e3β]
  exact h2

end ComplementGeneral

section IndexFormula

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}

theorem burnsideF4b_card_nbrs [Finite α.G1] [Finite α.G2] (hc : c.IsFaithful) (u : c.Γ) :
    Nat.card (CosetGeom.nbrs u) = α.qv (CosetGeom.vtype u) + 1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hcard : Nat.card (CosetGeom.nbrs u) =
      Nat.card (CosetGeom.nbrs (c.baseVert (CosetGeom.vtype u))) :=
    calc Nat.card (CosetGeom.nbrs u)
        = Nat.card (CosetGeom.nbrs (g • c.baseVert (CosetGeom.vtype u))) := by rw [hg]
      _ = _ := card_nbrs_smul g _
  have i1 : α.α1.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have i2 : α.α2.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  generalize CosetGeom.vtype u = b at hcard ⊢
  cases b
  · have : Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := nbrs_xv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qOne
    simp only [Bool.false_eq_true, ↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.xv) = _
    rw [this]
    omega
  · have : Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := nbrs_lv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qTwo
    simp only [↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.lv) = _
    rw [this]
    omega

def burnsideF4b_extSet {n : ℕ} (q : GPath c.graph n) : Set c.Γ :=
  {w | c.graph.Adj (q n) w ∧ (1 ≤ n → w ≠ q (n - 1))}

theorem burnsideF4b_card_extSet [Finite α.G1] [Finite α.G2] (hc : c.IsFaithful) {n : ℕ}
    (q : GPath c.graph n) :
    Nat.card ↥(burnsideF4b_extSet q) =
      if n = 0 then α.qv (CosetGeom.vtype (q 0)) + 1 else α.qv (CosetGeom.vtype (q n)) := by
  by_cases hn : n = 0
  · subst hn
    have : burnsideF4b_extSet q = CosetGeom.nbrs (q 0) := by
      ext w
      simp only [burnsideF4b_extSet, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, fun h1 => absurd h1 (by omega)⟩
    rw [this, burnsideF4b_card_nbrs hc]
    simp
  · have hn1 : 1 ≤ n := by omega
    have hadj : c.graph.Adj (q n) (q (n - 1)) := by
      have := (q.adj (n - 1) (by omega)).symm
      rwa [show n - 1 + 1 = n by omega] at this
    have : burnsideF4b_extSet q = CosetGeom.nbrs (q n) \ {q (n - 1)} := by
      ext w
      simp only [burnsideF4b_extSet, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact fun h => ⟨h.1, h.2 hn1⟩
      · exact fun h => ⟨h.1, fun _ => h.2⟩
    rw [this]
    simp only [hn, ↓reduceIte]
    have h1 : (CosetGeom.nbrs (q n) \ {q (n - 1)}).ncard = (CosetGeom.nbrs (q n)).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hadj
    have h2 : Nat.card ↥(CosetGeom.nbrs (q n)) = α.qv (CosetGeom.vtype (q n)) + 1 :=
      burnsideF4b_card_nbrs hc _
    rw [Nat.card_coe_set_eq, h1, ← Nat.card_coe_set_eq, h2]
    simp

theorem burnsideF4b_relIndex_succ [Finite α.G1] [Finite α.G2] (hc : c.IsFaithful)
    (hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b) {m : ℕ} {a : c.Γ}
    (htrans : ∀ q q' : GPath c.graph (m + 1), q ∈ GPath.nbPaths c.graph a (m + 1) →
      q' ∈ GPath.nbPaths c.graph a (m + 1) → ∃ g : c.G0, g • a = a ∧ g • q = q')
    {n : ℕ} (hn : n ≤ m) {p : GPath c.graph (n + 1)} (hp : p ∈ GPath.nbPaths c.graph a (n + 1)) :
    (p.stabPath : Subgroup c.G0).relIndex ((p.take n (Nat.le_succ n)).stabPath : Subgroup c.G0) =
      Nat.card ↥(burnsideF4b_extSet (p.take n (Nat.le_succ n))) := by
  set r : GPath c.graph n := p.take n (Nat.le_succ n) with hr
  have hrp : ∀ i, i ≤ n → r i = p i := fun i hi => GPath.take_apply_of_le _ _ _ hi
  have hr_nb : r ∈ GPath.nbPaths c.graph a n :=
    ⟨by rw [hrp 0 (Nat.zero_le n)]; exact hp.1, hp.2.take n _⟩
  have hGp : (p.stabPath : Subgroup c.G0) ≤ (r.stabPath : Subgroup c.G0) := by
    intro g hg i hi
    rw [hrp i hi]
    exact hg i (by omega)
  have hmem : ∀ g : c.G0, g ∈ (r.stabPath : Subgroup c.G0) → (g ∈ (p.stabPath : Subgroup c.G0) ↔
      g • p (n + 1) = p (n + 1)) := by
    intro g hg
    constructor
    · intro h
      exact h (n + 1) le_rfl
    · intro h i hi
      by_cases hin : i ≤ n
      · rw [← hrp i hin]; exact hg i hin
      · have : i = n + 1 := by omega
        subst this
        exact h
  have hstab : MulAction.stabilizer (r.stabPath : Subgroup c.G0) (p (n + 1)) =
      (p.stabPath : Subgroup c.G0).subgroupOf (r.stabPath : Subgroup c.G0) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact (hmem g.1 g.2).symm
  have horb : MulAction.orbit (r.stabPath : Subgroup c.G0) (p (n + 1)) = burnsideF4b_extSet r := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      have hg : ∀ i, i ≤ n → (g : c.G0) • r i = r i := g.2
      refine ⟨?_, fun h1 => ?_⟩
      · have h := (GraphAction.adj_smul (g : c.G0) (p n) (p (n + 1))).mpr (p.adj n (Nat.lt_succ_self n))
        have e : (g : c.G0) • p n = p n := by rw [← hrp n le_rfl]; exact hg n le_rfl
        rw [e] at h
        rw [hrp n le_rfl]
        exact h
      · intro heq
        have e1 : (g : c.G0) • p (n - 1) = p (n - 1) := by
          rw [← hrp (n - 1) (by omega)]; exact hg (n - 1) (by omega)
        have e2 : (g : c.G0) • p (n + 1) = (g : c.G0) • p (n - 1) := by
          show (g : c.G0) • p (n + 1) = _
          rw [e1, ← hrp (n - 1) (by omega)]
          exact heq
        have := MulAction.injective (g : c.G0) e2
        exact hp.2 (n - 1) (by omega) (by rw [show n - 1 + 2 = n + 1 by omega]; exact this.symm)
    · intro hw
      have hy : c.graph.Adj (r n) (p (n + 1)) := by
        rw [hrp n le_rfl]; exact p.adj n (Nat.lt_succ_self n)
      have hy1 : 1 ≤ n → p (n + 1) ≠ r (n - 1) := by
        intro h1 heq
        rw [hrp (n - 1) (by omega)] at heq
        exact hp.2 (n - 1) (by omega) (by rw [show n - 1 + 2 = n + 1 by omega]; exact heq.symm)
      obtain ⟨g, hga, hgr, hgw⟩ := GPath.exists_fix_path_smul_eq hval htrans hn hr_nb hy hw.1
        hy1 hw.2
      refine ⟨⟨g, fun i hi => ?_⟩, hgw⟩
      have := congrArg (fun q : GPath c.graph n => q i) hgr
      simpa using this
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

theorem burnsideF4b_relIndex_pathNum [Finite α.G1] [Finite α.G2] (hc : c.IsFaithful)
    (hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b) {m : ℕ} {a : c.Γ}
    (htrans : ∀ q q' : GPath c.graph (m + 1), q ∈ GPath.nbPaths c.graph a (m + 1) →
      q' ∈ GPath.nbPaths c.graph a (m + 1) → ∃ g : c.G0, g • a = a ∧ g • q = q') :
    ∀ n : ℕ, n ≤ m + 1 → ∀ p : GPath c.graph n, p ∈ GPath.nbPaths c.graph a n →
      (p.stabPath : Subgroup c.G0).relIndex (stv c a) = α.pathNum (CosetGeom.vtype a) n := by
  intro n
  induction n with
  | zero =>
    intro _ p hp
    have : (p.stabPath : Subgroup c.G0) = stv c a := by
      ext g
      rw [GPath.mem_stabPath_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        have := h 0 le_rfl
        rwa [hp.1] at this
      · intro h i hi
        have : i = 0 := by omega
        subst this
        rw [hp.1]
        exact h
    rw [this, Subgroup.relIndex_self]
    rfl
  | succ n ih =>
    intro hn p hp
    set r : GPath c.graph n := p.take n (Nat.le_succ n) with hr
    have hrp : ∀ i, i ≤ n → r i = p i := fun i hi => GPath.take_apply_of_le _ _ _ hi
    have hr_nb : r ∈ GPath.nbPaths c.graph a n :=
      ⟨by rw [hrp 0 (Nat.zero_le n)]; exact hp.1, hp.2.take n _⟩
    have h1 := burnsideF4b_relIndex_succ hc hval htrans (by omega : n ≤ m) hp
    have h2 := ih (by omega) r hr_nb
    have hGp : (p.stabPath : Subgroup c.G0) ≤ (r.stabPath : Subgroup c.G0) := by
      intro g hg i hi
      rw [hrp i hi]
      exact hg i (by omega)
    have hGr : (r.stabPath : Subgroup c.G0) ≤ stv c a := GPath.stabPath_le_stabilizer r hr_nb.1
    have h3 := Subgroup.relIndex_mul_relIndex (p.stabPath : Subgroup c.G0)
      (r.stabPath : Subgroup c.G0) (stv c a) hGp hGr
    rw [h1, h2, burnsideF4b_card_extSet hc r, hr_nb.1] at h3
    rw [← h3]
    have hv : CosetGeom.vtype (r n) = if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a :=
      vtype_path_end (c := c) ⟨r, hr_nb⟩
    show _ = α.pathNum (CosetGeom.vtype a) n *
      (if n = 0 then α.qv (CosetGeom.vtype a) + 1
        else α.qv (if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a))
    rw [mul_comm]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte, hv]

end IndexFormula

section Eight

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y} {m : ℕ}

theorem burnsideF4b_TC.facts46 (T : burnsideF4b_TC c m) (hm2 : 2 ≤ m) : Facts46 c m := by
  have hm := T.hm
  refine ⟨T.faithful, T.thick1, T.thick2, hm2, ?_, ?_, ?_, ?_⟩
  · intro n hn a p hp
    exact ⟨T.dist_nbPath hn.le hp, fun q hq0 hqn hqg => T.unique_geod hn hp hq0 hqn hqg⟩
  · intro a p hp
    exact T.dist_nbPath le_rfl hp
  · intro a p hp
    rcases T.alt hp with ⟨-, hi⟩ | ⟨-, hii⟩
    · exact Or.inl hi
    · exact Or.inr (T.geods_bij hii)
  · intro a _ q q' hq hq'
    exact GPath.trans_le T.hval (T.trans a) 1 m (by omega) q q' hq hq'

theorem burnsideF4b_lemma_F46_8 (T : burnsideF4b_TC c m) {Qx Ql : Subgroup c.G0}
    (hQ : QNormalized Qx Ql)
    (hbase : ∀ (b : Bool) (q : GPath c.graph m),
      q ∈ GPath.nbPaths c.graph (c.baseVert b) m →
      IsComplementIn q.stabPath (cond b Ql Qx) (stv c (c.baseVert b) ⊓ stv c (q 1)))
    (a : c.Γ) {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    c.graph.dist a (p m) = m ∧
    ((∀ t : GPath c.graph m, t 0 = a → t m = p m → t.IsGeodesic → t = p) ∨
      (IsComplementIn (stv c a ⊓ stv c (p m)) (c.Qvert Qx Ql a) (stv c a) ∧
        (∀ t₁ t₂ t₃ t₄ : GPath c.graph m, t₁ ∈ c.geods m a (p m) →
          t₂ ∈ c.geods m a (p m) → t₃ ∈ c.geods m a (p m) → t₄ ∈ c.geods m a (p m) →
          t₁ ≠ t₂ → t₃ ≠ t₄ → ∃ g : c.G0, g • a = a ∧ g • p m = p m ∧ g • t₁ = t₃ ∧
            g • t₂ = t₄) ∧
        Set.BijOn (fun t : GPath c.graph m => t 1) (c.geods m a (p m)) (CosetGeom.nbrs a))) := by
  have hm := T.hm
  refine ⟨T.dist_nbPath le_rfl hp, ?_⟩
  rcases T.alt hp with ⟨-, hi⟩ | ⟨-, hii⟩
  · exact Or.inl hi
  right
  have hc := burnsideF4b_complement_of_base hQ hbase a hp
  refine ⟨⟨hc.1.trans inf_le_left, inf_le_left, ?_, ?_⟩, hii.2.1, T.geods_bij hii⟩
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx1 := hc.1 hx.1
    have hx2 : x ∈ p.stabPath := by
      rw [T.stabPath_eq hp]
      exact ⟨hx1, hx.2.2⟩
    have : x ∈ c.Qvert Qx Ql a ⊓ p.stabPath := ⟨hx.1, hx2⟩
    rw [hc.2.2.1] at this
    exact this
  · intro g hg
    have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg
    have hadj : c.graph.Adj a (p 1) := by
      rw [← hp.1]; exact p.adj 0 (by omega)
    have hadj' : c.graph.Adj a (g • p 1) := by
      have := (GraphAction.adj_smul g a (p 1)).mpr hadj
      rwa [hga] at this
    obtain ⟨h, hha, hhb, hhy⟩ := T.trans_nbrs hii hadj hadj'
    have hmem : h⁻¹ * g ∈ stv c a ⊓ stv c (p 1) := by
      refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
      · rw [mul_smul, hga, inv_smul_eq_iff]; exact hha.symm
      · rw [mul_smul, ← hhy, inv_smul_smul]
    obtain ⟨q, hq, k, hk, hqk⟩ := hc.2.2.2 _ hmem
    have hkab : k ∈ stv c a ⊓ stv c (p m) := by
      rw [T.stabPath_eq hp] at hk
      exact ⟨hk.1.1, hk.2⟩
    have hhK : h ∈ stv c a ⊓ stv c (p m) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hha, MulAction.mem_stabilizer_iff.mpr hhb⟩
    have hconj : conjSub h (c.Qvert Qx Ql a) = c.Qvert Qx Ql a := by
      rw [← Qvert_smul hQ h a, hha]
    refine ⟨h * q * h⁻¹, ?_, h * k, (stv c a ⊓ stv c (p m)).mul_mem hhK hkab, ?_⟩
    · rw [← hconj]; exact mul_mem_conjSub hq
    · calc h * q * h⁻¹ * (h * k) = h * (q * k) := by group
        _ = g := by rw [hqk]; group

end Eight

section ComplPath

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7

theorem burnsideF4b_TC.compl_path {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {m : ℕ} (T : burnsideF4b_TC c m) {Q : Subgroup c.G0} {u : c.Γ}
    (hcompl : ∀ v : c.Γ, c.graph.dist u v = m →
      IsComplementIn (stv c u ⊓ stv c v) Q (stv c u))
    (hQle : ∀ w : c.Γ, c.graph.Adj u w → Q ≤ stv c w)
    {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph u m) :
    IsComplementIn p.stabPath Q (stv c u ⊓ stv c (p 1)) := by
  have hm := T.hm
  have hd : c.graph.dist u (p m) = m := T.dist_nbPath le_rfl hp
  have h1 := hcompl (p m) hd
  have hadj : c.graph.Adj u (p 1) := by
    rw [← hp.1]; exact p.adj 0 (by omega)
  have hQ : Q ≤ stv c u ⊓ stv c (p 1) := le_inf h1.1 (hQle _ hadj)
  have h2 := h1.inf_left hQ inf_le_left
  have e : (p.stabPath : Subgroup c.G0) = (stv c u ⊓ stv c (p m)) ⊓ (stv c u ⊓ stv c (p 1)) := by
    rw [T.stabPath_eq hp]
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [e]
  exact h2

end ComplPath

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_F46Body (κ : GLKind) (p : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) : Prop :=
    (∀ a : β.Γ,
      (IsLieExtAmalgam M₁ M₂ → β.PathTrans a (κ.m + 1)) ∧
      ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) →
        (CosetGeom.vtype a = false → β.PathTrans a κ.m) ∧
        (CosetGeom.vtype a = true →
          β.PathTrans a (κ.m - 1) ∧
          (∃ q₁ ∈ GPath.nbPaths β.graph a κ.m, ∃ q₂ ∈ GPath.nbPaths β.graph a κ.m,
            GPath.nbPaths β.graph a κ.m = pathOrbit (stv β a) q₁ ∪ pathOrbit (stv β a) q₂ ∧
            Disjoint (pathOrbit (stv β a) q₁) (pathOrbit (stv β a) q₂) ∧
            Nat.card ↥(pathOrbit (stv β a) q₁) = Nat.card ↥(pathOrbit (stv β a) q₂)) ∧
          ∀ q₁ ∈ GPath.nbPaths β.graph a κ.m, ∀ q₂ ∈ GPath.nbPaths β.graph a κ.m, q₁ κ.m = q₂ κ.m →
            ∃ g ∈ stv β a ⊓ stv β (q₁ κ.m), g • q₁ = q₂))) ∧
    (∃ r : PermQuasiEquiv ↥(stv ι ι.xv) (PathSet ι.graph ι.xv) ↥(stv β β.xv) (PathSet β.graph β.xv),
        (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
          ((r.grp ⟨f1 (c := ι) a, MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a)⟩ : ↥(stv β β.xv)) :
            β.G0) = f1 (c := β) a) ∧
        ∀ pp : PathSet ι.graph ι.xv, (r.set pp).1 = pp.1 ∧ (pp.NoBack ↔ (r.set pp).NoBack)) ∧
    (∃ r : PermQuasiEquiv ↥(stv ι ι.lv) (PathSet ι.graph ι.lv) ↥(stv β β.lv) (PathSet β.graph β.lv),
        (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2,
          ((r.grp ⟨f2 (c := ι) a, MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)⟩ : ↥(stv β β.lv)) :
            β.G0) = f2 (c := β) a) ∧
        ∀ pp : PathSet ι.graph ι.lv, (r.set pp).1 = pp.1 ∧ (pp.NoBack ↔ (r.set pp).NoBack)) ∧
    (∀ n : ℕ, n ≤ κ.m → ∀ a : β.Γ, ∀ q : GPath β.graph n, q ∈ GPath.nbPaths β.graph a n →
      (0 < n → ¬ ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) ∧ CosetGeom.vtype a = true ∧ n = κ.m) →
        (∀ j : ℕ, n = 2 * j + 1 → (q.stabPath : Subgroup β.G0).relIndex (stv β a) =
          (qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1) *
            ((RankTwoAmalgam.ofSubgroups M₁ M₂).qOne * (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo) ^ j) ∧
        (∀ j : ℕ, n = 2 * j + 2 → (q.stabPath : Subgroup β.G0).relIndex (stv β a) =
          (qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1) *
            ((RankTwoAmalgam.ofSubgroups M₁ M₂).qOne * (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo) ^ j *
            qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (!CosetGeom.vtype a))) ∧
      (n < κ.m →
        (∀ u ∈ CosetGeom.sphere n a, ∀ v ∈ CosetGeom.sphere n a, ∃ g ∈ stv β a, g • u = v) ∧
        q n ∈ CosetGeom.sphere n a ∧ q.IsGeodesic ∧
        (∀ r : GPath β.graph n, r 0 = a → r n = q n → r.IsGeodesic → r = q) ∧
        (2 ≤ n → ∀ S : Set β.Γ, ¬ IsPolygon β.graph S (2 * n)) ∧
        Nat.card ↥(CosetGeom.sphere n a) = (q.stabPath : Subgroup β.G0).relIndex (stv β a))) ∧
    (∀ a : β.Γ, ∀ q : GPath β.graph κ.m, q ∈ GPath.nbPaths β.graph a κ.m →
      (IsComplementIn (q.stabPath : Subgroup β.G0) (Qu p Gp β (q κ.m))
          (stv β (q (κ.m - 1)) ⊓ stv β (q κ.m)) ∨
        ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) ∧ CosetGeom.vtype a = false ∧
          (q.stabPath : Subgroup β.G0) ⊓ Qu p Gp β (q κ.m) = ⊥ ∧
          (Qu p Gp β (q κ.m) ⊔ (q.stabPath : Subgroup β.G0)).relIndex
            (stv β (q (κ.m - 1)) ⊓ stv β (q κ.m)) = 2)) ∧
      (q κ.m ∈ CosetGeom.sphere κ.m a ∧
        (∀ r ∈ GPath.nbPaths β.graph a κ.m, r.IsGeodesic ∧ r κ.m ∈ CosetGeom.sphere κ.m a) ∧
        ((∀ r : GPath β.graph κ.m, r 0 = a → r κ.m = q κ.m → r.IsGeodesic → r = q) ∨
          (IsComplementIn (stv β a ⊓ stv β (q κ.m)) (Qu p Gp β a) (stv β a) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m), q₁ ≠ q₂ →
              ∀ r₁ ∈ β.geods κ.m a (q κ.m), ∀ r₂ ∈ β.geods κ.m a (q κ.m), r₁ ≠ r₂ →
                ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) =
              qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)) ∨
          ((Gp = ⊤ ∧ κ = .Tits) ∧ CosetGeom.vtype a = false ∧
            Nonempty (↥(stv β a ⊓ stv β (q κ.m)) ≃* DihedralGroup 5) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m),
              ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) = 5 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)) ∨
          ((Gp = ⊤ ∧ κ = .G2d) ∧ CosetGeom.vtype a = false ∧
            Nonempty (↥(stv β a ⊓ stv β (q κ.m)) ≃* Multiplicative (ZMod 3)) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m),
              ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) = 3 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)))))

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F46_of_body
    (h : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ → burnsideF4b_F46Body κ p Gp M₁ M₂ β ι) :
    F_4_6 := h

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_LieFacts : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → IsLieExtAmalgam M₁ M₂ →
      (∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (κ.m + 1)) ∧
      (∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.dist u v = κ.m →
        IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) u)
          (stv (incl M₁ M₂) u))

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 in
theorem burnsideF4b_qv_mul (α : RankTwoAmalgam.{0}) (b : Bool) :
    α.qv b * α.qv (!b) = α.qOne * α.qTwo := by
  cases b
  · rfl
  · exact mul_comm _ _

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 in
theorem burnsideF4b_F46Body_ext (hL : burnsideF4b_LieFacts) (hP : burnsideF4b_Parabolics) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hκ : ¬ (κ = .G2d ∨ κ = .Tits)) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) (hι : ι = incl M₁ M₂) :
    burnsideF4b_F46Body κ p Gp M₁ M₂ β ι := by
  subst hι
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have hext : IsLieExtAmalgam M₁ M₂ := ⟨κ, p, f, Gp, not_or.mp hκ, hyp⟩
  have hthick := burnsideF4b_thick hP hyp
  have hm : 2 ≤ κ.m := by cases κ <;> simp [GLKind.m]
  have hN : Gp.Normal := hyp.normal
  have hparab := hP κ p f E Gp M₁ M₂ hyp
  have hQle := burnsideF4b_pCoreOf_le (burnsideF4a_prime_of_isGenLie hyp.model) hparab
  have hιtrans : ∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (κ.m + 1) :=
    (hL κ p f E Gp M₁ M₂ hyp hext).1
  have hιcompl : ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.dist u v = κ.m →
      IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) u)
        (stv (incl M₁ M₂) u) := (hL κ p f E Gp M₁ M₂ hyp hext).2
  have hTι : burnsideF4b_TC (incl M₁ M₂) κ.m :=
    ⟨incl_faithful M₁ M₂, hthick.1, hthick.2, hιtrans, by omega⟩
  have hβtrans : ∀ a : β.Γ, β.PathTrans a (κ.m + 1) := fun a =>
    pathTrans_transfer β hβ (incl M₁ M₂) (incl_faithful M₁ M₂) (κ.m + 1) hιtrans a
  have hTβ : burnsideF4b_TC β κ.m := ⟨hβ, hthick.1, hthick.2, hβtrans, by omega⟩
  have Fβ : β.Facts46 κ.m := hTβ.facts46 hm
  have hQβ := burnsideF4b_QNormalized p hN β
  have hQι := burnsideF4b_QNormalized p hN (incl M₁ M₂)
  have hbaseι : ∀ (b : Bool) (q : GPath (incl M₁ M₂).graph κ.m),
      q ∈ GPath.nbPaths (incl M₁ M₂).graph ((incl M₁ M₂).baseVert b) κ.m →
      IsComplementIn q.stabPath (cond b (Ql p Gp (incl M₁ M₂)) (Qx p Gp (incl M₁ M₂)))
        (stv (incl M₁ M₂) ((incl M₁ M₂).baseVert b) ⊓ stv (incl M₁ M₂) (q 1)) := by
    intro b q hq
    have e := Qvert_baseVert hQι b
    have hQle' : ∀ w : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj ((incl M₁ M₂).baseVert b) w →
        cond b (Ql p Gp (incl M₁ M₂)) (Qx p Gp (incl M₁ M₂)) ≤ stv (incl M₁ M₂) w := by
      intro w hw
      cases b
      · exact burnsideF4b_Qx_le_stv p hN hQle.1 (incl M₁ M₂) hw
      · exact burnsideF4b_Ql_le_stv p hN hQle.2 (incl M₁ M₂) hw
    refine hTι.compl_path (fun v hv => ?_) hQle' hq
    have := hιcompl ((incl M₁ M₂).baseVert b) v hv
    unfold Qu at this
    rwa [e] at this
  have hbaseβ : ∀ (b : Bool) (q : GPath β.graph κ.m),
      q ∈ GPath.nbPaths β.graph (β.baseVert b) κ.m →
      IsComplementIn q.stabPath (cond b (Ql p Gp β) (Qx p Gp β))
        (stv β (β.baseVert b) ⊓ stv β (q 1)) := by
    intro b q hq
    cases b
    · exact burnsideF4b_transfer_x hβ (incl_faithful M₁ M₂) (by omega : 1 ≤ κ.m)
        ((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁) (fun q' hq' => hbaseι false q' hq') hq
    · exact burnsideF4b_transfer_l hβ (incl_faithful M₁ M₂) (by omega : 1 ≤ κ.m)
        ((pCoreOf p (Gp ⊓ M₂)).subgroupOf M₂) (fun q' hq' => hbaseι true q' hq') hq
  have hthree := burnsideF4a_F46_three β hβ (incl M₁ M₂) (incl_faithful M₁ M₂)
  refine ⟨fun a => ⟨fun _ => hβtrans a, fun h => absurd h.2 hκ⟩, hthree.1, hthree.2, ?_, ?_⟩
  · intro n hn a q hq
    refine ⟨fun hn0 _ => ?_, fun hnm => ?_⟩
    · have hidx := burnsideF4b_relIndex_pathNum hβ hTβ.hval (hTβ.trans a) n (by omega) q hq
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [hidx, hj, RankTwoAmalgam.pathNum_odd, burnsideF4b_qv_mul]
        rfl
      · rw [hidx, hj, RankTwoAmalgam.pathNum_even, burnsideF4b_qv_mul]
        rfl
    · refine ⟨fun u hu v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨g, hga, hgv⟩ := hTβ.trans_sphere hnm.le a hu hv
        exact ⟨g, MulAction.mem_stabilizer_iff.mpr hga, hgv⟩
      · exact hTβ.dist_nbPath hnm.le hq
      · show β.graph.dist (q 0) (q n) = n
        rw [hq.1]
        exact hTβ.dist_nbPath hnm.le hq
      · intro r hr0 hrn hrg
        exact hTβ.unique_geod hnm hq hr0 hrn hrg
      · intro h2 S
        exact Fβ.no_polygon h2 hnm S
      · rw [Nat.card_coe_set_eq]
        exact hTβ.lemma_F46_7 hnm hq
  · intro a q hq
    have hm1 : 1 ≤ κ.m := by omega
    refine ⟨Or.inl (burnsideF4b_complement_end hQβ hm1 hbaseβ a hq), ?_⟩
    obtain ⟨hd, hcase⟩ := burnsideF4b_lemma_F46_8 hTβ hQβ hbaseβ a hq
    refine ⟨hd, fun r hr => ⟨?_, Fβ.dist_m a r hr⟩, ?_⟩
    · show β.graph.dist (r 0) (r κ.m) = κ.m
      rw [hr.1]
      exact Fβ.dist_m a r hr
    · rcases hcase with hi | ⟨hc, h2, hb⟩
      · exact Or.inl hi
      · refine Or.inr (Or.inl ⟨hc, ?_, ?_, hb⟩)
        · intro q₁ hq₁ q₂ hq₂ hne r₁ hr₁ r₂ hr₂ hne'
          obtain ⟨g, hga, hgb, h1, h2'⟩ := h2 q₁ q₂ r₁ r₂ hq₁ hq₂ hr₁ hr₂ hne hne'
          exact ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hga, MulAction.mem_stabilizer_iff.mpr hgb⟩,
            h1, h2'⟩
        · rw [Nat.card_congr (hb.equiv _), burnsideF4b_card_nbrs hβ a]
          rfl

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_IotaSmall_of (hF : burnsideF4b_Facts46All) (h5 : F_4_5) :
    burnsideF4b_IotaSmall := by
  intro κ p f E _ Gp M₁ M₂ hyp
  haveI := hyp.finite
  have Fι := hF κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂)
  obtain ⟨S, hS⟩ := (h5 κ p f E Gp M₁ M₂ hyp (incl M₁ M₂) rfl).1.polygon
  exact Fι.isSmall_of_polygon hS

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
def burnsideF4b_F46Exc : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → (κ = .G2d ∨ κ = .Tits) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ → burnsideF4b_F46Body κ p Gp M₁ M₂ β ι

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4b_F46 (hL : burnsideF4b_LieFacts) (hP : burnsideF4b_Parabolics)
    (hexc : burnsideF4b_F46Exc) : F_4_6 :=
  burnsideF4b_F46_of_body fun κ p f E _ Gp M₁ M₂ hyp Y _ β hβ ι hι => by
    by_cases hκ : κ = .G2d ∨ κ = .Tits
    · exact hexc κ p f E Gp M₁ M₂ hyp hκ Y β hβ ι hι
    · exact burnsideF4b_F46Body_ext hL hP hyp hκ β hβ ι hι

open CFSG.ASVolI.ChF in
theorem burnsideF4b_F417 (h8 : F_4_8) : F_4_17 :=
  fun κ p f E _ Gp M₁ M₂ hyp _ => h8 κ p f E Gp M₁ M₂ hyp

end CFSG.ASVolI

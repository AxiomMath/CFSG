module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Delta

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

section Extend

variable {V : Type} {H : Type} [Group H] [MulAction H V] {Γ : SimpleGraph V}
  [GraphAction H Γ] {n : ℕ} {Good : ∀ s : ℕ, GPath Γ s → Prop}

namespace GoodPathSystem

theorem existsUnique_extendTo (hG : GoodPathSystem H Γ n Good) {s t : ℕ}
    (p : GPath Γ s) (hs : n + 1 ≤ s) (hst : s ≤ t) (hp : Good s p) :
    ∃! q : GPath Γ t, Good t q ∧ ∀ i, i ≤ s → q i = p i := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨p, ⟨hp, fun _ _ => rfl⟩, fun q hq => GPath.ext' hq.2⟩
  | succ t ht ih =>
    obtain ⟨q, ⟨hqq, hqp⟩, hqu⟩ := ih
    obtain ⟨w, ⟨hw, hwg⟩, hwu⟩ := hG.extend t q (le_trans hs ht) hqq
    refine ⟨q.snoc w hw, ⟨hwg, fun i hi => ?_⟩, fun r hr => ?_⟩
    · rw [GPath.snoc_of_le _ _ _ (le_trans hi ht)]
      exact hqp i hi
    · have hrt : r.take t (Nat.le_succ t) = q := by
        refine hqu (r.take t (Nat.le_succ t))
          ⟨hG.take (t + 1) r t (Nat.le_succ t) hr.1, fun i hi => ?_⟩
        rw [GPath.take_apply_of_le _ _ _ (le_trans hi ht)]
        exact hr.2 i hi
      have hqt : q t = r t := by
        rw [← hrt, GPath.take_apply_of_le _ _ _ le_rfl]
      have hradj : Γ.Adj (q t) (r (t + 1)) := by
        rw [hqt]
        exact r.adj t (Nat.lt_succ_self t)
      have hlast : r (t + 1) = w := by
        refine hwu (r (t + 1)) ⟨hradj, ?_⟩
        have he : q.snoc (r (t + 1)) hradj = r := by
          refine GPath.ext' fun i hi => ?_
          rcases Nat.lt_or_ge i (t + 1) with hlt | hge
          · rw [GPath.snoc_of_le _ _ _ (by omega)]
            rw [← hrt, GPath.take_apply_of_le _ _ _ (by omega)]
          · have hlast' : i = t + 1 := by omega
            subst hlast'
            rw [GPath.snoc_last]
        rw [he]
        exact hr.1
      refine GPath.ext' fun i hi => ?_
      rcases Nat.lt_or_ge i (t + 1) with hlt | hge
      · have hi' : i ≤ t := by omega
        rw [← GPath.take_apply_of_le r t (Nat.le_succ t) hi', hrt,
          GPath.snoc_of_le _ _ _ hi']
      · have hi' : i = t + 1 := by omega
        subst hi'
        rw [hlast, GPath.snoc_last]

end GoodPathSystem

end Extend

section Hat

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

noncomputable def hatFun (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (n : ℕ) (z z' : c.Γ) (a : c.G0) (u : c.Γ) :
    c.Γ :=
  if c.graph.dist z u ≤ n - 1 then a • u
  else if h : ∃ p : GPath c.graph (2 * n), Good _ p ∧ p 0 = u ∧ p (n - 1) = z' ∧ p n = z ∧
      p (n + 1) = a⁻¹ • z' then a • (Classical.choose h) (2 * n)
  else a • u

theorem hatFun_of_dist_le {z z' : c.Γ} {a : c.G0} {u : c.Γ}
    (hu : c.graph.dist z u ≤ n - 1) : hatFun c Good n z z' a u = a • u := by
  unfold hatFun
  rw [if_pos hu]

theorem dist_smul_right (a : c.G0) (x v : c.Γ) :
    c.graph.dist x (a • v) = c.graph.dist (a⁻¹ • x) v := by
  rw [← GPath.dist_smul (CosetGeom.connected rfl) a⁻¹ x (a • v), inv_smul_smul]

section Setup

variable {z z' : c.Γ} {a : c.G0}

theorem adj_base_edge
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) : c.graph.Adj z z' := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CosetGeom.adj_γ₀_γ₁
  · exact CosetGeom.adj_γ₀_γ₁.symm

theorem mem_edgeBall_iff (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (r : ℕ) (u : c.Γ) :
    u ∈ edgeBall r c ↔
      c.graph.dist z u ≤ r ∨ c.graph.dist z' u ≤ r := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [edgeBall, Set.mem_setOf_eq]
  · simp only [edgeBall, Set.mem_setOf_eq]
    exact Or.comm

private theorem adj_z_inv_smul_z' (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (ha : a • z = z) : c.graph.Adj z (a⁻¹ • z') := by
  have h1 : a⁻¹ • z = z := inv_smul_eq_iff.mpr ha.symm
  have h2 : c.graph.Adj (a⁻¹ • z') (a⁻¹ • z) :=
    (GraphAction.adj_smul a⁻¹ z' z).mpr (adj_base_edge hz).symm
  rw [h1] at h2
  exact h2.symm

theorem dist_eq_of_far (hn : 3 ≤ n)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {u : c.Γ}
    (hu : u ∈ edgeBall (n - 1) c) (hnot : ¬ c.graph.dist z u ≤ n - 1) :
    c.graph.dist z u = n ∧ c.graph.dist z' u = n - 1 := by
  have hlt : c.graph.dist z' u < n := by
    have hle : c.graph.dist z' u ≤ n - 1 := by
      rcases (mem_edgeBall_iff hz (n - 1) u).mp hu with h | h
      · exact absurd h hnot
      · exact h
    exact Nat.lt_of_le_pred (by omega) hle
  have hge : n ≤ c.graph.dist z u := by omega
  have hd := GPath.dist_adj_succ_or (CosetGeom.connected rfl)
    (fun x y hxy => CosetGeom.vtype_ne_of_adj hxy) u (adj_base_edge hz)
  rw [SimpleGraph.dist_comm (u := u) (v := z'), SimpleGraph.dist_comm (u := u) (v := z)] at hd
  clear hu hnot
  rcases hd with h | h
  · exfalso
    have h1 : n ≤ c.graph.dist z' u := by
      rw [h]
      exact Nat.le_trans hge (Nat.le_succ _)
    exact absurd hlt (Nat.not_lt.mpr h1)
  · have h1 : c.graph.dist z u ≤ n := by
      rw [h]
      exact Nat.lt_iff_add_one_le.mp hlt
    have h2 : c.graph.dist z u = n := le_antisymm h1 hge
    refine ⟨h2, ?_⟩
    rw [h2] at h
    set a := c.graph.dist z' u with ha
    omega

theorem uniqueGeod_succ (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth) :
    UniqueGeod c.graph (n + 1) := by
  refine uniqueGeod_of_le_egirth (CosetGeom.connected rfl) ?_
  rwa [show 2 * (n + 1) = 2 * n + 2 by omega]

theorem exists_good_path_of_far (hn : 3 ≤ n)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    (hz' : a • z' ≠ z') {u : c.Γ} (hu : u ∈ edgeBall (n - 1) c)
    (hnot : ¬ c.graph.dist z u ≤ n - 1) :
    ∃ p : GPath c.graph (2 * n), Good (2 * n) p ∧ p 0 = u ∧ p (n - 1) = z' ∧ p n = z ∧
      p (n + 1) = a⁻¹ • z' := by
  obtain ⟨hdz, hdz'⟩ := dist_eq_of_far hn hz hu hnot
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  obtain ⟨g, hg0, hgN, hgnb⟩ :=
    GPath.exists_geodesic' (n := n - 1) hconn u z'
      (by rw [SimpleGraph.dist_comm]; exact hdz')
  have hgeo : g.IsGeodesic := by
    show c.graph.dist (g 0) (g (n - 1)) = n - 1
    rw [hg0, hgN, SimpleGraph.dist_comm]
    exact hdz'
  have hxy : c.graph.Adj z z' := adj_base_edge hz
  have h1 : c.graph.Adj (g (n - 1)) z := hgN.symm ▸ hxy.symm
  have h2 : c.graph.Adj ((g.snoc z h1) ((n - 1) + 1)) (a⁻¹ • z') :=
    (GPath.snoc_last g z h1).symm ▸ adj_z_inv_smul_z' hz ha
  set q : GPath c.graph (n - 1 + 1 + 1) := (g.snoc z h1).snoc (a⁻¹ • z') h2 with hqdef
  have hq_le : ∀ i, i ≤ n - 1 → q i = g i := by
    intro i hi
    rw [hqdef, GPath.snoc_of_le _ _ _ (by omega), GPath.snoc_of_le _ _ _ hi]
  have hq0 : q 0 = u := by
    rw [hq_le 0 (Nat.zero_le _)]
    exact hg0
  have hqN1 : q (n - 1) = z' := by
    rw [hq_le (n - 1) le_rfl]
    exact hgN
  have hqN : q ((n - 1) + 1) = z := by
    rw [hqdef, GPath.snoc_of_le _ _ _ le_rfl]
    exact GPath.snoc_last g z h1
  have hqN2 : q ((n - 1) + 1 + 1) = a⁻¹ • z' := by
    rw [hqdef]
    exact GPath.snoc_last _ _ _
  have hqnb : q.NoBack := by
    intro i hi
    by_cases hc1 : i + 2 ≤ n - 1
    · rw [hq_le i (by omega), hq_le (i + 2) hc1]
      exact hgnb i hc1
    · by_cases hc2 : i + 2 = (n - 1) + 1
      · rw [hq_le i (by omega), show q (i + 2) = z from by rw [hc2]; exact hqN]
        intro hgz
        have hpi : c.graph.dist u (g i) = i := by
          have h := GPath.dist_prefix hconn g hgeo (i := i) (by omega)
          rwa [hg0] at h
        have huz : c.graph.dist u z = n := by rw [SimpleGraph.dist_comm]; exact hdz
        rw [hgz, huz] at hpi
        omega
      · have hc3 : i + 2 = (n - 1) + 1 + 1 := by omega
        rw [show q i = z' from by rw [show i = n - 1 by omega]; exact hqN1,
          show q (i + 2) = a⁻¹ • z' from by rw [hc3]; exact hqN2]
        intro heq
        apply hz'
        have h : a • z' = a • (a⁻¹ • z') := by rw [← heq]
        rwa [← mul_smul, mul_inv_cancel, one_smul] at h
  have hqgood : Good ((n - 1) + 1 + 1) q := hG.short _ q (by omega) hqnb
  obtain ⟨p, ⟨hpgood, hpeq⟩, -⟩ :=
    hG.existsUnique_extendTo (s := (n - 1) + 1 + 1) (t := 2 * n) q
      (show n + 1 ≤ (n - 1) + 1 + 1 by omega)
      (show (n - 1) + 1 + 1 ≤ 2 * n by omega) hqgood
  have hpn : p n = p ((n - 1) + 1) := by congr 1; omega
  have hpn2 : p (n + 1) = p ((n - 1) + 1 + 1) := by congr 1; omega
  refine ⟨p, hpgood, ?_, ?_, ?_, ?_⟩
  · rw [hpeq 0 (by omega), hq0]
  · rw [hpeq (n - 1) (by omega), hqN1]
  · rw [hpn, hpeq ((n - 1) + 1) (by omega), hqN]
  · rw [hpn2, hpeq ((n - 1) + 1 + 1) (by omega), hqN2]

theorem hatFun_of_smul_eq (hn : 3 ≤ n) (hG : GoodPathSystem c.G0 c.graph n Good) {z z' : c.Γ}
    {a : c.G0} (hz' : a • z' = z') (u : c.Γ) :
    hatFun c Good n z z' a u = a • u := by
  by_cases hd : c.graph.dist z u ≤ n - 1
  · exact hatFun_of_dist_le hd
  · have hempty : ¬ ∃ p : GPath c.graph (2 * n), Good (2 * n) p ∧ p 0 = u ∧
        p (n - 1) = z' ∧ p n = z ∧ p (n + 1) = a⁻¹ • z' := by
      rintro ⟨p, hp, -, h1, h2, h3⟩
      have hnb : p.NoBack := hG.noBack (2 * n) p hp
      have hzinv : a⁻¹ • z' = z' := inv_smul_eq_iff.mpr hz'.symm
      have heq : p (n - 1) = p (n + 1) := by rw [h1, h3, hzinv]
      refine hnb (n - 1) (show n - 1 + 2 ≤ 2 * n by omega) ?_
      rwa [show n - 1 + 2 = n + 1 by omega]
    unfold hatFun
    rw [if_neg hd, dif_neg hempty]

theorem hatFun_eq_of_good (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {z z' : c.Γ} {a : c.G0} {u : c.Γ}
    {p : GPath c.graph (2 * n)} (hp : Good (2 * n) p) (hp0 : p 0 = u)
    (hpn1 : p (n - 1) = z') (hpn : p n = z) (hpn2 : p (n + 1) = a⁻¹ • z') :
    hatFun c Good n z z' a u = a • p (2 * n) := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ x y, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun x y h => CosetGeom.vtype_ne_of_adj h
  have hnb : p.NoBack := hG.noBack (2 * n) p hp
  have hgeop : (p.take (n - 1) (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
      (show n - 1 ≤ n + 1 by omega) _ (hnb.take (n - 1) (by omega))
  have hduz : c.graph.dist u z = n := by
    have h : (p.take n (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU n
        (show n ≤ n + 1 by omega) _ (hnb.take n (by omega))
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le n),
      GPath.take_apply_of_le _ _ _ le_rfl, hp0, hpn] at h
    exact h
  have hnot : ¬ c.graph.dist z u ≤ n - 1 := by
    rw [SimpleGraph.dist_comm, hduz]
    omega
  have hex : ∃ p : GPath c.graph (2 * n), Good (2 * n) p ∧ p 0 = u ∧ p (n - 1) = z' ∧
      p n = z ∧ p (n + 1) = a⁻¹ • z' := ⟨p, hp, hp0, hpn1, hpn, hpn2⟩
  set q : GPath c.graph (2 * n) := Classical.choose hex with hqdef
  have hqspec : Good (2 * n) q ∧ q 0 = u ∧ q (n - 1) = z' ∧ q n = z ∧
      q (n + 1) = a⁻¹ • z' := Classical.choose_spec hex
  obtain ⟨hqgood, hq0, hqN1, hqN, hqN2⟩ := hqspec
  have hqnb : q.NoBack := hG.noBack (2 * n) q hqgood
  have hpre : ∀ i, i ≤ n - 1 → q i = p i := by
    intro i hi
    have htake : q.take (n - 1) (by omega) = p.take (n - 1) (by omega) := by
      refine hU (n - 1) _ _ ?_ ?_ ?_ ?_ (by omega)
      · exact GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
          (show n - 1 ≤ n + 1 by omega) _ (hqnb.take _ _)
      · exact hgeop
      · rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
          GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]
        exact hq0.trans hp0.symm
      · rw [GPath.take_apply_of_le _ _ _ le_rfl, GPath.take_apply_of_le _ _ _ le_rfl]
        exact hqN1.trans hpn1.symm
    rw [← GPath.take_apply_of_le q (n - 1) (by omega) hi,
      ← GPath.take_apply_of_le p (n - 1) (by omega) hi, htake]
  have hagree : ∀ i, i ≤ n + 1 → q i = p.take (n + 1) (by omega) i := by
    intro i hi
    rw [GPath.take_apply_of_le _ _ _ hi]
    by_cases hi1 : i ≤ n - 1
    · exact hpre i hi1
    · have hi2 : i = n ∨ i = n + 1 := by omega
      rcases hi2 with rfl | rfl
      · exact hqN.trans hpn.symm
      · exact hqN2.trans hpn2.symm
  unfold hatFun
  rw [if_neg hnot, dif_pos hex]
  congr 1
  have hpt : Good (n + 1) (p.take (n + 1) (by omega)) := hG.take (2 * n) p (n + 1) (by omega) hp
  obtain ⟨r, ⟨hrgood, hreq⟩, hruniq⟩ :=
    hG.existsUnique_extendTo (s := n + 1) (t := 2 * n) (p.take (n + 1) (by omega)) le_rfl
      (show n + 1 ≤ 2 * n by omega) hpt
  have hqr : q = r := by
    refine hruniq q ⟨hqgood, ?_⟩
    intro i hi
    exact hagree i hi
  have hpr : p = r := by
    refine hruniq p ⟨hp, ?_⟩
    intro i hi
    exact (GPath.take_apply_of_le p (n + 1) _ hi).symm
  have h1 : (Classical.choose hex) = r := hqr
  have h2 : p = r := hpr
  exact (congrArg (fun x : GPath c.graph (2 * n) => x.toFun (2 * n)) h1).trans
    (congrArg (fun x : GPath c.graph (2 * n) => x.toFun (2 * n)) h2).symm

theorem hatFun_mem_edgeBall (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    {u : c.Γ} (hu : u ∈ edgeBall (n - 1) c) :
    hatFun c Good n z z' a u ∈ edgeBall (n - 1) c := by
  rw [mem_edgeBall_iff hz (n - 1)]
  by_cases hd : c.graph.dist z u ≤ n - 1
  · left
    rw [hatFun_of_dist_le hd, GPath.dist_smul_fix (CosetGeom.connected rfl) ha]
    exact hd
  · right
    have hfar : c.graph.dist z' u ≤ n - 1 := by
      rcases (mem_edgeBall_iff hz (n - 1) u).mp hu with h | h
      · exact absurd h hd
      · exact h
    by_cases hz' : a • z' = z'
    · rw [hatFun_of_smul_eq hn hG hz' u, dist_smul_right, inv_smul_eq_iff.mpr hz'.symm]
      exact hfar
    · obtain ⟨p, hp, hp0, hpn1, hpn, hpn2⟩ :=
        exists_good_path_of_far hn hG hz ha hz' hu hd
      rw [hatFun_eq_of_good hn hgirth hG hp hp0 hpn1 hpn hpn2, dist_smul_right]
      have hdrop := GPath.dist_le_length (CosetGeom.connected rfl) (p.drop (n + 1) (by omega))
      rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl, Nat.add_zero,
        show n + 1 + (2 * n - (n + 1)) = 2 * n by omega,
        show 2 * n - (n + 1) = n - 1 by omega, hpn2] at hdrop
      exact hdrop

theorem hatFun_inv_hatFun (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    {u : c.Γ} (hu : u ∈ edgeBall (n - 1) c) :
    hatFun c Good n z z' a⁻¹ (hatFun c Good n z z' a u) = u := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ x y, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun x y h => CosetGeom.vtype_ne_of_adj h
  by_cases hd : c.graph.dist z u ≤ n - 1
  · have h1 : c.graph.dist z (hatFun c Good n z z' a u) ≤ n - 1 := by
      rw [hatFun_of_dist_le hd, GPath.dist_smul_fix (CosetGeom.connected rfl) ha]
      exact hd
    rw [hatFun_of_dist_le h1, hatFun_of_dist_le hd, ← mul_smul, inv_mul_cancel, one_smul]
  · obtain ⟨hdz, hdz'⟩ := dist_eq_of_far hn hz hu hd
    by_cases hz' : a • z' = z'
    · rw [hatFun_of_smul_eq hn hG hz' u,
        hatFun_of_smul_eq (a := a⁻¹) hn hG (inv_smul_eq_iff.mpr hz'.symm) (a • u),
        ← mul_smul, inv_mul_cancel, one_smul]
    · obtain ⟨p, hp, hp0, hpn1, hpn, hpn2⟩ :=
        exists_good_path_of_far hn hG hz ha hz' hu hd
      have hhat : hatFun c Good n z z' a u = a • p (2 * n) :=
        hatFun_eq_of_good hn hgirth hG hp hp0 hpn1 hpn hpn2
      have hdzp : c.graph.dist z (p (2 * n)) = n := by
        have hnb : p.NoBack := hG.noBack (2 * n) p hp
        have hgeo : (p.drop n (by omega)).IsGeodesic :=
          GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (2 * n - n)
            (show 2 * n - n ≤ n + 1 by omega) _ (hnb.drop n (by omega))
        rw [GPath.IsGeodesic, GPath.drop_apply _ _ _ (Nat.zero_le _),
          GPath.drop_apply _ _ _ le_rfl, Nat.add_zero,
          show n + (2 * n - n) = 2 * n by omega, show 2 * n - n = n by omega, hpn] at hgeo
        exact hgeo
      have hfar : ¬ c.graph.dist z (a • p (2 * n)) ≤ n - 1 := by
        rw [GPath.dist_smul_fix (CosetGeom.connected rfl) ha, hdzp]
        omega
      have hrgood : Good (2 * n) (a • p.rev) := hG.smul (2 * n) a p.rev (hG.rev (2 * n) p hp)
      have hr0 : (a • p.rev) 0 = a • p (2 * n) := by
        rw [GPath.smul_apply, GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero]
      have hrN1 : (a • p.rev) (n - 1) = z' := by
        rw [GPath.smul_apply, GPath.rev_apply _ (by omega),
          show 2 * n - (n - 1) = n + 1 by omega, hpn2, ← mul_smul, mul_inv_cancel, one_smul]
      have hrN : (a • p.rev) n = z := by
        rw [GPath.smul_apply, GPath.rev_apply _ (by omega),
          show 2 * n - n = n by omega, hpn, ha]
      have hrN2 : (a • p.rev) (n + 1) = (a⁻¹)⁻¹ • z' := by
        rw [GPath.smul_apply, GPath.rev_apply _ (by omega),
          show 2 * n - (n + 1) = n - 1 by omega, hpn1]
        rw [inv_inv]
      rw [hhat, hatFun_eq_of_good (a := a⁻¹) hn hgirth hG hrgood hr0 hrN1 hrN hrN2]
      rw [GPath.smul_apply, GPath.rev_apply _ le_rfl, Nat.sub_self, hp0, ← mul_smul,
        inv_mul_cancel, one_smul]

end Setup

end Hat

end CFSG.Quasithin.Stroth.WeissDelta

end

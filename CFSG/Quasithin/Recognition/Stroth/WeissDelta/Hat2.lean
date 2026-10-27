module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Hat

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

section Adj

variable {z z' : c.Γ} {a : c.G0}

private def deltaRel (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (n : ℕ) (u v : c.Γ) : Prop :=
  (c.graph.Adj u v ∧ (u ∈ edgeBall (n - 2) c ∨ v ∈ edgeBall (n - 2) c)) ∨
    TypeB c Good n u v

private theorem delta_adj_iff {u v : ↥(edgeBall (n - 1) c)} :
    (delta c Good n).Adj u v ↔
      u ≠ v ∧ (deltaRel c Good n ↑u ↑v ∨ deltaRel c Good n ↑v ↑u) :=
  SimpleGraph.fromRel_adj _ _ _

private theorem typeB_of_middle (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {p : GPath c.graph (2 * n - 1)} (hp : Good (2 * n - 1) p)
    (hmid : (p (n - 1) = z ∧ p n = z') ∨ (p (n - 1) = z' ∧ p n = z)) :
    TypeB c Good n (p 0) (p (2 * n - 1)) := by
  refine ⟨p, hp, rfl, rfl, ?_⟩
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

private theorem typeB_middle_of (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {u v : c.Γ} (h : TypeB c Good n u v) :
    ∃ p : GPath c.graph (2 * n - 1), Good (2 * n - 1) p ∧ p 0 = u ∧ p (2 * n - 1) = v ∧
      ((p (n - 1) = z ∧ p n = z') ∨ (p (n - 1) = z' ∧ p n = z)) := by
  obtain ⟨p, hp, hp0, hpv, hmid⟩ := h
  refine ⟨p, hp, hp0, hpv, ?_⟩
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hmid
  · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

private theorem dist_le_succ_of_mem_edgeBall (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {r : ℕ} {u : c.Γ} (hu : u ∈ edgeBall r c) : c.graph.dist z u ≤ r + 1 := by
  rcases (mem_edgeBall_iff hz r u).mp hu with h | h
  · omega
  · have hd := GPath.dist_adj_succ_or (CosetGeom.connected rfl)
      (fun x y hxy => CosetGeom.vtype_ne_of_adj hxy) u (adj_base_edge hz)
    rw [SimpleGraph.dist_comm (u := u) (v := z'), SimpleGraph.dist_comm (u := u) (v := z)] at hd
    rcases hd with hd | hd
    · set d := c.graph.dist z u with hd1
      set d' := c.graph.dist z' u with hd2
      omega
    · rw [hd]
      exact Nat.add_le_add_right h 1

private theorem smul_mem_edgeBall (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {b : c.G0} (hb : b • z = z) (hb' : b • z' = z') {r : ℕ} {u : c.Γ}
    (hu : u ∈ edgeBall r c) : b • u ∈ edgeBall r c := by
  rcases (mem_edgeBall_iff hz r u).mp hu with h | h
  · refine (mem_edgeBall_iff hz r (b • u)).mpr (Or.inl ?_)
    rw [GPath.dist_smul_fix (CosetGeom.connected rfl) hb]
    exact h
  · refine (mem_edgeBall_iff hz r (b • u)).mpr (Or.inr ?_)
    rw [dist_smul_right b, inv_smul_eq_iff.mpr hb'.symm]
    exact h

private theorem deltaRel_smul (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {b : c.G0}
    (hb : b • z = z) (hb' : b • z' = z') {u v : c.Γ} (h : deltaRel c Good n u v) :
    deltaRel c Good n (b • u) (b • v) := by
  rcases h with ⟨hadj, h2 | h2⟩ | hB
  · exact Or.inl ⟨(GraphAction.adj_smul b u v).mpr hadj, Or.inl (smul_mem_edgeBall hz hb hb' h2)⟩
  · exact Or.inl ⟨(GraphAction.adj_smul b u v).mpr hadj, Or.inr (smul_mem_edgeBall hz hb hb' h2)⟩
  · obtain ⟨q, hq, hq0, hqv, hmid⟩ := typeB_middle_of hz hB
    have hmid' : ((b • q) (n - 1) = z ∧ (b • q) n = z') ∨
        ((b • q) (n - 1) = z' ∧ (b • q) n = z) := by
      rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [GPath.smul_apply, h1, hb], by rw [GPath.smul_apply, h2, hb']⟩
      · exact Or.inr ⟨by rw [GPath.smul_apply, h1, hb'], by rw [GPath.smul_apply, h2, hb]⟩
    have hTB := typeB_of_middle hz (hG.smul (2 * n - 1) b q hq) hmid'
    refine Or.inr ?_
    rwa [show (b • q) 0 = b • u from by rw [GPath.smul_apply, hq0],
      show (b • q) (2 * n - 1) = b • v from by rw [GPath.smul_apply, hqv]] at hTB

private theorem deltaRel_hat_of_near {z z' : c.Γ} {a : c.G0}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z) {u v : c.Γ}
    (hu : c.graph.dist z u ≤ n - 1) (hv : c.graph.dist z v ≤ n - 1)
    (hadj : c.graph.Adj u v) :
    deltaRel c Good n (hatFun c Good n z z' a u) (hatFun c Good n z z' a v) := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ x y, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun x y h => CosetGeom.vtype_ne_of_adj h
  rw [hatFun_of_dist_le hu, hatFun_of_dist_le hv]
  refine Or.inl ⟨(GraphAction.adj_smul a u v).mpr hadj, ?_⟩
  rcases GPath.dist_adj_succ_or hconn hc z hadj with h | h
  · left
    refine (mem_edgeBall_iff hz (n - 2) (a • u)).mpr (Or.inl ?_)
    rw [GPath.dist_smul_fix (CosetGeom.connected rfl) ha]
    set du := c.graph.dist z u
    set dv := c.graph.dist z v
    omega
  · right
    refine (mem_edgeBall_iff hz (n - 2) (a • v)).mpr (Or.inl ?_)
    rw [GPath.dist_smul_fix (CosetGeom.connected rfl) ha]
    set du := c.graph.dist z u
    set dv := c.graph.dist z v
    omega

private theorem deltaRel_hat_of_near_far (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    (hne : a • z' ≠ z') {u v : c.Γ} (hu : u ∈ edgeBall (n - 1) c)
    (hfar : ¬ c.graph.dist z u ≤ n - 1) (hadj : c.graph.Adj u v)
    (hv2 : v ∈ edgeBall (n - 2) c) :
    deltaRel c Good n (hatFun c Good n z z' a v) (hatFun c Good n z z' a u) := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ x y, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun x y h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  obtain ⟨hdu, hdu'⟩ := dist_eq_of_far hn hz hu hfar
  have hvv : c.graph.dist z v ≤ n - 1 := by
    have h := dist_le_succ_of_mem_edgeBall hz hv2
    set dv := c.graph.dist z v
    omega
  have hzv : c.graph.dist z v = n - 1 := by
    rcases GPath.dist_adj_succ_or hconn hc z hadj with h | h
    · exfalso
      have h1 : c.graph.dist z v ≤ n - 1 := hvv
      set du := c.graph.dist z u
      set dv := c.graph.dist z v
      omega
    · set du := c.graph.dist z u
      set dv := c.graph.dist z v
      omega
  have hzv' : c.graph.dist z' v = n - 2 := by
    have hle : c.graph.dist z' v ≤ n - 2 := by
      rcases (mem_edgeBall_iff hz (n - 2) v).mp hv2 with h | h
      · exfalso
        set dv := c.graph.dist z v
        omega
      · exact h
    have hd := GPath.dist_adj_succ_or (CosetGeom.connected rfl)
      (fun x y hxy => CosetGeom.vtype_ne_of_adj hxy) v (adj_base_edge hz)
    rw [SimpleGraph.dist_comm (u := v) (v := z'), SimpleGraph.dist_comm (u := v) (v := z)] at hd
    rcases hd with h | h
    · exfalso
      set dv := c.graph.dist z v
      set dv' := c.graph.dist z' v
      omega
    · set dv := c.graph.dist z v
      set dv' := c.graph.dist z' v
      omega
  obtain ⟨p, hp, hp0, hpn1, hpn, hpn2⟩ := exists_good_path_of_far hn hG hz ha hne hu hfar
  have hhatv : hatFun c Good n z z' a v = a • v := hatFun_of_dist_le hvv
  have hhatu : hatFun c Good n z z' a u = a • p (2 * n) :=
    hatFun_eq_of_good hn hgirth hG hp hp0 hpn1 hpn hpn2
  have hp1 : p 1 = v := by
    have hnb : p.NoBack := hG.noBack (2 * n) p hp
    have hgeo : (p.take (n - 1) (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
        (show n - 1 ≤ n + 1 by omega) _ (hnb.take (n - 1) (by omega))
    have hle : c.graph.dist (p 1) z' ≤ n - 2 := by
      have h := GPath.dist_le_sub hconn (p.take (n - 1) (by omega)) (i := 1) (j := n - 1)
        (by omega) le_rfl
      rw [GPath.take_apply_of_le _ _ _ (show 1 ≤ n - 1 by omega),
        GPath.take_apply_of_le _ _ _ le_rfl, hpn1] at h
      exact h
    have hd1 : c.graph.dist (p 1) z' = n - 2 := by
      have h1 : c.graph.dist (p 0) (p 1) = 1 := by
        rw [SimpleGraph.dist_eq_one_iff_adj]
        exact p.adj 0 (by omega)
      have h2 : c.graph.dist (p 0) z' = n - 1 := by rw [hp0, SimpleGraph.dist_comm]; exact hdu'
      have h3 : c.graph.dist (p 0) z' ≤ c.graph.dist (p 0) (p 1) + c.graph.dist (p 1) z' :=
        hconn.dist_triangle
      set d1 := c.graph.dist (p 1) z'
      omega
    have hlt : c.graph.dist z' u < n + 1 := by rw [hdu']; omega
    have hd2 : c.graph.dist z' (p 1) + 1 = c.graph.dist z' u := by
      rw [← SimpleGraph.dist_comm (u := p 1) (v := z'), hd1, hdu']
      omega
    have hd3 : c.graph.dist z' v + 1 = c.graph.dist z' u := by rw [hzv', hdu']; omega
    exact (eq_of_adj_of_dist_succ_of_le_egirth hconn hgirth hlt hadj
      (by rw [← hp0]; exact p.adj 0 (by omega)) hd3 hd2).symm
  let hk : 1 ≤ 2 * n := by omega
  let r : GPath c.graph (2 * n - 1) := p.drop 1 hk
  have hr : ∀ i, i ≤ 2 * n - 1 → r i = p (1 + i) := fun i hi => GPath.drop_apply p 1 hk hi
  have hgp : Good (2 * n - 1) r := hG.drop (2 * n) p 1 hk hp
  have e0 : r 0 = p 1 := by rw [hr 0 (Nat.zero_le _), Nat.add_zero]
  have e1 : r (n - 1) = p n := by
    rw [hr (n - 1) (by omega), show 1 + (n - 1) = n by omega]
  have e2 : r n = p (n + 1) := by
    rw [hr n (by omega), show 1 + n = n + 1 by omega]
  have e3 : r (2 * n - 1) = p (2 * n) := by
    rw [hr (2 * n - 1) le_rfl, show 1 + (2 * n - 1) = 2 * n by omega]
  have hmid : ((a • r) (n - 1) = z ∧ (a • r) n = z') ∨
      ((a • r) (n - 1) = z' ∧ (a • r) n = z) := by
    left
    refine ⟨?_, ?_⟩
    · rw [GPath.smul_apply, e1, hpn, ha]
    · rw [GPath.smul_apply, e2, hpn2, ← mul_smul, mul_inv_cancel, one_smul]
  have hTB := typeB_of_middle hz (hG.smul (2 * n - 1) a r hgp) hmid
  have h0 : (a • r) 0 = a • v := by rw [GPath.smul_apply, e0, hp1]
  have hlast : (a • r) (2 * n - 1) = a • p (2 * n) := by
    rw [GPath.smul_apply, e3]
  rw [hhatv, hhatu]
  exact Or.inr (by rwa [h0, hlast] at hTB)

private theorem deltaRel_hat_of_typeB_mid (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    (hne : a • z' ≠ z') {u v : c.Γ}
    {q : GPath c.graph (2 * n - 1)} (hq : Good (2 * n - 1) q) (hq0 : q 0 = u)
    (hqv : q (2 * n - 1) = v) (hmid1 : q (n - 1) = z') (hmid2 : q n = z) :
    deltaRel c Good n (hatFun c Good n z z' a u) (hatFun c Good n z z' a v) ∨
      deltaRel c Good n (hatFun c Good n z z' a v) (hatFun c Good n z z' a u) := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ x y, c.graph.Adj x y → CosetGeom.vtype x ≠ CosetGeom.vtype y :=
    fun x y h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hqnb : q.NoBack := hG.noBack (2 * n - 1) q hq
  have hduz : c.graph.dist u z = n := by
    have hgeo : (q.take n (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU n
        (show n ≤ n + 1 by omega) _ (hqnb.take n (by omega))
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le n),
      GPath.take_apply_of_le _ _ _ le_rfl, hq0, hmid2] at hgeo
    exact hgeo
  have hdu' : c.graph.dist z' u = n - 1 := by
    have hgeo : (q.take (n - 1) (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
        (show n - 1 ≤ n + 1 by omega) _ (hqnb.take (n - 1) (by omega))
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le (n - 1)),
      GPath.take_apply_of_le _ _ _ le_rfl, hq0, hmid1] at hgeo
    rw [SimpleGraph.dist_comm]
    exact hgeo
  have hfar : ¬ c.graph.dist z u ≤ n - 1 := by
    rw [SimpleGraph.dist_comm, hduz]
    omega
  have hu : u ∈ edgeBall (n - 1) c :=
    (mem_edgeBall_iff hz (n - 1) u).mpr (Or.inr (by rw [hdu']))
  have hvv : c.graph.dist z v ≤ n - 1 := by
    have h := GPath.dist_le_length hconn (q.drop n (by omega))
    rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl, Nat.add_zero,
      show n + (2 * n - 1 - n) = 2 * n - 1 by omega,
      show 2 * n - 1 - n = n - 1 by omega, hmid2, hqv] at h
    exact h
  have hhatv : hatFun c Good n z z' a v = a • v := hatFun_of_dist_le hvv
  obtain ⟨p, hp, hp0, hpn1, hpn, hpn2⟩ := exists_good_path_of_far hn hG hz ha hne hu hfar
  have hhatu : hatFun c Good n z z' a u = a • p (2 * n) :=
    hatFun_eq_of_good hn hgirth hG hp hp0 hpn1 hpn hpn2
  have hagn : ∀ i, i ≤ n → q i = p i := by
    intro i hi
    by_cases hi1 : i ≤ n - 1
    · have hqgeo : (q.take (n - 1) (by omega)).IsGeodesic :=
        GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
          (show n - 1 ≤ n + 1 by omega) _ (hqnb.take (n - 1) (by omega))
      have hpgeo : (p.take (n - 1) (by omega)).IsGeodesic :=
        GPath.isGeodesic_of_noBack (m := n + 1) hconn hc hU (n - 1)
          (show n - 1 ≤ n + 1 by omega) _ ((hG.noBack (2 * n) p hp).take (n - 1) (by omega))
      have heq : q.take (n - 1) (by omega) = p.take (n - 1) (by omega) := by
        refine hU (n - 1) _ _ hqgeo hpgeo ?_ ?_ (by omega)
        · rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
            GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]
          exact hq0.trans hp0.symm
        · rw [GPath.take_apply_of_le _ _ _ le_rfl, GPath.take_apply_of_le _ _ _ le_rfl]
          exact hmid1.trans hpn1.symm
      rw [← GPath.take_apply_of_le q (n - 1) (by omega) hi1,
        ← GPath.take_apply_of_le p (n - 1) (by omega) hi1, heq]
    · have hi' : i = n := by omega
      subst hi'
      exact hmid2.trans hpn.symm
  by_cases hdeg : q (n + 1) = a⁻¹ • z'
  ·
    have htake : p.take (2 * n - 1) (by omega) = q := by
      have hpt : Good (n + 1) (p.take (n + 1) (by omega)) :=
        hG.take (2 * n) p (n + 1) (by omega) hp
      obtain ⟨r, ⟨hrgood, hreq⟩, hruniq⟩ :=
        hG.existsUnique_extendTo (s := n + 1) (t := 2 * n - 1) (p.take (n + 1) (by omega))
          le_rfl (show n + 1 ≤ 2 * n - 1 by omega) hpt
      have hqr : q = r := by
        refine hruniq q ⟨hq, fun i hi => ?_⟩
        rw [GPath.take_apply_of_le _ _ _ hi]
        by_cases hi1 : i ≤ n
        · exact hagn i hi1
        · have hi2 : i = n + 1 := by omega
          subst hi2
          exact hdeg.trans hpn2.symm
      have hpr : p.take (2 * n - 1) (by omega) = r := by
        refine hruniq (p.take (2 * n - 1) (by omega)) ⟨hG.take (2 * n) p (2 * n - 1) (by omega) hp,
          fun i hi => ?_⟩
        rw [GPath.take_apply_of_le _ _ _ hi,
          GPath.take_apply_of_le _ _ _ (le_trans hi (by omega))]
      exact hpr.trans hqr.symm
    have hpv : p (2 * n - 1) = v := by
      rw [← hqv, ← htake, GPath.take_apply_of_le _ _ _ le_rfl]
    have hav2 : a • v ∈ edgeBall (n - 2) c := by
      have h := GPath.dist_le_length hconn (q.drop (n + 1) (by omega))
      rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl, Nat.add_zero,
        show n + 1 + (2 * n - 1 - (n + 1)) = 2 * n - 1 by omega,
        show 2 * n - 1 - (n + 1) = n - 2 by omega, hdeg, hqv] at h
      exact (mem_edgeBall_iff hz (n - 2) (a • v)).mpr (Or.inr (by rwa [dist_smul_right]))
    have hadj : c.graph.Adj (a • p (2 * n - 1)) (a • p (2 * n)) := by
      have h := p.adj (2 * n - 1) (show 2 * n - 1 < 2 * n by omega)
      rw [show 2 * n - 1 + 1 = 2 * n by omega] at h
      exact (GraphAction.adj_smul a (p (2 * n - 1)) (p (2 * n))).mpr h
    have hav2' : a • p (2 * n - 1) ∈ edgeBall (n - 2) c := by rw [hpv]; exact hav2
    refine Or.inl ?_
    rw [hhatu, hhatv, ← hpv]
    exact Or.inl ⟨hadj.symm, Or.inr hav2'⟩
  ·
    obtain ⟨r, hrgood, hr1, hr2⟩ := hG.lemma3 p q hp hq hagn (by rw [hpn2]; exact hdeg)
    have hpN1 : p ((n - 1) + 1) = p n := by congr 1; omega
    have e1 : r (n - 1) = z := by
      rw [hr2 (n - 1) le_rfl (by omega), hpN1, hpn]
    have e2 : r n = a⁻¹ • z' := by rw [hr2 n (by omega) (by omega), hpn2]
    have hmid : ((a • r) (n - 1) = z ∧ (a • r) n = z') ∨
        ((a • r) (n - 1) = z' ∧ (a • r) n = z) := by
      left
      exact ⟨by rw [GPath.smul_apply, e1, ha],
        by rw [GPath.smul_apply, e2, ← mul_smul, mul_inv_cancel, one_smul]⟩
    have hTB := typeB_of_middle hz (hG.smul (2 * n - 1) a r hrgood) hmid
    have e0 : r 0 = v := by
      rw [hr1 0 (Nat.zero_le _), Nat.sub_zero, hqv]
    have e3 : r (2 * n - 1) = p (2 * n) := by
      rw [hr2 (2 * n - 1) (by omega) le_rfl, show 2 * n - 1 + 1 = 2 * n by omega]
    have h0 : (a • r) 0 = a • v := by rw [GPath.smul_apply, e0]
    have hlast : (a • r) (2 * n - 1) = a • p (2 * n) := by rw [GPath.smul_apply, e3]
    refine Or.inr ?_
    rw [hhatu, hhatv]
    exact Or.inr (by rwa [h0, hlast] at hTB)

private theorem deltaRel_hat_of_typeB (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    (hne : a • z' ≠ z') {u v : c.Γ} (hB : TypeB c Good n u v) :
    deltaRel c Good n (hatFun c Good n z z' a u) (hatFun c Good n z z' a v) ∨
      deltaRel c Good n (hatFun c Good n z z' a v) (hatFun c Good n z z' a u) := by
  obtain ⟨q, hq, hq0, hqv, hmid⟩ := typeB_middle_of hz hB
  rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hqrev : Good (2 * n - 1) q.rev := hG.rev (2 * n - 1) q hq
    have h0 : q.rev 0 = v := by rw [GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero, hqv]
    have hlast : q.rev (2 * n - 1) = u := by
      rw [GPath.rev_apply _ le_rfl, Nat.sub_self, hq0]
    have h1' : q.rev (n - 1) = z' := by
      rw [GPath.rev_apply _ (by omega), show 2 * n - 1 - (n - 1) = n by omega, h2]
    have h2' : q.rev n = z := by
      rw [GPath.rev_apply _ (by omega), show 2 * n - 1 - n = n - 1 by omega, h1]
    exact Or.comm.mp (deltaRel_hat_of_typeB_mid hn hgirth hG hz ha hne hqrev h0 hlast h1' h2')
  · exact deltaRel_hat_of_typeB_mid hn hgirth hG hz ha hne hq hq0 hqv h1 h2

private theorem not_mem_edgeBall_two_of_far (hn : 3 ≤ n)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {u : c.Γ}
    (hu : u ∈ edgeBall (n - 1) c) (hfar : ¬ c.graph.dist z u ≤ n - 1) :
    u ∉ edgeBall (n - 2) c := by
  obtain ⟨h1, h2⟩ := dist_eq_of_far hn hz hu hfar
  intro hmem
  rcases (mem_edgeBall_iff hz (n - 2) u).mp hmem with h | h <;> omega

private theorem deltaRel_hat_of_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    (hne : a • z' ≠ z') {u v : c.Γ} (hu : u ∈ edgeBall (n - 1) c)
    (hv : v ∈ edgeBall (n - 1) c) (hadj : c.graph.Adj u v)
    (h2 : u ∈ edgeBall (n - 2) c ∨ v ∈ edgeBall (n - 2) c) :
    deltaRel c Good n (hatFun c Good n z z' a u) (hatFun c Good n z z' a v) ∨
      deltaRel c Good n (hatFun c Good n z z' a v) (hatFun c Good n z z' a u) := by
  by_cases huA : c.graph.dist z u ≤ n - 1
  · by_cases hvA : c.graph.dist z v ≤ n - 1
    · exact Or.inl (deltaRel_hat_of_near hz ha huA hvA hadj)
    · have hv2 : u ∈ edgeBall (n - 2) c := by
        rcases h2 with h | h
        · exact h
        · exact absurd h (not_mem_edgeBall_two_of_far hn hz hv hvA)
      exact Or.inl (deltaRel_hat_of_near_far hn hgirth hG hz ha hne hv hvA hadj.symm hv2)
  · have hu2 : v ∈ edgeBall (n - 2) c := by
      rcases h2 with h | h
      · exact absurd h (not_mem_edgeBall_two_of_far hn hz hu huA)
      · exact h
    exact Or.inr (deltaRel_hat_of_near_far hn hgirth hG hz ha hne hu huA hadj hu2)

theorem hatFun_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) (ha : a • z = z)
    {u v : ↥(edgeBall (n - 1) c)} (huv : (delta c Good n).Adj u v) :
    (delta c Good n).Adj ⟨hatFun c Good n z z' a u, hatFun_mem_edgeBall hn hgirth hG hz ha u.2⟩
      ⟨hatFun c Good n z z' a v, hatFun_mem_edgeBall hn hgirth hG hz ha v.2⟩ := by
  rw [delta_adj_iff] at huv ⊢
  obtain ⟨hne, hrel⟩ := huv
  have hmemu : (u : c.Γ) ∈ edgeBall (n - 1) c := u.2
  have hmemv : (v : c.Γ) ∈ edgeBall (n - 1) c := v.2
  have hinj : ∀ {x y : c.Γ}, x ∈ edgeBall (n - 1) c → y ∈ edgeBall (n - 1) c →
      hatFun c Good n z z' a x = hatFun c Good n z z' a y → x = y := by
    intro x y hx hy he
    have h1 := hatFun_inv_hatFun hn hgirth hG hz ha hx
    have h2 := hatFun_inv_hatFun hn hgirth hG hz ha hy
    rw [he] at h1
    exact h1.symm.trans h2
  refine ⟨?_, ?_⟩
  · intro he
    exact hne (Subtype.ext (hinj hmemu hmemv (congrArg Subtype.val he)))
  · change deltaRel c Good n (hatFun c Good n z z' a (u : c.Γ)) (hatFun c Good n z z' a (v : c.Γ)) ∨
      deltaRel c Good n (hatFun c Good n z z' a (v : c.Γ)) (hatFun c Good n z z' a (u : c.Γ))
    by_cases hfix : a • z' = z'
    · have h1 : hatFun c Good n z z' a (u : c.Γ) = a • (u : c.Γ) :=
        hatFun_of_smul_eq hn hG hfix (u : c.Γ)
      have h2 : hatFun c Good n z z' a (v : c.Γ) = a • (v : c.Γ) :=
        hatFun_of_smul_eq hn hG hfix (v : c.Γ)
      rcases hrel with h | h
      · exact Or.inl (by rw [h1, h2]; exact deltaRel_smul hG hz ha hfix h)
      · exact Or.inr (by rw [h1, h2]; exact deltaRel_smul hG hz ha hfix h)
    · rcases hrel with (⟨hadj, h2⟩ | hB) | (⟨hadj, h2⟩ | hB)
      · exact deltaRel_hat_of_adj hn hgirth hG hz ha hfix hmemu hmemv hadj h2
      · exact deltaRel_hat_of_typeB hn hgirth hG hz ha hfix hB
      · exact Or.comm.mp (deltaRel_hat_of_adj hn hgirth hG hz ha hfix hmemv hmemu hadj h2)
      · exact Or.comm.mp (deltaRel_hat_of_typeB hn hgirth hG hz ha hfix hB)

end Adj

section Perm

@[expose] noncomputable def hatPerm (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {z : c.Γ} (z' : c.Γ)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (a : ↥(MulAction.stabilizer c.G0 z)) : Equiv.Perm ↥(edgeBall (n - 1) c) where
  toFun u := ⟨hatFun c Good n z z' (a : c.G0) u,
    hatFun_mem_edgeBall hn hgirth hG hz (MulAction.mem_stabilizer_iff.mp a.2) u.2⟩
  invFun u := ⟨hatFun c Good n z z' ((a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) : c.G0) u,
    hatFun_mem_edgeBall hn hgirth hG hz
      (inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp a.2).symm) u.2⟩
  left_inv u := Subtype.ext
    (hatFun_inv_hatFun hn hgirth hG hz (MulAction.mem_stabilizer_iff.mp a.2) u.2)
  right_inv u := Subtype.ext (by
    have h := hatFun_inv_hatFun (a := ((a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) : c.G0))
      hn hgirth hG hz (inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp a.2).symm) u.2
    have h2 : ((a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) : c.G0)⁻¹ = (a : c.G0) := by
      rw [show ((a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) : c.G0) = (a : c.G0)⁻¹ from rfl,
        inv_inv]
    rwa [h2] at h)

theorem hatPerm_inv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {z : c.Γ} (z' : c.Γ)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (a : ↥(MulAction.stabilizer c.G0 z)) :
    (hatPerm hn hgirth hG z' hz a)⁻¹ =
      hatPerm hn hgirth hG z' hz (a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) := by
  refine Equiv.ext fun u => Subtype.ext ?_
  rfl

theorem hatPerm_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {z : c.Γ} (z' : c.Γ)
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (a : ↥(MulAction.stabilizer c.G0 z)) {u v : ↥(edgeBall (n - 1) c)} :
    (delta c Good n).Adj (hatPerm hn hgirth hG z' hz a u) (hatPerm hn hgirth hG z' hz a v) ↔
      (delta c Good n).Adj u v := by
  constructor
  · intro h
    have h' : (delta c Good n).Adj
        ((hatPerm hn hgirth hG z' hz (a⁻¹ : ↥(MulAction.stabilizer c.G0 z)))
          (hatPerm hn hgirth hG z' hz a u))
        ((hatPerm hn hgirth hG z' hz (a⁻¹ : ↥(MulAction.stabilizer c.G0 z)))
          (hatPerm hn hgirth hG z' hz a v)) :=
      hatFun_adj (a := ((a⁻¹ : ↥(MulAction.stabilizer c.G0 z)) : c.G0)) hn hgirth hG hz
        (inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp a.2).symm) h
    have e1 : (hatPerm hn hgirth hG z' hz (a⁻¹ : ↥(MulAction.stabilizer c.G0 z)))
        (hatPerm hn hgirth hG z' hz a u) = u := by
      rw [← hatPerm_inv]
      exact Equiv.symm_apply_apply _ _
    have e2 : (hatPerm hn hgirth hG z' hz (a⁻¹ : ↥(MulAction.stabilizer c.G0 z)))
        (hatPerm hn hgirth hG z' hz a v) = v := by
      rw [← hatPerm_inv]
      exact Equiv.symm_apply_apply _ _
    rwa [e1, e2] at h'
  · intro h
    exact hatFun_adj hn hgirth hG hz (MulAction.mem_stabilizer_iff.mp a.2) h

@[expose] noncomputable def hatX (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) : Equiv.Perm ↥(edgeBall (n - 1) c) :=
  hatPerm hn hgirth hG c.lv (Or.inl ⟨rfl, rfl⟩) a

@[expose] noncomputable def hatY (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) : Equiv.Perm ↥(edgeBall (n - 1) c) :=
  hatPerm hn hgirth hG c.xv (Or.inr ⟨rfl, rfl⟩) a

theorem hatX_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) (u : ↥(edgeBall (n - 1) c)) :
    ((hatX hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) =
      hatFun c Good n c.xv c.lv (a : c.G0) (u : c.Γ) := rfl

theorem hatY_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) (u : ↥(edgeBall (n - 1) c)) :
    ((hatY hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) =
      hatFun c Good n c.lv c.xv (a : c.G0) (u : c.Γ) := rfl

theorem hatX_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) {u v : ↥(edgeBall (n - 1) c)} :
    (delta c Good n).Adj (hatX hn hgirth hG a u) (hatX hn hgirth hG a v) ↔
      (delta c Good n).Adj u v :=
  hatPerm_adj hn hgirth hG c.lv (Or.inl ⟨rfl, rfl⟩) a

theorem hatY_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) {u v : ↥(edgeBall (n - 1) c)} :
    (delta c Good n).Adj (hatY hn hgirth hG a u) (hatY hn hgirth hG a v) ↔
      (delta c Good n).Adj u v :=
  hatPerm_adj hn hgirth hG c.xv (Or.inr ⟨rfl, rfl⟩) a

theorem hatX_of_smul_eq (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) (ha : (a : c.G0) • c.lv = c.lv)
    (u : ↥(edgeBall (n - 1) c)) :
    ((hatX hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) = (a : c.G0) • (u : c.Γ) := by
  rw [hatX_apply]
  exact hatFun_of_smul_eq hn hG ha (u : c.Γ)

theorem hatY_of_smul_eq (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) (ha : (a : c.G0) • c.xv = c.xv)
    (u : ↥(edgeBall (n - 1) c)) :
    ((hatY hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) = (a : c.G0) • (u : c.Γ) := by
  rw [hatY_apply]
  exact hatFun_of_smul_eq hn hG ha (u : c.Γ)

end Perm

end CFSG.Quasithin.Stroth.WeissDelta

end

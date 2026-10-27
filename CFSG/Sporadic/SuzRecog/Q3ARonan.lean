module

public import CFSG.Sporadic.SuzRecog.Q3AGraph
public import CFSG.Sporadic.Co1Patterson.GraphRonan

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup SimpleGraph CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  Check CFSG.Sporadic.Co1Patterson CFSG.Monster.B.Recog

theorem reachable_smul (g : ↥suzM) {u v : Vtx} (h : a4Graph.Reachable u v) :
    a4Graph.Reachable (g • u) (g • v) :=
  h.map (conjIso g).toHom

theorem dist_smul_le (g : ↥suzM) {u v : Vtx} (h : a4Graph.Reachable u v) :
    a4Graph.dist (g • u) (g • v) ≤ a4Graph.dist u v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc a4Graph.dist (g • u) (g • v) ≤ (p.map (conjIso g).toHom).length := dist_le _
    _ = a4Graph.dist u v := by rw [Walk.length_map, hp]

theorem dist_smul (g : ↥suzM) (u v : Vtx) : a4Graph.dist (g • u) (g • v) = a4Graph.dist u v := by
  by_cases h : a4Graph.Reachable u v
  · refine le_antisymm (dist_smul_le g h) ?_
    have := dist_smul_le g⁻¹ (reachable_smul g h)
    rwa [inv_smul_smul, inv_smul_smul] at this
  · have h' : ¬ a4Graph.Reachable (g • u) (g • v) := fun h' => h (by
      have := reachable_smul g⁻¹ h'
      rwa [inv_smul_smul, inv_smul_smul] at this)
    rw [dist_eq_zero_of_not_reachable h, dist_eq_zero_of_not_reachable h']

theorem exists_mid_of_length_two {u w : Vtx} (p : a4Graph.Walk u w) (hp : p.length = 2) :
    ∃ c, a4Graph.Adj u c ∧ a4Graph.Adj c w := by
  cases p with
  | nil => simp only [Walk.length_nil] at hp; omega
  | cons h₁ p =>
    cases p with
    | nil => simp only [Walk.length_cons, Walk.length_nil] at hp; omega
    | cons h₂ p =>
      cases p with
      | nil => exact ⟨_, h₁, h₂⟩
      | cons h₃ p => simp only [Walk.length_cons] at hp; omega

theorem preconnected_image (g : ↥suzM) {S : Set Vtx} (h : (a4Graph.induce S).Preconnected) :
    (a4Graph.induce ((g • ·) '' S)).Preconnected := by
  let f : a4Graph.induce S →g a4Graph.induce ((g • ·) '' S) :=
    { toFun := fun x => ⟨g • x.1, x.1, x.2, rfl⟩
      map_rel' := fun h => a4Graph_adj_smul g h }
  rintro ⟨_, u, hu, rfl⟩ ⟨_, w, hw, rfl⟩
  exact (h ⟨u, hu⟩ ⟨w, hw⟩).map f

theorem ronanSet_smul (g : ↥suzM) (a b : Vtx) (n : ℕ) :
    {c | a4Graph.Adj (g • a) c ∧ a4Graph.dist c (g • b) = n} =
      (g • ·) '' {c | a4Graph.Adj a c ∧ a4Graph.dist c b = n} := by
  ext c
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ • c, ⟨?_, ?_⟩, smul_inv_smul g c⟩
    · rw [← a4Graph_adj_smul_iff g, smul_inv_smul]
      exact h1
    · rw [← dist_smul g, smul_inv_smul]
      exact h2
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨a4Graph_adj_smul g h1, by rw [dist_smul]; exact h2⟩

theorem q2Good_of_data {a b g c c' : Vtx} (hbg : a4Graph.Adj b g) (hac : a4Graph.Adj a c)
    (hcb : a4Graph.Adj c b) (hgc' : a4Graph.Adj g c') (hc'a : a4Graph.Adj c' a)
    (h : c = c' ∨ a4Graph.Adj c c') : Q2Good a4Graph a b g := by
  refine .pent hac hcb hbg hgc' hc'a ?_
  rcases h with rfl | h
  · exact .centre hac.symm hcb hgc'.symm
  · exact .rot (.rot (.rot (.rot (.chord (Or.inr h.symm)))))

theorem rootDist_le_three (r : ℕ) : rootDist r ≤ 3 := by
  unfold rootDist
  split_ifs <;> omega

theorem rootDist_of_ne {r : ℕ} (h0 : r ≠ 0) :
    rootDist r = if isNbr0 r then 1 else if (nbrsOf r).any isNbr0 then 2 else 3 := by
  rw [rootDist, ite_eq_right (by simpa using h0)]

theorem rootDist_eq_three {r : ℕ} (h : rootDist r = 3) :
    r ≠ 0 ∧ isNbr0 r = false ∧ ∀ y ∈ nbrsOf r, isNbr0 y = false := by
  by_cases h0 : r = 0
  · subst h0
    simp [rootDist] at h
  rw [rootDist_of_ne h0] at h
  by_cases h1 : isNbr0 r = true
  · rw [ite_eq_left h1] at h
    omega
  rw [ite_eq_right h1] at h
  by_cases h2 : (nbrsOf r).any isNbr0 = true
  · rw [ite_eq_left h2] at h
    omega
  refine ⟨h0, Bool.eq_false_iff.2 h1, fun y hy => ?_⟩
  exact Bool.eq_false_iff.2 fun hy' => h2 (Array.any_eq_true'.2 ⟨y, hy, hy'⟩)

section Check


theorem vDist_eq {k : ℕ} (hk : k < 22880) : vDist k = rootDist froot[k]! := by
  obtain ⟨hrlt, hrr, -⟩ := forest_node hk
  unfold vDist distArr
  rw [ite_eq_left hk, getElem!_map_range hrlt]
  simp [hrr]

theorem exists_nbr_two {r : ℕ} (hr : r < 22880) (hrr : froot[r]! = r) (h3 : rootDist r = 3) :
    ∃ y ∈ nbrsOf r, vDist y = 2 := by
  have h := Array.all_eq_true'.1 distOK_true r (mem_roots.2 ⟨hr, hrr⟩)
  simp only [h3, bne_self_eq_false, Bool.false_or] at h
  obtain ⟨y, hy, hy2⟩ := Array.any_eq_true'.1 h
  exact ⟨y, hy, by simpa using hy2⟩

end Check

theorem dist_root_le_two (hN : NrhoBound) {r : ℕ} (hr : r < 22880) (hrd : rootDist r ≤ 2) :
    a4Graph.Reachable v0 (vtx r) ∧ a4Graph.dist v0 (vtx r) = rootDist r := by
  by_cases h0 : r = 0
  · subst h0
    rw [vtx_zero, show rootDist 0 = 0 by simp [rootDist]]
    exact ⟨Reachable.refl _, dist_self⟩
  have hne : v0 ≠ vtx r := fun e =>
    h0 (vtx_injective hr (by norm_num) (e.symm.trans vtx_zero.symm))
  rw [rootDist_of_ne h0] at hrd ⊢
  by_cases h1 : isNbr0 r = true
  · have hadj := (adj_v0_vtx_iff hN hr).2 h1
    rw [ite_eq_left h1]
    exact ⟨hadj.reachable, dist_eq_one_iff_adj.2 hadj⟩
  have hnadj : ¬ a4Graph.Adj v0 (vtx r) := fun h => h1 ((adj_v0_vtx_iff hN hr).1 h)
  rw [ite_eq_right h1] at hrd ⊢
  by_cases h2 : (nbrsOf r).any isNbr0 = true
  · obtain ⟨y, hy, hy0⟩ := Array.any_eq_true'.1 h2
    obtain ⟨hylt, hry⟩ := mem_nbrsOf hN hy
    let p : a4Graph.Walk v0 (vtx r) := .cons ((adj_v0_vtx_iff hN hylt).2 hy0) (.cons hry.symm .nil)
    rw [ite_eq_left h2]
    exact ⟨p.reachable, dist_eq_two_of_walk p rfl hne hnadj⟩
  rw [ite_eq_right h2] at hrd
  omega

theorem dist_of_root (hN : NrhoBound) {k : ℕ} (hk : k < 22880)
    (h : a4Graph.Reachable v0 (vtx froot[k]!) ∧
      a4Graph.dist v0 (vtx froot[k]!) = rootDist froot[k]!) :
    a4Graph.Reachable v0 (vtx k) ∧ a4Graph.dist v0 (vtx k) = vDist k := by
  obtain ⟨g, hg0, hg⟩ := exists_stab_root hN hk
  refine ⟨?_, ?_⟩
  · have := reachable_smul g h.1
    rwa [hg0, hg] at this
  · rw [vDist_eq hk, ← h.2, ← dist_smul g v0 (vtx froot[k]!), hg0, hg]

theorem dist_v0_vtx (hN : NrhoBound) {k : ℕ} (hk : k < 22880) :
    a4Graph.Reachable v0 (vtx k) ∧ a4Graph.dist v0 (vtx k) = vDist k := by
  have h2 : ∀ k < 22880, vDist k ≤ 2 →
      a4Graph.Reachable v0 (vtx k) ∧ a4Graph.dist v0 (vtx k) = vDist k := by
    intro k hk hd
    obtain ⟨hrlt, -, -⟩ := forest_node hk
    exact dist_of_root hN hk (dist_root_le_two hN hrlt (by rwa [vDist_eq hk] at hd))
  have h3 : ∀ r < 22880, froot[r]! = r →
      a4Graph.Reachable v0 (vtx r) ∧ a4Graph.dist v0 (vtx r) = rootDist r := by
    intro r hr hrr
    by_cases hd : rootDist r ≤ 2
    · exact dist_root_le_two hN hr hd
    have h3 : rootDist r = 3 := by
      have := rootDist_le_three r
      omega
    obtain ⟨hr0, hn, hnn⟩ := rootDist_eq_three h3
    obtain ⟨y, hy, hy2⟩ := exists_nbr_two hr hrr h3
    obtain ⟨hylt, hry⟩ := mem_nbrsOf hN hy
    obtain ⟨hyR, hyd⟩ := h2 y hylt (by omega)
    have hreach : a4Graph.Reachable v0 (vtx r) := hyR.trans hry.symm.reachable
    refine ⟨hreach, ?_⟩
    rw [h3]
    apply le_antisymm
    · obtain ⟨p, hp⟩ := hyR.exists_walk_length_eq_dist
      have := dist_le (p.concat hry.symm)
      rw [Walk.length_concat, hp, hyd, hy2] at this
      omega
    · by_contra hlt
      have hne : v0 ≠ vtx r := fun e =>
        hr0 (vtx_injective hr (by norm_num) (e.symm.trans vtx_zero.symm))
      have hnadj : ¬ a4Graph.Adj v0 (vtx r) := fun h => by
        rw [(adj_v0_vtx_iff hN hr).1 h] at hn
        exact absurd hn (by decide)
      have hd0 : a4Graph.dist v0 (vtx r) ≠ 0 := fun h => hne (hreach.dist_eq_zero_iff.1 h)
      have hd1 : a4Graph.dist v0 (vtx r) ≠ 1 := fun h => hnadj (dist_eq_one_iff_adj.1 h)
      obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      obtain ⟨c, hc0, hcr⟩ := exists_mid_of_length_two p (by omega)
      obtain ⟨y', hy', rfl⟩ := exists_mem_nbrsOf hN hcr.symm
      have := (adj_v0_vtx_iff hN (mem_nbrsOf hN hy').1).1 hc0
      rw [hnn y' hy'] at this
      exact absurd this (by decide)
  obtain ⟨hrlt, hrr, -⟩ := forest_node hk
  exact dist_of_root hN hk (h3 _ hrlt hrr)

theorem reachable_and_dist_le (hN : NrhoBound) (x y : Vtx) :
    a4Graph.Reachable x y ∧ a4Graph.dist x y ≤ 3 := by
  obtain ⟨g, rfl⟩ := exists_smul x
  obtain ⟨k, hk, hky⟩ := exists_vtx hN (g⁻¹ • y)
  have hy : y = g • vtx k := by rw [hky, smul_inv_smul]
  subst hy
  obtain ⟨hR, hd⟩ := dist_v0_vtx hN hk
  refine ⟨reachable_smul g hR, ?_⟩
  rw [dist_smul, hd, vDist_eq hk]
  exact rootDist_le_three _

theorem a4_preconnected (hN : NrhoBound) : a4Graph.Preconnected := fun x y =>
  (reachable_and_dist_le hN x y).1

theorem forall_of_root (hN : NrhoBound) (P : Vtx → Vtx → Prop)
    (hP : ∀ (g : ↥suzM) a b, P a b → P (g • a) (g • b)) (d : ℕ)
    (hroot : ∀ r < 22880, froot[r]! = r → rootDist r = d → P (vtx r) v0) :
    ∀ a b, a4Graph.dist a b = d → P a b := by
  intro a b hab
  obtain ⟨g, rfl⟩ := exists_smul b
  obtain ⟨k, hk, hka⟩ := exists_vtx hN (g⁻¹ • a)
  obtain ⟨h, hh0, hh⟩ := exists_stab_root hN hk
  obtain ⟨hrlt, hrr, -⟩ := forest_node hk
  have hd : vDist k = d := by
    rw [← (dist_v0_vtx hN hk).2, hka, ← hab, dist_comm, ← dist_smul g⁻¹ a (g • v0),
      inv_smul_smul]
  have h1 := hP h _ _ (hroot _ hrlt hrr (by rw [← vDist_eq hk]; exact hd))
  rw [hh, hh0, hka] at h1
  have h2 := hP g _ _ h1
  rwa [smul_inv_smul] at h2

theorem forall_of_root' (hN : NrhoBound) (P : Vtx → Vtx → Prop)
    (hP : ∀ (g : ↥suzM) a b, P a b → P (g • a) (g • b)) (d : ℕ)
    (hroot : ∀ r < 22880, froot[r]! = r → rootDist r = d → P v0 (vtx r)) :
    ∀ a b, a4Graph.dist a b = d → P a b := fun a b hab =>
  forall_of_root hN (fun a b => P b a) (fun g a b h => hP g b a h) d hroot b a
    (by rw [dist_comm]; exact hab)

theorem preconnected_of_spanCheck (hN : NrhoBound) {D : Array ℕ} {t : Array ℕ × Array ℕ}
    (h : spanCheck D t = true) (hD : ∀ y ∈ D, y < 22880) {S : Set Vtx}
    (hS : ∀ c, c ∈ S ↔ ∃ y ∈ D, vtx y = c) : (a4Graph.induce S).Preconnected := by
  have hmemD : ∀ b (hb : b < D.size), D[b]! ∈ D := fun b hb => by
    rw [getElem!_pos D b hb]
    exact Array.getElem_mem hb
  have hS' : ∀ b (hb : b < D.size), vtx D[b]! ∈ S := fun b hb => (hS _).2 ⟨_, hmemD b hb, rfl⟩
  have hnode : ∀ u : S, ∃ b, ∃ hb : b < D.size, u = ⟨vtx D[b]!, hS' b hb⟩ := by
    rintro ⟨u, hu⟩
    obtain ⟨y, hy, rfl⟩ := (hS u).1 hu
    obtain ⟨b, hb, rfl⟩ := Array.getElem_of_mem hy
    exact ⟨b, hb, Subtype.ext (show vtx D[b] = vtx D[b]! by rw [getElem!_pos D b hb])⟩
  rcases Nat.eq_zero_or_pos D.size with h0 | hpos
  · intro u
    obtain ⟨b, hb, -⟩ := hnode u
    omega
  unfold spanCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hall := allLt_iff.1 h.2
  have key : ∀ n b (hb : b < D.size), t.2[b]! = n →
      (a4Graph.induce S).Reachable ⟨vtx D[0]!, hS' 0 hpos⟩ ⟨vtx D[b]!, hS' b hb⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb hn
      have hb' := hall b hb
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hb'
      rcases hb' with rfl | ⟨⟨hp, hd⟩, ha⟩
      · exact Reachable.refl _
      · have hadj : (a4Graph.induce S).Adj ⟨vtx D[t.1[b]!]!, hS' _ hp⟩ ⟨vtx D[b]!, hS' b hb⟩ :=
          (adj_vtx_iff hN (hD _ (hmemD _ hp)) (hD _ (hmemD _ hb))).2 ha
        exact (ih _ (hn ▸ hd) _ hp rfl).trans hadj.reachable
  intro u v
  obtain ⟨b, hb, rfl⟩ := hnode u
  obtain ⟨b', hb', rfl⟩ := hnode v
  exact (key _ b hb rfl).symm.trans (key _ b' hb' rfl)

theorem ronan_i_root (hN : NrhoBound) {r : ℕ} (hr : r < 22880) (hrr : froot[r]! = r)
    (h2 : 2 ≤ rootDist r) :
    (a4Graph.induce
      {c | a4Graph.Adj (vtx r) c ∧ a4Graph.dist c v0 = rootDist r - 1}).Preconnected := by
  have hs := Array.all_eq_true'.1 spanOK_true r (mem_roots.2 ⟨hr, hrr⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
  have hsc : spanCheck (downSet r) (spanPin r) = true := hs.resolve_left (by omega)
  refine preconnected_of_spanCheck hN hsc (fun y hy => ?_) (fun c => ?_)
  · unfold downSet at hy
    exact (mem_nbrsOf hN (Array.mem_filter.1 hy).1).1
  · unfold downSet
    constructor
    · rintro ⟨hc, hd⟩
      obtain ⟨y, hy, rfl⟩ := exists_mem_nbrsOf hN hc
      have hylt := (mem_nbrsOf hN hy).1
      refine ⟨y, Array.mem_filter.2 ⟨hy, ?_⟩, rfl⟩
      rw [dist_comm, (dist_v0_vtx hN hylt).2] at hd
      simp only [beq_iff_eq]
      omega
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := Array.mem_filter.1 hy
      obtain ⟨hylt, hadj⟩ := mem_nbrsOf hN hy1
      refine ⟨hadj, ?_⟩
      rw [dist_comm, (dist_v0_vtx hN hylt).2]
      simp only [beq_iff_eq] at hy2
      omega

theorem ronan_i (hN : NrhoBound) (i : ℕ) (hi2 : 2 ≤ i) (a b : Vtx) (hab : a4Graph.dist a b = i) :
    (a4Graph.induce {c | a4Graph.Adj a c ∧ a4Graph.dist c b = i - 1}).Preconnected := by
  refine forall_of_root hN (fun a b => (a4Graph.induce
    {c | a4Graph.Adj a c ∧ a4Graph.dist c b = i - 1}).Preconnected) ?_ i ?_ a b hab
  · intro g a b h
    rw [ronanSet_smul]
    exact preconnected_image g h
  · intro r hr hrr hri
    have := ronan_i_root hN hr hrr (by omega)
    rwa [hri] at this

theorem q2_root (hN : NrhoBound) {r : ℕ} (hr : r < 22880) (hrr : froot[r]! = r)
    (h2 : rootDist r = 2) (g : Vtx) (hg : a4Graph.dist v0 g = 2) (hrg : a4Graph.Adj (vtx r) g) :
    ∃ c c', a4Graph.Adj v0 c ∧ a4Graph.Adj c (vtx r) ∧ a4Graph.Adj g c' ∧ a4Graph.Adj c' v0 ∧
      (c = c' ∨ a4Graph.Adj c c') := by
  obtain ⟨y, hy, rfl⟩ := exists_mem_nbrsOf hN hrg
  obtain ⟨hylt, -⟩ := mem_nbrsOf hN hy
  have hyd : vDist y = 2 := by
    rw [← (dist_v0_vtx hN hylt).2]
    exact hg
  have hq := Array.all_eq_true'.1 q2OK_true r (mem_roots.2 ⟨hr, hrr⟩)
  simp only [h2, bne_self_eq_false, Bool.false_or] at hq
  unfold q2At at hq
  have hqy := Array.all_eq_true'.1 hq y hy
  simp only [hyd, bne_self_eq_false, Bool.false_or, Bool.or_eq_true] at hqy
  have hCr : ∀ cc ∈ ((nbrsOf r).filter isNbr0).map (fun c => (c, cArrInv c)),
      ∃ c, cc.2 = cArrInv c ∧ c < 22880 ∧ a4Graph.Adj v0 (vtx c) ∧
        a4Graph.Adj (vtx c) (vtx r) := by
    intro cc hcc
    obtain ⟨c, hc, rfl⟩ := Array.mem_map.1 hcc
    obtain ⟨hc1, hc2⟩ := Array.mem_filter.1 hc
    obtain ⟨hclt, hrc⟩ := mem_nbrsOf hN hc1
    exact ⟨c, rfl, hclt, (adj_v0_vtx_iff hN hclt).2 hc2, hrc.symm⟩
  rcases hqy with h1 | h1
  · obtain ⟨cc, hcc, hadj⟩ := Array.any_eq_true'.1 h1
    obtain ⟨c, hcc2, hclt, hc0, hcr⟩ := hCr cc hcc
    rw [hcc2] at hadj
    have hcy : a4Graph.Adj (vtx c) (vtx y) := (adj_vtx_iff hN hclt hylt).2 hadj
    exact ⟨vtx c, vtx c, hc0, hcr, hcy.symm, hc0.symm, Or.inl rfl⟩
  · obtain ⟨cc, hcc, hany⟩ := Array.any_eq_true'.1 h1
    obtain ⟨c, hcc2, hclt, hc0, hcr⟩ := hCr cc hcc
    obtain ⟨c', hc', hadj⟩ := Array.any_eq_true'.1 hany
    obtain ⟨hc'1, hc'2⟩ := Array.mem_filter.1 hc'
    obtain ⟨hc'lt, hyc'⟩ := mem_nbrsOf hN hc'1
    rw [hcc2] at hadj
    have hcc' : a4Graph.Adj (vtx c) (vtx c') := (adj_vtx_iff hN hclt hc'lt).2 hadj
    exact ⟨vtx c, vtx c', hc0, hcr, hyc', ((adj_v0_vtx_iff hN hc'lt).2 hc'2).symm, Or.inr hcc'⟩

theorem ronan_q2 (hN : NrhoBound) (a b : Vtx) (hab : a4Graph.dist a b = 2) (g : Vtx)
    (hag : a4Graph.dist a g = 2) (hbg : a4Graph.Adj b g) : Q2Good a4Graph a b g := by
  have key := forall_of_root' hN (fun a b => ∀ g, a4Graph.dist a g = 2 → a4Graph.Adj b g →
      ∃ c c', a4Graph.Adj a c ∧ a4Graph.Adj c b ∧ a4Graph.Adj g c' ∧ a4Graph.Adj c' a ∧
        (c = c' ∨ a4Graph.Adj c c')) ?_ 2 ?_ a b hab
  · obtain ⟨c, c', h1, h2, h3, h4, h5⟩ := key g hag hbg
    exact q2Good_of_data hbg h1 h2 h3 h4 h5
  · intro x a b H g hg hbg
    obtain ⟨c, c', h1, h2, h3, h4, h5⟩ := H (x⁻¹ • g)
      (by rw [← dist_smul x, smul_inv_smul]; exact hg)
      (by rw [← a4Graph_adj_smul_iff x, smul_inv_smul]; exact hbg)
    refine ⟨x • c, x • c', a4Graph_adj_smul x h1, a4Graph_adj_smul x h2, ?_,
      a4Graph_adj_smul x h4, h5.imp (congrArg (x • ·)) (a4Graph_adj_smul x)⟩
    have := a4Graph_adj_smul x h3
    rwa [smul_inv_smul] at this
  · intro r hr hrr h2 g hg hrg
    exact q2_root hN hr hrr h2 g hg hrg

theorem not_adj_three (hN : NrhoBound) (a b : Vtx) (hab : a4Graph.dist a b = 3) (g : Vtx)
    (hag : a4Graph.dist a g = 3) : ¬ a4Graph.Adj b g := by
  refine forall_of_root' hN (fun a b => ∀ g, a4Graph.dist a g = 3 → ¬ a4Graph.Adj b g) ?_ 3 ?_
    a b hab g hag
  · intro x a b H g hg hbg
    exact H (x⁻¹ • g) (by rw [← dist_smul x, smul_inv_smul]; exact hg)
      (by rw [← a4Graph_adj_smul_iff x, smul_inv_smul]; exact hbg)
  · intro r hr hrr h3 g hg hrg
    obtain ⟨y, hy, rfl⟩ := exists_mem_nbrsOf hN hrg
    obtain ⟨hylt, -⟩ := mem_nbrsOf hN hy
    have hyd : vDist y = 3 := by
      rw [← (dist_v0_vtx hN hylt).2]
      exact hg
    have hl := Array.all_eq_true'.1 layer3OK_true r (mem_roots.2 ⟨hr, hrr⟩)
    simp only [h3, bne_self_eq_false, Bool.false_or] at hl
    have := Array.all_eq_true'.1 hl y hy
    simp [hyd] at this

theorem a4_triangulable (hN : NrhoBound) : Triangulable a4Graph := by
  refine triangulable_of_ronan_q2 (d := 3) (fun x y => (reachable_and_dist_le hN x y).2)
    (fun i hi2 _ a b hab => ronan_i hN i hi2 a b hab)
    (fun a b g hab hag hbg => ronan_q2 hN a b hab g hag hbg) ?_
  intro i hi3 hi3' a b g hab hag hbg
  obtain rfl : i = 3 := by omega
  exact absurd hbg (not_adj_three hN a b hab g hag)

end CFSG.Sporadic.SuzRecog.Q3A

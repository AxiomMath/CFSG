module

public import CFSG.Quasithin.Recognition.F4Setting

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin

universe u w

section PathTrans

variable {V : Type u} {Γ : SimpleGraph V}

theorem nb_dist {m : ℕ} (hP : IsGenPolygon Γ m) {k : ℕ} (hk : k ≤ m) (p : GPath Γ k)
    (hp : p.NoBack) : Γ.dist (p 0) (p k) = k := by
  obtain ⟨c, hc⟩ := hP.bipartite
  exact GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod k hk p hp

theorem dist_zero_m {m : ℕ} (hP : IsGenPolygon Γ m) (p : GPath Γ (m + 1)) (hp : p.NoBack) :
    Γ.dist (p 0) (p m) = m := by
  have hm1 : m ≤ m + 1 := Nat.le_succ m
  have := nb_dist hP (le_refl m) (p.take m hm1) (hp.take m hm1)
  simpa [GPath.take_apply_of_le _ _ _ (le_refl m), GPath.take_apply_of_le _ _ _ (Nat.zero_le m)]
    using this

theorem dist_one_succ {m : ℕ} (hP : IsGenPolygon Γ m) (p : GPath Γ (m + 1)) (hp : p.NoBack) :
    Γ.dist (p 1) (p (m + 1)) = m := by
  have h1m : 1 ≤ m + 1 := by omega
  have h := nb_dist hP (show m + 1 - 1 ≤ m by omega) (p.drop 1 h1m) (hp.drop 1 h1m)
  rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl] at h
  rw [show 1 + (m + 1 - 1) = m + 1 by omega, add_zero] at h
  rw [h]
  omega

theorem dist_zero_succ {m : ℕ} (hm : 1 ≤ m) (hP : IsGenPolygon Γ m) (p : GPath Γ (m + 1))
    (hp : p.NoBack) : Γ.dist (p 0) (p (m + 1)) = m - 1 := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have h1 := dist_zero_m hP p hp
  have h2 := hP.diam_le (p 0) (p (m + 1))
  have h3 := GPath.dist_adj_succ_or hP.connected hc (p 0) (p.adj m (by omega))
  omega

theorem exists_first {m : ℕ} (hm : 2 ≤ m) (hP : IsGenPolygon Γ m) (u w : V)
    (h : Γ.dist u w = m - 1) : ∃ b, Γ.Adj u b ∧ Γ.dist b w = m - 2 := by
  obtain ⟨r, hr0, hrn, -⟩ := GPath.exists_geodesic' hP.connected u w h
  have hadj : Γ.Adj u (r 1) := by
    have := r.adj 0 (by omega)
    rwa [hr0] at this
  refine ⟨r 1, hadj, ?_⟩
  have h1 := GPath.dist_le_sub hP.connected r (show 1 ≤ m - 1 by omega) le_rfl
  rw [hrn] at h1
  have h2 : Γ.dist u (r 1) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have h3 := hP.connected.dist_triangle (u := u) (v := r 1) (w := w)
  omega

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

theorem pathTrans_aux {m : ℕ} (hm : 3 ≤ m) (hP : IsGenPolygon Γ m) (u : V) (Q : Subgroup H)
    (hQu : ∀ x ∈ Q, x • u = u) (hQfix : ∀ w, Γ.Adj u w → ∀ x ∈ Q, x • w = w)
    (hQtrans : ∀ v v', Γ.dist u v = m → Γ.dist u v' = m → ∃ x ∈ Q, x • v = v')
    (h2 : ∀ a b a' b', Γ.Adj u a → Γ.Adj u b → a ≠ b → Γ.Adj u a' → Γ.Adj u b' → a' ≠ b' →
      ∃ g : H, g • u = u ∧ g • a = a' ∧ g • b = b')
    (q q' : GPath Γ (m + 1)) (hq0 : q 0 = u) (hq : q.NoBack) (hq'0 : q' 0 = u)
    (hq' : q'.NoBack) : ∃ g : H, g • u = u ∧ g • q = q' := by
  have hconn := hP.connected
  obtain ⟨c, hc⟩ := hP.bipartite
  have hU := hP.uniqueGeod
  have hdw : Γ.dist u (q (m + 1)) = m - 1 := by
    have := dist_zero_succ (by omega) hP q hq
    rwa [hq0] at this
  have hdw' : Γ.dist u (q' (m + 1)) = m - 1 := by
    have := dist_zero_succ (by omega) hP q' hq'
    rwa [hq'0] at this
  obtain ⟨b, hub, hbw⟩ := exists_first (by omega) hP u _ hdw
  obtain ⟨b', hub', hb'w⟩ := exists_first (by omega) hP u _ hdw'
  have hqa : Γ.Adj u (q 1) := by
    have := q.adj 0 (by omega)
    rwa [hq0] at this
  have hqa' : Γ.Adj u (q' 1) := by
    have := q'.adj 0 (by omega)
    rwa [hq'0] at this
  have hab : q 1 ≠ b := by
    intro h
    have h1 := dist_one_succ hP q hq
    rw [h] at h1
    omega
  have hab' : q' 1 ≠ b' := by
    intro h
    have h1 := dist_one_succ hP q' hq'
    rw [h] at h1
    omega
  obtain ⟨g₀, hg₀u, hg₀a, hg₀b⟩ := h2 (q 1) b (q' 1) b' hqa hub hab hqa' hub' hab'
  have hdq : Γ.dist u (g₀ • q m) = m := by
    have h1 := GPath.dist_smul hconn g₀ (q 0) (q m)
    rw [hq0, hg₀u] at h1
    rw [h1]
    have := dist_zero_m hP q hq
    rwa [hq0] at this
  have hdq' : Γ.dist u (q' m) = m := by
    have := dist_zero_m hP q' hq'
    rwa [hq'0] at this
  obtain ⟨x, hxQ, hx⟩ := hQtrans _ _ hdq hdq'
  have hgu : (x * g₀) • u = u := by rw [mul_smul, hg₀u, hQu x hxQ]
  have hga : (x * g₀) • q 1 = q' 1 := by rw [mul_smul, hg₀a]; exact hQfix _ hqa' x hxQ
  have hgb : (x * g₀) • b = b' := by rw [mul_smul, hg₀b]; exact hQfix _ hub' x hxQ
  have hgm : (x * g₀) • q m = q' m := by rw [mul_smul]; exact hx
  refine ⟨x * g₀, hgu, ?_⟩
  set p : GPath Γ (m + 1) := (x * g₀) • q with hp
  have hpnb : p.NoBack := GPath.smul_noBack hq
  have hp0 : p 0 = u := by rw [hp, GPath.smul_apply, hq0, hgu]
  have hp1 : p 1 = q' 1 := by rw [hp, GPath.smul_apply, hga]
  have hpm : p m = q' m := by rw [hp, GPath.smul_apply, hgm]
  have hpb : Γ.dist b' (p (m + 1)) = m - 2 := by
    rw [hp, GPath.smul_apply, ← hgb, GPath.dist_smul hconn]
    exact hbw
  have hm1 : m ≤ m + 1 := Nat.le_succ m
  have h1m : 1 ≤ m := by omega
  have hmid : ∀ i, 1 ≤ i → i ≤ m → p i = q' i := by
    have hsnb : ((p.take m hm1).drop 1 h1m).NoBack := (hpnb.take m hm1).drop 1 h1m
    have hsnb' : ((q'.take m hm1).drop 1 h1m).NoBack := (hq'.take m hm1).drop 1 h1m
    have hg1 : ((p.take m hm1).drop 1 h1m).IsGeodesic := nb_dist hP (by omega) _ hsnb
    have hg2 : ((q'.take m hm1).drop 1 h1m).IsGeodesic := nb_dist hP (by omega) _ hsnb'
    have heq := hU (m - 1) _ _ hg1 hg2
      (by
        rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ (Nat.zero_le _),
          GPath.take_apply_of_le _ _ _ (by omega), GPath.take_apply_of_le _ _ _ (by omega)]
        exact hp1)
      (by
        rw [GPath.drop_apply _ _ _ le_rfl, GPath.drop_apply _ _ _ le_rfl,
          GPath.take_apply_of_le _ _ _ (by omega), GPath.take_apply_of_le _ _ _ (by omega)]
        rw [show 1 + (m - 1) = m by omega]
        exact hpm) (by omega)
    intro i hi1 hi2
    have := congrArg (fun r : GPath Γ (m - 1) => r (i - 1)) heq
    rw [GPath.drop_apply _ _ _ (by omega), GPath.drop_apply _ _ _ (by omega),
      GPath.take_apply_of_le _ _ _ (by omega), GPath.take_apply_of_le _ _ _ (by omega),
      show 1 + (i - 1) = i by omega] at this
    exact this
  have hlast : p (m + 1) = q' (m + 1) := by
    have hdv : Γ.dist b' (q' m) = m - 1 := by
      have h1 := GPath.dist_adj_succ_or hconn hc (q' m) hub'
      have h3 := hP.diam_le (q' m) b'
      have e1 : Γ.dist (q' m) u = m := by rw [SimpleGraph.dist_comm]; exact hdq'
      have e2 : Γ.dist b' (q' m) = Γ.dist (q' m) b' := SimpleGraph.dist_comm
      omega
    obtain ⟨r, hr0, hrn, -⟩ := GPath.exists_geodesic' hconn b' (p (m + 1)) hpb
    obtain ⟨r', hr'0, hr'n, -⟩ := GPath.exists_geodesic' hconn b' (q' (m + 1)) hb'w
    have hadj : Γ.Adj (r (m - 2)) (q' m) := by
      rw [hrn, ← hpm]
      exact (p.adj m (by omega)).symm
    have hadj' : Γ.Adj (r' (m - 2)) (q' m) := by
      rw [hr'n]
      exact (q'.adj m (by omega)).symm
    have hR0 : (r.snoc (q' m) hadj) 0 = b' := by
      rw [GPath.snoc_of_le _ _ _ (Nat.zero_le _), hr0]
    have hR'0 : (r'.snoc (q' m) hadj') 0 = b' := by
      rw [GPath.snoc_of_le _ _ _ (Nat.zero_le _), hr'0]
    have hRg : (r.snoc (q' m) hadj).IsGeodesic := by
      show Γ.dist ((r.snoc (q' m) hadj) 0) ((r.snoc (q' m) hadj) (m - 2 + 1)) = m - 2 + 1
      rw [hR0, GPath.snoc_last, hdv]
      omega
    have hR'g : (r'.snoc (q' m) hadj').IsGeodesic := by
      show Γ.dist ((r'.snoc (q' m) hadj') 0) ((r'.snoc (q' m) hadj') (m - 2 + 1)) = m - 2 + 1
      rw [hR'0, GPath.snoc_last, hdv]
      omega
    have heq := hU (m - 2 + 1) _ _ hRg hR'g (by rw [hR0, hR'0]) (by
      rw [GPath.snoc_last, GPath.snoc_last]) (by omega)
    have := congrArg (fun R : GPath Γ (m - 2 + 1) => R (m - 2)) heq
    rwa [GPath.snoc_of_le _ _ _ le_rfl, GPath.snoc_of_le _ _ _ le_rfl, hrn, hr'n] at this
  refine GPath.ext' fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [hp0, hq'0]
  · rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact hmid i hi0 (by omega)
    · rw [show i = m + 1 by omega]
      exact hlast

end PathTrans

section Setting

open CFSG.Quasithin.RankTwoAmalgam.Completion

variable (S : LieSetting.{u, w})

structure BaseFacts (u : S.ι.Γ) : Prop where
  Qfix : ∀ w, S.ι.graph.Adj u w → ∀ x ∈ S.Qbar u, x • w = w
  Qtrans : ∀ v v' : S.ι.Γ, S.ι.graph.dist u v = S.m → S.ι.graph.dist u v' = S.m →
    ∃ x ∈ S.Qbar u, x • v = v'
  Qfree : ∀ v : S.ι.Γ, S.ι.graph.dist u v = S.m → ∀ x ∈ S.Qbar u, x • v = v → x = 1
  two : ∀ a b a' b' : S.ι.Γ, S.ι.graph.Adj u a → S.ι.graph.Adj u b → a ≠ b →
    S.ι.graph.Adj u a' → S.ι.graph.Adj u b' → a' ≠ b' →
    ∃ g : S.ι.G0, g • u = u ∧ g • a = a' ∧ g • b = b'

variable {S} {u : S.ι.Γ}

theorem BaseFacts.pathTrans (hP : IsGenPolygon S.ι.graph S.m) (h : BaseFacts S u) :
    S.ι.PathTrans u (S.m + 1) := by
  intro q q' hq hq'
  exact pathTrans_aux S.hm hP u (S.Qbar u)
    (fun x hx => MulAction.mem_stabilizer_iff.mp (S.Qbar_le_stv u hx)) h.Qfix h.Qtrans h.two q q'
    hq.1 hq.2 hq'.1 hq'.2

theorem BaseFacts.compl (hP : IsGenPolygon S.ι.graph S.m) (h : BaseFacts S u) :
    ∀ v : S.ι.Γ, S.ι.graph.dist u v = S.m →
      IsComplementIn (stv S.ι u ⊓ stv S.ι v) (S.Qbar u) (stv S.ι u) := by
  intro v hv
  refine ⟨S.Qbar_le_stv u, inf_le_left, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxQ, hxu, hxv⟩
    exact Subgroup.mem_bot.mpr (h.Qfree v hv x hxQ (MulAction.mem_stabilizer_iff.mp hxv))
  · intro g hg
    have hgu : g • u = u := MulAction.mem_stabilizer_iff.mp hg
    have hd : S.ι.graph.dist u (g • v) = S.m := by
      have := GPath.dist_smul hP.connected g u v
      rw [hgu] at this
      rw [this]
      exact hv
    obtain ⟨x, hxQ, hx⟩ := h.Qtrans v (g • v) hv hd
    have hxu : x ∈ stv S.ι u := S.Qbar_le_stv u hxQ
    have hxv : x⁻¹ * g ∈ stv S.ι v := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hx, inv_smul_smul]
    exact ⟨x, hxQ, x⁻¹ * g, ⟨(stv S.ι u).mul_mem ((stv S.ι u).inv_mem hxu) hg, hxv⟩, by simp⟩

variable (S) in
theorem facts45L_of_baseFacts (thick1 : 2 ≤ S.α.qOne) (thick2 : 2 ≤ S.α.qTwo)
    (hP : IsGenPolygon S.ι.graph S.m) (hx : BaseFacts S S.ι.xv) (hl : BaseFacts S S.ι.lv) :
    S.Facts45L :=
  LieSetting.Facts45L.ofBase S thick1 thick2 hP (hx.pathTrans hP) (hl.pathTrans hP)
    (hx.compl hP) (hl.compl hP)
    (fun w hw x hxQ => MulAction.mem_stabilizer_iff.mpr (hx.Qfix w hw x hxQ))
    (fun w hw x hxQ => MulAction.mem_stabilizer_iff.mpr (hl.Qfix w hw x hxQ))

end Setting

end CFSG.Quasithin.H13.F431.F45

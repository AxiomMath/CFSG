module

public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

section Tree

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem dist_eq_add_of_geo_ne {u x w : Vtx X} (hxu : 0 < X.treeGraph.dist x u)
    (hxw : 0 < X.treeGraph.dist x w) (hne : geo X x u 1 ≠ geo X x w 1) :
    X.treeGraph.dist u w = X.treeGraph.dist u x + X.treeGraph.dist x w := by
  suffices H : ∀ m : ℕ, ∀ x : Vtx X, X.treeGraph.dist x w = m + 1 →
      0 < X.treeGraph.dist x u → geo X x u 1 ≠ geo X x w 1 →
      X.treeGraph.dist u w = X.treeGraph.dist u x + (m + 1) by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hxw.ne'
    rw [hm]
    exact H m x hm hxu hne
  intro m
  induction m with
  | zero =>
    intro x hx hxu hne'
    have hy : geo X x w 1 = w := geo_of_le X (by omega)
    have hadj : X.treeGraph.Adj x w := by
      rw [← hy]
      exact adj_geo_one X (by omega)
    rcases dist_adj_cases X hadj u with h1 | h1
    · omega
    · exfalso
      apply hne'
      rw [hy]
      symm
      apply eq_geo_one X hadj
      rw [tdist_comm X w u, tdist_comm X x u]
      omega
  | succ m ih =>
    intro x hx hxu hne'
    have hadj : X.treeGraph.Adj x (geo X x w 1) := adj_geo_one X (by omega)
    have hyw : X.treeGraph.dist (geo X x w 1) w = m + 1 := by
      rw [dist_geo_right X (by omega), hx]
      omega
    have hdu : X.treeGraph.dist u (geo X x w 1) = X.treeGraph.dist u x + 1 := by
      rcases dist_adj_cases X hadj u with h1 | h1
      · exact h1
      · exfalso
        apply hne'
        symm
        apply eq_geo_one X hadj
        rw [tdist_comm X (geo X x w 1) u, tdist_comm X x u]
        omega
    have hyu : 0 < X.treeGraph.dist (geo X x w 1) u := by
      rw [tdist_comm]
      omega
    have hne'' : geo X (geo X x w 1) u 1 ≠ geo X (geo X x w 1) w 1 := by
      have e1 : geo X (geo X x w 1) u 1 = x := by
        symm
        apply eq_geo_one X hadj.symm
        rw [tdist_comm X x u, tdist_comm X (geo X x w 1) u]
        omega
      rw [e1]
      intro he
      have := dist_geo_right X (u := geo X x w 1) (w := w) (i := 1) (by omega)
      rw [← he, hyw, hx] at this
      omega
    have := ih (geo X x w 1) hyw hyu hne''
    omega

theorem geo_ext {s' s t : Vtx X} (hs : X.treeGraph.dist s' s = 2) (ht : 0 < X.treeGraph.dist s t)
    (hne : geo X s s' 1 ≠ geo X s t 1) :
    X.treeGraph.dist s' t = X.treeGraph.dist s t + 2 ∧
      ∀ i ≤ X.treeGraph.dist s t, geo X s' t (i + 2) = geo X s t i := by
  have hss' : 0 < X.treeGraph.dist s s' := by
    rw [tdist_comm]
    omega
  have hd := dist_eq_add_of_geo_ne hss' ht hne
  rw [hs] at hd
  refine ⟨by omega, fun i hi => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · symm
    rw [geo_zero]
    apply eq_geo_of_dist X hs
    rw [hs, hd]
  · symm
    have hsx : X.treeGraph.dist s (geo X s t i) = i := dist_geo X hi
    have hne' : geo X s s' 1 ≠ geo X s (geo X s t i) 1 := by
      rwa [geo_geo X (by omega) hi]
    have hd' := dist_eq_add_of_geo_ne hss' (by omega) hne'
    rw [hs, hsx] at hd'
    apply eq_geo_of_dist X (by rw [hd']; omega)
    rw [hd', dist_geo_right X hi, hd]
    omega

end Tree

section Transport

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_base_crit (h : PUHyp M T L) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ γ γ') :
    ∃ g : (puAmalgam h.le).Universal, γ = g • baseA _ ∧ geo _ γ γ' 1 = g • baseB _ ∧
      IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') ∧
      geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 1 = baseB _ := by
  have hb0 := h.critDist_pos
  have hdd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  have hadj : (puAmalgam h.le).treeGraph.Adj γ (geo _ γ γ' 1) := adj_geo_one _ (by omega)
  obtain ⟨g, rfl, hgβ⟩ := exists_smul_base_edge _ hc.1 hadj
  refine ⟨g, rfl, hgβ, ?_, ?_⟩
  · have := (isCritical_smul _ g⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  · have := geo_smul _ g⁻¹ (g • baseA (puAmalgam h.le)) γ' 1
    rw [hgβ] at this
    simpa only [inv_smul_smul] using this

theorem s59_gp (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    2 ^ k < (S5.bSub h.le L γ).relIndex (S5.uSub h.le L (geo _ γ γ' 2)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, -, hc', hβ'⟩ := exists_base_crit h hc
  have key := h59 G M T L h hmin hb k F _ _ a hd _ hc' hβ'
  have e : geo _ (g • baseA (puAmalgam h.le)) γ' 2 = g • geo _ (baseA _) (g⁻¹ • γ') 2 := by
    rw [← geo_smul, smul_inv_smul]
  rw [e, S5B.bSub_smul h.le hLn, S5B.uSub_smul h.le hLn,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact key

theorem exists_lam_not_le (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56 : S56) (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ∃ μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      ¬ ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
  have hd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have h59' := h59 G M T L h hmin hb k F _ _ a hd _ hc hαβ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  by_contra hno
  push Not at hno
  have := S5B.s57 h32 hX2 h52 h54 h55 h56 h hmin (by omega) hd hc hαβ hβδ
    hno
  omega

omit [Fintype F] in
theorem exists_step_sel (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (Good : Vtx (puAmalgam h.le) → Vtx (puAmalgam h.le) → Prop)
    (hsel : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ μ₀ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
        ¬ ZM _ μ₀ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) ∧ Good α' μ₀)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    ∃ μ, IsCritical _ μ (geo _ γ' γ 2) ∧
      (puAmalgam h.le).treeGraph.dist μ γ' = critDist (puAmalgam h.le) + 2 ∧
      (∀ i ≤ critDist (puAmalgam h.le), geo _ μ γ' (i + 2) = geo _ γ γ' i) ∧
      (∃ t ∈ stab _ γ, t • geo _ γ γ' 2 = μ) ∧
      ∃ g : (puAmalgam h.le).Universal, γ = g • baseA (puAmalgam h.le) ∧
        geo _ γ γ' 1 = g • baseB _ ∧
        g⁻¹ • μ ∈ S5.lam h (2 ^ k) a (g⁻¹ • γ') (g⁻¹ • geo _ γ γ' 2) ∧
        Good (g⁻¹ • γ') (g⁻¹ • μ) := by
  have hb0 := h.critDist_pos
  have hdd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, hγ, hgβ, hc', hβ'⟩ := exists_base_crit h hc
  have hd'' : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • γ') =
      critDist (puAmalgam h.le) := hc'.2.1
  have e2 : g⁻¹ • geo _ γ γ' 2 = geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2 := by
    rw [hγ, ← geo_smul, inv_smul_smul]
  have e3 : geo _ γ' γ 2 = g • geo _ (g⁻¹ • γ') (baseA (puAmalgam h.le)) 2 := by
    rw [hγ, ← geo_smul, smul_inv_smul]
  obtain ⟨μ₀, hμ₀, hZμ₀, hgood⟩ := hsel _ hc' hβ'
  obtain ⟨t₀, ht₀, hμ₀t⟩ : ∃ t₀ ∈ stab _ (baseA (puAmalgam h.le)),
      μ₀ = t₀ • geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2 := by
    obtain ⟨g', x, hg', hx, -, hμeq⟩ := hμ₀
    have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
    rcases hμeq with rfl | rfl
    · exact ⟨g'⁻¹, inv_mem hg', rfl⟩
    · exact ⟨x⁻¹ * g'⁻¹, mul_mem (inv_mem hxst) (inv_mem hg'), by rw [mul_smul]⟩
  set μ := g • μ₀ with hμdef
  have hμγ : (puAmalgam h.le).treeGraph.dist μ γ = 2 := by
    have h1 := dist_smul _ t₀ (geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2) (baseA _)
    rw [(mem_stab _).1 ht₀] at h1
    rw [hμdef, hγ, dist_smul, hμ₀t, h1, tdist_comm, dist_geo _ (by omega)]
  have hμM : IsMVtx _ μ := by
    rw [hμdef, hμ₀t, isMVtx_smul, isMVtx_smul,
      isMVtx_geo _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • γ') by omega)]
    exact iff_of_true (isMVtx_baseA _) ⟨1, rfl⟩
  have hZμ : ¬ ZM _ μ ≤ Qv _ (geo _ γ' γ 2) := by
    rw [hμdef, e3, zm_smul, qv_smul, map_conj_le_map_conj_iff]
    exact hZμ₀
  have hγσ : (puAmalgam h.le).treeGraph.dist γ (geo _ γ' γ 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hdd]
  have hμσ : (puAmalgam h.le).treeGraph.dist μ (geo _ γ' γ 2) = critDist (puAmalgam h.le) := by
    have t1 := dist_triangle _ μ γ (geo _ γ' γ 2)
    have t2 : critDist (puAmalgam h.le) ≤
        (puAmalgam h.le).treeGraph.dist μ (geo _ γ' γ 2) := by
      by_contra hlt
      exact hZμ (zm_le_qv_of_dist_lt _ hμM (by omega))
    omega
  have hcμ : IsCritical _ μ (geo _ γ' γ 2) := ⟨hμM, hμσ, hZμ⟩
  have hne : geo _ γ μ 1 ≠ geo _ γ γ' 1 := by
    intro he
    have h1 : (puAmalgam h.le).treeGraph.dist (geo _ γ μ 1) μ = 1 := by
      rw [dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hμγ]
    have e4 : geo _ γ' γ 2 = geo _ γ γ' (critDist (puAmalgam h.le) - 2) := by
      have := geo_symm _ (u := γ) (w := γ') (i := critDist (puAmalgam h.le) - 2) (by omega)
      rwa [hdd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
        at this
    have h2 : (puAmalgam h.le).treeGraph.dist (geo _ γ γ' 1) (geo _ γ' γ 2) =
        critDist (puAmalgam h.le) - 3 := by
      rw [e4, dist_geo_geo _ (by omega) (by omega)]
      omega
    have t := dist_triangle _ μ (geo _ γ μ 1) (geo _ γ' γ 2)
    rw [tdist_comm _ μ (geo _ γ μ 1), h1, he, h2] at t
    omega
  obtain ⟨hμγ', hgeo⟩ := geo_ext hμγ (by omega) hne
  refine ⟨μ, hcμ, by rw [hμγ', hdd], fun i hi => hgeo i (by omega), ?_, g, hγ, hgβ, ?_⟩
  · refine ⟨g * t₀ * g⁻¹, ?_, ?_⟩
    · rw [hγ, mem_stab_smul]
      simpa [mul_assoc] using ht₀
    · rw [hμdef, hμ₀t, ← e2, mul_smul, mul_smul]
  · rw [hμdef, inv_smul_smul, e2]
    exact ⟨hμ₀, hgood⟩

omit [Fintype F] in
theorem exists_chain_sel (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (Good : Vtx (puAmalgam h.le) → Vtx (puAmalgam h.le) → Prop)
    (hsel : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ μ₀ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
        ¬ ZM _ μ₀ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) ∧ Good α' μ₀)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') (N : ℕ) :
    ∃ s, (puAmalgam h.le).treeGraph.dist s α' = critDist (puAmalgam h.le) + 2 * N ∧
      geo _ s α' (2 * N) = α ∧
      (∀ j ≤ N, IsCritical _ (geo _ s α' (2 * j))
        (geo _ s α' (2 * j + critDist (puAmalgam h.le)))) ∧
      ∀ j, 1 ≤ j → j ≤ N →
        (∃ t ∈ stab _ (geo _ s α' (2 * j)),
            t • geo _ s α' (2 * j + 2) = geo _ s α' (2 * j - 2)) ∧
        ∃ g : (puAmalgam h.le).Universal, geo _ s α' (2 * j) = g • baseA (puAmalgam h.le) ∧
          geo _ s α' (2 * j + 1) = g • baseB _ ∧
          g⁻¹ • geo _ s α' (2 * j - 2) ∈ S5.lam h (2 ^ k) a
            (g⁻¹ • geo _ s α' (2 * j + critDist (puAmalgam h.le)))
            (g⁻¹ • geo _ s α' (2 * j + 2)) ∧
          Good (g⁻¹ • geo _ s α' (2 * j + critDist (puAmalgam h.le)))
            (g⁻¹ • geo _ s α' (2 * j - 2)) := by
  have hb0 := h.critDist_pos
  have hdd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨b, hbdef⟩ : ∃ b, critDist (puAmalgam h.le) = b := ⟨_, rfl⟩
  have hb4 : 4 < b := hbdef ▸ hb
  rw [hbdef] at hb0 hdd ⊢
  induction N with
  | zero =>
    refine ⟨α, by rw [hdd]; rfl, by simp, fun j hj => ?_, fun j hj hj' => by omega⟩
    obtain rfl : j = 0 := by omega
    rw [Nat.mul_zero, zero_add, ← hdd, geo_dist, geo_zero]
    exact hc
  | succ N ih =>
    obtain ⟨s, hsd, hsα, hcrit, hlam⟩ := ih
    set P := geo _ s α' with hP
    have hc0 := hcrit 0 (Nat.zero_le _)
    rw [Nat.mul_zero, zero_add] at hc0
    have hP0 : P 0 = s := geo_zero _ _ _
    rw [hP0] at hc0
    obtain ⟨μ, hcμ, hμd, hμgeo, hμt, hμlam⟩ :=
      exists_step_sel h hb Good hsel hc0
    rw [hbdef] at hμd hμgeo
    have hsb : (puAmalgam h.le).treeGraph.dist s (P b) = b := dist_geo _ (by omega)
    have hgg : ∀ i ≤ b, geo _ s (P b) i = P i := fun i hi => geo_geo _ hi (by omega)
    have hμs : (puAmalgam h.le).treeGraph.dist μ s = 2 := by
      have := hμgeo 0 (Nat.zero_le _)
      rw [zero_add, geo_zero] at this
      rw [← this, dist_geo _ (by omega)]
    have hne : geo _ s μ 1 ≠ geo _ s α' 1 := by
      intro he
      have e1 : geo _ s α' 1 = geo _ s (P b) 1 := (hgg 1 (by omega)).symm
      have h1 : (puAmalgam h.le).treeGraph.dist (geo _ s μ 1) μ = 1 := by
        rw [dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hμs]
      have h2 : (puAmalgam h.le).treeGraph.dist (geo _ s (P b) 1) (P b) = b - 1 := by
        rw [dist_geo_right _ (by omega), hsb]
      have t := dist_triangle _ μ (geo _ s μ 1) (P b)
      rw [tdist_comm _ μ (geo _ s μ 1), h1, he, e1, h2, hμd] at t
      omega
    obtain ⟨hμα', hshift⟩ := geo_ext hμs (by omega) hne
    have hQ : ∀ i ≤ b + 2 * N, geo _ μ α' (i + 2) = P i :=
      fun i hi => hshift i (by rw [hsd]; exact hi)
    refine ⟨μ, by rw [hμα', hsd]; ring, ?_, ?_, ?_⟩
    · rw [show 2 * (N + 1) = 2 * N + 2 by ring, hQ _ (by omega), hsα]
    · intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have q : geo _ μ α' (2 * 0 + b) = P (b - 2) := by
          rw [show 2 * 0 + b = (b - 2) + 2 by omega]
          exact hQ _ (by omega)
        have e4 : geo _ (P b) s 2 = P (b - 2) := by
          have := geo_symm _ (u := s) (w := P b) (i := b - 2) (by omega)
          rw [hsb, show b - (b - 2) = 2 by omega, hgg _ (by omega)] at this
          exact this
        rw [q, Nat.mul_zero, geo_zero, ← e4]
        exact hcμ
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have q0 : geo _ μ α' (2 * (j' + 1)) = P (2 * j') := by
          rw [show 2 * (j' + 1) = 2 * j' + 2 by ring]
          exact hQ _ (by omega)
        have qb : geo _ μ α' (2 * (j' + 1) + b) = P (2 * j' + b) := by
          rw [show 2 * (j' + 1) + b = (2 * j' + b) + 2 by ring]
          exact hQ _ (by omega)
        rw [q0, qb]
        exact hcrit j' (by omega)
    · intro j hj hj'
      rcases Nat.lt_or_ge j 2 with hj1 | hj2
      · obtain rfl : j = 1 := by omega
        have q0 : geo _ μ α' (2 * 1) = s := by
          rw [show 2 * 1 = 0 + 2 by rfl, hQ 0 (by omega), hP0]
        have q1 : geo _ μ α' (2 * 1 + 1) = geo _ s (P b) 1 := by
          rw [show 2 * 1 + 1 = 1 + 2 by rfl, hQ 1 (by omega), hgg 1 (by omega)]
        have q2 : geo _ μ α' (2 * 1 + 2) = geo _ s (P b) 2 := by
          rw [show 2 * 1 + 2 = 2 + 2 by rfl, hQ 2 (by omega), hgg 2 (by omega)]
        have qm : geo _ μ α' (2 * 1 - 2) = μ := geo_zero _ _ _
        have qb : geo _ μ α' (2 * 1 + b) = P b := by
          rw [show 2 * 1 + b = b + 2 by ring]
          exact hQ _ (by omega)
        rw [q0, q1, q2, qm, qb]
        obtain ⟨t, ht, hteq⟩ := hμt
        exact ⟨⟨t, ht, hteq⟩, hμlam⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hj'1 : 1 ≤ j' := by omega
        have q0 : geo _ μ α' (2 * (j' + 1)) = P (2 * j') := by
          rw [show 2 * (j' + 1) = 2 * j' + 2 by ring]
          exact hQ _ (by omega)
        have q1 : geo _ μ α' (2 * (j' + 1) + 1) = P (2 * j' + 1) := by
          rw [show 2 * (j' + 1) + 1 = (2 * j' + 1) + 2 by ring]
          exact hQ _ (by omega)
        have q2 : geo _ μ α' (2 * (j' + 1) + 2) = P (2 * j' + 2) := by
          rw [show 2 * (j' + 1) + 2 = (2 * j' + 2) + 2 by ring]
          exact hQ _ (by omega)
        have qm : geo _ μ α' (2 * (j' + 1) - 2) = P (2 * j' - 2) := by
          rw [show 2 * (j' + 1) - 2 = (2 * j' - 2) + 2 by omega]
          exact hQ _ (by omega)
        have qb : geo _ μ α' (2 * (j' + 1) + b) = P (2 * j' + b) := by
          rw [show 2 * (j' + 1) + b = (2 * j' + b) + 2 by ring]
          exact hQ _ (by omega)
        rw [q0, q1, q2, qm, qb]
        exact hlam j' hj'1 (by omega)

theorem exists_chain (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') (N : ℕ) :
    ∃ s, (puAmalgam h.le).treeGraph.dist s α' = critDist (puAmalgam h.le) + 2 * N ∧
      geo _ s α' (2 * N) = α ∧
      (∀ j ≤ N, IsCritical _ (geo _ s α' (2 * j))
        (geo _ s α' (2 * j + critDist (puAmalgam h.le)))) ∧
      ∀ j, 1 ≤ j → j ≤ N →
        (∃ t ∈ stab _ (geo _ s α' (2 * j)),
            t • geo _ s α' (2 * j + 2) = geo _ s α' (2 * j - 2)) ∧
        ∃ g : (puAmalgam h.le).Universal, geo _ s α' (2 * j) = g • baseA (puAmalgam h.le) ∧
          geo _ s α' (2 * j + 1) = g • baseB _ ∧
          g⁻¹ • geo _ s α' (2 * j - 2) ∈ S5.lam h (2 ^ k) a
            (g⁻¹ • geo _ s α' (2 * j + critDist (puAmalgam h.le)))
            (g⁻¹ • geo _ s α' (2 * j + 2)) := by
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_chain_sel h hb (fun _ _ => True)
    (fun _ hc' hβ' => (exists_lam_not_le h32 hX2 h52 h54 h55 h56 h59 h hmin hb hd hc'
      hβ').imp fun _ hμ => ⟨hμ.1, hμ.2, trivial⟩) hc N
  refine ⟨s, h1, h2, h3, fun j hj1 hjN => ⟨(h4 j hj1 hjN).1, ?_⟩⟩
  obtain ⟨g, h5, h6, h7, -⟩ := (h4 j hj1 hjN).2
  exact ⟨g, h5, h6, h7⟩

end Transport

end S510

end CFSG.Quasithin.MS93

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBase

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

theorem end_dist (hP : IsGenPolygon Γ 6) {a : V} {n : ℕ} (hn : n ≤ 6) {p : GPath Γ n}
    (hp : p ∈ GPath.nbPaths Γ a n) : Γ.dist a (p n) = n := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have := GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod n hn p hp.2
  rw [← hp.1]
  exact this

theorem eq_of_first_last (hP : IsGenPolygon Γ 6) {a : V} {r r' : GPath Γ 6}
    (hr : r ∈ GPath.nbPaths Γ a 6) (hr' : r' ∈ GPath.nbPaths Γ a 6) (h1 : r 1 = r' 1)
    (h6 : r 6 = r' 6) : r = r' := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have g1 : r.IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 6 le_rfl r hr.2
  have g2 : r'.IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 6 le_rfl r' hr'.2
  have d1 := GPath.IsGeodesic.drop hP.connected g1 1 (by norm_num)
  have d2 := GPath.IsGeodesic.drop hP.connected g2 1 (by norm_num)
  have e : r.drop 1 (by norm_num) = r'.drop 1 (by norm_num) := by
    refine hP.uniqueGeod (6 - 1) _ _ d1 d2 ?_ ?_ (by norm_num)
    · rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ (Nat.zero_le _)]
      exact h1
    · rw [GPath.drop_apply _ _ _ le_rfl, GPath.drop_apply _ _ _ le_rfl]
      exact h6
  exact TitsGeo.eq_of_drop_eq' (by norm_num) (by rw [hr.1, hr'.1]) e

theorem first_eq_of_pen (hP : IsGenPolygon Γ 6) {a : V} {r r' : GPath Γ 6}
    (hr : r ∈ GPath.nbPaths Γ a 6) (hr' : r' ∈ GPath.nbPaths Γ a 6) (h5 : r 5 = r' 5) :
    r 1 = r' 1 := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have g1 : (r.take 5 (by norm_num)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 5 (by norm_num) _
      (hr.2.take 5 (by norm_num))
  have g2 : (r'.take 5 (by norm_num)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 5 (by norm_num) _
      (hr'.2.take 5 (by norm_num))
  have e := hP.uniqueGeod 5 _ _ g1 g2
    (by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 5), GPath.take_apply_of_le _ _ _
      (Nat.zero_le 5), hr.1, hr'.1])
    (by rw [GPath.take_apply_of_le _ _ _ le_rfl, GPath.take_apply_of_le _ _ _ le_rfl]; exact h5)
    (by norm_num)
  have := congrArg (fun t : GPath Γ 5 => t 1) e
  simpa [GPath.take_apply_of_le _ _ _ (show 1 ≤ 5 by norm_num)] using this

theorem mem_stabPath_of_fix [GraphAction X Γ] (hP : IsGenPolygon Γ 6) {a : V} {r : GPath Γ 6}
    (hr : r ∈ GPath.nbPaths Γ a 6) {k : X} (hka : k • a = a) (hk1 : k • r 1 = r 1)
    (hk6 : k • r 6 = r 6) : k ∈ (r.stabPath : Subgroup X) := by
  have e : k • r = r :=
    eq_of_first_last hP (TitsGeo.smul_mem_nbPaths hr hka) hr (by simpa using hk1)
      (by simpa using hk6)
  intro i hi
  have := congrArg (fun t : GPath Γ 6 => t i) e
  simpa using this

theorem exists_base_path (hP : IsGenPolygon Γ 6) {a w b : V} (hw : Γ.Adj a w)
    (hb : Γ.dist a b = 6) : ∃ r ∈ GPath.nbPaths Γ a 6, r 1 = w ∧ r 6 = b := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have hwb : Γ.dist b w = 5 := by
    have hba : Γ.dist b a = 6 := by rw [SimpleGraph.dist_comm]; exact hb
    have h1 := GPath.dist_adj_succ_or hP.connected hc b hw
    have h2 := hP.diam_le b w
    omega
  obtain ⟨g, hg0, hg5, -⟩ := GPath.exists_geodesic' hP.connected b w (n := 5) hwb
  let g' : GPath Γ 6 := g.snoc a (by rw [hg5]; exact hw.symm)
  have hg'0 : g' 0 = b := by
    have : g' 0 = g 0 := GPath.snoc_of_le _ _ _ (Nat.zero_le _)
    rw [this, hg0]
  have hg'5 : g' 5 = w := by
    have : g' 5 = g 5 := GPath.snoc_of_le _ _ _ le_rfl
    rw [this, hg5]
  have hg'6 : g' 6 = a := GPath.snoc_last _ _ _
  have hrev0 : g'.rev 0 = a := by rw [GPath.rev_apply _ (by norm_num)]; exact hg'6
  have hrev1 : g'.rev 1 = w := by rw [GPath.rev_apply _ (by norm_num)]; exact hg'5
  have hrev6 : g'.rev 6 = b := by rw [GPath.rev_apply _ le_rfl]; exact hg'0
  have hdist : Γ.dist (g'.rev 0) (g'.rev 6) = 6 := by
    rw [hrev0, hrev6]
    exact hb
  exact ⟨g'.rev, ⟨hrev0, GPath.noBack_of_dist_eq hP.connected _ hdist⟩, hrev1, hrev6⟩

theorem exists_path_pen (hP : IsGenPolygon Γ 6) {a b y : V} (hb : Γ.dist a b = 6)
    (hy : Γ.Adj b y) : ∃ r ∈ GPath.nbPaths Γ a 6, r 5 = y ∧ r 6 = b := by
  obtain ⟨r, hr, hr1, hr6⟩ := exists_base_path hP hy (by rw [SimpleGraph.dist_comm]; exact hb)
  refine ⟨r.rev, ⟨?_, hr.2.rev⟩, ?_, ?_⟩
  · rw [GPath.rev_apply _ (by norm_num)]
    exact hr6
  · rw [GPath.rev_apply _ (by norm_num)]
    exact hr1
  · rw [GPath.rev_apply _ le_rfl]
    exact hr.1

theorem exists_other {N : Set V} (h : 2 ≤ N.ncard) (w : V) : ∃ c ∈ N, c ≠ w := by
  obtain ⟨c, hc, hne⟩ := Set.exists_ne_of_one_lt_ncard (s := N) (by omega) w
  exact ⟨c, hc, hne⟩

theorem exists_third {N : Set V} (h : 3 ≤ N.ncard) (w₁ w₂ : V) :
    ∃ c ∈ N, c ≠ w₁ ∧ c ≠ w₂ := by
  have h2 : ({w₁, w₂} : Set V).ncard < N.ncard := by
    have := Set.ncard_insert_le w₁ ({w₂} : Set V)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨c, hc, hn⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h2
  exact ⟨c, hc, fun e => hn (Or.inl e), fun e => hn (Or.inr e)⟩

theorem sup_trans {N : Set V} {S₁ S₂ : Subgroup X} {w₁ w₂ c : V} (hw₁ : w₁ ∈ N) (hw₂ : w₂ ∈ N)
    (hc : c ∈ N) (h12 : w₁ ≠ w₂) (hc1 : c ≠ w₁) (hc2 : c ≠ w₂)
    (t₁ : ∀ y ∈ N, ∀ y' ∈ N, y ≠ w₁ → y' ≠ w₁ → ∃ g ∈ S₁, g • y = y')
    (t₂ : ∀ y ∈ N, ∀ y' ∈ N, y ≠ w₂ → y' ≠ w₂ → ∃ g ∈ S₂, g • y = y') {y y' : V} (hy : y ∈ N)
    (hy' : y' ∈ N) : ∃ g ∈ S₁ ⊔ S₂, g • y = y' := by
  by_cases h1 : y ≠ w₁ ∧ y' ≠ w₁
  · obtain ⟨g, hg, e⟩ := t₁ y hy y' hy' h1.1 h1.2
    exact ⟨g, Subgroup.mem_sup_left hg, e⟩
  by_cases h2 : y ≠ w₂ ∧ y' ≠ w₂
  · obtain ⟨g, hg, e⟩ := t₂ y hy y' hy' h2.1 h2.2
    exact ⟨g, Subgroup.mem_sup_right hg, e⟩
  have e1 : y = w₁ ∨ y' = w₁ := by tauto
  have e2 : y = w₂ ∨ y' = w₂ := by tauto
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
  · exact absurd rfl h12
  · obtain ⟨g₁, hg₁, e₁⟩ := t₂ y hy c hc h12 hc2
    obtain ⟨g₂, hg₂, e₂⟩ := t₁ c hc y' hy' hc1 h12.symm
    exact ⟨g₂ * g₁, Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₂) (Subgroup.mem_sup_right hg₁),
      by rw [mul_smul, e₁, e₂]⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := t₁ y hy c hc h12.symm hc1
    obtain ⟨g₂, hg₂, e₂⟩ := t₂ c hc y' hy' hc2 h12
    exact ⟨g₂ * g₁, Subgroup.mul_mem _ (Subgroup.mem_sup_right hg₂) (Subgroup.mem_sup_left hg₁),
      by rw [mul_smul, e₁, e₂]⟩
  · exact absurd rfl h12

section TwoTrans

variable [GraphAction X Γ] {a b₀ : V}

theorem stab_trans (hP : IsGenPolygon Γ 6)
    (horb : ∀ b, Γ.dist a b = 6 → ∃ g : X, g • a = a ∧ g • b₀ = b)
    (htwo : ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ →
      v₁ ≠ v₂ → ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂)
    {p : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ a 6) {y y' : V} (hy : Γ.Adj a y)
    (hy' : Γ.Adj a y') (hyw : y ≠ p 1) (hy'w : y' ≠ p 1) :
    ∃ g ∈ (p.stabPath : Subgroup X), g • y = y' := by
  obtain ⟨h, hha, hhb⟩ := horb _ (end_dist hP le_rfl hp)
  have hh1 : h⁻¹ • a = a := by rw [inv_smul_eq_iff, hha]
  have hadj : ∀ z, Γ.Adj a z → Γ.Adj a (h⁻¹ • z) := fun z hz => by
    have := (GraphAction.adj_smul h⁻¹ a z).mpr hz
    rwa [hh1] at this
  have hp1 : Γ.Adj a (p 1) := by
    have := p.adj 0 (by norm_num)
    rwa [hp.1] at this
  obtain ⟨k, hka, hkb, hkw, hky⟩ := htwo (h⁻¹ • p 1) (h⁻¹ • y) (h⁻¹ • p 1) (h⁻¹ • y')
    (hadj _ hp1) (hadj _ hy) (fun e => hyw (smul_left_cancel h⁻¹ e).symm) (hadj _ hp1)
    (hadj _ hy') (fun e => hy'w (smul_left_cancel h⁻¹ e).symm)
  refine ⟨h * k * h⁻¹, mem_stabPath_of_fix hP hp ?_ ?_ ?_, ?_⟩
  · rw [mul_smul, mul_smul, hh1, hka, hha]
  · rw [mul_smul, mul_smul, hkw, smul_inv_smul]
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hhb.symm, hkb, hhb]
  · rw [mul_smul, mul_smul, hky, smul_inv_smul]

omit [GraphAction X Γ] in
theorem trans_of_two (hcard : 2 ≤ (Γ.neighborSet a).ncard)
    (htwo : ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ →
      v₁ ≠ v₂ → ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂)
    {u u' : V} (hu : Γ.Adj a u) (hu' : Γ.Adj a u') :
    ∃ k : X, k • a = a ∧ k • b₀ = b₀ ∧ k • u = u' := by
  obtain ⟨c, hc, hcu⟩ := exists_other hcard u
  obtain ⟨c', hc', hcu'⟩ := exists_other hcard u'
  obtain ⟨k, h1, h2, h3, -⟩ := htwo u c u' c' hu hc (Ne.symm hcu) hu' hc' (Ne.symm hcu')
  exact ⟨k, h1, h2, h3⟩

theorem noFix_of_two (hP : IsGenPolygon Γ 6) (hcard : 3 ≤ (Γ.neighborSet a).ncard)
    (horb : ∀ b, Γ.dist a b = 6 → ∃ g : X, g • a = a ∧ g • b₀ = b)
    (htwo : ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ →
      v₁ ≠ v₂ → ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂)
    {p : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ a 6) {y : V} (hy : Γ.Adj (p 6) y) (hne : y ≠ p 5) :
    ¬ ∀ g ∈ (p.stabPath : Subgroup X), g • y = y := by
  intro hall
  obtain ⟨r, hr, hr5, hr6⟩ := exists_path_pen hP (end_dist hP le_rfl hp) hy
  have hr1 : r 1 ≠ p 1 := fun e => hne (by
    have := eq_of_first_last hP hr hp e hr6
    rw [← hr5, this])
  have hradj : Γ.Adj a (r 1) := by
    have := r.adj 0 (by norm_num)
    rwa [hr.1] at this
  obtain ⟨c, hc, hcp, hcr⟩ := exists_third hcard (p 1) (r 1)
  obtain ⟨g, hg, hgc⟩ := stab_trans hP horb htwo hp hradj hc hr1 hcp
  have hga : g • a = a := by simpa [hp.1] using hg 0 (Nat.zero_le _)
  have h5 : (g • r) 5 = r 5 := by
    rw [GPath.smul_apply, hr5]
    exact hall g hg
  have := first_eq_of_pen hP (TitsGeo.smul_mem_nbPaths hr hga) hr h5
  rw [GPath.smul_apply, hgc] at this
  exact hcr this

theorem transPair_of_two (hP : IsGenPolygon Γ 6) (hcard : 3 ≤ (Γ.neighborSet a).ncard)
    (horb : ∀ b, Γ.dist a b = 6 → ∃ g : X, g • a = a ∧ g • b₀ = b)
    (htwo : ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ →
      v₁ ≠ v₂ → ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂)
    {p q : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ a 6) (hq : q ∈ GPath.nbPaths Γ a 6)
    (hpq : p 1 ≠ q 1) {y y' : V} (hy : Γ.Adj a y) (hy' : Γ.Adj a y') :
    ∃ g ∈ ((p.stabPath : Subgroup X) ⊔ q.stabPath), g • y = y' := by
  have hp1 : Γ.Adj a (p 1) := by
    have := p.adj 0 (by norm_num)
    rwa [hp.1] at this
  have hq1 : Γ.Adj a (q 1) := by
    have := q.adj 0 (by norm_num)
    rwa [hq.1] at this
  obtain ⟨c, hc, hcp, hcq⟩ := exists_third hcard (p 1) (q 1)
  exact sup_trans (N := Γ.neighborSet a) hp1 hq1 hc hpq hcp hcq
    (fun y hy y' hy' h1 h2 => stab_trans hP horb htwo hp hy hy' h1 h2)
    (fun y hy y' hy' h1 h2 => stab_trans hP horb htwo hq hy hy' h1 h2) hy hy'

end TwoTrans

end CFSG.Quasithin.D4Hex

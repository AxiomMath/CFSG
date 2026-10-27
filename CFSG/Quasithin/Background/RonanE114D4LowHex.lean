module

public import CFSG.Quasithin.Background.RonanE114D4LowRoot

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage4.Hex CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4

section General

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem adj_smul_iff' (g : X) {y z : V D} : (Γ D).Adj (g • y) (g • z) ↔ (Γ D).Adj y z :=
  GraphAction.adj_smul (Γ := Γ D) g y z

theorem fix_inv_smul {A : Subgroup X} {g : X} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) {y : V D}
    (hy : ∀ a ∈ A, a • y = y) : ∀ a ∈ A, a • (g⁻¹ • y) = g⁻¹ • y := by
  intro a ha
  have h1 := hy _ (hg a ha)
  calc a • (g⁻¹ • y) = g⁻¹ • ((g * a * g⁻¹) • y) := by simp [mul_smul]
    _ = g⁻¹ • y := by rw [h1]

theorem fix_smul {A : Subgroup X} {g : X} (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) {y : V D}
    (hy : ∀ a ∈ A, a • y = y) : ∀ a ∈ A, a • (g • y) = g • y := by
  intro a ha
  have h1 := hy _ (hg a ha)
  calc a • (g • y) = g • ((g⁻¹ * a * g) • y) := by simp [mul_smul]
    _ = g • y := by rw [h1]

theorem dist_cases_odd {g h : X} (h6 : n = 6) :
    (Γ D).dist (h • v D false) (g • v D true) = 1 ∨
      (Γ D).dist (h • v D false) (g • v D true) = 3 ∨
      (Γ D).dist (h • v D false) (g • v D true) = 5 := by
  have hodd := odd_dist_smul_v D g h
  rw [SimpleGraph.dist_comm] at hodd
  have hle := dist_le D (h • v D false) (g • v D true)
  obtain ⟨k, hk⟩ := hodd
  omega

theorem dist_cases_even {g h : X} (i : Bool) (h6 : n = 6) :
    (Γ D).dist (h • v D i) (g • v D i) = 0 ∨ (Γ D).dist (h • v D i) (g • v D i) = 2 ∨
      (Γ D).dist (h • v D i) (g • v D i) = 4 ∨ (Γ D).dist (h • v D i) (g • v D i) = 6 := by
  have hev := even_dist_smul_v D h g i
  have hle := dist_le D (h • v D i) (g • v D i)
  obtain ⟨k, hk⟩ := hev
  omega

end General

section Hex

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [CharP K 2] {σ : K →+* K}
  {hσ : ∀ c, σ (σ (σ c)) = c} {D : RankTwoSystem X 6} {ψ : ∀ i : Fin 6, d43Par σ i → X}
  (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) (hψ : D4Coords D hσ ψ) (hσ1 : ∃ c : K, σ c ≠ c)

include hU in
theorem root_three_fix_v (i : Bool) : ∀ a ∈ D.root 3, a • v D i = v D i := by
  intro a ha
  rw [smul_v_eq_iff]
  cases i
  · exact pCoreOf_le 2 _ (root_le_Q_false D (k := 3) (by norm_num) (by norm_num) hU ha)
  · exact pCoreOf_le 2 _ (root_le_Q_true D (k := 3) (by norm_num) (by norm_num) hU ha)

include hU hψ hσ1

theorem point_three {z : V D} (hz : (Γ D).dist (v D false) z = 3)
    (hfix : ∀ a ∈ D.root 3, a • z = z) :
    D.root 3 ⊓ rad D z = ⊥ ∧ ∃ u, (Γ D).Adj z u ∧ (∀ a ∈ D.root 3, a • u = u) ∧
      ∀ w w', (Γ D).Adj z w → (Γ D).Adj z w' → w ≠ u → w' ≠ u →
        ∃ a ∈ D.root 3, a • w = w' := by
  have hconn := (isGenPolygon D).connected
  obtain ⟨p, hp0, hp3, hpnb⟩ := GPath.exists_geodesic' hconn (v D false) z hz
  have hpd : (Γ D).dist (p 0) (p 3) = 3 := by rw [hp0, hp3, hz]
  have hfixi : ∀ a ∈ D.root 3, ∀ i ≤ 3, a • p i = p i := fun a ha i hi =>
    fix_of_geodesic D (by norm_num) p hpd (by rw [hp0]; exact root_three_fix_v hU false a ha)
      (by rw [hp3]; exact hfix a ha) hi
  have h01 : (Γ D).Adj (v D false) (p 1) := hp0 ▸ p.adj 0 (by norm_num)
  obtain ⟨g, hgP, hgv, hgX⟩ := exists_normalizing_of_adj hU hψ h01
  have hgX1 : ∀ a ∈ D.root 3, g * a * g⁻¹ ∈ D.root 3 := fun a ha => (hgX a ha).1
  have hgX2 : ∀ a ∈ D.root 3, g⁻¹ * a * g ∈ D.root 3 := fun a ha => (hgX a ha).2
  have h12 : (Γ D).Adj (p 1) (p 2) := p.adj 1 (by norm_num)
  have h23 : (Γ D).Adj (p 2) (p 3) := p.adj 2 (by norm_num)
  have h12' : (Γ D).Adj (v D true) (g⁻¹ • p 2) := by
    rw [← adj_smul_iff' D g, smul_inv_smul, hgv]
    exact h12
  have hgv2 : g • v D false = v D false := (smul_v_eq_iff D g false).2 hgP
  have hm_ne : g⁻¹ • p 2 ≠ v D false := by
    intro h
    apply hpnb 0 (by norm_num)
    rw [hp0, show (0 : ℕ) + 2 = 2 from rfl, ← smul_inv_smul g (p 2), h, hgv2]
  have hz1 : g⁻¹ • z ≠ v D true := by
    intro h
    have h1 : z = p 1 := by rw [← smul_inv_smul g z, h, hgv]
    have h2 := GPath.dist_prefix hconn p hpd (i := 1) (by norm_num)
    rw [hp0, ← h1, hz] at h2
    exact absurd h2 (by norm_num)
  have hfz' : ∀ a ∈ D.root 3, a • (g⁻¹ • z) = g⁻¹ • z := fix_inv_smul D hgX1 hfix
  have hfm' : ∀ a ∈ D.root 3, a • (g⁻¹ • p 2) = g⁻¹ • p 2 :=
    fix_inv_smul D hgX1 (fun a ha => hfixi a ha 2 (by norm_num))
  have h2z : (Γ D).Adj (g⁻¹ • p 2) (g⁻¹ • z) := by
    rw [adj_smul_iff', ← hp3]
    exact h23
  rcases nbr_true D h12' with h | ⟨x, hx, hxe⟩
  · exact absurd h hm_ne
  by_cases hx1 : x = 1
  · subst hx1
    rw [one_mul] at hxe
    rw [hxe] at h2z
    obtain ⟨hbot, htr⟩ := arm_point hU hψ h2z hz1
    refine ⟨?_, g • (mi D true • v D false), ?_, ?_, ?_⟩
    · rw [eq_bot_iff]
      intro a hai
      obtain ⟨ha, haz⟩ := Subgroup.mem_inf.1 hai
      rw [Subgroup.mem_bot]
      have h1 : g⁻¹ * a * g ∈ D.root 3 ⊓ rad D (g⁻¹ • z) := by
        refine Subgroup.mem_inf.2 ⟨hgX2 a ha, ?_⟩
        rw [mem_rad_smul_iff, inv_inv]
        simpa [mul_assoc] using haz
      rw [hbot, Subgroup.mem_bot] at h1
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h1]
      group
    · have := (adj_smul_iff' D g).2 h2z
      rw [smul_inv_smul] at this
      exact this.symm
    · exact fix_smul D hgX2 (fun a ha => pCoreOf_le 2 _ (root_three_le_rad_arm hU hψ ha))
    · intro w w' hw hw' hwu hw'u
      have hw1 : (Γ D).Adj (g⁻¹ • z) (g⁻¹ • w) := (adj_smul_iff' D g⁻¹).2 hw
      have hw1' : (Γ D).Adj (g⁻¹ • z) (g⁻¹ • w') := (adj_smul_iff' D g⁻¹).2 hw'
      have hne1 : g⁻¹ • w ≠ mi D true • v D false := fun h => hwu (by rw [← h, smul_inv_smul])
      have hne1' : g⁻¹ • w' ≠ mi D true • v D false :=
        fun h => hw'u (by rw [← h, smul_inv_smul])
      obtain ⟨a, ha, haw⟩ := htr _ _ hw1 hw1' hne1 hne1'
      refine ⟨g * a * g⁻¹, hgX1 a ha, ?_⟩
      calc (g * a * g⁻¹) • w = g • (a • (g⁻¹ • w)) := by simp [mul_smul]
        _ = w' := by rw [haw, smul_inv_smul]
  · exfalso
    obtain ⟨hnot, -, -⟩ := active_line hU hψ hσ1 hx hx1
    apply hnot
    have hxm : x * mi D true ∈ P D true :=
      (P D true).mul_mem (B_le_P D true (D.root_le_B le_rfl (by norm_num) hx)) (mi_mem_P D true)
    have hadj1 : (Γ D).Adj ((x * mi D true) • v D false) (v D true) :=
      (adj_true_of_mem D hxm).symm
    have hadj2 : (Γ D).Adj ((x * mi D true) • v D false) (g⁻¹ • z) := by
      rw [← hxe]
      exact h2z
    refine le_rad D hU hadj1 hadj2 (Ne.symm hz1) ?_ ?_ (root_three_fix_v hU true) hfz'
    · intro a ha
      rw [← hxe]
      exact hfm' a ha
    · exact hU.2.1.to_le (D.root_le_U (by norm_num) (by norm_num))

theorem point_class {y : V D} (hy : ∃ h : X, y = h • v D true)
    (hfix : ∀ a ∈ D.root 3, a • y = y) :
    D.root 3 ≤ rad D y ∨ (D.root 3 ⊓ rad D y = ⊥ ∧ ∃ u, (Γ D).Adj y u ∧
      (∀ a ∈ D.root 3, a • u = u) ∧ ∀ w w', (Γ D).Adj y w → (Γ D).Adj y w' → w ≠ u → w' ≠ u →
        ∃ a ∈ D.root 3, a • w = w') := by
  have hconn := (isGenPolygon D).connected
  have hX2 : IsPGroup 2 (D.root 3) := hU.2.1.to_le (D.root_le_U (by norm_num) (by norm_num))
  obtain ⟨h, rfl⟩ := hy
  have hcases := dist_cases_odd D (g := h) (h := 1) rfl
  rw [one_smul] at hcases
  rcases hcases with hd | hd | hd
  · left
    exact root_three_le_rad_of_adj hU hψ (SimpleGraph.dist_eq_one_iff_adj.1 hd)
  · right
    exact point_three hU hψ hσ1 hd hfix
  · exfalso
    obtain ⟨p, hp0, hp5, hpnb⟩ := GPath.exists_geodesic' hconn (v D false) (h • v D true) hd
    have hpd : (Γ D).dist (p 0) (p 5) = 5 := by rw [hp0, hp5, hd]
    have hfixi : ∀ a ∈ D.root 3, ∀ i ≤ 5, a • p i = p i := fun a ha i hi =>
      fix_of_geodesic D (by norm_num) p hpd (by rw [hp0]; exact root_three_fix_v hU false a ha)
        (by rw [hp5]; exact hfix a ha) hi
    have hz3 : (Γ D).dist (v D false) (p 3) = 3 := by
      have := GPath.dist_prefix hconn p hpd (i := 3) (by norm_num)
      rwa [hp0] at this
    obtain ⟨hbot, -⟩ := point_three hU hψ hσ1 hz3 (fun a ha => hfixi a ha 3 (by norm_num))
    have h32 : (Γ D).Adj (p 3) (p 2) := (p.adj 2 (by norm_num)).symm
    have h34 : (Γ D).Adj (p 3) (p 4) := p.adj 3 (by norm_num)
    have hne : p 2 ≠ p 4 := hpnb 2 (by norm_num)
    have hle := le_rad D hU h32 h34 hne (R := D.root 3)
      (fun a ha => MulAction.mem_stabilizer_iff.2 (hfixi a ha 3 (by norm_num))) hX2
      (fun a ha => hfixi a ha 2 (by norm_num)) (fun a ha => hfixi a ha 4 (by norm_num))
    have h3 : D.root 3 = ⊥ := by rw [← inf_eq_left.2 hle]; exact hbot
    exact D.roots.ne_bot 3 ⟨by norm_num, by norm_num⟩ h3

theorem line_class {e : V D} (he : ∃ h : X, e = h • v D false)
    (hfix : ∀ a ∈ D.root 3, a • e = e) :
    D.root 3 ≤ rad D e ∨ ∃ u, (Γ D).Adj e u ∧ (∀ a ∈ D.root 3, a • u = u) ∧
      (∀ w w', (Γ D).Adj e w → (Γ D).Adj e w' → w ≠ u → w' ≠ u → ∃ a ∈ D.root 3, a • w = w') ∧
      ∀ p p', (Γ D).Adj e p → (Γ D).Adj e p' → p ≠ p' →
        ¬ D.root 3 ⊓ rad D e ≤ rad D p ⊓ rad D p' := by
  have hconn := (isGenPolygon D).connected
  have hX2 : IsPGroup 2 (D.root 3) := hU.2.1.to_le (D.root_le_U (by norm_num) (by norm_num))
  obtain ⟨h, rfl⟩ := he
  have hcases := dist_cases_even D (g := h) (h := 1) false rfl
  rw [one_smul] at hcases
  have hthree : ∀ z w w' : V D, (Γ D).dist (v D false) z = 3 → (∀ a ∈ D.root 3, a • z = z) →
      (Γ D).Adj z w → (Γ D).Adj z w' → w ≠ w' → (∀ a ∈ D.root 3, a • w = w) →
        (∀ a ∈ D.root 3, a • w' = w') → False := by
    intro z w w' hz hfz hw hw' hne hfw hfw'
    obtain ⟨hbot, -⟩ := point_three hU hψ hσ1 hz hfz
    have hle := le_rad D hU hw hw' hne (R := D.root 3)
      (fun a ha => MulAction.mem_stabilizer_iff.2 (hfz a ha)) hX2 hfw hfw'
    have h3 : D.root 3 = ⊥ := by rw [← inf_eq_left.2 hle]; exact hbot
    exact D.roots.ne_bot 3 ⟨by norm_num, by norm_num⟩ h3
  rcases hcases with hd | hd | hd | hd
  · left
    have he : h • v D false = v D false := ((hconn.dist_eq_zero_iff).1 hd).symm
    rw [he, rad_v]
    exact root_le_Q_false D (k := 3) (by norm_num) (by norm_num) hU
  · obtain ⟨p, hp0, hp2, hpnb⟩ := GPath.exists_geodesic' hconn (v D false) (h • v D false) hd
    have hpd : (Γ D).dist (p 0) (p 2) = 2 := by rw [hp0, hp2, hd]
    have h01 : (Γ D).Adj (v D false) (p 1) := hp0 ▸ p.adj 0 (by norm_num)
    have h12 : (Γ D).Adj (p 1) (p 2) := p.adj 1 (by norm_num)
    obtain ⟨g, hgP, hgv, hgX⟩ := exists_normalizing_of_adj hU hψ h01
    have hgX1 : ∀ a ∈ D.root 3, g * a * g⁻¹ ∈ D.root 3 := fun a ha => (hgX a ha).1
    have hgX2 : ∀ a ∈ D.root 3, g⁻¹ * a * g ∈ D.root 3 := fun a ha => (hgX a ha).2
    have h12' : (Γ D).Adj (v D true) (g⁻¹ • p 2) := by
      rw [← adj_smul_iff' D g, smul_inv_smul, hgv]
      exact h12
    have hgv2 : g • v D false = v D false := (smul_v_eq_iff D g false).2 hgP
    have hm_ne : g⁻¹ • p 2 ≠ v D false := by
      intro h'
      apply hpnb 0 (by norm_num)
      rw [hp0, show (0 : ℕ) + 2 = 2 from rfl, ← smul_inv_smul g (p 2), h', hgv2]
    rcases nbr_true D h12' with h' | ⟨x, hx, hxe⟩
    · exact absurd h' hm_ne
    have hep : h • v D false = g • ((x * mi D true) • v D false) := by
      rw [← hxe, smul_inv_smul, hp2]
    by_cases hx1 : x = 1
    · subst hx1
      left
      intro a ha
      rw [hep, one_mul, mem_rad_smul_iff]
      exact root_three_le_rad_arm hU hψ (hgX2 a ha)
    · right
      obtain ⟨-, htr, hnot⟩ := active_line hU hψ hσ1 hx hx1
      set e' := (x * mi D true) • v D false with he'
      refine ⟨g • v D true, ?_, ?_, ?_, ?_⟩
      · rw [hep]
        exact (adj_smul_iff' D g).2 (by
          have hxm : x * mi D true ∈ P D true :=
            (P D true).mul_mem (B_le_P D true (D.root_le_B le_rfl (by norm_num) hx))
              (mi_mem_P D true)
          exact (adj_true_of_mem D hxm).symm)
      · exact fix_smul D hgX2 (root_three_fix_v hU true)
      · intro w w' hw hw' hwu hw'u
        rw [hep] at hw hw'
        have hw1 : (Γ D).Adj e' (g⁻¹ • w) := by
          have := (adj_smul_iff' D g⁻¹).2 hw
          rwa [inv_smul_smul] at this
        have hw1' : (Γ D).Adj e' (g⁻¹ • w') := by
          have := (adj_smul_iff' D g⁻¹).2 hw'
          rwa [inv_smul_smul] at this
        have hne1 : g⁻¹ • w ≠ v D true := fun h' => hwu (by rw [← h', smul_inv_smul])
        have hne1' : g⁻¹ • w' ≠ v D true := fun h' => hw'u (by rw [← h', smul_inv_smul])
        obtain ⟨a, ha, haw⟩ := htr _ _ hw1 hw1' hne1 hne1'
        refine ⟨g * a * g⁻¹, hgX1 a ha, ?_⟩
        calc (g * a * g⁻¹) • w = g • (a • (g⁻¹ • w)) := by simp [mul_smul]
          _ = w' := by rw [haw, smul_inv_smul]
      · intro q q' hq hq' hqq hle
        rw [hep] at hq hq' hle
        have hq1 : (Γ D).Adj e' (g⁻¹ • q) := by
          have := (adj_smul_iff' D g⁻¹).2 hq
          rwa [inv_smul_smul] at this
        have hq1' : (Γ D).Adj e' (g⁻¹ • q') := by
          have := (adj_smul_iff' D g⁻¹).2 hq'
          rwa [inv_smul_smul] at this
        apply hnot _ _ hq1 hq1' (fun h' => hqq (smul_left_cancel _ h'))
        intro b hb
        obtain ⟨hb3, hbe⟩ := Subgroup.mem_inf.1 hb
        have h1 : g * b * g⁻¹ ∈ D.root 3 ⊓ rad D (g • e') := by
          refine Subgroup.mem_inf.2 ⟨hgX1 b hb3, ?_⟩
          rw [mem_rad_smul_iff]
          simpa [mul_assoc] using hbe
        obtain ⟨h2, h3⟩ := Subgroup.mem_inf.1 (hle h1)
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [mem_rad_smul_iff, inv_inv]
          simpa [mul_assoc] using h2
        · rw [mem_rad_smul_iff, inv_inv]
          simpa [mul_assoc] using h3
  · exfalso
    obtain ⟨p, hp0, hp4, hpnb⟩ := GPath.exists_geodesic' hconn (v D false) (h • v D false) hd
    have hpd : (Γ D).dist (p 0) (p 4) = 4 := by rw [hp0, hp4, hd]
    have hfixi : ∀ a ∈ D.root 3, ∀ i ≤ 4, a • p i = p i := fun a ha i hi =>
      fix_of_geodesic D (by norm_num) p hpd (by rw [hp0]; exact root_three_fix_v hU false a ha)
        (by rw [hp4]; exact hfix a ha) hi
    have hz3 : (Γ D).dist (v D false) (p 3) = 3 := by
      have := GPath.dist_prefix hconn p hpd (i := 3) (by norm_num)
      rwa [hp0] at this
    exact hthree (p 3) (p 2) (p 4) hz3 (fun a ha => hfixi a ha 3 (by norm_num))
      (p.adj 2 (by norm_num)).symm (p.adj 3 (by norm_num)) (hpnb 2 (by norm_num))
      (fun a ha => hfixi a ha 2 (by norm_num)) (fun a ha => hfixi a ha 4 (by norm_num))
  · exfalso
    have hd1 : (Γ D).dist (v D true) (h • v D false) = 5 := by
      have hodd := odd_dist_smul_v D 1 h
      rw [one_smul] at hodd
      have hle := dist_le D (v D true) (h • v D false)
      have htri : (Γ D).dist (v D false) (h • v D false) ≤
          (Γ D).dist (v D false) (v D true) + (Γ D).dist (v D true) (h • v D false) :=
        hconn.dist_triangle
      have h1 : (Γ D).dist (v D false) (v D true) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.2 (adj_v D).symm
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨q, hq0, hq5, hqnb⟩ := GPath.exists_geodesic' hconn (v D true) (h • v D false) hd1
    have hqd : (Γ D).dist (q 0) (q 5) = 5 := by rw [hq0, hq5, hd1]
    have hfixi : ∀ a ∈ D.root 3, ∀ i ≤ 5, a • q i = q i := fun a ha i hi =>
      fix_of_geodesic D (by norm_num) q hqd (by rw [hq0]; exact root_three_fix_v hU true a ha)
        (by rw [hq5]; exact hfix a ha) hi
    have hz3 : (Γ D).dist (v D false) (q 2) = 3 := by
      have h02 := GPath.dist_prefix hconn q hqd (i := 2) (by norm_num)
      rw [hq0] at h02
      have h25 := GPath.dist_le_sub hconn q (i := 2) (j := 5) (by norm_num) le_rfl
      rw [hq5] at h25
      have h1 : (Γ D).dist (v D false) (v D true) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.2 (adj_v D).symm
      have t1 : (Γ D).dist (v D false) (q 2) ≤
          (Γ D).dist (v D false) (v D true) + (Γ D).dist (v D true) (q 2) := hconn.dist_triangle
      have t2 : (Γ D).dist (v D false) (h • v D false) ≤
          (Γ D).dist (v D false) (q 2) + (Γ D).dist (q 2) (h • v D false) := hconn.dist_triangle
      omega
    exact hthree (q 2) (q 1) (q 3) hz3 (fun a ha => hfixi a ha 2 (by norm_num))
      (q.adj 1 (by norm_num)).symm (q.adj 2 (by norm_num)) (hqnb 1 (by norm_num))
      (fun a ha => hfixi a ha 1 (by norm_num)) (fun a ha => hfixi a ha 3 (by norm_num))

omit hψ hσ1 in
theorem sylow_line {e : V D} (he : ∃ h : X, e = h • v D false) (hne : e ≠ v D false) :
    ∃ p, (Γ D).Adj e p ∧ D.U ⊓ rad D e ≤ rad D p := by
  have hconn := (isGenPolygon D).connected
  obtain ⟨h, rfl⟩ := he
  set R := D.U ⊓ rad D (h • v D false) with hR
  have hR2 : IsPGroup 2 R := hU.2.1.to_le inf_le_left
  have hRv : ∀ (i : Bool), ∀ r ∈ R, r • v D i = v D i := fun i r hr =>
    (smul_v_eq_iff D r i).2 (B_le_P D i (D.U_le_B (Subgroup.mem_inf.1 hr).1))
  have hRe : ∀ r ∈ R, r • (h • v D false) = h • v D false := fun r hr =>
    pCoreOf_le 2 _ (Subgroup.mem_inf.1 hr).2
  have hcases := dist_cases_odd D (g := 1) (h := h) rfl
  rw [one_smul] at hcases
  have hgeo : ∀ k, k < 6 → 2 ≤ k → (Γ D).dist (h • v D false) (v D true) = k →
      ∃ p, (Γ D).Adj (h • v D false) p ∧ R ≤ rad D p := by
    intro k hk6 hk2 hd
    obtain ⟨q, hq0, hqk, hqnb⟩ := GPath.exists_geodesic' hconn (h • v D false) (v D true) hd
    have hqd : (Γ D).dist (q 0) (q k) = k := by rw [hq0, hqk, hd]
    have hfixi : ∀ r ∈ R, ∀ i ≤ k, r • q i = q i := fun r hr i hi =>
      fix_of_geodesic D hk6 q hqd (by rw [hq0]; exact hRe r hr)
        (by rw [hqk]; exact hRv true r hr) hi
    refine ⟨q 1, hq0 ▸ q.adj 0 (by omega), ?_⟩
    exact le_rad D hU (q.adj 0 (by omega)).symm (q.adj 1 (by omega)) (hqnb 0 (by omega))
      (fun r hr => MulAction.mem_stabilizer_iff.2 (hfixi r hr 1 (by omega))) hR2
      (fun r hr => hfixi r hr 0 (by omega)) (fun r hr => hfixi r hr 2 (by omega))
  rcases hcases with hd | hd | hd
  · have hadj : (Γ D).Adj (h • v D false) (v D true) := SimpleGraph.dist_eq_one_iff_adj.1 hd
    refine ⟨v D true, hadj, ?_⟩
    exact le_rad D hU hadj.symm (adj_v D) hne (fun r hr => MulAction.mem_stabilizer_iff.2
      (hRv true r hr)) hR2 hRe (hRv false)
  · exact hgeo 3 (by norm_num) (by norm_num) hd
  · exact hgeo 5 (by norm_num) (by norm_num) hd

end Hex

section Symmetry

variable {X : Type*} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n)
  (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤)

include hU in
theorem exists_symmetry (h : Nat.card (D.root 1) ≠ Nat.card (D.root n)) (α : MulAut X) :
    ∃ β : V D ≃ V D, (∀ (g : X) (y : V D), β (g • y) = α g • β y) ∧
      (∀ y w : V D, (Γ D).Adj (β y) (β w) ↔ (Γ D).Adj y w) ∧
      ∀ (i : Bool) (g : X), ∃ g' : X, β (g • v D i) = g' • v D i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let SU : Sylow 2 X := hU.2.1.toSylow hidx
  have hidx' : ¬ 2 ∣ (D.U.map α.toMonoidHom).index := by
    have e := Subgroup.index_map_equiv D.U α
    rw [show D.U.map α.toMonoidHom = D.U.map (α : X →* X) from rfl, e]
    exact hidx
  let SU' : Sylow 2 X := (hU.2.1.map α.toMonoidHom).toSylow hidx'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X SU SU'
  have hUc : D.U.map α.toMonoidHom = D.U.map (MulAut.conj c).toMonoidHom := by
    have := congrArg (fun S : Sylow 2 X => (S : Subgroup X)) hc
    simp only [Sylow.coe_subgroup_smul] at this
    exact this.symm
  set α' : MulAut X := (MulAut.conj c)⁻¹ * α with hα'
  have hα'U : D.U.map α'.toMonoidHom = D.U := by
    have e : D.U.map α'.toMonoidHom =
        (D.U.map α.toMonoidHom).map (MulAut.conj c)⁻¹.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [e, hUc, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, MulAut.inv_apply, mul_assoc]
  obtain ⟨β', hβ'g, hβ'a, hβ'v⟩ := exists_vertex_equiv D hU h α' hα'U
  have hαc : ∀ g : X, α g = c * α' g * c⁻¹ := by
    intro g
    simp [hα', MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]
  refine ⟨β'.trans (MulAction.toPerm c), fun g y => ?_, fun y w => ?_, fun i g => ?_⟩
  · show c • β' (g • y) = α g • (c • β' y)
    rw [hβ'g, hαc, mul_smul, mul_smul, inv_smul_smul]
  · show (Γ D).Adj (c • β' y) (c • β' w) ↔ _
    rw [adj_smul_iff', hβ'a]
  · refine ⟨c * α' g, ?_⟩
    show c • β' (g • v D i) = _
    rw [hβ'g, hβ'v, mul_smul]

variable {D}

theorem stab_symm {α : MulAut X} {β : V D ≃ V D} (hβ : ∀ (g : X) (y : V D), β (g • y) = α g • β y)
    (z : V D) : stab D (β z) = (stab D z).map α.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro hx
    apply β.injective
    rw [hβ, MulEquiv.apply_symm_apply, hx]
  · intro hx
    have := congrArg β hx
    rwa [hβ, MulEquiv.apply_symm_apply] at this

theorem rad_symm {α : MulAut X} {β : V D ≃ V D} (hβ : ∀ (g : X) (y : V D), β (g • y) = α g • β y)
    (z : V D) : rad D (β z) = (rad D z).map α.toMonoidHom := by
  rw [rad, stab_symm hβ]
  exact pCoreOf_map_mulEquiv 2 α _

end Symmetry

section HexAut

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [CharP K 2] {σ : K →+* K}
  {hσ : ∀ c, σ (σ (σ c)) = c} {D : RankTwoSystem X 6} {ψ : ∀ i : Fin 6, d43Par σ i → X}
  (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) (hψ : D4Coords D hσ ψ) (hσ1 : ∃ c : K, σ c ≠ c)

include hψ hσ1 in
theorem card_root_one_ne_six : Nat.card (D.root 1) ≠ Nat.card (D.root ((6 : ℕ) : ℤ)) := by
  have hb0 : Nat.card (D.root 1) = Nat.card K := by
    refine (Nat.card_congr (Equiv.ofBijective (fun s : K => (⟨ψ 0 s, hψ.mem 0 s⟩ : D.root 1))
      ⟨fun a b hab => hψ.inj 0 (congrArg Subtype.val hab), fun y => ?_⟩)).symm
    obtain ⟨s, hs⟩ := hψ.surj 0 y y.2
    exact ⟨s, Subtype.ext hs⟩
  have hb5 : Nat.card (D.root ((6 : ℕ) : ℤ)) = Nat.card (fixedField σ) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun s : fixedField σ =>
      (⟨ψ 5 s, hψ.mem 5 s⟩ : D.root ((6 : ℕ) : ℤ)))
      ⟨fun a b hab => hψ.inj 5 (congrArg Subtype.val hab), fun y => ?_⟩)).symm
    obtain ⟨s, hs⟩ := hψ.surj 5 y y.2
    exact ⟨s, Subtype.ext hs⟩
  haveI : Finite K := Finite.of_injective (ψ 0) (hψ.inj 0)
  rw [hb0, hb5]
  obtain ⟨c, hc⟩ := hσ1
  intro heq
  have hlt : Nat.card (fixedField σ) < Nat.card K := by
    have := Set.ncard_lt_ncard (s := (fixedField σ : Set K)) (t := Set.univ)
      (Set.ssubset_univ_iff.2 fun h => hc (by
        have : c ∈ (fixedField σ : Set K) := h ▸ Set.mem_univ c
        exact this)) (Set.toFinite _)
    rwa [Set.ncard_univ, ← Nat.card_coe_set_eq] at this
  omega

include hU hψ hσ1

theorem point_class_aut (α : MulAut X) {y : V D} (hy : ∃ h : X, y = h • v D true)
    (hA : (D.root 3).map α.toMonoidHom ≤ stab D y) :
    (D.root 3).map α.toMonoidHom ≤ rad D y ∨ ((D.root 3).map α.toMonoidHom ⊓ rad D y = ⊥ ∧
      ∃ u, (Γ D).Adj y u ∧ (∀ a ∈ (D.root 3).map α.toMonoidHom, a • u = u) ∧
        ∀ w w', (Γ D).Adj y w → (Γ D).Adj y w' → w ≠ u → w' ≠ u →
          ∃ a ∈ (D.root 3).map α.toMonoidHom, a • w = w') := by
  obtain ⟨β, hβg, hβa, hβt⟩ := exists_symmetry D hU (card_root_one_ne_six hψ hσ1) α
  set y' := β.symm y with hy'
  have hyy : β y' = y := by rw [hy', Equiv.apply_symm_apply]
  have hpt : ∃ h : X, y' = h • v D true := by
    obtain ⟨g, i, hgi⟩ := exists_smul_v D y'
    obtain ⟨g', hg'⟩ := hβt i g
    obtain ⟨h, rfl⟩ := hy
    have : vtype D.B D.N D.w₁ D.w₂ (h • v D true) = vtype D.B D.N D.w₁ D.w₂ (g' • v D i) := by
      rw [← hg', ← hgi, hyy]
    rw [vtype_smul_v, vtype_smul_v] at this
    subst this
    exact ⟨g, hgi⟩
  have hfix : ∀ a ∈ D.root 3, a • y' = y' := by
    intro a ha
    apply β.injective
    rw [hβg, hyy]
    exact hA ⟨a, ha, rfl⟩
  rcases point_class hU hψ hσ1 hpt hfix with hle | ⟨hbot, u', hu', hfu', htr⟩
  · left
    rw [← hyy, rad_symm hβg]
    exact Subgroup.map_mono hle
  · right
    refine ⟨?_, β u', ?_, ?_, ?_⟩
    · rw [← hyy, rad_symm hβg, ← Subgroup.map_inf_eq _ _ _ α.injective, hbot, Subgroup.map_bot]
    · rw [← hyy, hβa]
      exact hu'
    · rintro _ ⟨a, ha, rfl⟩
      show α a • β u' = β u'
      rw [← hβg, hfu' a ha]
    · intro w w' hw hw' hwu hw'u
      have hw1 : (Γ D).Adj y' (β.symm w) := by
        rw [← hβa, hyy, Equiv.apply_symm_apply]
        exact hw
      have hw1' : (Γ D).Adj y' (β.symm w') := by
        rw [← hβa, hyy, Equiv.apply_symm_apply]
        exact hw'
      have hne : β.symm w ≠ u' := fun h' => hwu (by rw [← h', Equiv.apply_symm_apply])
      have hne' : β.symm w' ≠ u' := fun h' => hw'u (by rw [← h', Equiv.apply_symm_apply])
      obtain ⟨a, ha, haw⟩ := htr _ _ hw1 hw1' hne hne'
      refine ⟨α a, ⟨a, ha, rfl⟩, ?_⟩
      have := congrArg β haw
      rwa [hβg, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

theorem line_class_aut (α : MulAut X) {e : V D} (he : ∃ h : X, e = h • v D false)
    (hA : (D.root 3).map α.toMonoidHom ≤ stab D e) :
    (D.root 3).map α.toMonoidHom ≤ rad D e ∨
      ∃ u, (Γ D).Adj e u ∧ (∀ a ∈ (D.root 3).map α.toMonoidHom, a • u = u) ∧
        (∀ w w', (Γ D).Adj e w → (Γ D).Adj e w' → w ≠ u → w' ≠ u →
          ∃ a ∈ (D.root 3).map α.toMonoidHom, a • w = w') ∧
        ∀ p p', (Γ D).Adj e p → (Γ D).Adj e p' → p ≠ p' →
          ¬ (D.root 3).map α.toMonoidHom ⊓ rad D e ≤ rad D p ⊓ rad D p' := by
  obtain ⟨β, hβg, hβa, hβt⟩ := exists_symmetry D hU (card_root_one_ne_six hψ hσ1) α
  set e' := β.symm e with he'
  have hee : β e' = e := by rw [he', Equiv.apply_symm_apply]
  have hln : ∃ h : X, e' = h • v D false := by
    obtain ⟨g, i, hgi⟩ := exists_smul_v D e'
    obtain ⟨g', hg'⟩ := hβt i g
    obtain ⟨h, rfl⟩ := he
    have : vtype D.B D.N D.w₁ D.w₂ (h • v D false) = vtype D.B D.N D.w₁ D.w₂ (g' • v D i) := by
      rw [← hg', ← hgi, hee]
    rw [vtype_smul_v, vtype_smul_v] at this
    subst this
    exact ⟨g, hgi⟩
  have hfix : ∀ a ∈ D.root 3, a • e' = e' := by
    intro a ha
    apply β.injective
    rw [hβg, hee]
    exact hA ⟨a, ha, rfl⟩
  rcases line_class hU hψ hσ1 hln hfix with hle | ⟨u', hu', hfu', htr, hnot⟩
  · left
    rw [← hee, rad_symm hβg]
    exact Subgroup.map_mono hle
  · right
    refine ⟨β u', ?_, ?_, ?_, ?_⟩
    · rw [← hee, hβa]
      exact hu'
    · rintro _ ⟨a, ha, rfl⟩
      show α a • β u' = β u'
      rw [← hβg, hfu' a ha]
    · intro w w' hw hw' hwu hw'u
      have hw1 : (Γ D).Adj e' (β.symm w) := by
        rw [← hβa, hee, Equiv.apply_symm_apply]
        exact hw
      have hw1' : (Γ D).Adj e' (β.symm w') := by
        rw [← hβa, hee, Equiv.apply_symm_apply]
        exact hw'
      have hne : β.symm w ≠ u' := fun h' => hwu (by rw [← h', Equiv.apply_symm_apply])
      have hne' : β.symm w' ≠ u' := fun h' => hw'u (by rw [← h', Equiv.apply_symm_apply])
      obtain ⟨a, ha, haw⟩ := htr _ _ hw1 hw1' hne hne'
      refine ⟨α a, ⟨a, ha, rfl⟩, ?_⟩
      have := congrArg β haw
      rwa [hβg, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    · intro p p' hp hp' hpp hle
      have hp1 : (Γ D).Adj e' (β.symm p) := by
        rw [← hβa, hee, Equiv.apply_symm_apply]
        exact hp
      have hp1' : (Γ D).Adj e' (β.symm p') := by
        rw [← hβa, hee, Equiv.apply_symm_apply]
        exact hp'
      apply hnot _ _ hp1 hp1' (fun h' => hpp (β.symm.injective h'))
      intro b hb
      obtain ⟨hb3, hbe⟩ := Subgroup.mem_inf.1 hb
      have h1 : α b ∈ (D.root 3).map α.toMonoidHom ⊓ rad D e := by
        refine Subgroup.mem_inf.2 ⟨⟨b, hb3, rfl⟩, ?_⟩
        rw [← hee, rad_symm hβg]
        exact ⟨b, hbe, rfl⟩
      obtain ⟨h2, h3⟩ := Subgroup.mem_inf.1 (hle h1)
      rw [← Equiv.apply_symm_apply β p, rad_symm hβg] at h2
      rw [← Equiv.apply_symm_apply β p', rad_symm hβg] at h3
      obtain ⟨b2, hb2, hb2e⟩ := h2
      obtain ⟨b3, hb3', hb3e⟩ := h3
      have e2 : b2 = b := α.injective hb2e
      have e3 : b3 = b := α.injective hb3e
      exact Subgroup.mem_inf.2 ⟨e2 ▸ hb2, e3 ▸ hb3'⟩

end HexAut

end CFSG.Quasithin.RonanE114Low

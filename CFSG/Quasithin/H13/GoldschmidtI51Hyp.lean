module

public import CFSG.Quasithin.H13.GoldschmidtI51Nb
public import CFSG.Quasithin.H13.GoldschmidtI51Rx

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

theorem faithful (hD : IsDSystem .C3 Gs) {g : G} (hg : ∀ x : G ⧸ Gs 0, g • x = x) : g = 1 := by
  let K : Subgroup G := (MulAction.toPermHom G (G ⧸ Gs 0)).ker
  have hK : K.Normal := MonoidHom.normal_ker _
  have hmemK : ∀ k : G, k ∈ K ↔ ∀ x : G ⧸ Gs 0, k • x = x := fun k => by
    rw [MonoidHom.mem_ker, Equiv.ext_iff]
    exact Iff.rfl
  have hKT : K ≤ Gs 0 ⊓ Gs 1 ⊓ Gs 2 := by
    intro k hk
    have hk' := (hmemK k).1 hk
    have hk0 : k ∈ Gs 0 := by
      have := hk' (oPt Gs)
      rw [smul_oPt', oPt, QuotientGroup.eq, mul_one] at this
      simpa using (Gs 0).inv_mem this
    exact QQ_le_TT hD 0 (Rx_le_Q0 hD ⟨hk0, fun p _ => hk' p⟩)
  have h1 := hD.d4core K hK hKT
  have hgK : g ∈ K := (hmemK g).2 hg
  rw [h1] at hgK
  exact Subgroup.mem_bot.1 hgK

theorem exists_moving (hD : IsDSystem .C3 Gs) {z : G ⧸ Gs 0} (hz : z ∈ D2 Gs) :
    ∃ r ∈ Rx Gs, r • z ≠ z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r0, hr0, hr01⟩ := Rx_ne hD
  apply hr01
  refine faithful hD (fun x => ?_)
  by_cases hx : Col Gs (oPt Gs) x
  · exact hr0.2 x hx
  · have hx2 := mem_D2_of_not_col hD hx
    obtain ⟨h, hh, rfl⟩ := D2_trans hD hz hx2
    have hconj := Rx_conj ((Gs 0).inv_mem hh) hr0
    rw [inv_inv] at hconj
    calc r0 • (h • z) = h • ((h⁻¹ * r0 * h) • z) := by simp [mul_smul]
      _ = h • z := by rw [hcon _ hconj]

@[expose] def OddTriple (Gs : Fin 3 → Subgroup G) (x y w : G ⧸ Gs 0) : Prop :=
  ∀ p, Col Gs w p ↔ (Col Gs x p ↔ Col Gs y p)

omit [Group G] [Finite G] in
theorem ncard_triple_union {α : Type*} [Finite α] (A B D C : Set α) (hA : A.ncard = 30)
    (hB : B.ncard = 30) (hD : D.ncard = 30) (hC : C.ncard = 15) (hAB : A ∩ B = C)
    (hAD : A ∩ D = C) (hBD : B ∩ D = C) : (A ∪ B ∪ D).ncard = 60 := by
  have h1 := Set.ncard_union_add_ncard_inter A B (Set.toFinite _) (Set.toFinite _)
  rw [hAB, hC, hA, hB] at h1
  have h2 := Set.ncard_union_add_ncard_inter (A ∪ B) D (Set.toFinite _) (Set.toFinite _)
  have h3 : (A ∪ B) ∩ D = C := by
    rw [Set.union_inter_distrib_right, hAD, hBD, Set.union_self]
  rw [h3, hC, hD] at h2
  omega

theorem odd_hyp (hD : IsDSystem .C3 Gs) {z : G ⧸ Gs 0} (hz : z ∈ D2 Gs) :
    ∃ w, OddTriple Gs (oPt Gs) z w := by
  obtain ⟨r, hr, hrz⟩ := exists_moving hD hz
  have hrG0 : r ∈ Gs 0 := hr.1
  have hzo : ¬ Col Gs (oPt Gs) z := hz.1
  have hwo : ¬ Col Gs (oPt Gs) (r • z) := fun h => hzo ((col_oPt_smul hrG0 z).1 h)
  have hcolw : ∀ p, Col Gs (oPt Gs) p → (Col Gs (r • z) p ↔ Col Gs z p) := fun p hp => by
    have := col_smul r z p
    rwa [hr.2 p hp] at this
  have hne_oz : oPt Gs ≠ z := fun h => hzo (h ▸ col_refl _)
  have hne_ow : oPt Gs ≠ r • z := fun h => hwo (h ▸ col_refl _)
  have hC15 : (Nb Gs (oPt Gs) ∩ Nb Gs z).ncard = 15 := ncard_Nb_inter_noncol hD hzo
  have hCw : Nb Gs (oPt Gs) ∩ Nb Gs (r • z) = Nb Gs (oPt Gs) ∩ Nb Gs z := by
    ext c
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h2⟩, fun h => hzo (h ▸ h2), (hcolw c h2).1 h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h2⟩, fun h => hwo (h ▸ h2), (hcolw c h2).2 h4⟩
  have hsub : Nb Gs (oPt Gs) ∩ Nb Gs z ⊆ Nb Gs z ∩ Nb Gs (r • z) := by
    intro c hc
    have hc' : c ∈ Nb Gs (oPt Gs) ∩ Nb Gs (r • z) := by rw [hCw]; exact hc
    exact ⟨hc.2, hc'.2⟩
  have hzw : ¬ Col Gs z (r • z) := by
    intro hcol
    have h13 := ncard_Nb_inter_col hD (Ne.symm hrz) hcol
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hZW : Nb Gs z ∩ Nb Gs (r • z) = Nb Gs (oPt Gs) ∩ Nb Gs z :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_Nb_inter_noncol hD hzw, hC15])
      (Set.toFinite _)).symm
  have hne_zw : z ≠ r • z := Ne.symm hrz
  have hcov : ∀ p : G ⧸ Gs 0, p = oPt Gs ∨ p = z ∨ p = r • z ∨
      p ∈ Nb Gs (oPt Gs) ∪ Nb Gs z ∪ Nb Gs (r • z) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hcon
    have h60 : (Nb Gs (oPt Gs) ∪ Nb Gs z ∪ Nb Gs (r • z)).ncard = 60 :=
      ncard_triple_union _ _ _ (Nb Gs (oPt Gs) ∩ Nb Gs z) (ncard_Nb hD _) (ncard_Nb hD _)
        (ncard_Nb hD _) hC15 rfl hCw hZW
    have hdis : Disjoint ({oPt Gs, z, r • z} : Set (G ⧸ Gs 0))
        (Nb Gs (oPt Gs) ∪ Nb Gs z ∪ Nb Gs (r • z)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rcases hx with rfl | rfl | rfl
      · rcases hx' with (h | h) | h
        · exact h.1 rfl
        · exact hzo (col_symm h.2)
        · exact hwo (col_symm h.2)
      · rcases hx' with (h | h) | h
        · exact hzo h.2
        · exact h.1 rfl
        · exact hzw (col_symm h.2)
      · rcases hx' with (h | h) | h
        · exact hwo h.2
        · exact hzw h.2
        · exact h.1 rfl
    have h3 : ({oPt Gs, z, r • z} : Set (G ⧸ Gs 0)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨_, _, _, hne_oz, hne_ow, hne_zw, rfl⟩
    have hU := Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _)
    rw [h3, h60] at hU
    have heq := Set.eq_of_subset_of_ncard_le (Set.subset_univ
      (({oPt Gs, z, r • z} : Set (G ⧸ Gs 0)) ∪ (Nb Gs (oPt Gs) ∪ Nb Gs z ∪ Nb Gs (r • z))))
      (by rw [Set.ncard_univ, card_Omega hD, hU]) (Set.toFinite _)
    have hpU : p ∈ ({oPt Gs, z, r • z} : Set (G ⧸ Gs 0)) ∪
        (Nb Gs (oPt Gs) ∪ Nb Gs z ∪ Nb Gs (r • z)) := by rw [heq]; exact Set.mem_univ p
    rcases hpU with h | h
    · rcases h with h | h | h
      · exact hp1 h
      · exact hp2 h
      · exact hp3 h
    · exact hp4 h
  refine ⟨r • z, fun p => ?_⟩
  by_cases hop : Col Gs (oPt Gs) p
  · rw [hcolw p hop]; simp [hop]
  · by_cases hpz : p = z
    · subst hpz
      simp only [hop, col_refl, iff_true]
      exact iff_false_intro (fun h => hzw (col_symm h))
    · by_cases hpw : p = r • z
      · subst hpw
        simp [hop, col_refl, hzw]
      · have hpA : p ∉ Nb Gs (oPt Gs) := fun h => hop h.2
        have hboth : ¬ (Col Gs z p ∧ Col Gs (r • z) p) := fun ⟨h1, h2⟩ => by
          have : p ∈ Nb Gs z ∩ Nb Gs (r • z) := ⟨⟨hpz, h1⟩, hpw, h2⟩
          rw [hZW] at this
          exact hpA this.1
        have hone : Col Gs z p ∨ Col Gs (r • z) p := by
          rcases hcov p with h | h | h | (h | h) | h
          · exact absurd h (fun h' => hop (h' ▸ col_refl _))
          · exact absurd h hpz
          · exact absurd h hpw
          · exact absurd h hpA
          · exact Or.inl h.2
          · exact Or.inr h.2
        simp only [hop, false_iff]
        constructor
        · intro hw hzp
          exact hboth ⟨hzp, hw⟩
        · intro hnz
          tauto

omit [Finite G] in
theorem OddTriple.smul {x y w : G ⧸ Gs 0} (h : OddTriple Gs x y w) (g : G) :
    OddTriple Gs (g • x) (g • y) (g • w) := fun p => by
  have h1 := h (g⁻¹ • p)
  rw [← col_smul g, smul_inv_smul, ← col_smul g x, ← col_smul g y, smul_inv_smul] at h1
  exact h1

theorem odd_col0 (hD : IsDSystem .C3 Gs) {s0 q0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hq0 : q0 ∈ QQ Gs 0) (hq01 : q0 ∉ QQ Gs 1) :
    OddTriple Gs (oPt Gs) ((s0 : G) : G ⧸ Gs 0) ((q0 * s0 : G) : G ⧸ Gs 0) := by
  have hq0G : q0 ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq0)
  have hq0P : q0 ∈ Gs 1 := TT_le 1 (QQ_le_TT hD 0 hq0)
  have hs1 : q0 * s0 ∈ Gs 1 := (Gs 1).mul_mem hq0P hs0
  have hs10 : q0 * s0 ∉ Gs 0 := fun h0 => hs00 (by
    simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hq0G) h0)
  intro p
  by_cases hop : Col Gs (oPt Gs) p
  ·
    have key : Col Gs ((q0 * s0 : G) : G ⧸ Gs 0) p ↔ Col Gs ((s0 : G) : G ⧸ Gs 0) p := by
      by_cases hpo : p = oPt Gs
      · subst hpo
        exact ⟨fun _ => col_symm (col_oPt.2 (G1_sub_Nbd hs0)),
          fun _ => col_symm (col_oPt.2 (G1_sub_Nbd hs1))⟩
      · have hpD : p ∈ Dlt Gs := ⟨hpo, hop⟩
        rw [col_y0_iff hD hs1 hs10 hpD, col_y0_iff hD hs0 hs00 hpD]
    rw [key]; simp [hop]
  ·
    have hp2 := mem_D2_of_not_col hD hop
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨hz1, y, hy, hyz⟩ := hp2
    have hg : g ∉ Nbd Gs := fun h' => hz1 (col_oPt.2 h')
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have ha := col_oPt.1 hy.2
    have hag := col_mk.1 hyz
    obtain ⟨s, hs, hs0', hcol⟩ := line_has_point hD hg ha hag 1 (Gs 0).one_mem
    have hboth : ¬ (Col Gs ((s0 : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0) ∧
        Col Gs ((q0 * s0 : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0)) := by
      rintro ⟨h1, h2⟩
      have c1 : g⁻¹ * (1 * s0) ∈ Nbd Gs := by
        have := col_of_mem (h := 1) (s := s0) (g := g) (by simpa using h1)
        exact this
      have c2 : g⁻¹ * (1 * (q0 * s0)) ∈ Nbd Gs :=
        col_of_mem (h := 1) (s := q0 * s0) (g := g) (by simpa using h2)
      have := line_point_unique hD hg (Gs 0).one_mem hs0 hs00 hs1 c1 c2
      have h' : s0⁻¹ * q0 * s0 ∈ Gs 0 := by simpa [mul_assoc] using this
      exact hq01 ((fix_iff hD hs0 hs00 hq0).1 h')
    have hone : Col Gs ((s0 : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0) ∨
        Col Gs ((q0 * s0 : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0) := by
      have hcs : Col Gs ((s : G) : G ⧸ Gs 0) (g : G ⧸ Gs 0) := by
        rw [col_mk]
        have := Nbd_inv hcol
        simpa using this
      rcases line_pts hD hs0 hs00 hq0 hq01 hs with h | h | h
      · exact absurd h hs0'
      · left
        have : ((s : G) : G ⧸ Gs 0) = ((s0 : G) : G ⧸ Gs 0) := by
          rw [QuotientGroup.eq]
          simpa using (Gs 0).inv_mem h
        rwa [this] at hcs
      · right
        have : ((s : G) : G ⧸ Gs 0) = ((q0 * s0 : G) : G ⧸ Gs 0) := by
          rw [QuotientGroup.eq]
          simpa using (Gs 0).inv_mem h
        rwa [this] at hcs
    simp only [hop, false_iff]
    constructor
    · intro hw hy0
      exact hboth ⟨hy0, hw⟩
    · intro hnz
      tauto

theorem odd_col (hD : IsDSystem .C3 Gs) {y : G ⧸ Gs 0} (hy : y ∈ Dlt Gs) :
    ∃ w, OddTriple Gs (oPt Gs) y w := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  have hy' := hy
  rw [Dlt_eq_orbit hD hs0 hs00 hq0 hq01, MulAction.mem_orbit_iff] at hy'
  obtain ⟨h, rfl⟩ := hy'
  have h0 := (odd_col0 hD hs0 hs00 hq0 hq01).smul (h : G)
  rw [smul_oPt h.2] at h0
  exact ⟨_, h0⟩

end CFSG.Quasithin.H13.I51

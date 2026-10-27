module

public import CFSG.Quasithin.H13.GoldschmidtI51Lines

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

@[expose] def D2 (Gs : Fin 3 → Subgroup G) : Set (G ⧸ Gs 0) :=
  {z | ¬ Col Gs (oPt Gs) z ∧ ∃ y ∈ Dlt Gs, Col Gs y z}

@[expose] def Ey (Gs : Fin 3 → Subgroup G) (y : G ⧸ Gs 0) : Set (G ⧸ Gs 0) :=
  {z | ¬ Col Gs (oPt Gs) z ∧ Col Gs y z}

@[expose] def Fpts (Gs : Fin 3 → Subgroup G) : Set (G ⧸ Gs 0) :=
  {y | y ∈ Dlt Gs ∧ lineOf Gs y ∈ FarLines Gs}

theorem ncard_Fpts (hD : IsDSystem .C3 Gs) : (Fpts Gs).ncard = 16 := by
  have := ncard_PtsOn hD (FarLines Gs)
  rw [ncard_FarLines hD] at this
  exact this

omit [Finite G] in
theorem far_of_lineOf {x : ↥(Gs 0)} (hx : (x : LinesO Gs) ∈ FarLines Gs) : ¬ Nr Gs x := by
  obtain ⟨f, hf, hnf⟩ := hx
  intro hnr
  have hP := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hf)
  have hP' : (f : G)⁻¹ * x ∈ Gs 0 ⊓ Gs 1 := by simpa using hP
  have := Nr_mul_right (v := ((f : G)⁻¹ * x)⁻¹) hnr ((Gs 0 ⊓ Gs 1).inv_mem hP')
  apply hnf
  have e : (x : G) * ((f : G)⁻¹ * x)⁻¹ = f := by group
  rwa [e] at this

theorem Ey_s0 (hD : IsDSystem .C3 Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0) :
    Ey Gs ((s0 : G) : G ⧸ Gs 0) = (fun w => s0 • w) '' Fpts Gs := by
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    induction z using QuotientGroup.induction_on with | _ g => ?_
    rw [col_oPt] at hz1
    rw [col_mk] at hz2
    obtain ⟨x, hx, s'', hs'', c, hc, hnx, hs''0, hge⟩ := decomp_far hD hz1 hs0 hz2
    have hmem : (x * s'') ∈ Nbd Gs := ⟨x, hx, s'', hs'', 1, (Gs 0).one_mem, by group⟩
    have hw : ((x * s'' : G) : G ⧸ Gs 0) ∈ Fpts Gs := by
      refine ⟨⟨?_, col_oPt.2 hmem⟩, ?_⟩
      · intro he
        rw [oPt, QuotientGroup.eq, mul_one] at he
        have h1 : x * s'' ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
        exact hs''0 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hx) h1)
      · rw [lineOf_eq hD hx hs'' hs''0]
        exact ⟨⟨x, hx⟩, rfl, hnx⟩
    refine ⟨_, hw, ?_⟩
    show ((s0 * (x * s'') : G) : G ⧸ Gs 0) = _
    rw [hge]
    have e : s0 * (x * s'') = s0 * x * s'' := by group
    rw [e, mk_mul_G0 hc]
  · rintro ⟨w, ⟨hwD, hwF⟩, rfl⟩
    obtain ⟨x, hx, s'', hs'', hs''0, rfl⟩ := rep_of_Dlt hwD
    rw [lineOf_eq hD hx hs'' hs''0] at hwF
    have hnx := far_of_lineOf (x := ⟨x, hx⟩) hwF
    have hnx' : ¬ Nr Gs x := hnx
    refine ⟨?_, ?_⟩
    · show ¬ Col Gs (oPt Gs) ((s0 * (x * s'') : G) : G ⧸ Gs 0)
      rw [col_oPt]
      have := far_not_col hD (s := s0⁻¹) ((Gs 1).inv_mem hs0)
        (fun h => hs00 (by simpa using (Gs 0).inv_mem h)) hx hnx' hs'' hs''0
      simpa using this
    · show Col Gs ((s0 : G) : G ⧸ Gs 0) ((s0 * (x * s'') : G) : G ⧸ Gs 0)
      rw [col_mk]
      exact ⟨x, hx, s'', hs'', 1, (Gs 0).one_mem, by group⟩

omit [Finite G] in
theorem smul_oPt {h : G} (hh : h ∈ Gs 0) : h • oPt Gs = oPt Gs := by
  show ((h * 1 : G) : G ⧸ Gs 0) = ((1 : G) : G ⧸ Gs 0)
  rw [QuotientGroup.eq]
  simpa using (Gs 0).inv_mem hh

omit [Finite G] in
theorem col_oPt_smul {h : G} (hh : h ∈ Gs 0) (z : G ⧸ Gs 0) :
    Col Gs (oPt Gs) (h • z) ↔ Col Gs (oPt Gs) z := by
  conv_lhs => rw [← smul_oPt hh]
  exact col_smul h _ _

omit [Finite G] in
theorem Ey_smul {h : G} (hh : h ∈ Gs 0) (y : G ⧸ Gs 0) :
    Ey Gs (h • y) = (fun w => h • w) '' Ey Gs y := by
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    refine ⟨h⁻¹ • z, ⟨?_, ?_⟩, by simp⟩
    · intro hc
      apply hz1
      have := (col_oPt_smul hh (h⁻¹ • z)).2 hc
      rwa [smul_inv_smul] at this
    · have := (col_smul h⁻¹ (h • y) z).2 hz2
      rwa [inv_smul_smul] at this
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    exact ⟨fun hc => hw1 ((col_oPt_smul hh w).1 hc), (col_smul h y w).2 hw2⟩

theorem ncard_Ey (hD : IsDSystem .C3 Gs) {y : G ⧸ Gs 0} (hy : y ∈ Dlt Gs) :
    (Ey Gs y).ncard = 16 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  rw [Dlt_eq_orbit hD hs0 hs00 hq0 hq01, MulAction.mem_orbit_iff] at hy
  obtain ⟨h, rfl⟩ := hy
  have h1 : ((h : ↥(Gs 0)) • ((s0 : G) : G ⧸ Gs 0)) = (h : G) • ((s0 : G) : G ⧸ Gs 0) := rfl
  rw [h1, Ey_smul h.2, Set.ncard_image_of_injective _ (MulAction.injective (h : G)),
    Ey_s0 hD hs0 hs00, Set.ncard_image_of_injective _ (MulAction.injective s0), ncard_Fpts hD]

theorem ncard_D2 (hD : IsDSystem .C3 Gs) : (D2 Gs).ncard = 32 := by
  classical
  have : Fintype (G ⧸ Gs 0) := Fintype.ofFinite _
  have hA : (Dlt Gs).toFinset.card = 30 := by
    rw [← Set.ncard_eq_toFinset_card' (Dlt Gs)]; exact ncard_Dlt hD
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Dlt Gs).toFinset) (t := (D2 Gs).toFinset) (fun y z => Col Gs y z)
  have hL : ∀ y ∈ (Dlt Gs).toFinset,
      ((D2 Gs).toFinset.bipartiteAbove (fun y z => Col Gs y z) y).card = 16 := by
    intro y hy
    have hy' : y ∈ Dlt Gs := by simpa using hy
    have : (D2 Gs).toFinset.bipartiteAbove (fun y z => Col Gs y z) y = (Ey Gs y).toFinset := by
      ext z
      rw [Finset.mem_bipartiteAbove, Set.mem_toFinset, Set.mem_toFinset]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, y, hy', h2⟩, h2⟩
    rw [this, ← Set.ncard_eq_toFinset_card' (Ey Gs y)]
    exact ncard_Ey hD hy'
  have hR : ∀ z ∈ (D2 Gs).toFinset,
      ((Dlt Gs).toFinset.bipartiteBelow (fun y z => Col Gs y z) z).card = 15 := by
    intro z hz
    have hz' : z ∈ D2 Gs := by simpa using hz
    induction z using QuotientGroup.induction_on with | _ g => ?_
    obtain ⟨hz1, y, hy, hyz⟩ := hz'
    have hg : g ∉ Nbd Gs := fun h' => hz1 (col_oPt.2 h')
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have ha : a ∈ Nbd Gs := col_oPt.1 hy.2
    have hag : a⁻¹ * g ∈ Nbd Gs := col_mk.1 hyz
    have : (Dlt Gs).toFinset.bipartiteBelow (fun y z => Col Gs y z) (g : G ⧸ Gs 0) =
        (Cz Gs g).toFinset := by
      ext w
      rw [Finset.mem_bipartiteBelow, Set.mem_toFinset, Set.mem_toFinset]
      exact Iff.rfl
    rw [this, ← Set.ncard_eq_toFinset_card' (Cz Gs g)]
    exact ncard_Cz hD hg ha hag
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, hA] at h
  rw [Set.ncard_eq_toFinset_card' (D2 Gs)]
  omega

@[expose] def Ybd (Gs : Fin 3 → Subgroup G) : Set G := {g | ∃ a ∈ Nbd Gs, ∃ b ∈ Nbd Gs, g = a * b}

theorem Ybd_mul_Nbd (hD : IsDSystem .C3 Gs) {g n : G} (hg : g ∈ Ybd Gs) (hn : n ∈ Nbd Gs) :
    g * n ∈ Ybd Gs := by
  by_cases hgN : g ∈ Nbd Gs
  · exact ⟨g, hgN, n, hn, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hg' : (a * b)⁻¹ ∉ Nbd Gs := fun h => hgN (by simpa using Nbd_inv h)
  have ha' : (a * b)⁻¹ * a ∈ Nbd Gs := by
    have := Nbd_inv hb
    simpa [mul_assoc] using this
  have hag' : ((a * b)⁻¹ * a)⁻¹ * (a * b)⁻¹ ∈ Nbd Gs := by
    have := Nbd_inv ha
    simpa [mul_assoc] using this
  have hall := line_has_point hD hg' ha' hag'
  obtain ⟨x, hx, t, ht, c, hc, rfl⟩ := hn
  obtain ⟨s, hs, hs0, hxs⟩ := hall x hx
  rw [inv_inv] at hxs
  refine ⟨a * b * x * s, by simpa [mul_assoc] using hxs, s⁻¹ * t * c, ?_, by group⟩
  exact Nbd_mul_G0 hc (G1_sub_Nbd ((Gs 1).mul_mem ((Gs 1).inv_mem hs) ht))

theorem Ybd_univ (hD : IsDSystem .C3 Gs) (g : G) : g ∈ Ybd Gs := by
  let N : Subgroup G :=
    { carrier := {x | ∀ g ∈ Ybd Gs, g * x ∈ Ybd Gs ∧ g * x⁻¹ ∈ Ybd Gs}
      mul_mem' := fun {x y} hx hy g hg => by
        refine ⟨?_, ?_⟩
        · have := (hy _ ((hx g hg).1)).1
          simpa [mul_assoc] using this
        · have := (hx _ ((hy g hg).2)).2
          simpa [mul_assoc] using this
      one_mem' := fun g hg => by simpa using hg
      inv_mem' := fun {x} hx g hg => ⟨(hx g hg).2, by simpa using (hx g hg).1⟩ }
  have hgen : ∀ x, x ∈ Nbd Gs → x⁻¹ ∈ Nbd Gs → x ∈ N := fun x hx hx' g hg =>
    ⟨Ybd_mul_Nbd hD hg hx, Ybd_mul_Nbd hD hg hx'⟩
  have h0 : Gs 0 ≤ N := fun x hx =>
    hgen x (G0_sub_Nbd hx) (G0_sub_Nbd ((Gs 0).inv_mem hx))
  have h1 : Gs 1 ≤ N := fun x hx =>
    hgen x (G1_sub_Nbd hx) (G1_sub_Nbd ((Gs 1).inv_mem hx))
  have h2 : Gs 2 ≤ N := fun x hx =>
    hgen x (G2_sub_Nbd hD hx) (G2_sub_Nbd hD ((Gs 2).inv_mem hx))
  have : (⊤ : Subgroup G) ≤ N := by
    rw [← hD.d4gen]; exact sup_le (sup_le h0 h1) h2
  have h1Y : (1 : G) ∈ Ybd Gs :=
    ⟨1, G0_sub_Nbd (Gs 0).one_mem, 1, G0_sub_Nbd (Gs 0).one_mem, by group⟩
  simpa using ((this (Subgroup.mem_top g)) 1 h1Y).1

theorem card_Omega (hD : IsDSystem .C3 Gs) : Nat.card (G ⧸ Gs 0) = 63 := by
  have hu : (Set.univ : Set (G ⧸ Gs 0)) = insert (oPt Gs) (Dlt Gs ∪ D2 Gs) := by
    ext z
    induction z using QuotientGroup.induction_on with | _ g => ?_
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_union, true_iff]
    by_cases hgN : g ∈ Nbd Gs
    · by_cases hz : (g : G ⧸ Gs 0) = oPt Gs
      · exact Or.inl hz
      · exact Or.inr (Or.inl ⟨hz, col_oPt.2 hgN⟩)
    · obtain ⟨a, ha, b, hb, rfl⟩ := Ybd_univ hD g
      refine Or.inr (Or.inr ⟨fun h' => hgN (col_oPt.1 h'), (a : G ⧸ Gs 0), ⟨?_, col_oPt.2 ha⟩, ?_⟩)
      · intro he
        rw [oPt, QuotientGroup.eq, mul_one] at he
        have haG : a ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
        exact hgN (G0_mul_Nbd haG hb)
      · rw [col_mk]; simpa using hb
  have hdisj : Disjoint (Dlt Gs) (D2 Gs) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2.1 hz1.2
  have hnot : oPt Gs ∉ Dlt Gs ∪ D2 Gs := by
    rintro (h | h)
    · exact h.1 rfl
    · exact h.1 (col_refl _)
  rw [← Set.ncard_univ, hu, Set.ncard_insert_of_notMem hnot (Set.toFinite _),
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ncard_Dlt hD, ncard_D2 hD]

end CFSG.Quasithin.H13.I51

module

public import CFSG.Quasithin.H13.GoldschmidtI51Dist

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

@[expose] def Nb (Gs : Fin 3 → Subgroup G) (u : G ⧸ Gs 0) : Set (G ⧸ Gs 0) :=
  {p | p ≠ u ∧ Col Gs u p}

omit [Finite G] in
theorem Nb_smul (g : G) (u : G ⧸ Gs 0) : Nb Gs (g • u) = (fun p => g • p) '' Nb Gs u := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ • p, ⟨fun h => h1 ?_, ?_⟩, by simp⟩
    · rw [inv_smul_eq_iff] at h; exact h
    · have := (col_smul g⁻¹ (g • u) p).2 h2
      rwa [inv_smul_smul] at this
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    exact ⟨fun h => hw1 (MulAction.injective g h), (col_smul g u w).2 hw2⟩

omit [Finite G] in
theorem Nb_oPt : Nb Gs (oPt Gs) = Dlt Gs := rfl

omit [Finite G] in
theorem smul_oPt' (g : G) : g • oPt Gs = ((g : G) : G ⧸ Gs 0) := by
  show ((g * 1 : G) : G ⧸ Gs 0) = _
  rw [mul_one]

theorem ncard_Nb (hD : IsDSystem .C3 Gs) (u : G ⧸ Gs 0) : (Nb Gs u).ncard = 30 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  rw [← smul_oPt', Nb_smul, Set.ncard_image_of_injective _ (MulAction.injective g), Nb_oPt,
    ncard_Dlt hD]

theorem mem_D2_of_not_col (hD : IsDSystem .C3 Gs) {z : G ⧸ Gs 0} (hz : ¬ Col Gs (oPt Gs) z) :
    z ∈ D2 Gs := by
  induction z using QuotientGroup.induction_on with | _ g => ?_
  refine ⟨hz, ?_⟩
  have hgN : g ∉ Nbd Gs := fun h => hz (col_oPt.2 h)
  obtain ⟨a, ha, b, hb, hab⟩ := Ybd_univ hD g
  refine ⟨(a : G ⧸ Gs 0), ⟨?_, col_oPt.2 ha⟩, ?_⟩
  · intro he
    rw [oPt, QuotientGroup.eq, mul_one] at he
    have haG : a ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
    exact hgN (by rw [hab]; exact G0_mul_Nbd haG hb)
  · rw [col_mk, hab]; simpa using hb

theorem col_y0_iff (hD : IsDSystem .C3 Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    {p : G ⧸ Gs 0} (hp : p ∈ Dlt Gs) : Col Gs ((s0 : G) : G ⧸ Gs 0) p ↔ p ∉ Fpts Gs := by
  obtain ⟨h, hh, t, ht, ht0, rfl⟩ := rep_of_Dlt hp
  rw [col_mk]
  constructor
  · intro hc hF
    obtain ⟨-, hl⟩ := hF
    rw [lineOf_eq hD hh ht ht0] at hl
    have hnf := far_of_lineOf (x := ⟨h, hh⟩) hl
    exact far_not_col hD hs0 hs00 hh hnf ht ht0 (by simpa [mul_assoc] using hc)
  · intro hnF
    by_contra hc
    apply hnF
    refine ⟨hp, ?_⟩
    rw [lineOf_eq hD hh ht ht0]
    exact ⟨⟨h, hh⟩, rfl, fun hnr => hc (by simpa [mul_assoc] using near_collinear hD hnr hs0 ht)⟩

theorem ncard_Nb_inter_y0 (hD : IsDSystem .C3 Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0) :
    (Nb Gs (oPt Gs) ∩ Nb Gs ((s0 : G) : G ⧸ Gs 0)).ncard = 13 := by
  have hy0 : ((s0 : G) : G ⧸ Gs 0) ∈ Dlt Gs := by
    refine ⟨?_, col_oPt.2 (G1_sub_Nbd hs0)⟩
    intro he
    rw [oPt, QuotientGroup.eq, mul_one] at he
    exact hs00 (by simpa using (Gs 0).inv_mem he)
  have hy0F : ((s0 : G) : G ⧸ Gs 0) ∉ Fpts Gs :=
    (col_y0_iff hD hs0 hs00 hy0).1 (col_refl _)
  have hset : Nb Gs (oPt Gs) ∩ Nb Gs ((s0 : G) : G ⧸ Gs 0) =
      (Dlt Gs \ Fpts Gs) \ {((s0 : G) : G ⧸ Gs 0)} := by
    ext p
    constructor
    · rintro ⟨hp, hp2, hp3⟩
      exact ⟨⟨hp, (col_y0_iff hD hs0 hs00 hp).1 hp3⟩, hp2⟩
    · rintro ⟨⟨hp, hpF⟩, hne⟩
      exact ⟨hp, hne, (col_y0_iff hD hs0 hs00 hp).2 hpF⟩
  have hsub : Fpts Gs ⊆ Dlt Gs := fun p hp => hp.1
  rw [hset, Set.ncard_sdiff_singleton_of_mem
    (show ((s0 : G) : G ⧸ Gs 0) ∈ Dlt Gs \ Fpts Gs from ⟨hy0, hy0F⟩), Set.ncard_sdiff hsub,
    ncard_Dlt hD, ncard_Fpts hD]

theorem ncard_Nb_inter_col (hD : IsDSystem .C3 Gs) {u v : G ⧸ Gs 0} (huv : u ≠ v)
    (hcol : Col Gs u v) : (Nb Gs u ∩ Nb Gs v).ncard = 13 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  have hw : (g : G)⁻¹ • v ∈ Dlt Gs := by
    refine ⟨fun h => huv ?_, ?_⟩
    · rw [inv_smul_eq_iff] at h
      rw [h, smul_oPt']
    · have := (col_smul g⁻¹ _ v).2 hcol
      rw [← smul_oPt', inv_smul_smul] at this
      exact this
  have hw' := hw
  rw [Dlt_eq_orbit hD hs0 hs00 hq0 hq01, MulAction.mem_orbit_iff] at hw'
  obtain ⟨h, hh⟩ := hw'
  have hv : v = (g * (h : G)) • ((s0 : G) : G ⧸ Gs 0) := by
    have h1 : ((h : ↥(Gs 0)) • ((s0 : G) : G ⧸ Gs 0)) = (h : G) • ((s0 : G) : G ⧸ Gs 0) := rfl
    rw [h1] at hh
    rw [mul_smul, hh, smul_inv_smul]
  have hu : ((g : G) : G ⧸ Gs 0) = (g * (h : G)) • oPt Gs := by
    rw [mul_smul, smul_oPt h.2, smul_oPt']
  rw [hv, hu, Nb_smul, Nb_smul, ← Set.image_inter (MulAction.injective _),
    Set.ncard_image_of_injective _ (MulAction.injective _)]
  exact ncard_Nb_inter_y0 hD hs0 hs00

theorem ncard_Nb_inter_noncol (hD : IsDSystem .C3 Gs) {u v : G ⧸ Gs 0}
    (huv : ¬ Col Gs u v) : (Nb Gs u ∩ Nb Gs v).ncard = 15 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  have hw : ¬ Col Gs (oPt Gs) ((g : G)⁻¹ • v) := fun h => huv (by
    have := (col_smul g _ _).2 h
    rwa [smul_inv_smul, smul_oPt'] at this)
  have hD2 := mem_D2_of_not_col hD hw
  have hv : v = (g : G) • ((g : G)⁻¹ • v) := (smul_inv_smul g v).symm
  have hu : ((g : G) : G ⧸ Gs 0) = (g : G) • oPt Gs := (smul_oPt' g).symm
  rw [hu, hv, Nb_smul, Nb_smul, ← Set.image_inter (MulAction.injective _),
    Set.ncard_image_of_injective _ (MulAction.injective _)]
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective ((g : G)⁻¹ • v)
  rw [← hg']
  rw [← hg'] at hD2
  obtain ⟨hz1, y, hy, hyz⟩ := hD2
  have hg : g' ∉ Nbd Gs := fun h' => hz1 (col_oPt.2 h')
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have ha := col_oPt.1 hy.2
  have hag := col_mk.1 hyz
  have hset : Nb Gs (oPt Gs) ∩ Nb Gs (g' : G ⧸ Gs 0) = Cz Gs g' := by
    ext p
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hp3, hp4⟩
      exact ⟨⟨hp1, hp2⟩, col_symm hp4⟩
    · rintro ⟨⟨hp1, hp2⟩, hp3⟩
      refine ⟨⟨hp1, hp2⟩, ?_, col_symm hp3⟩
      intro he
      rw [← he] at hz1
      exact hz1 hp2
  rw [hset]
  exact ncard_Cz hD hg ha hag

end CFSG.Quasithin.H13.I51

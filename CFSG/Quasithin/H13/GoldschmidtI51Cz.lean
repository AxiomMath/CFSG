module

public import CFSG.Quasithin.H13.GoldschmidtI51Prop
public import CFSG.Quasithin.H13.GoldschmidtI51Dich

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

theorem decomp_far (hD : IsDSystem .C3 Gs) {g s1 : G} (hg : g ∉ Nbd Gs) (hs1 : s1 ∈ Gs 1)
    (hcol : s1⁻¹ * g ∈ Nbd Gs) :
    ∃ x ∈ Gs 0, ∃ s'' ∈ Gs 1, ∃ c ∈ Gs 0, ¬ Nr Gs x ∧ s'' ∉ Gs 0 ∧ g = s1 * x * s'' * c := by
  obtain ⟨x, hx, s'', hs'', c, hc, e⟩ := hcol
  have hge : g = s1 * x * s'' * c := by
    have := congrArg (fun w => s1 * w) e
    simpa [mul_assoc] using this
  have hs''0 : s'' ∉ Gs 0 := fun h0 => hg ⟨1, (Gs 0).one_mem, s1, hs1, x * s'' * c,
    (Gs 0).mul_mem ((Gs 0).mul_mem hx h0) hc, by rw [hge]; group⟩
  refine ⟨x, hx, s'', hs'', c, hc, fun hnr => hg ?_, hs''0, hge⟩
  have h1 : (s1⁻¹)⁻¹ * x * s'' ∈ Nbd Gs := near_collinear hD hnr ((Gs 1).inv_mem hs1) hs''
  rw [hge]
  rw [inv_inv] at h1
  exact Nbd_mul_G0 hc (by simpa [mul_assoc] using h1)

theorem line_point_unique (hD : IsDSystem .C3 Gs) {g h s s' : G} (hg : g ∉ Nbd Gs)
    (hh : h ∈ Gs 0) (hs : s ∈ Gs 1) (_hs0 : s ∉ Gs 0) (hs' : s' ∈ Gs 1)
    (h1 : g⁻¹ * (h * s) ∈ Nbd Gs) (h2 : g⁻¹ * (h * s') ∈ Nbd Gs) : s⁻¹ * s' ∈ Gs 0 := by
  by_contra hne
  have hg' : h⁻¹ * g ∉ Nbd Gs := fun hc => hg (by
    have := G0_mul_Nbd hh hc
    simpa using this)
  have hcol : s⁻¹ * (h⁻¹ * g) ∈ Nbd Gs := by
    have := Nbd_inv h1
    simpa [mul_assoc] using this
  obtain ⟨x, hx, s'', hs'', c, hc, hnx, hs''0, hge⟩ := decomp_far hD hg' hs hcol
  have hs2 : s⁻¹ * s' ∈ Gs 1 := (Gs 1).mul_mem ((Gs 1).inv_mem hs) hs'
  have hnc := far_not_col hD hs2 hne hx hnx hs'' hs''0
  apply hnc
  have e : (s⁻¹ * s')⁻¹ * (x * s'') = ((c⁻¹ * ((x * s'')⁻¹ * (s⁻¹ * s')))⁻¹) * c⁻¹ := by
    group
  have h3 : c⁻¹ * ((x * s'')⁻¹ * (s⁻¹ * s')) ∈ Nbd Gs := by
    have h4 : (h⁻¹ * g)⁻¹ * (s') ∈ Nbd Gs := by
      have : (h⁻¹ * g)⁻¹ * s' = g⁻¹ * (h * s') := by group
      rw [this]; exact h2
    rw [hge] at h4
    have e2 : (s * x * s'' * c)⁻¹ * s' = c⁻¹ * ((x * s'')⁻¹ * (s⁻¹ * s')) := by group
    rwa [e2] at h4
  rw [e]
  exact Nbd_mul_G0 ((Gs 0).inv_mem hc) (Nbd_inv h3)

omit [Finite G] in
theorem mk_mul_G0 {u c : G} (hc : c ∈ Gs 0) : ((u * c : G) : G ⧸ Gs 0) = ((u : G) : G ⧸ Gs 0) := by
  rw [QuotientGroup.eq]
  have : (u * c)⁻¹ * u = c⁻¹ := by group
  rw [this]; exact (Gs 0).inv_mem hc

omit [Finite G] in
theorem rep_of_Dlt {y : G ⧸ Gs 0} (hy : y ∈ Dlt Gs) :
    ∃ h ∈ Gs 0, ∃ s ∈ Gs 1, s ∉ Gs 0 ∧ y = ((h * s : G) : G ⧸ Gs 0) := by
  obtain ⟨hy1, hy2⟩ := hy
  induction y using QuotientGroup.induction_on with | _ a => ?_
  rw [col_oPt] at hy2
  obtain ⟨x, hx, s, hs, c, hc, rfl⟩ := hy2
  have hpe := mk_mul_G0 (Gs := Gs) (u := x * s) hc
  refine ⟨x, hx, s, hs, fun h0 => hy1 ?_, hpe⟩
  rw [hpe, oPt, QuotientGroup.eq, mul_one]
  exact (Gs 0).inv_mem ((Gs 0).mul_mem hx h0)

abbrev LinesO (Gs : Fin 3 → Subgroup G) : Type := ↥(Gs 0) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)

noncomputable def lineOf (Gs : Fin 3 → Subgroup G) (y : G ⧸ Gs 0) : LinesO Gs :=
  haveI : Nonempty (LinesO Gs) := ⟨((1 : ↥(Gs 0)) : LinesO Gs)⟩
  Classical.epsilon fun x : LinesO Gs =>
    ∃ h : ↥(Gs 0), (h : LinesO Gs) = x ∧ ∃ s ∈ Gs 1, y = (((h : G) * s : G) : G ⧸ Gs 0)

theorem lineOf_eq (hD : IsDSystem D Gs) {h s : G} (hh : h ∈ Gs 0) (hs : s ∈ Gs 1)
    (hs0 : s ∉ Gs 0) : lineOf Gs ((h * s : G) : G ⧸ Gs 0) = ((⟨h, hh⟩ : ↥(Gs 0)) : LinesO Gs) := by
  have hex : ∃ x : LinesO Gs, ∃ h' : ↥(Gs 0), (h' : LinesO Gs) = x ∧ ∃ s' ∈ Gs 1,
      ((h * s : G) : G ⧸ Gs 0) = (((h' : G) * s' : G) : G ⧸ Gs 0) :=
    ⟨_, ⟨h, hh⟩, rfl, s, hs, rfl⟩
  have : Nonempty (LinesO Gs) := ⟨((1 : ↥(Gs 0)) : LinesO Gs)⟩
  obtain ⟨h', hh', s', hs', he⟩ := Classical.epsilon_spec hex
  show Classical.epsilon _ = _
  rw [← hh', QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rw [QuotientGroup.eq] at he
  have hrel : s⁻¹ * (h⁻¹ * h') * s' ∈ Gs 0 := by simpa [mul_assoc] using he
  have h0 : h⁻¹ * h' ∈ Gs 0 := (Gs 0).mul_mem ((Gs 0).inv_mem hh) h'.2
  have h1 : h⁻¹ * h' ∈ Gs 1 := uniq_line hD hs hs0 hs' h0 hrel
  have e : (h' : G)⁻¹ * h = (h⁻¹ * h')⁻¹ := by group
  show ((h' : G)⁻¹ * h) ∈ Gs 0 ⊓ Gs 1
  rw [e]
  exact ⟨(Gs 0).inv_mem h0, (Gs 1).inv_mem h1⟩

@[expose] def Cz (Gs : Fin 3 → Subgroup G) (g : G) : Set (G ⧸ Gs 0) :=
  {y | y ∈ Dlt Gs ∧ Col Gs y ((g : G) : G ⧸ Gs 0)}

omit [Finite G] in
theorem col_of_mem {h s g : G} (hc : Col Gs (((h * s : G)) : G ⧸ Gs 0) (g : G ⧸ Gs 0)) :
    g⁻¹ * (h * s) ∈ Nbd Gs := by
  rw [col_mk] at hc
  have := Nbd_inv hc
  simpa using this

theorem ncard_Cz (hD : IsDSystem .C3 Gs) {g a : G} (hg : g ∉ Nbd Gs) (ha : a ∈ Nbd Gs)
    (hag : a⁻¹ * g ∈ Nbd Gs) : (Cz Gs g).ncard = 15 := by
  have hall := line_has_point hD hg ha hag
  have hcard : (Set.univ : Set (LinesO Gs)).ncard = 15 := by
    rw [Set.ncard_univ, ← Subgroup.index_eq_card]; exact (gqLoc hD).idx01
  rw [← hcard]
  refine Set.ncard_congr (fun y _ => lineOf Gs y) (fun _ _ => Set.mem_univ _) ?_ ?_
  · intro y1 y2 hy1 hy2 heq
    obtain ⟨h1, hh1, s1, hs1, hs10, rfl⟩ := rep_of_Dlt hy1.1
    obtain ⟨h2, hh2, s2, hs2, hs20, rfl⟩ := rep_of_Dlt hy2.1
    rw [lineOf_eq hD hh1 hs1 hs10, lineOf_eq hD hh2 hs2 hs20] at heq
    have hP := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)
    have hP' : h1⁻¹ * h2 ∈ Gs 0 ⊓ Gs 1 := by simpa using hP
    have c1 := col_of_mem hy1.2
    have c2 : g⁻¹ * (h1 * ((h1⁻¹ * h2) * s2)) ∈ Nbd Gs := by
      have := col_of_mem hy2.2
      simpa [mul_assoc] using this
    have := line_point_unique hD hg hh1 hs1 hs10
      ((Gs 1).mul_mem hP'.2 hs2) c1 c2
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using this
  · intro x _
    induction x using QuotientGroup.induction_on with | _ h => ?_
    obtain ⟨s, hs, hs0, hcol⟩ := hall h.1 h.2
    have hy : (((h : G) * s : G) : G ⧸ Gs 0) ∈ Cz Gs g := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro he
        rw [oPt, QuotientGroup.eq, mul_one] at he
        have h1 : (h : G) * s ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
        exact hs0 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem h.2) h1)
      · rw [col_oPt]; exact ⟨h, h.2, s, hs, 1, (Gs 0).one_mem, by group⟩
      · rw [col_mk]
        have := Nbd_inv hcol
        simpa using this
    exact ⟨_, hy, lineOf_eq hD h.2 hs hs0⟩

end CFSG.Quasithin.H13.I51

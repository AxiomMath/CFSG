module

public import CFSG.Quasithin.H13.GoldschmidtI51Cz

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

omit [Finite G] in
theorem ncard_orbit_lines (f : ↥(Gs 0)) :
    (MulAction.orbit ↥((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)) (f : LinesO Gs)).ncard =
      ((Gs 0 ⊓ Gs 1) ⊓ cj (f : G) (Gs 0 ⊓ Gs 1)).relIndex (Gs 0 ⊓ Gs 1) := by
  rw [ncard_orbit_coset ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)) ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)) f]
  have h1 : ((Gs 0 ⊓ Gs 1) ⊓ cj (f : G) (Gs 0 ⊓ Gs 1)).subgroupOf (Gs 0) =
      (Gs 0 ⊓ Gs 1).subgroupOf (Gs 0) ⊓ cj f ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)) := by
    ext u
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cj]
    rfl
  rw [← Subgroup.relIndex_subgroupOf (inf_le_left : Gs 0 ⊓ Gs 1 ≤ Gs 0), h1]

omit [Finite G] in
theorem Nr_mul_right {u v : G} (hu : Nr Gs u) (hv : v ∈ Gs 0 ⊓ Gs 1) : Nr Gs (u * v) := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hu
  exact ⟨a, ha, b, hb, c * v, (Gs 0 ⊓ Gs 1).mul_mem hc hv, by group⟩

omit [Finite G] in
theorem mk_mul_P {u p : ↥(Gs 0)} (hp : (p : G) ∈ Gs 0 ⊓ Gs 1) :
    ((u * p : ↥(Gs 0)) : LinesO Gs) = (u : LinesO Gs) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : ((u * p)⁻¹ * u : ↥(Gs 0)) = p⁻¹ := by group
  rw [this]
  exact (Gs 0 ⊓ Gs 1).inv_mem hp

@[expose] def FarLines (Gs : Fin 3 → Subgroup G) : Set (LinesO Gs) :=
  {x | ∃ f : ↥(Gs 0), (f : LinesO Gs) = x ∧ ¬ Nr Gs f}

theorem ncard_FarLines (hD : IsDSystem .C3 Gs) : (FarLines Gs).ncard = 8 := by
  obtain ⟨f0, hf0, hnf0, hidx⟩ := (gqLoc hD).farE
  have hor : FarLines Gs = MulAction.orbit ↥((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0))
      ((⟨f0, hf0⟩ : ↥(Gs 0)) : LinesO Gs) := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨f, rfl, hnf⟩
      obtain ⟨p, hp, p', hp', hfe⟩ := (gqLoc hD).farT f0 hf0 hnf0 f f.2 hnf
      refine ⟨⟨⟨p, hp.1⟩, Subgroup.mem_subgroupOf.2 hp⟩, ?_⟩
      have : (f : ↥(Gs 0)) = ⟨p, hp.1⟩ * ⟨f0, hf0⟩ * ⟨p', hp'.1⟩ := Subtype.ext (by simpa using hfe)
      rw [this, mk_mul_P hp']
      rfl
    · rintro ⟨⟨p, hp⟩, rfl⟩
      refine ⟨⟨p, p.2⟩ * ⟨f0, hf0⟩, rfl, fun hnr => hnf0 ?_⟩
      have := Nr_mul_left (v := (p : G)⁻¹)
        ((Gs 0 ⊓ Gs 1).inv_mem (Subgroup.mem_subgroupOf.1 hp)) hnr
      simpa using this
  rw [hor, ncard_orbit_lines, hidx]

theorem pts_on_line (hD : IsDSystem .C3 Gs) {s0 q0 h : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hq0 : q0 ∈ QQ Gs 0) (hq01 : q0 ∉ QQ Gs 1) (hh : h ∈ Gs 0) {y : G ⧸ Gs 0}
    (hy : y ∈ Dlt Gs) (hl : lineOf Gs y = ((⟨h, hh⟩ : ↥(Gs 0)) : LinesO Gs)) :
    y = ((h * s0 : G) : G ⧸ Gs 0) ∨ y = ((h * (q0 * s0) : G) : G ⧸ Gs 0) := by
  obtain ⟨h', hh', s', hs', hs'0, rfl⟩ := rep_of_Dlt hy
  rw [lineOf_eq hD hh' hs' hs'0] at hl
  have hP := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hl)
  have hP'' : h'⁻¹ * h ∈ Gs 0 ⊓ Gs 1 := by simpa using hP
  have hP' : h⁻¹ * h' ∈ Gs 0 ⊓ Gs 1 := by
    have := (Gs 0 ⊓ Gs 1).inv_mem hP''
    simpa using this
  have hmem : (h⁻¹ * h') * s' ∈ Gs 1 := (Gs 1).mul_mem hP'.2 hs'
  have hmem0 : (h⁻¹ * h') * s' ∉ Gs 0 := fun h0 => hs'0 (by
    have := (Gs 0).mul_mem ((Gs 0).inv_mem hP'.1) h0
    rwa [inv_mul_cancel_left] at this)
  have e : h' * s' = h * ((h⁻¹ * h') * s') := by group
  rcases line_pts hD hs0 hs00 hq0 hq01 hmem with h1 | h1 | h1
  · exact absurd h1 hmem0
  · left
    rw [e]; symm; rw [QuotientGroup.eq]
    have : (h * s0)⁻¹ * (h * ((h⁻¹ * h') * s')) = s0⁻¹ * ((h⁻¹ * h') * s') := by group
    rw [this]; exact h1
  · right
    rw [e]; symm; rw [QuotientGroup.eq]
    have : (h * (q0 * s0))⁻¹ * (h * ((h⁻¹ * h') * s')) = (q0 * s0)⁻¹ * ((h⁻¹ * h') * s') := by
      group
    rw [this]; exact h1

theorem ncard_PtsOn (hD : IsDSystem .C3 Gs) (S : Set (LinesO Gs)) :
    {y : G ⧸ Gs 0 | y ∈ Dlt Gs ∧ lineOf Gs y ∈ S}.ncard = 2 * S.ncard := by
  classical
  have : Fintype (G ⧸ Gs 0) := Fintype.ofFinite _
  have : Fintype (LinesO Gs) := Fintype.ofFinite _
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  have hq0G : q0 ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq0)
  have hq0P : q0 ∈ Gs 0 ⊓ Gs 1 := Q0_le_P01 hD hq0
  have hne : ∀ h : G, ((h * s0 : G) : G ⧸ Gs 0) ≠ ((h * (q0 * s0) : G) : G ⧸ Gs 0) := by
    intro h he
    rw [QuotientGroup.eq] at he
    have h' : s0⁻¹ * q0 * s0 ∈ Gs 0 := by
      have : (h * s0)⁻¹ * (h * (q0 * s0)) = s0⁻¹ * q0 * s0 := by group
      rwa [this] at he
    exact hq01 ((fix_iff hD hs0 hs00 hq0).1 h')
  rw [Set.ncard_eq_toFinset_card' {y : G ⧸ Gs 0 | y ∈ Dlt Gs ∧ lineOf Gs y ∈ S},
    Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := lineOf Gs) (t := S.toFinset)
      (fun y hy => by simpa using (Set.mem_toFinset.1 hy).2)]
  rw [Finset.sum_const_nat (m := 2) (fun x hx => ?_), mul_comm]
  have hxS : x ∈ S := by simpa using hx
  induction x using QuotientGroup.induction_on with | _ h => ?_
  have hpair : (Set.toFinset {y : G ⧸ Gs 0 | y ∈ Dlt Gs ∧ lineOf Gs y ∈ S}).filter
      (fun y => lineOf Gs y = (h : LinesO Gs)) =
      {((h * s0 : G) : G ⧸ Gs 0), ((h * (q0 * s0) : G) : G ⧸ Gs 0)} := by
    ext y
    simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hyD, -⟩, hl⟩
      exact pts_on_line hD hs0 hs00 hq0 hq01 h.2 hyD hl
    · rintro (rfl | rfl)
      · have hD' : ((h * s0 : G) : G ⧸ Gs 0) ∈ Dlt Gs := by
          refine ⟨?_, ?_⟩
          · intro he
            rw [oPt, QuotientGroup.eq, mul_one] at he
            have h1 : (h : G) * s0 ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
            exact hs00 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem h.2) h1)
          · rw [col_oPt]; exact ⟨h, h.2, s0, hs0, 1, (Gs 0).one_mem, by group⟩
        have hl := lineOf_eq hD h.2 hs0 hs00
        exact ⟨⟨hD', by rw [hl]; exact hxS⟩, hl⟩
      · have hs1 : q0 * s0 ∈ Gs 1 := (Gs 1).mul_mem hq0P.2 hs0
        have hs10 : q0 * s0 ∉ Gs 0 := fun h0 => hs00 (by
          simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hq0G) h0)
        have hD' : ((h * (q0 * s0) : G) : G ⧸ Gs 0) ∈ Dlt Gs := by
          refine ⟨?_, ?_⟩
          · intro he
            rw [oPt, QuotientGroup.eq, mul_one] at he
            have h1 : (h : G) * (q0 * s0) ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
            exact hs10 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem h.2) h1)
          · rw [col_oPt]; exact ⟨h, h.2, q0 * s0, hs1, 1, (Gs 0).one_mem, by group⟩
        have hl := lineOf_eq hD h.2 hs1 hs10
        exact ⟨⟨hD', by rw [hl]; exact hxS⟩, hl⟩
  rw [hpair, Finset.card_pair (hne h)]

end CFSG.Quasithin.H13.I51

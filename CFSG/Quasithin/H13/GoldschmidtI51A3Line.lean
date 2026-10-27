module

public import CFSG.Quasithin.H13.GoldschmidtI51A3Loc

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

@[expose] def L0 (Gs : Fin 3 → Subgroup G) : Set (G ⧸ Gs 0) :=
  {p | ∃ s ∈ Gs 1, p = ((s : G) : G ⧸ Gs 0)}

@[expose] def Line (Gs : Fin 3 → Subgroup G) (g : G) : Set (G ⧸ Gs 0) :=
  {p | ∃ s ∈ Gs 1, p = ((g * s : G) : G ⧸ Gs 0)}

omit [Finite G] in
theorem Line_mul_G1 {g t : G} (ht : t ∈ Gs 1) : Line Gs (g * t) = Line Gs g := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨t * s, (Gs 1).mul_mem ht hs, by rw [mul_assoc]⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨t⁻¹ * s, (Gs 1).mul_mem ((Gs 1).inv_mem ht) hs, ?_⟩
    have e : g * s = g * t * (t⁻¹ * s) := by group
    rw [e]

omit [Finite G] in
theorem smul_mem_Line (h : G) {g : G} {p : G ⧸ Gs 0} (hp : p ∈ Line Gs g) :
    h • p ∈ Line Gs (h * g) := by
  obtain ⟨s, hs, rfl⟩ := hp
  refine ⟨s, hs, ?_⟩
  show ((h * (g * s) : G) : G ⧸ Gs 0) = ((h * g * s : G) : G ⧸ Gs 0)
  rw [mul_assoc]

omit [Finite G] in
theorem Line_eq_image (Gs : Fin 3 → Subgroup G) (g : G) :
    Line Gs g = (fun p => g • p) '' L0 Gs := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨((s : G) : G ⧸ Gs 0), ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

theorem exists_third {X : Type*} [Finite X] {S : Set X} (hS : S.ncard = 3) {x y : X}
    (_hx : x ∈ S) (_hy : y ∈ S) (hxy : x ≠ y) : ∃ z ∈ S, z ≠ x ∧ z ≠ y := by
  by_contra h
  push Not at h
  have hsub : S ⊆ {x, y} := fun w hw => by
    by_cases hwx : w = x
    · simp [hwx]
    · simp [h w hw hwx]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hxy] at this
  omega

theorem eq_of_mem_three {X : Type*} [Finite X] {S : Set X} (hS : S.ncard = 3) {x y z z' : X}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hz' : z' ∈ S) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hxz' : x ≠ z') (hyz' : y ≠ z') : z = z' := by
  by_contra hzz
  have hy4 : y ∉ ({z, z'} : Set X) := by simp [hyz, hyz']
  have hx4 : x ∉ ({y, z, z'} : Set X) := by simp [hxy, hxz, hxz']
  have h4 : ({x, y, z, z'} : Set X).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hx4 (Set.toFinite _),
      Set.ncard_insert_of_notMem hy4 (Set.toFinite _), Set.ncard_pair hzz]
  have hsub : ({x, y, z, z'} : Set X) ⊆ S := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    exacts [hx, hy, hz, hz']
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem ncard_L0 (hD : IsDSystem D Gs) : (L0 Gs).ncard = 3 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  have hq0G : q0 ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq0)
  have hq0P : q0 ∈ Gs 0 ⊓ Gs 1 := Q0_le_P01 hD hq0
  have hs1 : q0 * s0 ∈ Gs 1 := (Gs 1).mul_mem hq0P.2 hs0
  have hs10 : q0 * s0 ∉ Gs 0 := fun h0 => hs00 (by
    simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hq0G) h0)
  have hL : L0 Gs = {oPt Gs, ((s0 : G) : G ⧸ Gs 0), ((q0 * s0 : G) : G ⧸ Gs 0)} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases line_pts hD hs0 hs00 hq0 hq01 ht with h | h | h
      · left
        rw [oPt, QuotientGroup.eq, mul_one]
        exact (Gs 0).inv_mem h
      · right; left
        rw [QuotientGroup.eq]
        simpa using (Gs 0).inv_mem h
      · right; right
        rw [QuotientGroup.eq]
        simpa using (Gs 0).inv_mem h
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, (Gs 1).one_mem, rfl⟩
      · exact ⟨s0, hs0, rfl⟩
      · exact ⟨q0 * s0, hs1, rfl⟩
  have hne1 : oPt Gs ≠ ((s0 : G) : G ⧸ Gs 0) := fun he => hs00 (by
    rw [oPt, QuotientGroup.eq, inv_one, one_mul] at he
    exact he)
  have hne2 : oPt Gs ≠ ((q0 * s0 : G) : G ⧸ Gs 0) := fun he => hs10 (by
    rw [oPt, QuotientGroup.eq, inv_one, one_mul] at he
    exact he)
  have hne3 : ((s0 : G) : G ⧸ Gs 0) ≠ ((q0 * s0 : G) : G ⧸ Gs 0) := by
    intro he
    rw [QuotientGroup.eq] at he
    have h' : s0⁻¹ * q0 * s0 ∈ Gs 0 := by simpa [mul_assoc] using he
    exact hq01 ((fix_iff hD hs0 hs00 hq0).1 h')
  exact Set.ncard_eq_three.2 ⟨_, _, _, hne1, hne2, hne3, hL⟩

theorem ncard_Line (hD : IsDSystem D Gs) (g : G) : (Line Gs g).ncard = 3 := by
  rw [Line_eq_image, Set.ncard_image_of_injective _ (MulAction.injective g), ncard_L0 hD]

theorem Line_eq_of_two (hD : IsDSystem D Gs) {g g' : G} {x y : G ⧸ Gs 0} (hxy : x ≠ y)
    (hx : x ∈ Line Gs g) (hy : y ∈ Line Gs g) (hx' : x ∈ Line Gs g') (hy' : y ∈ Line Gs g') :
    Line Gs g = Line Gs g' := by
  obtain ⟨s1, hs1, hx1⟩ := hx
  obtain ⟨s2, hs2, hy1⟩ := hy
  obtain ⟨t1, ht1, hx2⟩ := hx'
  obtain ⟨t2, ht2, hy2⟩ := hy'
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = (g * s1)⁻¹ * (g' * t1) := ⟨_, rfl⟩
  have ha : a ∈ Gs 0 := by rw [ha_def]; exact QuotientGroup.eq.1 (hx1.symm.trans hx2)
  have hb : (g * s2)⁻¹ * (g' * t2) ∈ Gs 0 := QuotientGroup.eq.1 (hy1.symm.trans hy2)
  have hs0 : s1⁻¹ * s2 ∉ Gs 0 := fun h0 => hxy (by
    rw [hx1, hy1, QuotientGroup.eq]
    have e : (g * s1)⁻¹ * (g * s2) = s1⁻¹ * s2 := by group
    rw [e]; exact h0)
  have hrel : (s1⁻¹ * s2)⁻¹ * a * (t1⁻¹ * t2) ∈ Gs 0 := by
    have e : (s1⁻¹ * s2)⁻¹ * a * (t1⁻¹ * t2) = (g * s2)⁻¹ * (g' * t2) := by
      rw [ha_def]; group
    rw [e]; exact hb
  have ha1 : a ∈ Gs 1 := uniq_line hD ((Gs 1).mul_mem ((Gs 1).inv_mem hs1) hs2) hs0
    ((Gs 1).mul_mem ((Gs 1).inv_mem ht1) ht2) ha hrel
  have e : g * s1 * a = g' * t1 := by rw [ha_def]; group
  calc Line Gs g = Line Gs (g * s1) := (Line_mul_G1 hs1).symm
    _ = Line Gs (g * s1 * a) := (Line_mul_G1 ha1).symm
    _ = Line Gs (g' * t1) := by rw [e]
    _ = Line Gs g' := Line_mul_G1 ht1

@[expose] def Ln (Gs : Fin 3 → Subgroup G) (x y z : G ⧸ Gs 0) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∃ g : G, x ∈ Line Gs g ∧ y ∈ Line Gs g ∧ z ∈ Line Gs g

omit [Finite G] in
theorem Ln_swap12 {x y z : G ⧸ Gs 0} (h : Ln Gs x y z) : Ln Gs y x z := by
  obtain ⟨h1, h2, h3, g, hx, hy, hz⟩ := h
  exact ⟨h1.symm, h3, h2, g, hy, hx, hz⟩

omit [Finite G] in
theorem Ln_swap23 {x y z : G ⧸ Gs 0} (h : Ln Gs x y z) : Ln Gs x z y := by
  obtain ⟨h1, h2, h3, g, hx, hy, hz⟩ := h
  exact ⟨h2, h1, h3.symm, g, hx, hz, hy⟩

omit [Finite G] in
theorem Ln_smul (h : G) {x y z : G ⧸ Gs 0} (hl : Ln Gs x y z) :
    Ln Gs (h • x) (h • y) (h • z) := by
  obtain ⟨h1, h2, h3, g, hx, hy, hz⟩ := hl
  exact ⟨fun e => h1 (MulAction.injective h e), fun e => h2 (MulAction.injective h e),
    fun e => h3 (MulAction.injective h e), h * g, smul_mem_Line h hx, smul_mem_Line h hy,
    smul_mem_Line h hz⟩

theorem Ln_uniq (hD : IsDSystem D Gs) {x y z z' : G ⧸ Gs 0} (h : Ln Gs x y z)
    (h' : Ln Gs x y z') : z = z' := by
  obtain ⟨h1, h2, h3, g, hx, hy, hz⟩ := h
  obtain ⟨h1', h2', h3', g', hx', hy', hz'⟩ := h'
  have hL := Line_eq_of_two hD h1 hx hy hx' hy'
  rw [hL] at hz
  exact eq_of_mem_three (ncard_Line hD g') hx' hy' hz hz' h1 h2 h3 h2' h3'

theorem Ln_exists (hD : IsDSystem .A3 Gs) {x y : G ⧸ Gs 0} (hxy : x ≠ y) :
    ∃ z, Ln Gs x y z := by
  induction x using QuotientGroup.induction_on with | _ g => ?_
  induction y using QuotientGroup.induction_on with | _ h => ?_
  obtain ⟨a, ha, s, hs, c, hc, e⟩ := Nbd_univ_A3 hD (g⁻¹ * h)
  have hh : h = g * a * s * c := by
    have := congrArg (fun w => g * w) e
    simpa [mul_assoc] using this
  have hx : ((g : G) : G ⧸ Gs 0) ∈ Line Gs (g * a) :=
    ⟨1, (Gs 1).one_mem, by rw [mul_one, mk_mul_G0 ha]⟩
  have hy : ((h : G) : G ⧸ Gs 0) ∈ Line Gs (g * a) :=
    ⟨s, hs, by rw [hh, mk_mul_G0 hc]⟩
  obtain ⟨z, hz, hzx, hzy⟩ := exists_third (ncard_Line hD (g * a)) hx hy hxy
  exact ⟨z, hxy, Ne.symm hzx, Ne.symm hzy, g * a, hx, hy, hz⟩

end CFSG.Quasithin.H13.I51

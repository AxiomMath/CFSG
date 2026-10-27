module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgDef
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Plane

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin

namespace PgGeom

variable {F : Type} [Field F]

section Points

theorem pt_eq_span (p : Pt F) : ∃ v : V3 F, v ≠ 0 ∧ p.1 = Submodule.span F {v} := by
  have hne : p.1 ≠ ⊥ := by
    intro h
    have := p.2
    rw [h] at this
    simp at this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, ?_⟩
  have hle : Submodule.span F {v} ≤ p.1 := by
    rw [Submodule.span_le]
    simpa using hv
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_singleton hv0]
  exact p.2.symm

@[expose] def mkPt (v : V3 F) (hv : v ≠ 0) : Pt F :=
  ⟨Submodule.span F {v}, finrank_span_singleton hv⟩

theorem mem_mkPt {v : V3 F} (hv : v ≠ 0) : v ∈ (mkPt v hv).1 :=
  Submodule.mem_span_singleton_self v

theorem inc_mkPt_iff {v : V3 F} {hv : v ≠ 0} {L : Ln F} : inc (mkPt v hv) L ↔ v ∈ L.1 := by
  show Submodule.span F {v} ≤ L.1 ↔ v ∈ L.1
  rw [Submodule.span_le]
  simp

theorem inf_pts_eq_bot {p p' : Pt F} (h : p ≠ p') : p.1 ⊓ p'.1 = ⊥ := by
  by_contra hne
  have h1 : Module.finrank F ↥(p.1 ⊓ p'.1) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.mp h0)
  have h2 : Module.finrank F ↥(p.1 ⊓ p'.1) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : p.1 ⊓ p'.1 ≤ p.1)
    have hp := p.2
    omega
  have h3 : Module.finrank F ↥(p.1 ⊓ p'.1) = 1 := by omega
  have e1 : p.1 ⊓ p'.1 = p.1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h3, p.2])
  have e2 : p.1 ⊓ p'.1 = p'.1 := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h3, p'.2])
  exact h (Subtype.ext (e1.symm.trans e2))

theorem finrank_sup_pts {p p' : Pt F} (h : p ≠ p') : Module.finrank F ↥(p.1 ⊔ p'.1) = 2 := by
  have := Submodule.finrank_sup_add_finrank_inf_eq p.1 p'.1
  rw [inf_pts_eq_bot h, finrank_bot, p.2, p'.2] at this
  omega

theorem line_eq_sup {L : Ln F} {p p' : Pt F} (h : p ≠ p') (h1 : p.1 ≤ L.1) (h2 : p'.1 ≤ L.1) :
    L.1 = p.1 ⊔ p'.1 := by
  symm
  exact Submodule.eq_of_le_of_finrank_eq (sup_le h1 h2) (by rw [finrank_sup_pts h, L.2])

@[expose] def mkLine (p p' : Pt F) (h : p ≠ p') : Ln F := ⟨p.1 ⊔ p'.1, finrank_sup_pts h⟩

theorem inc_mkLine_left (p p' : Pt F) (h : p ≠ p') : inc p (mkLine p p' h) := le_sup_left

theorem inc_mkLine_right (p p' : Pt F) (h : p ≠ p') : inc p' (mkLine p p' h) := le_sup_right

end Points

section Axioms

theorem two_pts (a a' : Pt F) (b b' : Ln F) (h1 : inc a b) (h2 : inc a' b) (h3 : inc a b')
    (h4 : inc a' b') (hne : a ≠ a') : b = b' :=
  Subtype.ext ((line_eq_sup hne h1 h2).trans (line_eq_sup hne h3 h4).symm)

theorem finrank_v3 : Module.finrank F (V3 F) = 3 := by simp

theorem exB (L : Ln F) : ∃ p : Pt F, inc p L := by
  have hne : L.1 ≠ ⊥ := by
    intro h
    have := L.2
    rw [h] at this
    simp at this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨mkPt v hv0, inc_mkPt_iff.mpr hv⟩

theorem pt_on (L L' : Ln F) (hne : L ≠ L') : ∃ p : Pt F, inc p L ∧ inc p L' := by
  have hlt : L.1 < L.1 ⊔ L'.1 := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hle : L'.1 ≤ L.1 := by
      rw [h]
      exact le_sup_right
    exact hne (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [L.2, L'.2])).symm)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank F ↥(L.1 ⊔ L'.1) ≤ 3 := by
    have := Submodule.finrank_le (L.1 ⊔ L'.1)
    rwa [finrank_v3] at this
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq L.1 L'.1
  rw [L.2] at h1
  rw [L.2, L'.2] at h3
  have h4 : Module.finrank F ↥(L.1 ⊓ L'.1) = 1 := by omega
  have hne' : L.1 ⊓ L'.1 ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h4
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  exact ⟨mkPt v hv0, inc_mkPt_iff.mpr hv.1, inc_mkPt_iff.mpr hv.2⟩

theorem line_through (a a' : Pt F) (h : a ≠ a') : ∃ L : Ln F, inc a L ∧ inc a' L :=
  ⟨mkLine a a' h, inc_mkLine_left a a' h, inc_mkLine_right a a' h⟩

@[expose] def ev (i : Fin 3) : V3 F := Pi.single i 1

theorem ev_apply (i j : Fin 3) : (ev i : V3 F) j = if j = i then 1 else 0 := by
  simp [ev, Pi.single_apply]

theorem ev_ne_zero (i : Fin 3) : (ev i : V3 F) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [ev_apply] at this

@[expose] def epts (i : Fin 3) : Pt F := mkPt (ev i) (ev_ne_zero i)

theorem epts_ne {i j : Fin 3} (h : i ≠ j) : (epts i : Pt F) ≠ epts j := by
  intro heq
  have hmem : (ev j : V3 F) ∈ (epts i : Pt F).1 := by
    rw [heq]
    exact mem_mkPt (ev_ne_zero j)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have := congrFun hc j
  simp [ev_apply, h.symm] at this

@[expose] def eline (i j : Fin 3) (h : i ≠ j) : Ln F := mkLine (epts i) (epts j) (epts_ne h)

theorem inc_eline_left {i j : Fin 3} (h : i ≠ j) : inc (epts i : Pt F) (eline i j h) :=
  inc_mkLine_left _ _ _

theorem inc_eline_right {i j : Fin 3} (h : i ≠ j) : inc (epts j : Pt F) (eline i j h) :=
  inc_mkLine_right _ _ _

theorem ev_mem_eline_left {i j : Fin 3} (h : i ≠ j) : (ev i : V3 F) ∈ (eline i j h).1 :=
  inc_eline_left h (mem_mkPt (ev_ne_zero i))

theorem ev_mem_eline_right {i j : Fin 3} (h : i ≠ j) : (ev j : V3 F) ∈ (eline i j h).1 :=
  inc_eline_right h (mem_mkPt (ev_ne_zero j))

theorem eline_apply_third {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {v : V3 F}
    (hv : v ∈ (eline i j hij : Ln F).1) : v k = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [ev_apply, hki, hkj]

theorem eline_ne {i j k l m : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hmi : m ≠ i) (hmj : m ≠ j)
    (hmk : m = k ∨ m = l) : (eline i j hij : Ln F) ≠ eline k l hkl := by
  intro heq
  have hmem : (ev m : V3 F) ∈ (eline i j hij : Ln F).1 := by
    rw [heq]
    rcases hmk with rfl | rfl
    · exact ev_mem_eline_left hkl
    · exact ev_mem_eline_right hkl
  have := eline_apply_third hij hmi hmj hmem
  simp [ev_apply] at this

theorem triangle : ∃ (a₀ a₁ a₂ : Pt F) (b₀ b₁ b₂ : Ln F), inc a₀ b₀ ∧ inc a₁ b₀ ∧ inc a₁ b₁ ∧
    inc a₂ b₁ ∧ inc a₂ b₂ ∧ inc a₀ b₂ ∧ a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₂ ≠ a₀ ∧ b₀ ≠ b₁ ∧ b₁ ≠ b₂ ∧
    b₂ ≠ b₀ := by
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  have d20 : (2 : Fin 3) ≠ 0 := by decide
  exact ⟨epts 0, epts 1, epts 2, eline 0 1 d01, eline 1 2 d12, eline 2 0 d20,
    inc_eline_left d01, inc_eline_right d01, inc_eline_left d12, inc_eline_right d12,
    inc_eline_left d20, inc_eline_right d20, epts_ne d01, epts_ne d12, epts_ne d20,
    eline_ne d01 d12 (by decide) (by decide) (Or.inr rfl),
    eline_ne d12 d20 (by decide) (by decide) (Or.inr rfl),
    eline_ne d20 d01 (by decide) (by decide) (Or.inr rfl)⟩

theorem exists_second_line (p : Pt F) : ∃ L₁ L₂ : Ln F, inc p L₁ ∧ inc p L₂ ∧ L₁ ≠ L₂ := by
  obtain ⟨v, hv0, hv⟩ := pt_eq_span p
  have hnle : ¬ (⊤ : Submodule F (V3 F)) ≤ p.1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_top, finrank_v3, p.2] at this
    omega
  obtain ⟨u, -, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hu0 : u ≠ 0 := fun h => hu (h ▸ p.1.zero_mem)
  have hpu : p ≠ mkPt u hu0 := fun h => hu (h ▸ mem_mkPt hu0)
  let L₁ : Ln F := mkLine p (mkPt u hu0) hpu
  have hnle2 : ¬ (⊤ : Submodule F (V3 F)) ≤ L₁.1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_top, finrank_v3, L₁.2] at this
    omega
  obtain ⟨w, -, hw⟩ := IsConcreteLE.not_le_iff_exists.mp hnle2
  have hw0 : w ≠ 0 := fun h => hw (h ▸ L₁.1.zero_mem)
  have hpw : p ≠ mkPt w hw0 := by
    intro h
    apply hw
    have hwp : w ∈ p.1 := by
      rw [h]
      exact mem_mkPt hw0
    exact inc_mkLine_left p (mkPt u hu0) hpu hwp
  refine ⟨L₁, mkLine p (mkPt w hw0) hpw, inc_mkLine_left _ _ _, inc_mkLine_left _ _ _, ?_⟩
  intro heq
  apply hw
  have : w ∈ (mkLine p (mkPt w hw0) hpw).1 := inc_mkLine_right _ _ _ (mem_mkPt hw0)
  rw [← heq] at this
  exact this

theorem thickA (p : Pt F) : 2 ≤ {L : Ln F | inc p L}.encard := by
  obtain ⟨L₁, L₂, h1, h2, hne⟩ := exists_second_line p
  have hpair : ({L₁, L₂} : Set (Ln F)).encard = 2 := Set.encard_pair hne
  rw [← hpair]
  refine Set.encard_le_encard ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact h2

theorem thickB (L : Ln F) : 2 ≤ {p : Pt F | inc p L}.encard := by
  obtain ⟨p₁, h1⟩ := exB L
  have hnle : ¬ L.1 ≤ p₁.1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [L.2, p₁.2] at this
    exact absurd this (by norm_num)
  obtain ⟨v₂, hv₂L, hv₂p⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hv₂0 : v₂ ≠ 0 := fun h => hv₂p (h ▸ p₁.1.zero_mem)
  have hne : p₁ ≠ mkPt v₂ hv₂0 := fun h => hv₂p (h ▸ mem_mkPt hv₂0)
  have hinc2 : inc (mkPt v₂ hv₂0) L := inc_mkPt_iff.mpr hv₂L
  have hpair : ({p₁, mkPt v₂ hv₂0} : Set (Pt F)).encard = 2 := Set.encard_pair hne
  rw [← hpair]
  refine Set.encard_le_encard ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact hinc2

theorem ppAxioms : PPAxioms (inc : Pt F → Ln F → Prop) where
  line_through := line_through
  two_pts a a' b b' h1 h2 h3 h4 hne := two_pts a a' b b' h1 h2 h3 h4 hne
  pt_on := pt_on
  exB := exB
  triangle := triangle
  thickA := thickA
  thickB := thickB

theorem isGenPolygon_gr : IsGenPolygon (Gr F) 3 := ppAxioms.isGenPolygon

end Axioms

end PgGeom

end CFSG.Quasithin.H13.F431.F45

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45SpGeomDef

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin

namespace SpGeom

variable {F : Type} [Field F]

section Linear

theorem pt_eq_span (p : Pt F) : ∃ v : W F, v ≠ 0 ∧ p.1 = Submodule.span F {v} := by
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

@[expose] def mkPt (v : W F) (hv : v ≠ 0) : Pt F :=
  ⟨Submodule.span F {v}, finrank_span_singleton hv⟩

theorem mem_mkPt {v : W F} (hv : v ≠ 0) : v ∈ (mkPt v hv).1 := Submodule.mem_span_singleton_self v

theorem pt_isotropic [CharP F 2] (p : Pt F) : ∀ x ∈ p.1, ∀ y ∈ p.1, minorForm F x y = 0 := by
  obtain ⟨v, -, hv⟩ := pt_eq_span p
  rw [hv]
  intro x hx y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [bf_self]

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
  exact Submodule.eq_of_le_of_finrank_eq (sup_le h1 h2) (by rw [finrank_sup_pts h, L.2.1])

theorem lagrangian (L : Ln F) {v : W F} (hv : ∀ x ∈ L.1, minorForm F x v = 0) : v ∈ L.1 := by
  have hle : L.1 ≤ (minorForm F).orthogonal L.1 := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact L.2.2 y hy x hx
  have hfr : Module.finrank F ↥((minorForm F).orthogonal L.1) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal minorForm_nondegenerate, L.2.1]
    simp
  have heq : L.1 = (minorForm F).orthogonal L.1 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, L.2.1])
  rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  exact hv x (heq ▸ hx)

end Linear

section Lines

variable [CharP F 2]

@[expose] def mkLine (p p' : Pt F) (hne : p ≠ p')
    (h : ∀ x ∈ p.1, ∀ y ∈ p'.1, minorForm F x y = 0) : Ln F :=
  ⟨p.1 ⊔ p'.1, finrank_sup_pts hne, by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
    have e1 := pt_isotropic p a₁ ha₁ b₁ hb₁
    have e2 := h a₁ ha₁ b₂ hb₂
    have e3 : minorForm F a₂ b₁ = 0 := by
      rw [bf_comm]
      exact h b₁ hb₁ a₂ ha₂
    have e4 := pt_isotropic p' a₂ ha₂ b₂ hb₂
    simp only [map_add, LinearMap.add_apply, e1, e2, e3, e4, add_zero]⟩

theorem inc_mkLine_left (p p' : Pt F) (hne : p ≠ p') (h) : inc p (mkLine p p' hne h) :=
  le_sup_left

theorem inc_mkLine_right (p p' : Pt F) (hne : p ≠ p') (h) : inc p' (mkLine p p' hne h) :=
  le_sup_right

omit [CharP F 2] in
theorem perp_of_gen {u v : W F} (huv : minorForm F u v = 0) (p p' : Pt F)
    (hp : p.1 = Submodule.span F {u}) (hp' : p'.1 = Submodule.span F {v}) :
    ∀ x ∈ p.1, ∀ y ∈ p'.1, minorForm F x y = 0 := by
  intro x hx y hy
  rw [hp] at hx
  rw [hp'] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [huv]

theorem exists_line_not_le (p : Pt F) (S : Submodule F (W F)) (hS : Module.finrank F ↥S < 3)
    (hpS : p.1 ≤ S) : ∃ L : Ln F, inc p L ∧ ¬ L.1 ≤ S := by
  obtain ⟨u, hu0, hu⟩ := pt_eq_span p
  have hfr : Module.finrank F ↥((minorForm F).orthogonal p.1) = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal minorForm_nondegenerate, p.2]
    simp
  have hnle : ¬ (minorForm F).orthogonal p.1 ≤ S := by
    intro hle
    have h3 : 3 ≤ Module.finrank F ↥S := by
      have := Submodule.finrank_mono hle
      rwa [hfr] at this
    exact absurd (lt_of_lt_of_le hS h3) (lt_irrefl _)
  obtain ⟨v, hvo, hvS⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hv0 : v ≠ 0 := fun h => hvS (h ▸ S.zero_mem)
  have huv : minorForm F u v = 0 := by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvo) u
      (by rw [hu]; exact Submodule.mem_span_singleton_self u)
    exact this
  let p' := mkPt v hv0
  have hne : p ≠ p' := by
    intro h
    apply hvS
    apply hpS
    rw [h]
    exact mem_mkPt hv0
  refine ⟨mkLine p p' hne (perp_of_gen huv p p' hu rfl), inc_mkLine_left p p' hne _, ?_⟩
  intro hle
  exact hvS (hle (inc_mkLine_right p p' hne _ (mem_mkPt hv0)))

theorem exA (p : Pt F) : ∃ L : Ln F, inc p L := by
  obtain ⟨L, hL, -⟩ := exists_line_not_le p p.1 (by rw [p.2]; norm_num) le_rfl
  exact ⟨L, hL⟩

theorem exists_other_line (p : Pt F) (L₁ : Ln F) (h : inc p L₁) :
    ∃ L₂ : Ln F, inc p L₂ ∧ L₂ ≠ L₁ := by
  obtain ⟨L, hL, hnle⟩ := exists_line_not_le p L₁.1 (by rw [L₁.2.1]; norm_num) h
  exact ⟨L, hL, fun heq => hnle (heq ▸ le_rfl)⟩

omit [CharP F 2] in
theorem exB (L : Ln F) : ∃ p : Pt F, inc p L := by
  have hne : L.1 ≠ ⊥ := by
    intro h
    have := L.2.1
    rw [h] at this
    simp at this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨mkPt v hv0, ?_⟩
  show Submodule.span F {v} ≤ L.1
  rw [Submodule.span_le]
  simpa using hv

theorem ax2 (p : Pt F) (L : Ln F) (h : ¬ inc p L) :
    ∃ (p' : Pt F) (M : Ln F), inc p M ∧ inc p' M ∧ inc p' L := by
  obtain ⟨u, hu0, hu⟩ := pt_eq_span p
  have hlt : Module.finrank F F < Module.finrank F ↥L.1 := by
    rw [L.2.1]
    simp
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := (minorForm F u).domRestrict L.1) hlt
  obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxu : minorForm F u (x : W F) = 0 := by
    simpa using hxker
  have hxv0 : (x : W F) ≠ 0 := fun hh => hx0 (Subtype.ext hh)
  let p' := mkPt (x : W F) hxv0
  have hincL : inc p' L := by
    show Submodule.span F {(x : W F)} ≤ L.1
    rw [Submodule.span_le]
    simp
  have hne : p ≠ p' := by
    intro heq
    exact h (heq ▸ hincL)
  exact ⟨p', mkLine p p' hne (perp_of_gen hxu p p' hu rfl), inc_mkLine_left p p' hne _,
    inc_mkLine_right p p' hne _, hincL⟩

omit [CharP F 2] in
theorem two_pts (a a' : Pt F) (b b' : Ln F) (h1 : inc a b) (h2 : inc a' b) (h3 : inc a b')
    (h4 : inc a' b') (hne : a ≠ a') : b = b' :=
  Subtype.ext ((line_eq_sup hne h1 h2).trans (line_eq_sup hne h3 h4).symm)

omit [CharP F 2] in
theorem no_triangle (a₀ a₁ a₂ : Pt F) (b₀ b₁ b₂ : Ln F) (h1 : inc a₀ b₀) (h2 : inc a₁ b₀)
    (h3 : inc a₁ b₁) (h4 : inc a₂ b₁) (h5 : inc a₂ b₂) (h6 : inc a₀ b₂) (n01 : a₀ ≠ a₁)
    (n12 : a₁ ≠ a₂) (_n20 : a₂ ≠ a₀) (m01 : b₀ ≠ b₁) : False := by
  have hb0 := line_eq_sup n01 h1 h2
  have h7 : inc a₂ b₀ := by
    intro v hv
    apply lagrangian b₀
    intro x hx
    rw [hb0] at hx
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
    have e0 : minorForm F x₀ v = 0 := b₂.2.2 x₀ (h6 hx₀) v (h5 hv)
    have e1 : minorForm F x₁ v = 0 := b₁.2.2 x₁ (h3 hx₁) v (h4 hv)
    simp only [map_add, LinearMap.add_apply, e0, e1, add_zero]
  exact m01 (two_pts a₁ a₂ b₀ b₁ h2 h7 h3 h4 n12)

end Lines

section Thick

variable [CharP F 2]

theorem thickA (p : Pt F) : 2 ≤ {L : Ln F | inc p L}.encard := by
  obtain ⟨L₁, h1⟩ := exA p
  obtain ⟨L₂, h2, hne⟩ := exists_other_line p L₁ h1
  have hpair : ({L₁, L₂} : Set (Ln F)).encard = 2 := Set.encard_pair (Ne.symm hne)
  rw [← hpair]
  refine Set.encard_le_encard ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact h2

omit [CharP F 2] in
theorem thickB (L : Ln F) : 2 ≤ {p : Pt F | inc p L}.encard := by
  obtain ⟨p₁, h1⟩ := exB L
  have hnle : ¬ L.1 ≤ p₁.1 := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [L.2.1, p₁.2] at this
    exact absurd this (by norm_num)
  obtain ⟨v₂, hv₂L, hv₂p⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hv₂0 : v₂ ≠ 0 := fun h => hv₂p (h ▸ p₁.1.zero_mem)
  have hne : p₁ ≠ mkPt v₂ hv₂0 := fun h => hv₂p (h ▸ mem_mkPt hv₂0)
  have hinc2 : inc (mkPt v₂ hv₂0) L := by
    show Submodule.span F {v₂} ≤ L.1
    rw [Submodule.span_le]
    simpa using hv₂L
  have hpair : ({p₁, mkPt v₂ hv₂0} : Set (Pt F)).encard = 2 := Set.encard_pair hne
  rw [← hpair]
  refine Set.encard_le_encard ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact hinc2

end Thick

section Octagon

variable [CharP F 2]

@[expose] def ev (i : Fin 4) : W F := Pi.single i 1

omit [CharP F 2] in
theorem ev_ne_zero (i : Fin 4) : (ev i : W F) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [ev] at this

@[expose] def epts (i : Fin 4) : Pt F := mkPt (ev i) (ev_ne_zero i)

omit [CharP F 2] in
theorem epts_ne {i j : Fin 4} (h : i ≠ j) : (epts i : Pt F) ≠ epts j := by
  intro heq
  have hmem : (ev j : W F) ∈ (epts i : Pt F).1 := by
    rw [heq]
    exact mem_mkPt (ev_ne_zero j)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have := congrFun hc j
  simp [ev, h.symm] at this

@[expose] def eline (i j : Fin 4) (h : i ≠ j) (hb : minorForm F (ev i : W F) (ev j) = 0) : Ln F :=
  mkLine (epts i) (epts j) (epts_ne h) (perp_of_gen hb _ _ rfl rfl)

theorem inc_eline_left {i j : Fin 4} (h : i ≠ j) (hb : minorForm F (ev i : W F) (ev j) = 0) :
    inc (epts i) (eline i j h hb) :=
  inc_mkLine_left _ _ _ _

theorem inc_eline_right {i j : Fin 4} (h : i ≠ j) (hb : minorForm F (ev i : W F) (ev j) = 0) :
    inc (epts j) (eline i j h hb) :=
  inc_mkLine_right _ _ _ _

theorem eline_ne {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k)
    (h1 : minorForm F (ev i : W F) (ev j) = 0) (h2 : minorForm F (ev j : W F) (ev k) = 0)
    (hik : minorForm F (ev i : W F) (ev k) ≠ 0) : eline i j hij h1 ≠ eline j k hjk h2 := by
  intro heq
  apply hik
  have hi : (ev i : W F) ∈ (eline i j hij h1).1 :=
    inc_eline_left hij h1 (mem_mkPt (ev_ne_zero i))
  have hk : (ev k : W F) ∈ (eline i j hij h1).1 := by
    rw [heq]
    exact inc_eline_right hjk h2 (mem_mkPt (ev_ne_zero k))
  exact (eline i j hij h1).2.2 _ hi _ hk

theorem octagon : ∃ (a₀ a₁ a₂ a₃ : Pt F) (b₀ b₁ b₂ b₃ : Ln F), inc a₀ b₀ ∧ inc a₁ b₀ ∧ inc a₁ b₁ ∧
    inc a₂ b₁ ∧ inc a₂ b₂ ∧ inc a₃ b₂ ∧ inc a₃ b₃ ∧ inc a₀ b₃ ∧ a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧
    a₃ ≠ a₀ ∧ b₀ ≠ b₁ ∧ b₁ ≠ b₂ ∧ b₂ ≠ b₃ ∧ b₃ ≠ b₀ := by
  have e01 : minorForm F (ev 0 : W F) (ev 1) = 0 := by rw [minorForm_apply]; simp [ev]
  have e13 : minorForm F (ev 1 : W F) (ev 3) = 0 := by rw [minorForm_apply]; simp [ev]
  have e32 : minorForm F (ev 3 : W F) (ev 2) = 0 := by rw [minorForm_apply]; simp [ev]
  have e20 : minorForm F (ev 2 : W F) (ev 0) = 0 := by rw [minorForm_apply]; simp [ev]
  have n03 : minorForm F (ev 0 : W F) (ev 3) ≠ 0 := by rw [minorForm_apply]; simp [ev]
  have n12 : minorForm F (ev 1 : W F) (ev 2) ≠ 0 := by rw [minorForm_apply]; simp [ev]
  have n30 : minorForm F (ev 3 : W F) (ev 0) ≠ 0 := by rw [minorForm_apply]; simp [ev]
  have n21 : minorForm F (ev 2 : W F) (ev 1) ≠ 0 := by rw [minorForm_apply]; simp [ev]
  have d01 : (0 : Fin 4) ≠ 1 := by decide
  have d13 : (1 : Fin 4) ≠ 3 := by decide
  have d32 : (3 : Fin 4) ≠ 2 := by decide
  have d20 : (2 : Fin 4) ≠ 0 := by decide
  exact ⟨epts 0, epts 1, epts 3, epts 2, eline 0 1 d01 e01, eline 1 3 d13 e13,
    eline 3 2 d32 e32, eline 2 0 d20 e20, inc_eline_left d01 e01, inc_eline_right d01 e01,
    inc_eline_left d13 e13, inc_eline_right d13 e13, inc_eline_left d32 e32,
    inc_eline_right d32 e32, inc_eline_left d20 e20, inc_eline_right d20 e20, epts_ne d01,
    epts_ne d13, epts_ne d32, epts_ne d20, eline_ne d01 d13 e01 e13 n03,
    eline_ne d13 d32 e13 e32 n12, eline_ne d32 d20 e32 e20 n30, eline_ne d20 d01 e20 e01 n21⟩

end Octagon

theorem gqAxioms [CharP F 2] : GQAxioms (inc : Pt F → Ln F → Prop) where
  exA := exA
  exB := exB
  two_pts a a' b b' h1 h2 h3 h4 hne := two_pts a a' b b' h1 h2 h3 h4 hne
  ax2 := ax2
  no_triangle := no_triangle
  octagon := octagon
  thickA := thickA
  thickB := thickB

theorem isGenPolygon_gr [CharP F 2] : IsGenPolygon (Gr F) 4 := gqAxioms.isGenPolygon

end SpGeom

end CFSG.Quasithin.H13.F431.F45

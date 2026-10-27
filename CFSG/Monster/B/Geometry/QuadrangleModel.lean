module

public import CFSG.Monster.B.Geometry.ModelResidue
public import CFSG.LieType.Chevalley.C2E6MinusSixBase
public import CFSG.LieType.Chevalley.C2E6MinusSixWitt

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (QVertex X Q IsTotallySingular)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[ext]
structure QFlag where
  pt : QVertex
  line : QVertex
  finrank_pt : finrank (ZMod 2) pt.1 = 1
  finrank_line : finrank (ZMod 2) line.1 = 2
  pt_le_line : pt.1 ≤ line.1

@[expose] def QFlag.SamePt (x y : QFlag) : Prop := x.pt = y.pt

@[expose] def QFlag.SameLine (x y : QFlag) : Prop := x.line = y.line

@[expose] def qflagTypeAut : Subgroup (Equiv.Perm QFlag) where
  carrier := {g | ∀ x y, ((g x).pt = (g y).pt ↔ x.pt = y.pt) ∧
    ((g x).line = (g y).line ↔ x.line = y.line)}
  mul_mem' {g h} hg hh x y :=
    ⟨(hg (h x) (h y)).1.trans (hh x y).1, (hg (h x) (h y)).2.trans (hh x y).2⟩
  one_mem' _ _ := ⟨Iff.rfl, Iff.rfl⟩
  inv_mem' {g} hg x y := by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
    exact ⟨this.1.symm, this.2.symm⟩

theorem mem_qflagTypeAut {g : Equiv.Perm QFlag} :
    g ∈ qflagTypeAut ↔ ∀ x y, ((g x).pt = (g y).pt ↔ x.pt = y.pt) ∧
      ((g x).line = (g y).line ↔ x.line = y.line) :=
  Iff.rfl

theorem perm_inv_apply_self {α : Type*} (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x :=
  Equiv.symm_apply_apply g x

theorem finrank_qvertex (v : QVertex) :
    finrank (ZMod 2) v.1 = 1 ∨ finrank (ZMod 2) v.1 = 2 :=
  v.2.2

theorem not_le_of_finrank {U V : Submodule (ZMod 2) X} (hU : finrank (ZMod 2) U = 2)
    (hV : finrank (ZMod 2) V = 1) : ¬U ≤ V := fun h => by
  have := Submodule.finrank_mono h
  omega

theorem qvertex_eq_of_le {u v : QVertex} (h : u.1 ≤ v.1)
    (hf : finrank (ZMod 2) u.1 = finrank (ZMod 2) v.1) : u = v :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h hf)

theorem forall_exists_ptOn : ∀ i : Fin 27, ∃ j : Fin 45, C2E6Overlap.PtOn i j := by decide

theorem forall_exists_ptOn' : ∀ j : Fin 45, ∃ i : Fin 27, C2E6Overlap.PtOn i j := by decide

theorem exists_qflag_pt {v : QVertex} (hv : finrank (ZMod 2) v.1 = 1) : ∃ x : QFlag, x.pt = v := by
  obtain ⟨a, rfl⟩ := C2E6Overlap.vertexOf_surjective v
  rcases a with i | j
  · obtain ⟨j, hj⟩ := forall_exists_ptOn i
    exact ⟨⟨C2E6Overlap.ptVertex i, C2E6Overlap.lnVertex j, C2E6Overlap.finrank_ptSub i,
      C2E6Overlap.finrank_lnSub j, C2E6Overlap.ptSub_le_lnSub_iff.mpr hj⟩, rfl⟩
  · have := C2E6Overlap.finrank_lnSub j
    change finrank (ZMod 2) (C2E6Overlap.lnSub j) = 1 at hv
    omega

theorem exists_qflag_line {v : QVertex} (hv : finrank (ZMod 2) v.1 = 2) :
    ∃ x : QFlag, x.line = v := by
  obtain ⟨a, rfl⟩ := C2E6Overlap.vertexOf_surjective v
  rcases a with i | j
  · have := C2E6Overlap.finrank_ptSub i
    change finrank (ZMod 2) (C2E6Overlap.ptSub i) = 2 at hv
    omega
  · obtain ⟨i, hi⟩ := forall_exists_ptOn' j
    exact ⟨⟨C2E6Overlap.ptVertex i, C2E6Overlap.lnVertex j, C2E6Overlap.finrank_ptSub i,
      C2E6Overlap.finrank_lnSub j, C2E6Overlap.ptSub_le_lnSub_iff.mpr hi⟩, rfl⟩

open _root_.Classical in
@[expose] noncomputable def qVertexMap (g : Equiv.Perm QFlag) (v : QVertex) : QVertex :=
  if h : finrank (ZMod 2) v.1 = 1 then (g (exists_qflag_pt h).choose).pt
  else (g (exists_qflag_line ((finrank_qvertex v).resolve_left h)).choose).line

section VertexMap

variable {g : Equiv.Perm QFlag} (hg : g ∈ qflagTypeAut)
include hg

theorem qVertexMap_pt (x : QFlag) : qVertexMap g x.pt = (g x).pt := by
  rw [qVertexMap, dite_eq_left x.finrank_pt]
  exact ((hg _ x).1).mpr (exists_qflag_pt x.finrank_pt).choose_spec

theorem qVertexMap_line (x : QFlag) : qVertexMap g x.line = (g x).line := by
  have h1 : ¬finrank (ZMod 2) x.line.1 = 1 := by rw [x.finrank_line]; omega
  rw [qVertexMap, dite_eq_right h1]
  exact ((hg _ x).2).mpr (exists_qflag_line ((finrank_qvertex x.line).resolve_left h1)).choose_spec

theorem qVertexMap_inv_comp (v : QVertex) : qVertexMap g⁻¹ (qVertexMap g v) = v := by
  rcases finrank_qvertex v with h | h
  · obtain ⟨x, rfl⟩ := exists_qflag_pt h
    rw [qVertexMap_pt hg, qVertexMap_pt (inv_mem hg), perm_inv_apply_self]
  · obtain ⟨x, rfl⟩ := exists_qflag_line h
    rw [qVertexMap_line hg, qVertexMap_line (inv_mem hg), perm_inv_apply_self]

theorem qVertexMap_comp_inv (v : QVertex) : qVertexMap g (qVertexMap g⁻¹ v) = v := by
  have := qVertexMap_inv_comp (inv_mem hg) v
  rwa [inv_inv] at this

@[expose] noncomputable def qVertexPerm : Equiv.Perm QVertex where
  toFun := qVertexMap g
  invFun := qVertexMap g⁻¹
  left_inv := qVertexMap_inv_comp hg
  right_inv := qVertexMap_comp_inv hg

theorem qVertexPerm_apply (v : QVertex) : qVertexPerm hg v = qVertexMap g v := rfl

theorem finrank_qVertexMap (v : QVertex) :
    finrank (ZMod 2) (qVertexMap g v).1 = finrank (ZMod 2) v.1 := by
  rcases finrank_qvertex v with h | h
  · obtain ⟨x, rfl⟩ := exists_qflag_pt h
    rw [qVertexMap_pt hg, (g x).finrank_pt, x.finrank_pt]
  · obtain ⟨x, rfl⟩ := exists_qflag_line h
    rw [qVertexMap_line hg, (g x).finrank_line, x.finrank_line]

omit hg in
theorem le_iff_exists_qflag' {u v : QVertex} (hu : finrank (ZMod 2) u.1 = 1)
    (hv : finrank (ZMod 2) v.1 = 2) : u.1 ≤ v.1 ↔ ∃ x : QFlag, x.pt = u ∧ x.line = v :=
  ⟨fun h => ⟨⟨u, v, hu, hv, h⟩, rfl, rfl⟩, by rintro ⟨x, rfl, rfl⟩; exact x.pt_le_line⟩

theorem qVertexMap_le_iff {u v : QVertex} (hu : finrank (ZMod 2) u.1 = 1)
    (hv : finrank (ZMod 2) v.1 = 2) : (qVertexMap g u).1 ≤ (qVertexMap g v).1 ↔ u.1 ≤ v.1 := by
  rw [le_iff_exists_qflag' ((finrank_qVertexMap hg u).trans hu)
      ((finrank_qVertexMap hg v).trans hv), le_iff_exists_qflag' hu hv]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨g⁻¹ x, ?_, ?_⟩
    · rw [← qVertexMap_pt (inv_mem hg), hx1, qVertexMap_inv_comp hg]
    · rw [← qVertexMap_line (inv_mem hg), hx2, qVertexMap_inv_comp hg]
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨g x, (qVertexMap_pt hg x).symm, (qVertexMap_line hg x).symm⟩

theorem qVertexPerm_mem_typeAut : qVertexPerm hg ∈ C2E6Overlap.typeAut := by
  refine ⟨fun v => finrank_qVertexMap hg v, fun u v => ?_⟩
  change (qVertexMap g u).1 ≤ (qVertexMap g v).1 ∨ (qVertexMap g v).1 ≤ (qVertexMap g u).1 ↔
    u.1 ≤ v.1 ∨ v.1 ≤ u.1
  have hinj : ∀ a b : QVertex, qVertexMap g a = qVertexMap g b ↔ a = b := fun a b =>
    (qVertexPerm hg).injective.eq_iff
  have hsame : ∀ a b : QVertex, finrank (ZMod 2) a.1 = finrank (ZMod 2) b.1 →
      (a.1 ≤ b.1 ∨ b.1 ≤ a.1 ↔ a = b) := fun a b hab =>
    ⟨fun h => h.elim (fun h => qvertex_eq_of_le h hab) fun h => (qvertex_eq_of_le h hab.symm).symm,
      fun h => Or.inl (h ▸ le_rfl)⟩
  rcases finrank_qvertex u with hu | hu <;> rcases finrank_qvertex v with hv | hv
  · rw [hsame _ _ (by rw [finrank_qVertexMap hg, finrank_qVertexMap hg, hu, hv]),
      hsame _ _ (by rw [hu, hv]), hinj]
  · have h1 : ¬(qVertexMap g v).1 ≤ (qVertexMap g u).1 :=
      not_le_of_finrank (by rw [finrank_qVertexMap hg, hv])
        (by rw [finrank_qVertexMap hg, hu])
    have h2 : ¬v.1 ≤ u.1 := not_le_of_finrank hv hu
    simp only [h1, h2, or_false]
    exact qVertexMap_le_iff hg hu hv
  · have h1 : ¬(qVertexMap g u).1 ≤ (qVertexMap g v).1 :=
      not_le_of_finrank (by rw [finrank_qVertexMap hg, hu])
        (by rw [finrank_qVertexMap hg, hv])
    have h2 : ¬u.1 ≤ v.1 := not_le_of_finrank hu hv
    simp only [h1, h2, false_or]
    exact qVertexMap_le_iff hg hv hu
  · rw [hsame _ _ (by rw [finrank_qVertexMap hg, finrank_qVertexMap hg, hu, hv]),
      hsame _ _ (by rw [hu, hv]), hinj]

end VertexMap

theorem eq_one_of_fix_planes {σ : Equiv.Perm QVertex} (hσ : σ ∈ C2E6Overlap.typeAut)
    {p L p' L' : QVertex} (hp : finrank (ZMod 2) p.1 = 1) (hL : finrank (ZMod 2) L.1 = 2)
    (hpL : p.1 ≤ L.1) (hp' : finrank (ZMod 2) p'.1 = 1) (hL' : finrank (ZMod 2) L'.1 = 2)
    (hpL' : p'.1 ≤ L'.1) (hLL : L.1 ⊓ L'.1 = ⊥)
    (hB : ∀ u ∈ p.1, ∀ v ∈ p'.1, u ≠ 0 → v ≠ 0 → QuadraticMap.polar Q u v ≠ 0)
    (h1 : σ p = p) (h2 : σ L = L) (h3 : σ p' = p') (h4 : σ L' = L')
    (h5 : ∀ M : QVertex, finrank (ZMod 2) M.1 = 2 → p.1 ≤ M.1 → σ M = M) : σ = 1 := by
  obtain ⟨φ, e1, e2, e3, e4⟩ := C2E6Overlap.exists_isometry_of_opposite L.2.1 L'.2.1 hp hL hpL
    hp' hL' hpL' hLL hB
  set ψ := C2E6Overlap.inducedPerm φ
  have hψ := C2E6Overlap.inducedPerm_mem_typeAut φ
  have hτ : ψ⁻¹ * σ * ψ ∈ C2E6Overlap.typeAut :=
    mul_mem (mul_mem (inv_mem hψ) hσ) hψ
  have hfix : ∀ v w : QVertex, ψ v = w → σ w = w → (ψ⁻¹ * σ * ψ) v = v := by
    intro v w hvw hw
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hvw, hw, ← hvw, perm_inv_apply_self]
  have hψv : ∀ (v w : QVertex), v.1.map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) = w.1 → ψ v = w :=
    fun v w h => Subtype.ext h
  have key := C2E6Overlap.eq_one_of_fix_base hτ fun f hf => by
    simp only [C2E6Overlap.rigidBase, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfix _ p (hψv _ _ (by rw [C2E6Overlap.vertexOf, C2E6Overlap.coe_ptVertex_zero, e1]))
        h1
    · exact hfix _ p' (hψv _ _ (by rw [C2E6Overlap.vertexOf, C2E6Overlap.coe_ptVertex_two, e3]))
        h3
    · exact hfix _ L (hψv _ _ (by rw [C2E6Overlap.vertexOf, C2E6Overlap.coe_lnVertex_zero, e2]))
        h2
    · exact hfix _ L' (hψv _ _ (by rw [C2E6Overlap.vertexOf, C2E6Overlap.coe_lnVertex_one, e4]))
        h4
    all_goals
      refine hfix _ _ rfl (h5 _ ?_ ?_)
      · rw [C2E6Overlap.coe_inducedPerm, LinearEquiv.finrank_map_eq]
        exact C2E6Overlap.finrank_lnSub _
      · rw [C2E6Overlap.coe_inducedPerm, ← e1]
        refine Submodule.map_mono ?_
        rw [← C2E6Overlap.coe_ptVertex_zero]
        exact C2E6Overlap.ptSub_le_lnSub_iff.mpr (by decide)
  calc σ = ψ * (ψ⁻¹ * σ * ψ) * ψ⁻¹ := by group
    _ = 1 := by rw [key]; group

@[expose] def QFlag.IsOpposite (x y : QFlag) : Prop :=
  x.line.1 ⊓ y.line.1 = ⊥ ∧
    ∀ u ∈ x.pt.1, ∀ v ∈ y.pt.1, u ≠ 0 → v ≠ 0 → QuadraticMap.polar Q u v ≠ 0

theorem QFlag.eq_one_of_fix {g : Equiv.Perm QFlag} (hg : g ∈ qflagTypeAut) {x y : QFlag}
    (hxy : x.IsOpposite y) (hx : g x = x) (hy : g y = y)
    (hpan : ∀ z : QFlag, z.pt = x.pt → g z = z) : g = 1 := by
  have hσ := eq_one_of_fix_planes (qVertexPerm_mem_typeAut hg) x.finrank_pt x.finrank_line
    x.pt_le_line y.finrank_pt y.finrank_line y.pt_le_line hxy.1 hxy.2
    (by rw [qVertexPerm_apply, qVertexMap_pt hg, hx])
    (by rw [qVertexPerm_apply, qVertexMap_line hg, hx])
    (by rw [qVertexPerm_apply, qVertexMap_pt hg, hy])
    (by rw [qVertexPerm_apply, qVertexMap_line hg, hy])
    (fun M hM hpM => by
      rw [qVertexPerm_apply]
      have := qVertexMap_line hg ⟨x.pt, M, x.finrank_pt, hM, hpM⟩
      rw [hpan ⟨x.pt, M, x.finrank_pt, hM, hpM⟩ rfl] at this
      exact this)
  ext z : 1
  have h1 : (g z).pt = z.pt := by
    rw [← qVertexMap_pt hg, ← qVertexPerm_apply hg, hσ]
    rfl
  have h2 : (g z).line = z.line := by
    rw [← qVertexMap_line hg, ← qVertexPerm_apply hg, hσ]
    rfl
  exact QFlag.ext h1 h2

theorem isTotallySingular_span_singleton {r : X} (hr : Q r = 0) :
    IsTotallySingular ((ZMod 2) ∙ r) := by
  intro x hx
  rcases C2E6Overlap.mem_span_singleton_zmod_two.mp hx with rfl | rfl
  · exact map_zero Q
  · exact hr

theorem pathLE_of_not_opposite {x y : QFlag} (h : ¬x.IsOpposite y) :
    PathLE QFlag.SameLine QFlag.SamePt 3 x y := by
  simp only [QFlag.IsOpposite, not_and_or] at h
  rcases h with h | h
  ·
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hrx : r ∈ x.line.1 := (Submodule.mem_inf.mp hr).1
    have hry : r ∈ y.line.1 := (Submodule.mem_inf.mp hr).2
    have hQ : Q r = 0 := x.line.2.1 r hrx
    let R : QVertex := ⟨(ZMod 2) ∙ r, isTotallySingular_span_singleton hQ,
      Or.inl (finrank_span_singleton hr0)⟩
    let z₁ : QFlag := ⟨R, x.line, finrank_span_singleton hr0, x.finrank_line,
      (Submodule.span_singleton_le_iff_mem _ _).mpr hrx⟩
    let z₂ : QFlag := ⟨R, y.line, finrank_span_singleton hr0, y.finrank_line,
      (Submodule.span_singleton_le_iff_mem _ _).mpr hry⟩
    exact .step (b := z₁) (Or.inl (show x.line = z₁.line from rfl))
      (.step (b := z₂) (Or.inr (show z₁.pt = z₂.pt from rfl))
        (.step (b := y) (Or.inl (show z₂.line = y.line from rfl)) (.refl 0 y)))
  ·
    push Not at h
    obtain ⟨u, hu, v, hv, hu0, hv0, huv⟩ := h
    have hxu : x.pt.1 = (ZMod 2) ∙ u := (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
      (by rw [finrank_span_singleton hu0, x.finrank_pt])).symm
    have hyv : y.pt.1 = (ZMod 2) ∙ v := (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
      (by rw [finrank_span_singleton hv0, y.finrank_pt])).symm
    by_cases e : x.pt = y.pt
    · exact .step (b := y) (Or.inr e) (.refl 2 y)
    have huv' : u ≠ v := fun h => e (Subtype.ext (by rw [hxu, hyv, h]))
    have hQu : Q u = 0 := x.line.2.1 u (x.pt_le_line hu)
    have hQv : Q v = 0 := y.line.2.1 v (y.pt_le_line hv)
    have hsing : IsTotallySingular (Submodule.span (ZMod 2) {u, v}) := by
      intro w hw
      rcases C2E6Overlap.mem_span_pair_zmod_two.mp hw with rfl | rfl | rfl | rfl
      · exact map_zero Q
      · exact hQu
      · exact hQv
      · rw [C2E6Overlap.Q_add, hQu, hQv, ← C2E6Overlap.polar_Q, huv]
        simp
    have hfin : finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 2 :=
      C2E6Overlap.finrank_span_pair_zmod_two hu0 hv0 huv'
    let N : QVertex := ⟨Submodule.span (ZMod 2) {u, v}, hsing, Or.inr hfin⟩
    let w₁ : QFlag := ⟨x.pt, N, x.finrank_pt, hfin, by
      rw [hxu]
      exact Submodule.span_mono (by simp)⟩
    let w₂ : QFlag := ⟨y.pt, N, y.finrank_pt, hfin, by
      rw [hyv]
      exact Submodule.span_mono (by simp)⟩
    exact .step (b := w₁) (Or.inr (show x.pt = w₁.pt from rfl))
      (.step (b := w₂) (Or.inl (show w₁.line = w₂.line from rfl))
        (.step (b := y) (Or.inr (show w₂.pt = y.pt from rfl)) (.refl 0 y)))

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (cs δ) in
@[expose] def IsQuadrangleFlagResidue (i j : ι) (x : C) : Prop :=
  ∃ f : C → QFlag, IsModelResidue cs δ QFlag.SameLine QFlag.SamePt i j x f

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem IsModelResidue.qflag_isOpposite {i j : ι} (hij : i ≠ j) (hM : M i j = 4) {x : C}
    {f : C → QFlag} (hf : IsModelResidue cs δ QFlag.SameLine QFlag.SamePt i j x f) {a b : C}
    (ha : a ∈ residue cs δ {i, j} x) (hb : b ∈ residue cs δ {i, j} x)
    (hab : δ a b = longest cs {i, j}) : (f a).IsOpposite (f b) := by
  by_contra h
  have h1 := hf.length_le hδ ha hb (pathLE_of_not_opposite h)
  have := finite_parabolic_pair (cs := cs) (i := i) (j := j) (by omega)
  obtain ⟨h2, -, h3⟩ := isLongest_braidWord (cs := cs) hij (by omega)
  rw [hab, ← h2.eq_longest, h3, hM] at h1
  omega

theorem IsQuadrangleFlagResidue.fix {i j : ι} (hij : i ≠ j) (hM : M i j = 4) {a : C}
    (h : IsQuadrangleFlagResidue cs δ i j a) {b : C} (hb : b ∈ residue cs δ {i, j} a)
    (hab : δ a b = longest cs {i, j}) {g : C → C}
    (hg : IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g) (hgb : g b = b)
    (hfix : ∀ y ∈ panel cs δ j a, g y = y) :
    ∀ y ∈ residue cs δ {i, j} a, g y = y := by
  obtain ⟨f, hf⟩ := h
  have ha := self_mem_residue (cs := cs) (δ := δ) {i, j} a
  obtain ⟨G, hG, hG1, hG2⟩ := hf.exists_perm (fun _ => rfl) (fun _ => rfl) hg
  have hGmem : G ∈ qflagTypeAut := fun u v => ⟨hG2 u v, hG1 u v⟩
  have hga : g a = a := hfix a (self_mem_residue _ a)
  have hpanel : ∀ z : QFlag, z.pt = (f a).pt → G z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hf.1.surjOn (Set.mem_univ z)
    rw [hG y hy]
    by_cases e : y = a
    · rw [e, hga]
    · congr 1
      exact hfix y ((mem_panel_iff hδ).mpr (Or.inr ((hf.2 a ha y hy).2.mpr ⟨Ne.symm e, hz.symm⟩)))
  have h1 := QFlag.eq_one_of_fix hGmem (hf.qflag_isOpposite hδ hij hM ha hb hab)
    (by rw [hG a ha, hga]) (by rw [hG b hb, hgb]) hpanel
  intro y hy
  have := hG y hy
  rw [h1] at this
  exact (hf.1.injOn hy (hg.1.mapsTo hy) this).symm

end CFSG.Monster.B.Geometry

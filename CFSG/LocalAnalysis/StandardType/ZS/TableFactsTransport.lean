module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsForms

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem family_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U] {m : ℕ} (hU : UseInputAt m)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X) (hs : SplitSupport X m) :
    Family p (movedGroup X) := by
  exact hU p (HardMathSupport.Kantor79.commutatorSpace X) (movedGroup X) hp hs.2.1
    (reflGen_movedGroup hX) (absIrred_movedGroup hX hs)

theorem exists_monomial_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U] {m : ℕ} (hm : 3 ≤ m)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X) (hs : SplitSupport X m)
    (himp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)) :
    ∃ (b : Module.Basis (Fin m) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
      (i₀ i₁ : Fin m) (ζ : (ZMod p)ˣ), i₀ ≠ i₁ ∧
        (movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ) := by
  exact exists_basis_eq_gmmn_or_g2mmn (U := HardMathSupport.Kantor79.commutatorSpace X) (n := m)
    hp hs.2.1 hm (reflGen_movedGroup hX) (absIrred_movedGroup hX hs) himp

theorem exists_pair_movedGroup_iff {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (P : ℕ → Prop) :
    (∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X, IsRefl p x ∧ IsRefl p y ∧ P (orderOf (x * y))) ↔
      ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ P (orderOf (x * y)) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have hord : ∀ x : X, orderOf (φ x) = orderOf x := fun x => orderOf_injective φ hinj x
  constructor
  · rintro ⟨x, hx, y, hy, hxr, hyr, hP⟩
    obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨y', rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨x', x'.2, y', y'.2, isRefl_of_isRefl_restrictHom hs hxr,
      isRefl_of_isRefl_restrictHom hs hyr, ?_⟩
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, ← hord (x' * y'), map_mul]
    exact hP
  · rintro ⟨x, hx, y, hy, hxr, hyr, hP⟩
    refine ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩,
      isRefl_restrictHom_of_isRefl hs hxr, isRefl_restrictHom_of_isRefl hs hyr, ?_⟩
    rw [← map_mul, hord (⟨x, hx⟩ * ⟨y, hy⟩), ← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hP

theorem exists_orderOf_movedGroup_iff {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (k : ℕ) :
    (∃ g ∈ movedGroup X, orderOf g = k) ↔ ∃ g ∈ X, orderOf g = k := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have hord : ∀ x : X, orderOf (φ x) = orderOf x := fun x => orderOf_injective φ hinj x
  constructor
  · rintro ⟨g, hg, hk⟩
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨g', g'.2, by rw [Subgroup.orderOf_coe, ← hord g']; exact hk⟩
  · rintro ⟨g, hg, hk⟩
    refine ⟨φ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    rw [hord ⟨g, hg⟩, ← Subgroup.orderOf_coe ⟨g, hg⟩]
    exact hk

theorem commutatorSpace_eq_of_le [Module.Finite (ZMod p) U] {X Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {m : ℕ} (hYX : Y ≤ X) (hX : SplitSupport X m) (hY : SplitSupport Y m) :
    HardMathSupport.Kantor79.commutatorSpace Y = HardMathSupport.Kantor79.commutatorSpace X := by
  have hle : HardMathSupport.Kantor79.commutatorSpace Y ≤
      HardMathSupport.Kantor79.commutatorSpace X := by
    rw [commutatorSpace_le_iff]
    intro h hh v
    exact Submodule.subset_span ⟨h, hYX hh, v, rfl⟩
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hY.2.1, hX.2.1])

private theorem tftr_isImprimitiveOnV_of_forall_conj {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (e : V ≃ₗ[ZMod p] V')
    {G : Subgroup (V ≃ₗ[ZMod p] V)} {G' : Subgroup (V' ≃ₗ[ZMod p] V')}
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ v, g' (e v) = e (g v))
    (h : Quasithin.SimsG4.IsImprimitiveOnV G) : Quasithin.SimsG4.IsImprimitiveOnV G' := by
  obtain ⟨r, W, hr, hWne, hindep, hsup, hperm⟩ := h
  let F := Submodule.orderIsoMapComap e
  have hF : ∀ i, F (W i) = (W i).map (e : V →ₗ[ZMod p] V') :=
    fun i => Submodule.orderIsoMapComap_apply _ _
  refine ⟨r, fun i => F (W i), hr, ?_, ?_, ?_, ?_⟩
  · intro i
    change F (W i) ≠ ⊥
    rw [hF i]
    exact Submodule.map_ne_bot_iff.mpr (hWne i)
  · simpa only [Function.comp_def, hF] using hindep.map_orderIso F
  · have hmap : (⨆ i, F (W i)) = ⨆ i, (W i).map (e : V →ₗ[ZMod p] V') := by
      simp only [hF]
    rw [hmap, ← Submodule.map_iSup (e : V →ₗ[ZMod p] V') W, hsup, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  · intro g' hg' i
    obtain ⟨g, hg, hconj⟩ := hG g' hg'
    obtain ⟨j, hj⟩ := hperm g hg i
    have hcomp : (g' : V' →ₗ[ZMod p] V') ∘ₗ (e : V →ₗ[ZMod p] V') =
        (e : V →ₗ[ZMod p] V') ∘ₗ (g : V →ₗ[ZMod p] V) := by
      ext v
      exact hconj v
    refine ⟨j, ?_⟩
    change (F (W i)).map (g' : V' →ₗ[ZMod p] V') = F (W j)
    rw [hF i, hF j, ← hj, ← Submodule.map_comp, ← Submodule.map_comp, hcomp]

theorem not_isImprimitiveOnV_movedGroup_of_le {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X)
    (hV : HardMathSupport.Kantor79.commutatorSpace Y =
      HardMathSupport.Kantor79.commutatorSpace X)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup Y)) :
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) := by
  intro himp
  apply hprim
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let V' := HardMathSupport.Kantor79.commutatorSpace Y
  let e : V ≃ₗ[ZMod p] V' := LinearEquiv.ofEq V V' hV.symm
  refine tftr_isImprimitiveOnV_of_forall_conj e ?_ himp
  intro g' hg'
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg'
  refine ⟨restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨y.1, hYX y.2⟩,
    ⟨⟨y.1, hYX y.2⟩, rfl⟩, ?_⟩
  intro v
  apply Subtype.ext
  simp only [e, restrictHom_apply, LinearEquiv.coe_ofEq_apply]

private theorem tftr_polarBilin_comp_add_comp {V C : Submodule (ZMod p) U} (h : IsCompl V C)
    (Q₀ : QuadraticForm (ZMod p) V) (Q₁ : QuadraticForm (ZMod p) C) (u v : U) :
    QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm)) u v =
      QuadraticMap.polarBilin Q₀ (V.projectionOnto C h u) (V.projectionOnto C h v) +
      QuadraticMap.polarBilin Q₁ (C.projectionOnto V h.symm u)
        (C.projectionOnto V h.symm v) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
    add_apply, map_add]
  abel

private theorem tftr_projectionOnto_eq_zero_of_forall {V C : Submodule (ZMod p) U}
    (h : IsCompl V C) {Q₀ : QuadraticForm (ZMod p) V} {Q₁ : QuadraticForm (ZMod p) C}
    (h₀ : (QuadraticMap.polarBilin Q₀).SeparatingLeft)
    (h₁ : (QuadraticMap.polarBilin Q₁).SeparatingLeft) {u : U}
    (hu : ∀ v : U, QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm)) u v = 0) :
    V.projectionOnto C h u = 0 ∧ C.projectionOnto V h.symm u = 0 := by
  have hVu : V.projectionOnto C h u = 0 := by
    apply h₀
    intro v
    have hv := hu (v : U)
    rw [tftr_polarBilin_comp_add_comp h Q₀ Q₁ u (v : U),
      Submodule.projectionOnto_apply_left h v,
      Submodule.projectionOnto_apply_right h.symm v] at hv
    simpa using hv
  have hCu : C.projectionOnto V h.symm u = 0 := by
    apply h₁
    intro v
    have hv := hu (v : U)
    rw [tftr_polarBilin_comp_add_comp h Q₀ Q₁ u (v : U),
      Submodule.projectionOnto_apply_right h v,
      Submodule.projectionOnto_apply_left h.symm v] at hv
    simpa using hv
  exact ⟨hVu, hCu⟩

private theorem tftr_projectionOnto_eq_zero_of_forall' {V C : Submodule (ZMod p) U}
    (h : IsCompl V C) {Q₀ : QuadraticForm (ZMod p) V} {Q₁ : QuadraticForm (ZMod p) C}
    (h₀ : (QuadraticMap.polarBilin Q₀).SeparatingRight)
    (h₁ : (QuadraticMap.polarBilin Q₁).SeparatingRight) {v : U}
    (hv : ∀ u : U, QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm)) u v = 0) :
    V.projectionOnto C h v = 0 ∧ C.projectionOnto V h.symm v = 0 := by
  have hVv : V.projectionOnto C h v = 0 := by
    apply h₀
    intro u
    have hu := hv (u : U)
    rw [tftr_polarBilin_comp_add_comp h Q₀ Q₁ (u : U) v,
      Submodule.projectionOnto_apply_left h u,
      Submodule.projectionOnto_apply_right h.symm u] at hu
    simpa using hu
  have hCv : C.projectionOnto V h.symm v = 0 := by
    apply h₁
    intro u
    have hu := hv (u : U)
    rw [tftr_polarBilin_comp_add_comp h Q₀ Q₁ (u : U) v,
      Submodule.projectionOnto_apply_right h u,
      Submodule.projectionOnto_apply_left h.symm u] at hu
    simpa using hu
  exact ⟨hVv, hCv⟩

private theorem tftr_nondegenerate_comp_add_comp {V C : Submodule (ZMod p) U} (h : IsCompl V C)
    {Q₀ : QuadraticForm (ZMod p) V} {Q₁ : QuadraticForm (ZMod p) C}
    (h₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (h₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate) :
    (QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm))).Nondegenerate := by
  have key : ∀ u : U, (∀ v : U, QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm)) u v = 0) → u = 0 := by
    intro u hu
    obtain ⟨hVu, hCu⟩ := tftr_projectionOnto_eq_zero_of_forall h h₀.1 h₁.1 hu
    have h1 : V.projection C h u = 0 := by
      rw [← Submodule.coe_projectionOnto_apply h u, hVu]
      rfl
    have h2 : C.projection V h.symm u = 0 := by
      rw [← Submodule.coe_projectionOnto_apply h.symm u, hCu]
      rfl
    have hsum := Submodule.projection_add_projection_eq_self h u
    rw [h1, h2, zero_add] at hsum
    exact hsum.symm
  have key' : ∀ v : U, (∀ u : U, QuadraticMap.polarBilin (Q₀.comp (V.projectionOnto C h) +
      Q₁.comp (C.projectionOnto V h.symm)) u v = 0) → v = 0 := by
    intro v hv
    obtain ⟨hVv, hCv⟩ := tftr_projectionOnto_eq_zero_of_forall' h h₀.2 h₁.2 hv
    have h1 : V.projection C h v = 0 := by
      rw [← Submodule.coe_projectionOnto_apply h v, hVv]
      rfl
    have h2 : C.projection V h.symm v = 0 := by
      rw [← Submodule.coe_projectionOnto_apply h.symm v, hCv]
      rfl
    have hsum := Submodule.projection_add_projection_eq_self h v
    rw [h1, h2, zero_add] at hsum
    exact hsum.symm
  exact ⟨key, key'⟩

private theorem tftr_projectionOnto_commutator_conj {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (g : X) (u : U) :
    (HardMathSupport.Kantor79.commutatorSpace X).projectionOnto (centralizerSpace X) hs.1
        ((g : U ≃ₗ[ZMod p] U) u) =
      restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) g
        ((HardMathSupport.Kantor79.commutatorSpace X).projectionOnto (centralizerSpace X) hs.1
          u) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let πV := V.projectionOnto C hs.1
  let πC := C.projectionOnto V hs.1.symm
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hdecomp : u = (πV u : U) + (πC u : U) := by
    rw [Submodule.coe_projectionOnto_apply, Submodule.coe_projectionOnto_apply]
    exact (Submodule.projection_add_projection_eq_self hs.1 u).symm
  have hmem : (g : U ≃ₗ[ZMod p] U) u - (φ g (πV u) : U) ∈ C := by
    have hgu : (g : U ≃ₗ[ZMod p] U) u =
        (g : U ≃ₗ[ZMod p] U) (πV u : U) + (g : U ≃ₗ[ZMod p] U) (πC u : U) := by
      have h7 : (g : U ≃ₗ[ZMod p] U) u =
          (g : U ≃ₗ[ZMod p] U) ((πV u : U) + (πC u : U)) := congrArg _ hdecomp
      rw [h7, map_add]
    have hgC : (g : U ≃ₗ[ZMod p] U) (πC u : U) = (πC u : U) :=
      (mem_centralizerSpace.mp (πC u).2) g g.2
    have hgV : (g : U ≃ₗ[ZMod p] U) (πV u : U) = (φ g (πV u) : U) :=
      (restrictHom_apply X V _ g (πV u)).symm
    rw [hgu, hgV, hgC, add_sub_cancel_left]
    exact (πC u).2
  have hzero : πV ((g : U ≃ₗ[ZMod p] U) u - (φ g (πV u) : U)) = 0 := by
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact hmem
  rw [map_sub, Submodule.projectionOnto_apply_left hs.1 (φ g (πV u)), sub_eq_zero] at hzero
  exact hzero

private theorem tftr_projectionOnto_centralizer_fixed {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (g : X) (u : U) :
    (centralizerSpace X).projectionOnto (HardMathSupport.Kantor79.commutatorSpace X) hs.1.symm
        ((g : U ≃ₗ[ZMod p] U) u) =
      (centralizerSpace X).projectionOnto (HardMathSupport.Kantor79.commutatorSpace X) hs.1.symm
        u := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let πV := V.projectionOnto C hs.1
  let πC := C.projectionOnto V hs.1.symm
  have hdecomp : u = (πV u : U) + (πC u : U) := by
    rw [Submodule.coe_projectionOnto_apply, Submodule.coe_projectionOnto_apply]
    exact (Submodule.projection_add_projection_eq_self hs.1 u).symm
  have hmem : (g : U ≃ₗ[ZMod p] U) u - u ∈ V := by
    have hgu : (g : U ≃ₗ[ZMod p] U) u =
        (g : U ≃ₗ[ZMod p] U) (πV u : U) + (g : U ≃ₗ[ZMod p] U) (πC u : U) := by
      have h7 : (g : U ≃ₗ[ZMod p] U) u =
          (g : U ≃ₗ[ZMod p] U) ((πV u : U) + (πC u : U)) := congrArg _ hdecomp
      rw [h7, map_add]
    have hgC : (g : U ≃ₗ[ZMod p] U) (πC u : U) = (πC u : U) :=
      (mem_centralizerSpace.mp (πC u).2) g g.2
    have h1 : (g : U ≃ₗ[ZMod p] U) (πV u : U) ∈ V :=
      apply_mem_commutatorSpace g.2 (πV u).2
    have h2 : (πV u : U) ∈ V := (πV u).2
    have heq : (g : U ≃ₗ[ZMod p] U) u - u =
        (g : U ≃ₗ[ZMod p] U) (πV u : U) - (πV u : U) := by
      have h6 : (g : U ≃ₗ[ZMod p] U) u - u =
          (g : U ≃ₗ[ZMod p] U) ((πV u : U) + (πC u : U)) -
            ((πV u : U) + (πC u : U)) :=
        congrArg (fun x : U => (g : U ≃ₗ[ZMod p] U) x - x) hdecomp
      rw [h6, map_add, hgC]
      abel
    rw [heq]
    exact sub_mem h1 h2
  have hzero : πC ((g : U ≃ₗ[ZMod p] U) u - u) = 0 := by
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact hmem
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem exists_isIsom_of_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport X l)
    (Q₀ : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    (hQ₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hinv : ∀ g ∈ movedGroup X, IsIsom p Q₀ g) :
    ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∀ v : HardMathSupport.Kantor79.commutatorSpace X, Q v = Q₀ v) ∧ ∀ g ∈ X, IsIsom p Q g := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let πV := V.projectionOnto C hs.1
  let πC := C.projectionOnto V hs.1.symm
  let Q₁ : QuadraticForm (ZMod p) C :=
    basisDiagForm (Module.finBasis (ZMod p) C) (fun _ => 1)
  let Q : QuadraticForm (ZMod p) U := Q₀.comp πV + Q₁.comp πC
  have hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate :=
    basisDiagForm_nondegenerate hp (Module.finBasis (ZMod p) C) (w := fun _ => 1)
      (fun _ => one_ne_zero)
  refine ⟨Q, tftr_nondegenerate_comp_add_comp hs.1 hQ₀ hQ₁, ?_, ?_⟩
  · intro v
    have hv : πV (v : U) = v := Submodule.projectionOnto_apply_left hs.1 v
    have hv0 : πC (v : U) = 0 := Submodule.projectionOnto_apply_right hs.1.symm v
    change Q₀ (πV (v : U)) + Q₁ (πC (v : U)) = Q₀ v
    rw [hv, hv0, QuadraticMap.map_zero, add_zero]
  · intro g hg u
    let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
    have hπV : πV (g u) = φ ⟨g, hg⟩ (πV u) :=
      tftr_projectionOnto_commutator_conj hs ⟨g, hg⟩ u
    have hπC : πC (g u) = πC u := tftr_projectionOnto_centralizer_fixed hs ⟨g, hg⟩ u
    have hQ : Q (g u) = Q u := by
      change Q₀ (πV (g u)) + Q₁ (πC (g u)) = Q₀ (πV u) + Q₁ (πC u)
      rw [hπV, hπC, hinv (φ ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩ (πV u)]
    exact hQ

end CFSG.StandardType.ZS.TableFacts

end

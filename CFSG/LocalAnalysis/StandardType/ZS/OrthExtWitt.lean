module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.OrthReflect
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflSmul
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl
public import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup
public import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
public import CFSG.ClassicalGroups.Orthogonal.NormClass.Generation
public import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def IsOrthOn (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (X : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X} ∨
    ∃ c : ZMod p, c ≠ 0 ∧ X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem IsOrthOn.isIsom {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (ho : IsOrthOn p Q X) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ X) : IsIsom p Q g := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rcases ho with hfull | ⟨c, hc, hclass⟩
    · rw [hfull] at hg
      exact (Subgroup.closure_le _).mpr
        (by rintro t ⟨_, htiso, _⟩; exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr htiso)
        hg
    · rw [hclass] at hg
      exact (Subgroup.closure_le _).mpr
        (by rintro t ⟨ht, _⟩; exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ht.2.1) hg
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO

private theorem isIsom_restrictHom {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} (hV : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V)
    {Q : QuadraticForm (ZMod p) U} {x : X} (hx : IsIsom p Q (x : U ≃ₗ[ZMod p] U)) :
    IsIsom p (Q.comp V.subtype) (restrictHom X V hV x) := by
  intro w
  change Q (((restrictHom X V hV x) w : V) : U) = Q (w : U)
  rw [restrictHom_apply]
  exact hx (w : U)

theorem eq_reflect_of_isRefl_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g : U ≃ₗ[ZMod p] U} (hg' : IsRefl p g) (hgi : IsIsom p Q g) {a : U}
    (haQ : Q a ≠ 0) (hga : g a = -a) :
    g = ClassicalGroups.Orthogonal.reflect Q a := by
  have hcl : ClassicalGroups.Orthogonal.reflect Q a ∈ ClassRefl p Q (Q a) :=
    (mem_classRefl_iff hp hQ haQ _).mpr ⟨a, rfl, rfl⟩
  have hra : ClassicalGroups.Orthogonal.reflect Q a a = -a :=
    reflect_apply_self haQ
  exact DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hg' hgi hcl.1 hcl.2.1
    (by rintro rfl; exact haQ (map_zero Q)) hga hra

private theorem polar_eq_zero_of_mem_centralizerSpace {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q : QuadraticForm (ZMod p) U} (hX : ∀ g ∈ X, IsIsom p Q g) {u v : U}
    (hu : u ∈ centralizerSpace X) (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace X) :
    QuadraticMap.polar Q u v = 0 := by
  have hmem : HardMathSupport.Kantor79.commutatorSpace X ≤
      LinearMap.ker (QuadraticMap.polarBilin Q u) := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro w ⟨x, hx, z, rfl⟩
    change (QuadraticMap.polarBilin Q u) (x z - z) = 0
    rw [QuadraticMap.polarBilin_apply_apply]
    have hfix : x u = u := (mem_centralizerSpace.mp hu) x hx
    have hpol := (hX x hx).polar_apply u z
    rw [hfix] at hpol
    rw [QuadraticMap.polar_sub_right, hpol, sub_self]
  exact LinearMap.mem_ker.mp (hmem hv)

private theorem reflect_apply_eq_self_of_mem_centralizerSpace
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hX : ∀ g ∈ X, IsIsom p Q g) {a : U}
    (ha : a ∈ HardMathSupport.Kantor79.commutatorSpace X) {u : U}
    (hu : u ∈ centralizerSpace X) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a u = u := by
  refine CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero ?_
  rw [QuadraticMap.polar_comm]
  exact polar_eq_zero_of_mem_centralizerSpace hX hu ha

private theorem nondegenerate_comp_subtype_of_splitSupport
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hs : SplitSupport X l)
    (hX : ∀ g ∈ X, IsIsom p Q g) :
    (QuadraticMap.polarBilin (Q.comp
      (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  have hdecomp : ∀ u : U, u ∈ V ⊔ C := by
    intro u
    rw [hs.1.sup_eq_top]
    trivial
  refine ⟨?_, ?_⟩
  · intro a ha
    apply Subtype.ext
    apply hQ.1 (a : U)
    intro u
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp (hdecomp u)
    rw [map_add, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    have h1 : QuadraticMap.polar Q (a : U) v = 0 := by
      have := ha ⟨v, hv⟩
      simpa [QuadraticMap.polar, QuadraticMap.comp_apply, map_add] using this
    have h2 : QuadraticMap.polar Q (a : U) w = 0 := by
      rw [QuadraticMap.polar_comm]
      exact polar_eq_zero_of_mem_centralizerSpace hX hw a.2
    rw [h1, h2, add_zero]
  · intro b hb
    apply Subtype.ext
    apply hQ.2 (b : U)
    intro u
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp (hdecomp u)
    rw [map_add, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polarBilin_apply_apply]
    have h1 : QuadraticMap.polar Q v (b : U) = 0 := by
      have := hb ⟨v, hv⟩
      simpa [QuadraticMap.polar, QuadraticMap.comp_apply, map_add] using this
    have h2 : QuadraticMap.polar Q w (b : U) = 0 := by
      exact polar_eq_zero_of_mem_centralizerSpace hX hw b.2
    rw [h1, h2, add_zero]

private theorem movedSpace_reflect_le {Q : QuadraticForm (ZMod p) U}
    {V : Submodule (ZMod p) U} {a : U} (ha : a ∈ V) :
    HardMathSupport.Kantor79.movedSpace (CFSG.ClassicalGroups.Orthogonal.reflect Q a) ≤ V :=
  (movedSpace_reflect_le_span Q a).trans
    ((Submodule.span_singleton_le_iff_mem a V).mpr ha)

private theorem eq_of_eq_on_splitSupport {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) {t x : U ≃ₗ[ZMod p] U} (hx : x ∈ X)
    (htC : ∀ c ∈ centralizerSpace X, t c = c)
    (htV : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, t v = x v) : t = x := by
  apply LinearEquiv.ext
  intro u
  have hu : u ∈ HardMathSupport.Kantor79.commutatorSpace X ⊔ centralizerSpace X := by
    rw [hs.1.sup_eq_top]
    trivial
  obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add, map_add, htV v hv, htC c hc, (mem_centralizerSpace.mp hc) x hx]

private theorem exists_reflect_of_isRefl_of_movedSpace_le [Module.Finite (ZMod p) U]
    (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {V : Submodule (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (htr : IsRefl p t) (htiso : IsIsom p Q t)
    (htle : HardMathSupport.Kantor79.movedSpace t ≤ V) :
    ∃ a : V, Q a.1 ≠ 0 ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 := by
  obtain ⟨a, haQ, hta⟩ :=
    CFSG.StandardType.ZS.DimThree.exists_root_of_isRefl_isIsom hp hQ htr htiso
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha0 : a ≠ 0 := fun h => haQ (by rw [h]; exact map_zero Q)
  have haV : a ∈ V := htle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
  refine ⟨⟨a, haV⟩, haQ, ?_⟩
  exact CFSG.StandardType.ZS.DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ htr htiso
    (isRefl_reflect hp haQ) (isIsom_reflect Q a) ha0 hta
    (reflect_apply_self haQ)

noncomputable def extendForm {V : Submodule (ZMod p) U}
    (Q' : QuadraticForm (ZMod p) V) (π : U →ₗ[ZMod p] V)
    (f : U →ₗ[ZMod p] ZMod p) (c : ZMod p) : QuadraticForm (ZMod p) U :=
  (Q'.comp π) + c • QuadraticMap.linMulLin f f

theorem extendForm_comp_subtype {V : Submodule (ZMod p) U}
    (Q' : QuadraticForm (ZMod p) V) (π : U →ₗ[ZMod p] V)
    (f : U →ₗ[ZMod p] ZMod p) (c : ZMod p)
    (hπ : ∀ v : V, π v.1 = v) (hf : ∀ v : V, f v.1 = 0) :
    (extendForm Q' π f c).comp V.subtype = Q' := by
  ext v
  simp [extendForm, hπ v, hf v]

theorem extendForm_apply_e {V : Submodule (ZMod p) U}
    (Q' : QuadraticForm (ZMod p) V) (π : U →ₗ[ZMod p] V)
    (f : U →ₗ[ZMod p] ZMod p) (c : ZMod p) {e : U}
    (hπe : π e = 0) (hfe : f e = 1) :
    extendForm Q' π f c e = c := by
  simp [extendForm, hπe, hfe]

theorem polar_extendForm {V : Submodule (ZMod p) U}
    (Q' : QuadraticForm (ZMod p) V) (π : U →ₗ[ZMod p] V)
    (f : U →ₗ[ZMod p] ZMod p) (c : ZMod p) (u v : U) :
    QuadraticMap.polar (extendForm Q' π f c) u v =
      QuadraticMap.polar Q' (π u) (π v) + (2 * c) * (f u * f v) := by
  have hcomp : QuadraticMap.polar (Q'.comp π) u v =
      QuadraticMap.polar Q' (π u) (π v) := by
    simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  have hlin : QuadraticMap.polar (QuadraticMap.linMulLin f f) u v =
      2 * (f u * f v) := by
    simp only [QuadraticMap.polar, QuadraticMap.linMulLin_apply, map_add, mul_add, add_mul]
    ring
  change QuadraticMap.polar (⇑(Q'.comp π) + ⇑(c • QuadraticMap.linMulLin f f)) u v = _
  rw [QuadraticMap.polar_add,
    show QuadraticMap.polar (⇑(c • QuadraticMap.linMulLin f f)) u v =
      c • QuadraticMap.polar (⇑(QuadraticMap.linMulLin f f)) u v from
        QuadraticMap.polar_smul (⇑(QuadraticMap.linMulLin f f)) c u v,
    hcomp, hlin]
  simp only [smul_eq_mul]
  ring

theorem eq_zero_of_extendForm_proj_eq_zero {V C : Submodule (ZMod p) U}
    (π : U →ₗ[ZMod p] V) (f : U →ₗ[ZMod p] ZMod p) {e : U}
    (hCspan : C = Submodule.span (ZMod p) {e}) (hker : ∀ x : U, π x = 0 → x ∈ C)
    (hfe : f e = 1) {x : U} (hπx : π x = 0) (hfx : f x = 0) : x = 0 := by
  have hxC : x ∈ C := hker x hπx
  rw [hCspan, Submodule.mem_span_singleton] at hxC
  obtain ⟨a, ha⟩ := hxC
  have hfa : f x = a := by
    rw [← ha, map_smul, hfe, smul_eq_mul, mul_one]
  rw [hfa] at hfx
  rw [hfx] at ha
  simpa using ha.symm

theorem extendForm_nondegenerate {V C : Submodule (ZMod p) U}
    {Q' : QuadraticForm (ZMod p) V} (hQ' : (QuadraticMap.polarBilin Q').Nondegenerate)
    (π : U →ₗ[ZMod p] V) (f : U →ₗ[ZMod p] ZMod p) {e : U} {c : ZMod p}
    (hc : c ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hCspan : C = Submodule.span (ZMod p) {e})
    (hker : ∀ x : U, π x = 0 → x ∈ C)
    (hπ : ∀ v : V, π v.1 = v) (hf : ∀ v : V, f v.1 = 0)
    (hπe : π e = 0) (hfe : f e = 1) :
    (QuadraticMap.polarBilin (extendForm Q' π f c)).Nondegenerate := by
  have h2c : (2 : ZMod p) * c ≠ 0 := mul_ne_zero h2 hc
  have hpol := polar_extendForm (Q' := Q') (π := π) (f := f) (c := c)
  have hzero : ∀ x : U, π x = 0 → f x = 0 → x = 0 :=
    fun x hπx hfx => eq_zero_of_extendForm_proj_eq_zero π f hCspan hker hfe hπx hfx
  constructor
  · intro x hx
    have hπx : π x = 0 := by
      apply hQ'.1 (π x)
      intro v
      have hv := hx v.1
      rw [QuadraticMap.polarBilin_apply_apply] at hv
      rw [hpol] at hv
      rw [QuadraticMap.polarBilin_apply_apply]
      simpa [hf v, hπ v] using hv
    have hfx : f x = 0 := by
      have hxe := hx e
      rw [QuadraticMap.polarBilin_apply_apply] at hxe
      rw [hpol, hπx, hπe, hfe] at hxe
      have hxe' : 2 * c * f x = 0 := by simpa [mul_comm] using hxe
      simpa [mul_comm] using (mul_eq_zero.mp hxe').resolve_left h2c
    exact hzero x hπx hfx
  · intro y hy
    have hπy : π y = 0 := by
      apply hQ'.2 (π y)
      intro v
      have hv := hy v.1
      rw [QuadraticMap.polarBilin_apply_apply] at hv
      rw [hpol] at hv
      rw [QuadraticMap.polarBilin_apply_apply]
      simpa [hf v, hπ v] using hv
    have hfy : f y = 0 := by
      have hye := hy e
      rw [QuadraticMap.polarBilin_apply_apply] at hye
      rw [hpol, hπy, hπe, hfe] at hye
      have hye' : 2 * c * f y = 0 := by simpa [mul_comm] using hye
      simpa [mul_comm] using (mul_eq_zero.mp hye').resolve_left h2c
    exact hzero y hπy hfy

private theorem reflect_apply_eq_reflect_comp {Q : QuadraticForm (ZMod p) U}
    {V : Submodule (ZMod p) U} {a : V} (v : V) :
    (CFSG.ClassicalGroups.Orthogonal.reflect Q a.1) (v : U) =
      ((CFSG.ClassicalGroups.Orthogonal.reflect (Q.comp V.subtype) a) v : U) := by
  by_cases hQa : Q a.1 = 0
  · have hQa' : (Q.comp V.subtype) a = 0 := by simpa using hQa
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQa,
      CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQa']
    rfl
  · have hQa' : (Q.comp V.subtype) a ≠ 0 := by simpa using hQa
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
      CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa']
    simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, Submodule.coe_add,
      Submodule.coe_sub, Submodule.coe_smul, QuadraticMap.polar]

private theorem restrictHom_reflect_eq {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} (hV : ∀ h ∈ H, ∀ w ∈ V, h w ∈ V)
    {Q : QuadraticForm (ZMod p) U} {Q' : QuadraticForm (ZMod p) V}
    (hcomp : Q.comp V.subtype = Q') {a : V}
    (hsH : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ H) :
    restrictHom H V hV ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a.1, hsH⟩ =
      CFSG.ClassicalGroups.Orthogonal.reflect Q' a := by
  ext v
  rw [restrictHom_apply]
  simpa [hcomp] using reflect_apply_eq_reflect_comp (Q := Q) (V := V) (a := a) v

private theorem map_conj_reflSet {Q : QuadraticForm (ZMod p) U} {V : Submodule (ZMod p) U}
    {g : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) :
    (MulAut.conj g).toMonoidHom '' {t | IsRefl p t ∧ IsIsom p Q t ∧
        HardMathSupport.Kantor79.movedSpace t ≤ V} =
      {t | IsRefl p t ∧ IsIsom p Q t ∧
        HardMathSupport.Kantor79.movedSpace t ≤ V.map (g : U →ₗ[ZMod p] U)} := by
  have hginv : IsIsom p Q g⁻¹ := isIsom_inv hg
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hmoved : HardMathSupport.Kantor79.movedSpace ((MulAut.conj g).toMonoidHom s) =
        (HardMathSupport.Kantor79.movedSpace s).map (g : U →ₗ[ZMod p] U) := by
      simpa using movedSpace_conj g s
    refine ⟨IsRefl.conj hs.1 g,
      isIsom_mul (isIsom_mul hg hs.2.1) hginv, ?_⟩
    rw [hmoved]
    exact Submodule.map_mono hs.2.2
  · rintro ⟨htr, htiso, htle⟩
    refine ⟨g⁻¹ * t * g, ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa using IsRefl.conj htr g⁻¹
    · exact isIsom_mul (isIsom_mul hginv htiso) hg
    · have hmapV : (V.map (g : U →ₗ[ZMod p] U)).map (↑g⁻¹ : U →ₗ[ZMod p] U) = V := by
        rw [← Submodule.map_comp]
        have hcomp : (↑g⁻¹ : U →ₗ[ZMod p] U).comp (g : U →ₗ[ZMod p] U) = LinearMap.id :=
          LinearMap.ext fun v => g.symm_apply_apply v
        rw [hcomp, Submodule.map_id]
      have hmoved : HardMathSupport.Kantor79.movedSpace (g⁻¹ * t * g) =
          (HardMathSupport.Kantor79.movedSpace t).map (↑g⁻¹ : U →ₗ[ZMod p] U) :=
        movedSpace_conj (g⁻¹) t
      rw [hmoved]
      exact (Submodule.map_mono htle).trans (le_of_eq hmapV)
    · change g * (g⁻¹ * t * g) * g⁻¹ = t
      group

private theorem map_conj_classReflSet {Q : QuadraticForm (ZMod p) U} {V : Submodule (ZMod p) U}
    {c : ZMod p} {g : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) :
    (MulAut.conj g).toMonoidHom '' {t | t ∈ ClassRefl p Q c ∧
        HardMathSupport.Kantor79.movedSpace t ≤ V} =
      {t | t ∈ ClassRefl p Q c ∧
        HardMathSupport.Kantor79.movedSpace t ≤ V.map (g : U →ₗ[ZMod p] U)} := by
  have hginv : IsIsom p Q g⁻¹ := isIsom_inv hg
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hmoved : HardMathSupport.Kantor79.movedSpace ((MulAut.conj g).toMonoidHom s) =
        (HardMathSupport.Kantor79.movedSpace s).map (g : U →ₗ[ZMod p] U) := by
      simpa using movedSpace_conj g s
    refine ⟨conj_mem_classRefl hg hs.1, ?_⟩
    rw [hmoved]
    exact Submodule.map_mono hs.2
  · rintro ⟨htc, htle⟩
    have hmapV : (V.map (g : U →ₗ[ZMod p] U)).map (↑g⁻¹ : U →ₗ[ZMod p] U) = V := by
      rw [← Submodule.map_comp]
      have hcomp : (↑g⁻¹ : U →ₗ[ZMod p] U).comp (g : U →ₗ[ZMod p] U) = LinearMap.id :=
        LinearMap.ext fun v => g.symm_apply_apply v
      rw [hcomp, Submodule.map_id]
    have hmoved : HardMathSupport.Kantor79.movedSpace (g⁻¹ * t * g) =
        (HardMathSupport.Kantor79.movedSpace t).map (↑g⁻¹ : U →ₗ[ZMod p] U) :=
      movedSpace_conj (g⁻¹) t
    refine ⟨g⁻¹ * t * g, ⟨conj_mem_classRefl hginv htc, ?_⟩, ?_⟩
    · rw [hmoved]
      exact (Submodule.map_mono htle).trans (le_of_eq hmapV)
    · change g * (g⁻¹ * t * g) * g⁻¹ = t
      group

theorem isOrthOn_map_conj {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hX : IsOrthOn p Q X) {g : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) :
    IsOrthOn p Q (X.map (MulAut.conj g).toMonoidHom) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let X' := X.map (MulAut.conj g).toMonoidHom
  have hV' : HardMathSupport.Kantor79.commutatorSpace X' =
      V.map (g : U →ₗ[ZMod p] U) := commutatorSpace_map_conj g
  rcases hX with hfull | ⟨c, hc, hclass⟩
  · left
    change X.map (MulAut.conj g).toMonoidHom = Subgroup.closure
      {t | IsRefl p t ∧ IsIsom p Q t ∧
        HardMathSupport.Kantor79.movedSpace t ≤
          HardMathSupport.Kantor79.commutatorSpace X'}
    rw [hV', hfull, MonoidHom.map_closure, map_conj_reflSet hg]
  · right
    refine ⟨c, hc, ?_⟩
    change X.map (MulAut.conj g).toMonoidHom = Subgroup.closure
      {t | t ∈ ClassRefl p Q c ∧
        HardMathSupport.Kantor79.movedSpace t ≤
          HardMathSupport.Kantor79.commutatorSpace X'}
    rw [hV', hclass, MonoidHom.map_closure, map_conj_classReflSet hg]

private theorem reflect_mem_of_restrict_mem {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport H l) {Q : QuadraticForm (ZMod p) U}
    {Q' : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)}
    (hcomp : Q.comp (HardMathSupport.Kantor79.commutatorSpace H).subtype = Q')
    (hfixC : ∀ (a : HardMathSupport.Kantor79.commutatorSpace H) (z : U),
      z ∈ centralizerSpace H → CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 z = z)
    {a : HardMathSupport.Kantor79.commutatorSpace H}
    (hres : CFSG.ClassicalGroups.Orthogonal.reflect Q' a ∈ movedGroup H) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ H := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let hV : ∀ h ∈ H, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  let φ : H →* (V ≃ₗ[ZMod p] V) := restrictHom H V hV
  have hmem' : CFSG.ClassicalGroups.Orthogonal.reflect Q' a ∈ φ.range := by
    simpa only [movedGroup, φ] using hres
  obtain ⟨x, hxphi⟩ := MonoidHom.mem_range.mp hmem'
  have hxH : (x : U ≃ₗ[ZMod p] U) ∈ H := x.2
  have hx_eq : (x : U ≃ₗ[ZMod p] U) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 := by
    symm
    refine eq_of_eq_on_splitSupport hs hxH (hfixC a) ?_
    intro v hv
    rw [← restrictHom_apply H V hV x ⟨v, hv⟩, hxphi, ← hcomp]
    exact reflect_apply_eq_reflect_comp (Q := Q) (V := V) (a := a) ⟨v, hv⟩
  rw [← hx_eq]
  exact hxH

private theorem isOrthOn_of_movedGroup_eq_orthogonal (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport H l)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Q' : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)}
    (hQ' : (QuadraticMap.polarBilin Q').Nondegenerate)
    (hcomp : Q.comp (HardMathSupport.Kantor79.commutatorSpace H).subtype = Q')
    (hfixC : ∀ (a : HardMathSupport.Kantor79.commutatorSpace H) (z : U),
      z ∈ centralizerSpace H → CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 z = z)
    (hfull : ∀ g, g ∈ movedGroup H ↔ IsIsom p Q' g) : IsOrthOn p Q H := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let hV : ∀ h ∈ H, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  let φ : H →* (V ≃ₗ[ZMod p] V) := restrictHom H V hV
  have hφinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let T : Set (U ≃ₗ[ZMod p] U) := {t | IsRefl p t ∧ IsIsom p Q t ∧
    HardMathSupport.Kantor79.movedSpace t ≤ V}
  have hTle : Subgroup.closure T ≤ H := by
    rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨a, -, hta⟩ := exists_reflect_of_isRefl_of_movedSpace_le hp hQ ht.1 ht.2.1 ht.2.2
    rw [hta]
    exact reflect_mem_of_restrict_mem hs hcomp hfixC
      ((hfull _).mpr (isIsom_reflect Q' a))
  left
  refine le_antisymm ?_ hTle
  intro h hh
  let K : Subgroup H := (Subgroup.closure T).subgroupOf H
  have hφh : φ ⟨h, hh⟩ ∈ movedGroup H := by
    change φ ⟨h, hh⟩ ∈ φ.range
    exact MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩
  have hcl : φ ⟨h, hh⟩ ∈ Subgroup.closure (Set.range (fun a : V =>
      CFSG.ClassicalGroups.Orthogonal.reflect Q' a)) :=
    CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect h2 hQ'
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ((hfull _).mp hφh))
  have hmap : Subgroup.closure (Set.range (fun a : V =>
      CFSG.ClassicalGroups.Orthogonal.reflect Q' a)) ≤ Subgroup.map φ K := by
    rw [Subgroup.closure_le]
    rintro r ⟨a, rfl⟩
    change CFSG.ClassicalGroups.Orthogonal.reflect Q' a ∈ Subgroup.map φ K
    by_cases hQa : Q' a = 0
    · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQa]
      exact Subgroup.one_mem _
    · have haQ : Q a.1 ≠ 0 := by simpa [← hcomp] using hQa
      have hsT : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ T :=
        ⟨isRefl_reflect hp haQ, isIsom_reflect Q a.1, movedSpace_reflect_le a.2⟩
      have hsH : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ H :=
        hTle (Subgroup.subset_closure hsT)
      exact Subgroup.mem_map.mpr ⟨⟨_, hsH⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure hsT), restrictHom_reflect_eq hV hcomp hsH⟩
  exact (Subgroup.mem_map_iff_mem hφinj).mp (hmap hcl)

private theorem isOrthOn_of_movedGroup_eq_classRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport H l)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Q' : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)}
    (hQ' : (QuadraticMap.polarBilin Q').Nondegenerate)
    (hcomp : Q.comp (HardMathSupport.Kantor79.commutatorSpace H).subtype = Q')
    (hfixC : ∀ (a : HardMathSupport.Kantor79.commutatorSpace H) (z : U),
      z ∈ centralizerSpace H → CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 z = z)
    {c' : ZMod p} (hc' : c' ≠ 0)
    (hclass : movedGroup H = Subgroup.closure (ClassRefl p Q' c')) : IsOrthOn p Q H := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let hV : ∀ h ∈ H, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  let φ : H →* (V ≃ₗ[ZMod p] V) := restrictHom H V hV
  have hφinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let T : Set (U ≃ₗ[ZMod p] U) := {t | t ∈ ClassRefl p Q c' ∧
    HardMathSupport.Kantor79.movedSpace t ≤ V}
  have hTle : Subgroup.closure T ≤ H := by
    rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨a, hQa, hta⟩ := (mem_classRefl_iff hp hQ hc' t).mp ht.1
    have hQa_ne : Q a ≠ 0 := by rw [hQa]; exact hc'
    have hta' : t a = -a := by rw [hta]; exact reflect_apply_self hQa_ne
    have haV : a ∈ V := ht.2 (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta')
    have hQ'a : Q' ⟨a, haV⟩ = c' := by rw [← hcomp]; simpa using hQa
    have hmem : CFSG.ClassicalGroups.Orthogonal.reflect Q' ⟨a, haV⟩ ∈ movedGroup H := by
      rw [hclass]
      exact Subgroup.subset_closure ((mem_classRefl_iff hp hQ' hc' _).mpr
        ⟨⟨a, haV⟩, hQ'a, rfl⟩)
    rw [hta]
    exact reflect_mem_of_restrict_mem hs hcomp hfixC hmem
  right
  refine ⟨c', hc', ?_⟩
  refine le_antisymm ?_ hTle
  intro h hh
  let K : Subgroup H := (Subgroup.closure T).subgroupOf H
  have hmap : Subgroup.closure (ClassRefl p Q' c') ≤ Subgroup.map φ K := by
    rw [Subgroup.closure_le]
    intro r hr
    obtain ⟨a, hQ'a, rfl⟩ := (mem_classRefl_iff hp hQ' hc' r).mp hr
    have hQa : Q a.1 = c' := by simpa [← hcomp] using hQ'a
    have hsT : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ T :=
      ⟨(mem_classRefl_iff hp hQ hc' _).mpr ⟨a.1, hQa, rfl⟩, movedSpace_reflect_le a.2⟩
    have hsH : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ H :=
      hTle (Subgroup.subset_closure hsT)
    exact Subgroup.mem_map.mpr ⟨⟨_, hsH⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.subset_closure hsT), restrictHom_reflect_eq hV hcomp hsH⟩
  exact (Subgroup.mem_map_iff_mem hφinj).mp
    (hmap (by rw [← hclass]; exact MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩))

theorem exists_mem_apply_eq_of_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hK : (∀ g, g ∈ K ↔ IsIsom p Q g) ∨ ((p = 3 → 5 ≤ Module.finrank (ZMod p) U) ∧
      ∃ c : ZMod p, c ≠ 0 ∧ K = Subgroup.closure (ClassRefl p Q c)))
    {e u : U} (he : Q e ≠ 0) (hu : Q u = Q e) : ∃ k ∈ K, k e = u := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases hK with hfull | ⟨hdim, c, hc, hKc⟩
  · refine CFSG.ClassicalGroups.Orthogonal.exists_mem_apply_eq_of_reflect_mul_reflect_mem
      h2 hQ h3 (X := K) ?_ he hu
    intro a b hab
    exact (hfull _).mpr (isIsom_mul (isIsom_reflect Q a) (isIsom_reflect Q b))
  · refine CFSG.ClassicalGroups.Orthogonal.exists_mem_apply_eq_of_reflect_mul_reflect_mem
      h2 hQ h3 (X := K) ?_ he hu
    intro a b hab
    rw [hKc]
    by_cases hp3 : p = 3
    · exact CFSG.StandardType.ZS.reflect_mul_reflect_mem_closure_classRefl
        hp (hdim hp3) hQ hc hab
    · have h3ne : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
      refine Subgroup.closure_mono ?_
        (CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_reflect
          h2 h3ne hQ hab hc)
      rintro t ⟨x, hx, rfl⟩
      exact (mem_classRefl_iff hp hQ hc _).mpr ⟨x, hx, rfl⟩

private theorem eq_span_singleton_centralizerSpace_of_splitSupport [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {e : U}
    (he : e ∈ centralizerSpace H) (he0 : e ≠ 0) :
    centralizerSpace H = Submodule.span (ZMod p) {e} := by
  have hposU : 0 < Module.finrank (ZMod p) U :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨e, he0⟩
  have hCfin : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have hV := hs.2.1
    have hsum' : Module.finrank (ZMod p) U - 1 +
        Module.finrank (ZMod p) (centralizerSpace H) = Module.finrank (ZMod p) U := by
      rw [← hV]
      exact Submodule.finrank_add_eq_of_isCompl hs.1
    have hU : (Module.finrank (ZMod p) U - 1) + 1 = Module.finrank (ZMod p) U :=
      Nat.sub_add_cancel hposU
    exact Nat.add_left_cancel (by rw [hsum', hU])
  exact eq_span_singleton_of_mem_of_finrank_eq_one hCfin he he0

private theorem reflect_extendForm_apply_eq_self {V C : Submodule (ZMod p) U}
    (Q' : QuadraticForm (ZMod p) V) (π : U →ₗ[ZMod p] V) (f : U →ₗ[ZMod p] ZMod p)
    (c : ZMod p) (hπC : ∀ z : U, z ∈ C → π z = 0) (hfV : ∀ v : V, f v.1 = 0)
    {a : V} {z : U} (hz : z ∈ C) :
    CFSG.ClassicalGroups.Orthogonal.reflect (extendForm Q' π f c) a.1 z = z := by
  refine CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero ?_
  rw [polar_extendForm]
  have hπz : π z = 0 := hπC z hz
  simp [hπz, hfV a]

private theorem exists_proj_coord [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {e : U} (he : e ∈ centralizerSpace H) (he0 : e ≠ 0) :
    ∃ f : U →ₗ[ZMod p] ZMod p,
      (∀ v : HardMathSupport.Kantor79.commutatorSpace H, f v.1 = 0) ∧ f e = 1 ∧
      centralizerSpace H = Submodule.span (ZMod p) {e} ∧
      (∀ x : U, (HardMathSupport.Kantor79.commutatorSpace H).projectionOnto
        (centralizerSpace H) hs.1 x = 0 → x ∈ centralizerSpace H) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let C := centralizerSpace H
  have hCspan : C = Submodule.span (ZMod p) {e} :=
    eq_span_singleton_centralizerSpace_of_splitSupport hs he he0
  let coordSpan : Submodule.span (ZMod p) {e} ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.coord (ZMod p) U e he0
  let coordC : C ≃ₗ[ZMod p] ZMod p :=
    (LinearEquiv.ofEq C (Submodule.span (ZMod p) {e}) hCspan).trans coordSpan
  let f : U →ₗ[ZMod p] ZMod p :=
    coordC.toLinearMap.comp (C.projectionOnto V hs.1.symm)
  have hfV : ∀ v : V, f v.1 = 0 := fun v => by
    simp [f]
  have hfe : f e = 1 := by
    have hproj : C.projectionOnto V hs.1.symm e = ⟨e, he⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hs.1.symm he
    have hcoord : coordC ⟨e, he⟩ = 1 := by
      change coordSpan (LinearEquiv.ofEq C (Submodule.span (ZMod p) {e}) hCspan
        ⟨e, he⟩) = 1
      rw [show (LinearEquiv.ofEq C (Submodule.span (ZMod p) {e}) hCspan) ⟨e, he⟩ =
        (⟨e, Submodule.mem_span_singleton_self e⟩ : Submodule.span (ZMod p) {e}) from
          Subtype.ext rfl, LinearEquiv.coord_self]
    simpa [f, hproj] using hcoord
  have hker : ∀ x : U, (V.projectionOnto C hs.1) x = 0 → x ∈ C := by
    intro x hx
    rw [← Submodule.ker_projectionOnto (p := V) (q := C) hs.1]
    exact hx
  exact ⟨f, hfV, hfe, hCspan, hker⟩

theorem exists_isOrthOn_of_isOrthType_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (horth : IsOrthType p (movedGroup H)) {e : U} (he : e ∈ centralizerSpace H) (he0 : e ≠ 0)
    {c : ZMod p} (hc : c ≠ 0) :
    ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      IsOrthOn p Q H ∧ Q e = c := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let C := centralizerSpace H
  obtain ⟨Q', hQ', hcases⟩ := horth
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨f, hfV, hfe, hCspan, hker⟩ := exists_proj_coord hs he he0
  let π : U →ₗ[ZMod p] V := V.projectionOnto C hs.1
  let Q : QuadraticForm (ZMod p) U := extendForm Q' π f c
  have hπe : π e = 0 := Submodule.projectionOnto_apply_of_mem_right hs.1 he
  have hπV : ∀ v : V, π v.1 = v := fun v => Submodule.projectionOnto_apply_of_mem_left hs.1 v.2
  have hcomp : Q.comp V.subtype = Q' := extendForm_comp_subtype Q' π f c hπV hfV
  have hfixC : ∀ (a : V) (z : U), z ∈ C →
      CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 z = z :=
    fun a z hz => reflect_extendForm_apply_eq_self Q' π f c
      (fun z hz => Submodule.projectionOnto_apply_of_mem_right hs.1 hz) hfV hz
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    extendForm_nondegenerate hQ' π f hc h2 hCspan hker hπV hfV hπe hfe
  refine ⟨Q, hQnd, ?_, extendForm_apply_e Q' π f c hπe hfe⟩
  rcases hcases with hfull | ⟨c', hc', hclass⟩
  · exact isOrthOn_of_movedGroup_eq_orthogonal hp hs hQnd hQ' hcomp hfixC hfull
  · exact isOrthOn_of_movedGroup_eq_classRefl hp hs hQnd hQ' hcomp hfixC hc' hclass

private theorem projectionOnto_apply_equiv {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {g : H} {x : U} :
    ((HardMathSupport.Kantor79.commutatorSpace H).projectionOnto
      (centralizerSpace H) hs.1 ((g : U ≃ₗ[ZMod p] U) x) : U) =
    (g : U ≃ₗ[ZMod p] U)
      ((HardMathSupport.Kantor79.commutatorSpace H).projectionOnto
        (centralizerSpace H) hs.1 x : U) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let C := centralizerSpace H
  let π := V.projectionOnto C hs.1
  have hx : x = π x + (x - π x) := by abel
  have hyC : x - π x ∈ C := by
    rw [← Submodule.ker_projectionOnto (p := V) (q := C) hs.1]
    change π (x - π x) = 0
    rw [map_sub, Submodule.projectionOnto_apply_of_mem_left hs.1 (π x).2, sub_self]
  have hgy : (g : U ≃ₗ[ZMod p] U) (x - π x) = x - π x :=
    (mem_centralizerSpace.mp hyC) g g.2
  have hgx : (g : U ≃ₗ[ZMod p] U) x =
      (g : U ≃ₗ[ZMod p] U) (π x) + (x - π x) := by
    conv_lhs => rw [hx]
    rw [map_add, hgy]
  have hgV : (g : U ≃ₗ[ZMod p] U) (π x) ∈ V :=
    apply_mem_commutatorSpace g.2 (π x).2
  have hπgx : π ((g : U ≃ₗ[ZMod p] U) x) = π ((g : U ≃ₗ[ZMod p] U) (π x)) := by
    rw [hgx, map_add, Submodule.projectionOnto_apply_of_mem_right hs.1 hyC, add_zero]
  have hπgV : π ((g : U ≃ₗ[ZMod p] U) (π x)) =
      (⟨(g : U ≃ₗ[ZMod p] U) (π x), hgV⟩ : V) :=
    Submodule.projectionOnto_apply_of_mem_left hs.1 hgV
  have h := congrArg (fun v : V => (v : U)) (hπgx.trans hπgV)
  exact h

private theorem isIsom_extendForm_of_mem {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {ψ : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)}
    (hψH : ∀ g ∈ movedGroup H, IsIsom p ψ g)
    {π : U →ₗ[ZMod p] (HardMathSupport.Kantor79.commutatorSpace H)}
    {f : U →ₗ[ZMod p] ZMod p} {c : ZMod p}
    (hπ : π = (HardMathSupport.Kantor79.commutatorSpace H).projectionOnto
      (centralizerSpace H) hs.1)
    (hfV : ∀ v : HardMathSupport.Kantor79.commutatorSpace H, f v.1 = 0) :
    ∀ g ∈ H, IsIsom p (extendForm ψ π f c) g := by
  intro g hg x
  let V := HardMathSupport.Kantor79.commutatorSpace H
  have hVmap : ∀ h ∈ H, ∀ w ∈ V, h w ∈ V :=
    fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  let r : V ≃ₗ[ZMod p] V := restrictHom H V hVmap ⟨g, hg⟩
  have hr_mem : r ∈ movedGroup H := by
    change r ∈ (restrictHom H V hVmap).range
    exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
  have hψ_inv : ψ (π ((g : U ≃ₗ[ZMod p] U) x)) = ψ (π x) := by
    have h_eq : π ((g : U ≃ₗ[ZMod p] U) x) = r (π x) := by
      apply Subtype.ext
      rw [hπ, projectionOnto_apply_equiv hs (g := ⟨g, hg⟩) (x := x), restrictHom_apply]
    rw [h_eq]
    exact hψH r hr_mem (π x)
  have hf_inv : f ((g : U ≃ₗ[ZMod p] U) x) = f x := by
    have hmem : (g : U ≃ₗ[ZMod p] U) x - x ∈ V := by
      have hmem' : (g : U ≃ₗ[ZMod p] U) x - x ∈
          HardMathSupport.Kantor79.movedSpace (g : U ≃ₗ[ZMod p] U) :=
        ⟨x, by simp [LinearMap.sub_apply]⟩
      exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hg hmem'
    have hf_zero : f ((g : U ≃ₗ[ZMod p] U) x - x) = 0 := hfV ⟨_, hmem⟩
    rw [map_sub] at hf_zero
    exact sub_eq_zero.mp hf_zero
  change ψ (π ((g : U ≃ₗ[ZMod p] U) x)) + c *
      (f ((g : U ≃ₗ[ZMod p] U) x) * f ((g : U ≃ₗ[ZMod p] U) x)) =
      ψ (π x) + c * (f x * f x)
  rw [hψ_inv, hf_inv]

theorem exists_isIsom_of_isIsom_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {ψ : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)}
    (hψ : (QuadraticMap.polarBilin ψ).Nondegenerate) (hψH : ∀ g ∈ movedGroup H, IsIsom p ψ g)
    {e : U} (he : e ∈ centralizerSpace H) (he0 : e ≠ 0) {c : ZMod p} (hc : c ≠ 0) :
    ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      Q.comp (HardMathSupport.Kantor79.commutatorSpace H).subtype = ψ ∧ Q e = c ∧
      ∀ g ∈ H, IsIsom p Q g := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let C := centralizerSpace H
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨f, hfV, hfe, hCspan, hker⟩ := exists_proj_coord hs he he0
  let π : U →ₗ[ZMod p] V := V.projectionOnto C hs.1
  let Q : QuadraticForm (ZMod p) U := extendForm ψ π f c
  have hπe : π e = 0 := Submodule.projectionOnto_apply_of_mem_right hs.1 he
  have hπV : ∀ v : V, π v.1 = v := fun v => Submodule.projectionOnto_apply_of_mem_left hs.1 v.2
  have hcomp : Q.comp V.subtype = ψ := extendForm_comp_subtype ψ π f c hπV hfV
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    extendForm_nondegenerate hψ π f hc h2 hCspan hker hπV hfV hπe hfe
  refine ⟨Q, hQnd, hcomp, extendForm_apply_e ψ π f c hπe hfe, ?_⟩
  intro g hg
  exact isIsom_extendForm_of_mem hs hψH (π := π) (f := f) (c := c) rfl hfV g hg

theorem eq_smul_of_polarBilin_eq_smul {Q₁ Q₂ : QuadraticForm (ZMod p) U}
    {μ : ZMod p} (h2 : (2 : ZMod p) ≠ 0)
    (h : QuadraticMap.polarBilin Q₁ = μ • QuadraticMap.polarBilin Q₂) :
    Q₁ = μ • Q₂ := by
  ext v
  have hv : QuadraticMap.polar Q₁ v v = μ * QuadraticMap.polar Q₂ v v := by
    have := congrArg (fun B : LinearMap.BilinForm (ZMod p) U => B v v) h
    simpa [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul] using this
  rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at hv
  field_simp [h2] at hv ⊢
  exact hv

private theorem polarBilin_restrict_apply_mem_movedGroup
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hXQ : ∀ g ∈ X, IsIsom p Q g) :
    ∀ g ∈ movedGroup X, ∀ u v,
      (QuadraticMap.polarBilin
        (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) (g u)) (g v) =
      (QuadraticMap.polarBilin
        (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) u) v := by
  intro g hg u v
  let V := HardMathSupport.Kantor79.commutatorSpace X
  have hVmap : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V :=
    fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have hg' : g ∈ (restrictHom X V hVmap).range := by
    simpa only [movedGroup] using hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg'
  have hu : ((restrictHom X V hVmap x u : V) : U) = (x : U ≃ₗ[ZMod p] U) (u : U) :=
    restrictHom_apply X V hVmap x u
  have hv : ((restrictHom X V hVmap x v : V) : U) = (x : U ≃ₗ[ZMod p] U) (v : U) :=
    restrictHom_apply X V hVmap x v
  exact (isIsom_restrictHom hVmap (hXQ x x.2)).polar_apply u v

private theorem exists_ne_zero_smul_eq_of_polarBilin_eq_smul {V : Submodule (ZMod p) U}
    (h2 : (2 : ZMod p) ≠ 0) {QX Q' : QuadraticForm (ZMod p) V}
    (hQ' : (QuadraticMap.polarBilin Q').Nondegenerate) {κ : ZMod p}
    (hκ : QuadraticMap.polarBilin Q' = κ • QuadraticMap.polarBilin QX) :
    ∃ μ : ZMod p, μ ≠ 0 ∧ QX = μ • Q' := by
  by_cases hV0 : V = ⊥
  · refine ⟨1, one_ne_zero, ?_⟩
    ext v
    have hvU : (v : U) = 0 := (Submodule.eq_bot_iff V).mp hV0 v v.2
    have hvV : v = 0 := Subtype.ext hvU
    rw [hvV]
    simp
  · have hκne : κ ≠ 0 := by
      intro hκ0
      have hzero : QuadraticMap.polarBilin Q' = 0 := by rw [hκ, hκ0, zero_smul]
      obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
      have hzeroV : (⟨v, hvmem⟩ : V) = 0 :=
        hQ'.1 ⟨v, hvmem⟩ fun y => by rw [hzero]; simp
      exact hv0 (congrArg (fun w : V => (w : U)) hzeroV)
    refine ⟨κ⁻¹, inv_ne_zero hκne, ?_⟩
    have hκ' : QuadraticMap.polarBilin QX = κ⁻¹ • QuadraticMap.polarBilin Q' := by
      rw [hκ, smul_smul, inv_mul_cancel₀ hκne, one_smul]
    exact eq_smul_of_polarBilin_eq_smul h2 hκ'

theorem isOrthOn_of_isOrthType_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X)
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1)) (hXQ : ∀ g ∈ X, IsIsom p Q g)
    (horth : IsOrthType p (movedGroup X)) : IsOrthOn p Q X := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let QX : QuadraticForm (ZMod p) V := Q.comp V.subtype
  have hQXnd : (QuadraticMap.polarBilin QX).Nondegenerate :=
    nondegenerate_comp_subtype_of_splitSupport hQ hs hXQ
  have hVmap : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V :=
    fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have hQXinv : ∀ g ∈ movedGroup X, ∀ u v,
      (QuadraticMap.polarBilin QX (g u)) (g v) = (QuadraticMap.polarBilin QX u) v :=
    polarBilin_restrict_apply_mem_movedGroup hXQ
  obtain ⟨Q', hQ', hcases⟩ := horth
  have hQ'inv : ∀ g ∈ movedGroup X, ∀ u v,
      (QuadraticMap.polarBilin Q' (g u)) (g v) = (QuadraticMap.polarBilin Q' u) v := by
    intro g hg u v
    rcases hcases with hfull | ⟨c', hc', hclass⟩
    · exact ((hfull g).mp hg).polar_apply u v
    · have hg' : g ∈ Subgroup.closure (ClassRefl p Q' c') := by rwa [← hclass]
      exact (isIsom_of_mem_closure_classRefl hg').polar_apply u v
  have hA : AbsIrred p (movedGroup X) :=
    absIrred_of_reflGen (reflGen_movedGroup hX) (irred_movedGroup_of_splitSupport hs)
  obtain ⟨κ, hκ⟩ := exists_eq_smul_of_absIrred hA hQXnd hQXinv hQ'inv
  obtain ⟨μ, hμ, hQXeq⟩ :=
    exists_ne_zero_smul_eq_of_polarBilin_eq_smul (ZMod.prime_ne_zero p 2 hp) hQ' hκ
  have hfixC : ∀ (a : V) (z : U), z ∈ C →
      CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 z = z :=
    fun a z hz => reflect_apply_eq_self_of_mem_centralizerSpace hXQ a.2 hz
  rcases hcases with hfull | ⟨c', hc', hclass⟩
  · refine isOrthOn_of_movedGroup_eq_orthogonal hp hs hQ hQXnd (by rfl) hfixC ?_
    intro g
    rw [hQXeq]
    exact (hfull g).trans (isIsom_smul_iff hμ g).symm
  · refine isOrthOn_of_movedGroup_eq_classRefl hp hs hQ hQXnd (by rfl) hfixC
      (mul_ne_zero hμ hc') ?_
    rw [hQXeq, classRefl_smul hμ]
    exact hclass

private theorem movedGroup_orthogonal_of_isOrthOn_full (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hQXnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate)
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) :
    ∀ g, g ∈ movedGroup X ↔
      IsIsom p (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) g := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let hVmap : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have hXQ : ∀ g ∈ X, IsIsom p Q g := fun g hg => IsOrthOn.isIsom (Or.inl hfull) hg
  intro g
  constructor
  · intro hg
    have hg' : g ∈ (restrictHom X V hVmap).range := by simpa only [movedGroup] using hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg'
    exact isIsom_restrictHom hVmap (hXQ x x.2)
  · intro hg
    refine CFSG.StandardType.ZS.DimThree.mem_of_isIsom_of_isRefl_mem hp hQXnd ?_ hg
    intro s hsr hsq
    obtain ⟨a, haQ, hsa⟩ :=
      CFSG.StandardType.ZS.DimThree.exists_root_of_isRefl_isIsom hp hQXnd hsr hsq
    have ha0 : a ≠ 0 := fun h => haQ (by rw [h]; exact map_zero (f := Q.comp V.subtype))
    have hQa : Q a.1 ≠ 0 := by simpa using haQ
    have hs_eq : s = CFSG.ClassicalGroups.Orthogonal.reflect (Q.comp V.subtype) a :=
      CFSG.StandardType.ZS.DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQXnd hsr hsq
        (isRefl_reflect hp haQ) (isIsom_reflect (Q.comp V.subtype) a)
        ha0 hsa (reflect_apply_self haQ)
    have htT : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈
        {t | IsRefl p t ∧ IsIsom p Q t ∧
          HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X} :=
      ⟨isRefl_reflect hp hQa, isIsom_reflect Q a.1, movedSpace_reflect_le a.2⟩
    have htX : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ X :=
      hfull.symm.le (Subgroup.subset_closure htT)
    have hmem : CFSG.ClassicalGroups.Orthogonal.reflect (Q.comp V.subtype) a ∈ movedGroup X := by
      have hrange : CFSG.ClassicalGroups.Orthogonal.reflect (Q.comp V.subtype) a ∈
          (restrictHom X V hVmap).range :=
        MonoidHom.mem_range.mpr ⟨⟨_, htX⟩, restrictHom_reflect_eq hVmap (by rfl) htX⟩
      simpa only [movedGroup] using hrange
    rw [hs_eq]
    exact hmem

private theorem movedGroup_contains_reflect_mul_reflect_of_class (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {c : ZMod p} (hc : c ≠ 0)
    (hQXnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate)
    (h3 : (3 : ZMod p) ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace X}) :
    ∀ a b : HardMathSupport.Kantor79.commutatorSpace X,
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) a =
        (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) b →
      CFSG.ClassicalGroups.Orthogonal.reflect
          (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) a *
        CFSG.ClassicalGroups.Orthogonal.reflect
          (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) b ∈ movedGroup X := by
  intro a b hab
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let QX : QuadraticForm (ZMod p) V := Q.comp V.subtype
  let hV : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V :=
    fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hmem : ∀ x : V, QX x = c → CFSG.ClassicalGroups.Orthogonal.reflect Q x.1 ∈ X := by
    intro x hx
    rw [hclass]
    exact Subgroup.subset_closure
      ⟨(mem_classRefl_iff hp hQ hc _).mpr ⟨x.1, by simpa [QX] using hx, rfl⟩,
        movedSpace_reflect_le x.2⟩
  have hlift : ∀ (x : V) (hx : QX x = c),
      restrictHom X V hV ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q x.1, hmem x hx⟩ =
        CFSG.ClassicalGroups.Orthogonal.reflect QX x :=
    fun x hx => restrictHom_reflect_eq hV rfl (hmem x hx)
  have hsub : Subgroup.closure (CFSG.ClassicalGroups.Orthogonal.reflect QX ''
      {x : V | QX x = c}) ≤ movedGroup X := by
    rw [Subgroup.closure_le]
    rintro r ⟨x, hx, rfl⟩
    have hrange : CFSG.ClassicalGroups.Orthogonal.reflect QX x ∈
        (restrictHom X V hV).range :=
      MonoidHom.mem_range.mpr ⟨⟨_, hmem x hx⟩, hlift x hx⟩
    exact hrange
  have hprod := CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_reflect
    (K := ZMod p) (V := V) (Q := QX) h2 h3 hQXnd hab hc
  exact hsub hprod

private theorem false_of_classRefl_three_order (hp3 : p = 3) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {x y : U ≃ₗ[ZMod p] U}
    (hx : x ∈ Subgroup.closure (ClassRefl p Q c)) (hy : y ∈ Subgroup.closure (ClassRefl p Q c))
    (hrx : IsRefl p x) (hry : IsRefl p y) (hord : 3 < orderOf (x * y)) : False := by
  have hle := orderOf_mul_le_three_of_classRefl_three hp3 hQ hc hx hy hrx hry
  omega

private theorem movedGroup_contains_reflect_mul_reflect_of_isOrthOn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : IsOrthOn p Q X)
    (hQXnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate)
    (hd : p = 3 → ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∀ a b : HardMathSupport.Kantor79.commutatorSpace X,
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) a =
        (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) b →
      CFSG.ClassicalGroups.Orthogonal.reflect
          (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) a *
        CFSG.ClassicalGroups.Orthogonal.reflect
          (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) b ∈ movedGroup X := by
  rcases hX with hfull | ⟨c, hc, hclass⟩
  · intro a b _
    exact (movedGroup_orthogonal_of_isOrthOn_full hp hQ hQXnd hfull _).mpr
      (isIsom_mul (isIsom_reflect _ a) (isIsom_reflect _ b))
  · by_cases hp3 : p = 3
    · exfalso
      obtain ⟨x, hx, y, hy, hrx, hry, hord⟩ := hd hp3
      have hsub : {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤
            HardMathSupport.Kantor79.commutatorSpace X} ⊆ ClassRefl p Q c :=
        fun _ ht => ht.1
      have hxcl : x ∈ Subgroup.closure (ClassRefl p Q c) :=
        Subgroup.closure_mono hsub (by rwa [hclass] at hx)
      have hycl : y ∈ Subgroup.closure (ClassRefl p Q c) :=
        Subgroup.closure_mono hsub (by rwa [hclass] at hy)
      exact false_of_classRefl_three_order hp3 hQ hc hxcl hycl hrx hry hord
    · have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
      exact movedGroup_contains_reflect_mul_reflect_of_class hp hQ hc hQXnd h3 hclass

private theorem exists_mem_apply_eq_of_mem_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {e u : U} (he : e ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hu : u ∈ HardMathSupport.Kantor79.commutatorSpace X)
    {kbar : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X} (hkbar : kbar ∈ movedGroup X)
    (hkeq : kbar ⟨e, he⟩ = ⟨u, hu⟩) : ∃ k ∈ X, (k : U ≃ₗ[ZMod p] U) e = u := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  have hmem : kbar ∈ (restrictHom X V
      (fun _ hh _ hw => apply_mem_commutatorSpace hh hw)).range := by
    simpa only [movedGroup, V] using hkbar
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨k, k.2, ?_⟩
  have hkapply : ((restrictHom X V
      (fun _ hh _ hw => apply_mem_commutatorSpace hh hw) k) ⟨e, he⟩ : U) =
      (k : U ≃ₗ[ZMod p] U) e :=
    restrictHom_apply X V _ k ⟨e, he⟩
  rw [← hkapply, hk]
  exact congrArg (fun w : V => (w : U)) hkeq

theorem exists_mem_apply_eq_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1)) (hX : IsOrthOn p Q X)
    (hd : p = 3 → ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {e u : U} (he : e ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hu : u ∈ HardMathSupport.Kantor79.commutatorSpace X) (he0 : Q e ≠ 0) (hue : Q u = Q e) :
    ∃ k ∈ X, k e = u := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let QX : QuadraticForm (ZMod p) V := Q.comp V.subtype
  have hXQ : ∀ g ∈ X, IsIsom p Q g := fun g hg => IsOrthOn.isIsom hX hg
  have hQXnd : (QuadraticMap.polarBilin QX).Nondegenerate :=
    nondegenerate_comp_subtype_of_splitSupport hQ hs hXQ
  have hdim : 3 ≤ Module.finrank (ZMod p) V := by
    have h := hs.2.1
    change Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 at h
    omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hXbar := movedGroup_contains_reflect_mul_reflect_of_isOrthOn hp hQ hX hQXnd hd
  have he' : QX ⟨e, he⟩ ≠ 0 := by simpa [QX] using he0
  have hue' : QX ⟨u, hu⟩ = QX ⟨e, he⟩ := by simpa [QX] using hue
  obtain ⟨kbar, hkbar, hkeq⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_mem_apply_eq_of_reflect_mul_reflect_mem
      (K := ZMod p) (V := V) (Q := QX) (X := movedGroup X) h2 hQXnd hdim hXbar he' hue'
  exact exists_mem_apply_eq_of_mem_movedGroup he hu hkbar hkeq

private theorem movedGroup_eq_closure_restrictHom_refl {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hX : ReflGen p X) :
    movedGroup X = Subgroup.closure
      (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ''
        {t : X | IsRefl p (t : U ≃ₗ[ZMod p] U)}) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let R : Set X := {t | IsRefl p (t : U ≃ₗ[ZMod p] U)}
  have htop : (⊤ : Subgroup X) = Subgroup.closure R := by
    apply Subgroup.map_injective X.subtype_injective
    rw [MonoidHom.map_closure]
    have hmap : (⊤ : Subgroup X).map X.subtype = (X : Subgroup (U ≃ₗ[ZMod p] U)) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap]
    have hset : X.subtype '' R = {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
      ext y
      exact ⟨fun ⟨t, ht, hty⟩ => hty ▸ ⟨t.2, ht⟩,
        fun ⟨hy, hr⟩ => ⟨⟨y, hy⟩, hr, rfl⟩⟩
    rw [hset, ← hX]
  have hmg : movedGroup X = φ.range := rfl
  rw [hmg, ← Subgroup.map_top φ, htop, MonoidHom.map_closure]

private theorem restrictHom_reflSet_eq_classRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)} {c : ZMod p} (hc : c ≠ 0)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQXnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace X}) :
    restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ''
      {t : X | IsRefl p (t : U ≃ₗ[ZMod p] U)} =
      ClassRefl p (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) c := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let QX : QuadraticForm (ZMod p) V := Q.comp V.subtype
  let hV : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  ext r
  constructor
  · rintro ⟨t, htR, rfl⟩
    have htcl : (t : U ≃ₗ[ZMod p] U) ∈ Subgroup.closure (ClassRefl p Q c) :=
      Subgroup.closure_mono (fun _ hs => hs.1) (hclass.le t.2)
    obtain ⟨a, hQa, hta⟩ := (mem_classRefl_iff hp hQ hc t.1).mp
      (mem_classRefl_of_isRefl_mem_closure hp hQ hc htcl htR)
    have hQa0 : Q a ≠ 0 := by rw [hQa]; exact hc
    have hta_neg : t.1 a = -a := by
      rw [hta]
      exact reflect_apply_self hQa0
    have haV : a ∈ V :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace t.2
        (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
          (ZMod.prime_ne_zero p 2 hp) hta_neg)
    have hmemX : CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ X := by
      have htX : (t : U ≃ₗ[ZMod p] U) ∈ X := t.2
      rwa [hta] at htX
    refine (mem_classRefl_iff hp hQXnd hc _).mpr ⟨⟨a, haV⟩, ?_, ?_⟩
    · simpa [QX] using hQa
    · have ht_eq : t = ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a, hmemX⟩ :=
        Subtype.ext hta
      rw [ht_eq]
      exact restrictHom_reflect_eq hV (a := ⟨a, haV⟩) rfl hmemX
  · intro hr
    obtain ⟨a, hQxa, rfl⟩ := (mem_classRefl_iff hp hQXnd hc r).mp hr
    have hQa : Q a.1 = c := by simpa [QX] using hQxa
    have hQa0 : Q a.1 ≠ 0 := by rw [hQa]; exact hc
    have hmemX : CFSG.ClassicalGroups.Orthogonal.reflect Q a.1 ∈ X :=
      hclass.symm.le (Subgroup.subset_closure
        ⟨(mem_classRefl_iff hp hQ hc _).mpr ⟨a.1, hQa, rfl⟩,
          movedSpace_reflect_le a.2⟩)
    refine ⟨⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a.1, hmemX⟩, ?_, ?_⟩
    · exact ((mem_classRefl_iff hp hQ hc _).mpr ⟨a.1, hQa, rfl⟩).1
    · exact restrictHom_reflect_eq hV rfl hmemX

private theorem movedGroup_eq_closure_classRefl_of_isOrthOn_class
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {c : ZMod p} (hc : c ≠ 0)
    (hnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace X}) :
    movedGroup X = Subgroup.closure
      (ClassRefl p (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype) c) := by
  have hrg : ReflGen p X := by
    change X = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t}
    apply le_antisymm
    · calc X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤
            HardMathSupport.Kantor79.commutatorSpace X} := hclass
        _ ≤ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
          refine Subgroup.closure_mono ?_
          rintro t ⟨htc, htle⟩
          exact ⟨hclass.symm.le (Subgroup.subset_closure ⟨htc, htle⟩), htc.1⟩
    · exact (Subgroup.closure_le _).mpr (fun t ht => ht.1)
  rw [movedGroup_eq_closure_restrictHom_refl hrg,
    restrictHom_reflSet_eq_classRefl hp hc hQ hnd hclass]

theorem isOrthType_movedGroup_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : IsOrthOn p Q X)
    (hnd : (QuadraticMap.polarBilin
      (Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate) :
    IsOrthType p (movedGroup X) := by
  let QX : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) :=
    Q.comp (HardMathSupport.Kantor79.commutatorSpace X).subtype
  rcases hX with hfull | ⟨c, hc, hclass⟩
  · refine ⟨QX, hnd, Or.inl ?_⟩
    exact fun g => movedGroup_orthogonal_of_isOrthOn_full hp hQ hnd hfull g
  · refine ⟨QX, hnd, Or.inr ⟨c, hc, ?_⟩⟩
    exact movedGroup_eq_closure_classRefl_of_isOrthOn_class hp hQ hc hnd hclass

end CFSG.StandardType.ZS

end

module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticPrimaryPairing
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer

public section

namespace CFSG.RankThree.Classical

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary (gl_centralizer mem_gl_centralizer glCentralizerEquivPi
  blockGL blockApply blockApply_mem blockApply_blockApply blockApply_one
  blockApply_glCentralizerEquivPi unitaryCentralizer mem_unitaryCentralizer supportedUnitary
  supportedUnitary_le_unitaryCentralizer supportedUnitary_le_gl_centralizer trivialOn
  eq_one_of_forall_apply_eq)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {x : LinearMap.GeneralLinearGroup K V}

theorem glue_apply_of_mem (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]))
    (i : primaryFactors (x : Module.End K V)) {v : V}
    (hv : v ∈ primaryComponent (x : Module.End K V) (i : K[X])) :
    ((((glCentralizerEquivPi hsq).symm Γ : gl_centralizer x) :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply (Γ i) v hv := by
  have h := blockApply_glCentralizerEquivPi hsq ((glCentralizerEquivPi hsq).symm Γ) i v hv
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

@[expose] noncomputable def blockRestrict (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (S : Set K[X]) (a : primaryFactors (x : Module.End K V)) :
    supportedUnitary B x S →* blockGL (x : Module.End K V) (a : K[X]) :=
  (Pi.evalMonoidHom (fun b : primaryFactors (x : Module.End K V) =>
      blockGL (x : Module.End K V) (b : K[X])) a).comp
    ((glCentralizerEquivPi hsq).toMonoidHom.comp
      (Subgroup.inclusion (supportedUnitary_le_gl_centralizer S)))

theorem blockApply_blockRestrict (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (S : Set K[X]) (a : primaryFactors (x : Module.End K V)) (g : supportedUnitary B x S)
    (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])) :
    blockApply (blockRestrict hsq S a g) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

namespace AltPrimaryData

variable (H : AltPrimaryData B x)
include H

theorem mem_unitaryCentralizer_iff_blocks {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ unitaryCentralizer B x ↔ Commute (g : Module.End K V) (x : Module.End K V) ∧
      ∀ b ∈ primaryFactors (x : Module.End K V),
        ∀ v ∈ primaryComponent (x : Module.End K V) b,
        ∀ w ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial b),
          B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w := by
  rw [mem_unitaryCentralizer]
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨hc, fun b _ v _ w _ => mem_sesqUnitaryGroup.mp hg v w⟩
  · rintro ⟨hc, h⟩
    refine ⟨mem_sesqUnitaryGroup.mpr fun v w => ?_, hc⟩
    have hsq := H.squarefree
    have hπ1 : ∀ c (u : V), primaryProjection (x : Module.End K V) c ((g : Module.End K V) u) =
        (g : Module.End K V) (primaryProjection (x : Module.End K V) c u) := fun c u =>
      (congrArg (fun T : Module.End K V => T u) (commute_aeval hc _).eq).symm
    rw [H.B_eq_sum ((g : Module.End K V) v) ((g : Module.End K V) w), H.B_eq_sum v w]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hπ1, hπ1]
    exact h b hb _ (primaryProjection_mem hsq hb v) _
      (primaryProjection_mem hsq (H.reciprocal_mem hb) w)

theorem eq_one_of_paired {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ supportedUnitary B x {a, reciprocalPolynomial a})
    (h1 : ∀ v ∈ primaryComponent (x : Module.End K V) a, (g : Module.End K V) v = v) :
    g = 1 := by
  have hsq := H.squarefree
  have hcomm := mem_unitaryCentralizer.mp hg.1
  refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
  by_cases hca : c = a
  · subst hca
    exact h1 v hv
  by_cases hcb : c = reciprocalPolynomial a
  · subst hcb
    have hgw : (g : Module.End K V) v - v ∈
        primaryComponent (x : Module.End K V) (reciprocalPolynomial a) :=
      Submodule.sub_mem _ (apply_mem_primaryComponent hcomm.2 hv) hv
    have hzero := H.eq_zero_of_perfect_right ha hgw fun u hu => by
      have e1 : B u ((g : Module.End K V) v) = B u v := by
        have := mem_sesqUnitaryGroup.mp hcomm.1 u v
        rw [h1 u hu] at this
        exact this
      rw [map_sub, e1, sub_self]
    exact sub_eq_zero.mp hzero
  · exact hg.2 c hc (by simp [hca, hcb]) v hv

theorem exists_inverse_adjoint_block {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (γ : blockGL (x : Module.End K V) a) :
    ∃ δ : blockGL (x : Module.End K V) (reciprocalPolynomial a),
      ∀ (v w : V) (hv : v ∈ primaryComponent (x : Module.End K V) a)
        (hw : w ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial a)),
        B (blockApply γ v hv) (blockApply δ w hw) = B v w := by
  classical
  have hsq := H.squarefree
  have hb := H.reciprocal_mem ha
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let ib : primaryFactors (x : Module.End K V) := ⟨reciprocalPolynomial a, hb⟩
  let Γ₀ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update 1 ia γ
  let g₀ : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ₀
  have hg₀ : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by
      rw [glue_apply_of_mem hsq Γ₀ ia hv]
      simp [Γ₀, ia]
  have hc₀ : Commute ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (x : Module.End K V) := mem_gl_centralizer.mp g₀.2
  let u : LinearMap.GeneralLinearGroup K V :=
    ⟨H.adj ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V),
      H.adj (((g₀ : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V),
      by rw [← H.adj_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, H.adj_one],
      by rw [← H.adj_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, H.adj_one]⟩
  have hu : u ∈ gl_centralizer x := mem_gl_centralizer.mpr (H.adj_commute hc₀)
  let ũ : gl_centralizer x := ⟨u, hu⟩
  refine ⟨(glCentralizerEquivPi hsq ũ ib)⁻¹, fun v w hv hw => ?_⟩
  have h1 : blockApply γ v hv = ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    (hg₀ v hv).symm
  have h2 : blockApply (glCentralizerEquivPi hsq ũ ib)
      (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) (blockApply_mem _ w hw) = w := by
    rw [blockApply_blockApply, mul_inv_cancel, blockApply_one]
  have h3 := (blockApply_glCentralizerEquivPi hsq ũ ib
    (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) (blockApply_mem _ w hw)).symm.trans h2
  calc B (blockApply γ v hv) (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw)
      = B (((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) := by rw [h1]
    _ = B v (H.adj ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw)) := H.adj_spec _ _ _
    _ = B v w := by rw [show H.adj ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) = w from h3]

theorem blockRestrict_surjective_of_paired {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ reciprocalPolynomial a) :
    Function.Surjective (blockRestrict (B := B) H.squarefree {a, reciprocalPolynomial a}
      ⟨a, ha⟩) := by
  classical
  intro γ
  have hsq := H.squarefree
  have hb := H.reciprocal_mem ha
  obtain ⟨δ, hδ⟩ := H.exists_inverse_adjoint_block ha γ
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let ib : primaryFactors (x : Module.End K V) := ⟨reciprocalPolynomial a, hb⟩
  have hiab : ia ≠ ib := fun h => hne (congrArg Subtype.val h)
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update (Function.update 1 ia γ) ib δ
  let g : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hΓa : Γ ia = γ := by simp [Γ, hiab]
  have hΓb : Γ ib = δ := by simp [Γ]
  have hΓo : ∀ i, i ≠ ia → i ≠ ib → Γ i = 1 := fun i h1 h2 => by simp [Γ, h1, h2]
  have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by rw [glue_apply_of_mem hsq Γ ia hv, hΓa]
  have hgb : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (reciprocalPolynomial a)),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply δ v hv :=
    fun v hv => by rw [glue_apply_of_mem hsq Γ ib hv, hΓb]
  have hgo : ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ a → c ≠ reciprocalPolynomial a →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro c hc hca hcb v hv
    rw [glue_apply_of_mem hsq Γ ⟨c, hc⟩ hv, hΓo ⟨c, hc⟩ (fun h => hca (congrArg Subtype.val h))
      (fun h => hcb (congrArg Subtype.val h)), blockApply_one]
  have hmem : (g : LinearMap.GeneralLinearGroup K V) ∈
      supportedUnitary B x {a, reciprocalPolynomial a} := by
    refine ⟨(H.mem_unitaryCentralizer_iff_blocks).mpr ⟨mem_gl_centralizer.mp g.2, ?_⟩, ?_⟩
    · intro c hc v hv w hw
      by_cases hca : c = a
      · subst hca
        rw [hga v hv, hgb w hw]
        exact hδ v w hv hw
      by_cases hcb : c = reciprocalPolynomial a
      · subst hcb
        have hw' : w ∈ primaryComponent (x : Module.End K V) a := by
          rwa [H.reciprocal_reciprocal ha] at hw
        rw [hgb v hv, hga w hw']
        have h1 := hδ w v hw' hv
        rw [H.skew (blockApply γ w hw'), H.skew w, h1]
      · have hc1 : reciprocalPolynomial c ≠ a := fun h => hcb (by
          rw [← h, H.reciprocal_reciprocal hc])
        have hc2 : reciprocalPolynomial c ≠ reciprocalPolynomial a :=
          fun h => hca (H.reciprocal_injOn hc ha h)
        rw [hgo c hc hca hcb v hv, hgo (reciprocalPolynomial c) (H.reciprocal_mem hc) hc1 hc2 w hw]
    · intro c hc hcS v hv
      exact hgo c hc (fun h => hcS (Or.inl h)) (fun h => hcS (Or.inr h)) v hv
  refine ⟨⟨(g : LinearMap.GeneralLinearGroup K V), hmem⟩, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact hga v v.2

theorem blockRestrict_injective_of_paired {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) :
    Function.Injective (blockRestrict (B := B) H.squarefree {a, reciprocalPolynomial a}
      ⟨a, ha⟩) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine H.eq_one_of_paired ha g.2 fun v hv => ?_
  have h1 := congrArg (fun γ : blockGL (x : Module.End K V) a =>
    ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) ⟨v, hv⟩ :
      primaryComponent (x : Module.End K V) a)) hg
  exact congrArg Subtype.val h1

@[expose] noncomputable def pairedEquiv {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ reciprocalPolynomial a) :
    supportedUnitary B x {a, reciprocalPolynomial a} ≃* blockGL (x : Module.End K V) a :=
  MulEquiv.ofBijective (blockRestrict H.squarefree {a, reciprocalPolynomial a} ⟨a, ha⟩)
    ⟨H.blockRestrict_injective_of_paired ha, H.blockRestrict_surjective_of_paired ha hne⟩

theorem blockApply_pairedEquiv {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hne : a ≠ reciprocalPolynomial a) (g : supportedUnitary B x {a, reciprocalPolynomial a})
    (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply (H.pairedEquiv ha hne g) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

theorem commute_of_disjoint {O O' : Set K[X]} (hd : Disjoint O O')
    {g g' : LinearMap.GeneralLinearGroup K V} (hg : g ∈ supportedUnitary B x O)
    (hg' : g' ∈ supportedUnitary B x O') : Commute g g' := by
  refine Units.ext (ext_primaryComponent H.squarefree fun b hb v hv => ?_)
  have hcomm := (mem_unitaryCentralizer.mp hg.1).2
  have hcomm' := (mem_unitaryCentralizer.mp hg'.1).2
  change (g : Module.End K V) ((g' : Module.End K V) v) =
    (g' : Module.End K V) ((g : Module.End K V) v)
  by_cases hO : b ∈ O
  · have hO' : b ∉ O' := fun h => Set.disjoint_left.mp hd hO h
    rw [hg'.2 b hb hO' v hv, hg'.2 b hb hO' _ (apply_mem_primaryComponent hcomm hv)]
  · by_cases hO' : b ∈ O'
    · rw [hg.2 b hb hO v hv, hg.2 b hb hO _ (apply_mem_primaryComponent hcomm' hv)]
    · rw [hg.2 b hb hO v hv, hg'.2 b hb hO' v hv, hg.2 b hb hO v hv]

theorem iSupIndep_supported {orbits : Set (Set K[X])}
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O') :
    iSupIndep (fun O : orbits => supportedUnitary B x (O : Set K[X])) := by
  intro O
  rw [Subgroup.disjoint_def]
  intro g hgO hgsup
  have hle : (⨆ (O' : orbits) (_ : O' ≠ O), supportedUnitary B x (O' : Set K[X])) ≤
      trivialOn x (O : Set K[X]) := by
    refine iSup₂_le fun O' hO' g' hg' b hb hbO v hv => ?_
    have hd := hdisj O' O'.2 O O.2 (fun h => hO' (Subtype.ext h))
    exact hg'.2 b hb (fun h => Set.disjoint_left.mp hd h hbO) v hv
  have hgT := hle hgsup
  refine eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => ?_
  by_cases hbO : b ∈ (O : Set K[X])
  · exact hgT b hb hbO v hv
  · exact hgO.2 b hb hbO v hv

theorem exists_component {O : Set K[X]}
    (hO : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O → reciprocalPolynomial b ∈ O)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ unitaryCentralizer B x) :
    ∃ gO ∈ supportedUnitary B x O, ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        (gO : Module.End K V) v = (g : Module.End K V) v := by
  classical
  have hsq := H.squarefree
  let g' : gl_centralizer x := ⟨g, (mem_unitaryCentralizer.mp hg).2 |> mem_gl_centralizer.mpr⟩
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    fun b => if (b : K[X]) ∈ O then glCentralizerEquivPi hsq g' b else 1
  let gO : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hin : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
      ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        (g : Module.End K V) v := by
    intro b hb hbO v hv
    rw [glue_apply_of_mem hsq Γ ⟨b, hb⟩ hv]
    simp only [Γ, hbO, ↓reduceIte]
    rfl
  have hout : ∀ b ∈ primaryFactors (x : Module.End K V), b ∉ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
      ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro b hb hbO v hv
    rw [glue_apply_of_mem hsq Γ ⟨b, hb⟩ hv]
    simp only [Γ, hbO, ↓reduceIte]
    rfl
  refine ⟨(gO : LinearMap.GeneralLinearGroup K V), ⟨?_, hout⟩, hin⟩
  refine (H.mem_unitaryCentralizer_iff_blocks).mpr ⟨mem_gl_centralizer.mp gO.2, ?_⟩
  intro c hc v hv w hw
  by_cases hcO : c ∈ O
  · rw [hin c hc hcO v hv, hin (reciprocalPolynomial c) (H.reciprocal_mem hc) (hO c hc hcO) w hw]
    exact ((H.mem_unitaryCentralizer_iff_blocks).mp hg).2 c hc v hv w hw
  · have hcO' : reciprocalPolynomial c ∉ O := fun h => hcO (by
      have := hO _ (H.reciprocal_mem hc) h
      rwa [H.reciprocal_reciprocal hc] at this)
    rw [hout c hc hcO v hv, hout (reciprocalPolynomial c) (H.reciprocal_mem hc) hcO' w hw]

theorem unitaryCentralizer_le_iSup {orbits : Set (Set K[X])}
    (hcov : ∀ b ∈ primaryFactors (x : Module.End K V), ∃ O ∈ orbits, b ∈ O)
    (hcl : ∀ O ∈ orbits, ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      reciprocalPolynomial b ∈ O) :
    unitaryCentralizer B x ≤ ⨆ O : orbits, supportedUnitary B x (O : Set K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ O : orbits, supportedUnitary B x (O : Set K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ g ∈ unitaryCentralizer B x,
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) → g ∈ M by
    intro g hg
    exact key (primaryFactors (x : Module.End K V)) g hg fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro g hg h
    have : g = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]
    exact M.one_mem
  | insert b F hbF ih =>
    intro g hg h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · obtain ⟨O, hO, hbO⟩ := hcov b hbΦ
      obtain ⟨gO, hgO, hgOeq⟩ := H.exists_component (hcl O hO) hg
      have hgOM : gO ∈ M := (le_iSup (fun O : orbits => supportedUnitary B x (O : Set K[X]))
        ⟨O, hO⟩) hgO
      have hg' : gO⁻¹ * g ∈ unitaryCentralizer B x :=
        (unitaryCentralizer B x).mul_mem ((unitaryCentralizer B x).inv_mem hgO.1) hg
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            ((gO : Module.End K V) u) = u := fun u => by
          rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
          rfl
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv]
          rw [← hgo, hinv, hgo]
      have := ih _ hg' h'
      have hg_eq : g = gO * (gO⁻¹ * g) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM this
    · refine ih g hg fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩

end AltPrimaryData

end CFSG.RankThree.Classical

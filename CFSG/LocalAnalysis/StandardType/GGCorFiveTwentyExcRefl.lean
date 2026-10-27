module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGExcReflTBData (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (Bs L J : Subgroup G) where
  Λ : Type
  [instFintype : Fintype Λ]
  coxeter : CoxeterMatrix Λ
  cartan : Matrix Λ Λ ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  model : Additive ↥Bs ≃+ V
  simple : Λ → MulAut ↥Bs
  coroot : Λ → V
  root : Λ → Module.Dual (ZMod p) V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  three_le_card : 3 ≤ Fintype.card Λ
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)
  simple_apply : ∀ i w, ggLin (p := p) model (simple i) w = w - root i w • coroot i
  automizer_eq : ggAutomizer L Bs = Subgroup.closure (Set.range simple)
  tbHyp : Module.finrank (ZMod p) V ≤
        Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range coroot)) + 1 ∨
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) model (ggAutNormalClosure L J Bs)) ≤ 1
  noncomm : ∃ (i j : Λ) (c c' : MulAut ↥Bs), c ∈ ggAutomizer L Bs ∧ c' ∈ ggAutomizer L Bs ∧
    c * simple i * c⁻¹ ∈ ggAutomizer J Bs ∧ c' * simple j * c'⁻¹ ∈ ggAutomizer J Bs ∧
    c * simple i * c⁻¹ * (c' * simple j * c'⁻¹) ≠ c' * simple j * c'⁻¹ * (c * simple i * c⁻¹)

attribute [instance] GGExcReflTBData.instFintype GGExcReflTBData.instAddCommGroup
  GGExcReflTBData.instModule

@[expose] def GGExcReflTBInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        ∀ [Fact p.Prime], Nonempty (GGExcReflTBData p Bs L J)

section NormalClosure

variable {G : Type} [Group G] {L J : Subgroup G} {Bs : Subgroup G}

theorem conj_mem_ggAutNormalClosure {a w : MulAut ↥Bs} (hw : w ∈ ggAutomizer L Bs)
    (ha : a ∈ ggAutomizer J Bs) : w * a * w⁻¹ ∈ ggAutNormalClosure L J Bs :=
  Subgroup.subset_closure ⟨w, mem_ggAutomizer_iff.mp hw, a, mem_ggAutomizer_iff.mp ha, rfl⟩

theorem ggAutNormalClosure_le_ggAutomizer (hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs) :
    ggAutNormalClosure L J Bs ≤ ggAutomizer L Bs := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨c, hc, a, ha, rfl⟩
  exact (ggAutomizer L Bs).mul_mem
    ((ggAutomizer L Bs).mul_mem (Subgroup.subset_closure hc) (hJL (Subgroup.subset_closure ha)))
    ((ggAutomizer L Bs).inv_mem (Subgroup.subset_closure hc))

theorem ne_conj_of_commute_ggAutNormalClosure {t s a w : MulAut ↥Bs}
    (htc : ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) (ha : a ∈ ggAutomizer J Bs)
    (hnc : s * a ≠ a * s) (hw : w ∈ ggAutomizer L Bs) : w * s * w⁻¹ ≠ t := by
  intro hwt
  apply hnc
  have h := htc _ (conj_mem_ggAutNormalClosure hw ha)
  rw [← hwt] at h
  calc s * a = w⁻¹ * ((w * s * w⁻¹) * (w * a * w⁻¹)) * w := by group
    _ = w⁻¹ * ((w * a * w⁻¹) * (w * s * w⁻¹)) * w := by rw [h]
    _ = a * s := by group

end NormalClosure

namespace GGExcReflTBData

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L J : Subgroup G}
  (T : GGExcReflTBData p Bs L J)

theorem root_coroot_self (i : T.Λ) : T.root i (T.coroot i) = 2 := by
  rw [T.pairing, T.isCartan.1 i]
  norm_num

theorem simple_mem (i : T.Λ) : T.simple i ∈ ggAutomizer L Bs := by
  rw [T.automizer_eq]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem conj_simple_apply (u : MulAut ↥Bs) (i : T.Λ) (v : T.V) :
    ggLin (p := p) T.model (u * T.simple i * u⁻¹) v =
      v - T.root i ((ggLin (p := p) T.model u).symm v) • ggLin (p := p) T.model u (T.coroot i) :=
  ggLin_conj_apply T.model u (T.simple i) (T.simple_apply i) v

theorem apply_conj_coroot_eq_zero (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {t : MulAut ↥Bs}
    (htA : t ∈ ggAutomizer ⊤ Bs) (htc : ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t)
    {y : T.V} {f : Module.Dual (ZMod p) T.V} (hfy : f y = 2)
    (hLt : ggLin (p := p) T.model t = reflection hfy) {i : T.Λ} {c a u : MulAut ↥Bs}
    (hc : c ∈ ggAutomizer L Bs) (hcJ : c * T.simple i * c⁻¹ ∈ ggAutomizer J Bs)
    (ha : a ∈ ggAutomizer J Bs) (hnc : c * T.simple i * c⁻¹ * a ≠ a * (c * T.simple i * c⁻¹))
    (hu : u ∈ ggAutomizer L Bs) : f (ggLin (p := p) T.model u (T.coroot i)) = 0 := by
  have hw : u * c⁻¹ ∈ ggAutomizer L Bs :=
    (ggAutomizer L Bs).mul_mem hu ((ggAutomizer L Bs).inv_mem hc)
  have hconj : u * T.simple i * u⁻¹ = (u * c⁻¹) * (c * T.simple i * c⁻¹) * (u * c⁻¹)⁻¹ := by
    group
  have hrN : u * T.simple i * u⁻¹ ∈ ggAutNormalClosure L J Bs := by
    rw [hconj]
    exact conj_mem_ggAutNormalClosure hw hcJ
  have hne : u * T.simple i * u⁻¹ ≠ t := by
    rw [hconj]
    exact ne_conj_of_commute_ggAutNormalClosure htc ha hnc hw
  have hrA : u * T.simple i * u⁻¹ ∈ ggAutomizer L Bs :=
    (ggAutomizer L Bs).mul_mem ((ggAutomizer L Bs).mul_mem hu (T.simple_mem i))
      ((ggAutomizer L Bs).inv_mem hu)
  have hrT : u * T.simple i * u⁻¹ ∈ ggInduced ⊤ Bs :=
    mem_ggAutomizer_iff.mp (ggAutomizer_mono Bs le_top hrA)
  have hgz : ((T.root i).comp ((ggLin (p := p) T.model u).symm : T.V →ₗ[ZMod p] T.V))
      (ggLin (p := p) T.model u (T.coroot i)) = 2 := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact T.root_coroot_self i
  have hLr : ggLin (p := p) T.model (u * T.simple i * u⁻¹) = reflection hgz :=
    ggLin_eq_reflection T.model hgz (T.conj_simple_apply u i)
  have hind := (ggReflection_linearIndependent_of_noTransvection hp2 hNT T.model
    (mem_ggAutomizer_iff.mp htA) hrT hne.symm hfy hgz hLt hLr).1
  have hcomm : reflection hfy * reflection hgz = reflection hgz * reflection hfy := by
    rw [← hLt, ← hLr, ← map_mul, ← map_mul, htc _ hrN]
  exact ggReflection_comm_cross_eq_zero hp2 hfy hgz hind hcomm

theorem exists_vanishing [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) (htA : t ∈ ggAutomizer ⊤ Bs)
    (htc : ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) :
    ∃ (y : T.V) (f : Module.Dual (ZMod p) T.V) (hfy : f y = 2),
      ggLin (p := p) T.model t = reflection hfy ∧ ∀ k, f (T.coroot k) = 0 := by
  haveI : Finite T.V := Finite.of_equiv ↥Bs (Additive.ofMul.trans T.model.toEquiv)
  obtain ⟨y, f, hfy, hty⟩ := exists_of_ggIsReflection T.model ht
  have hLt : ggLin (p := p) T.model t = reflection hfy := ggLin_eq_reflection T.model hfy hty
  refine ⟨y, f, hfy, hLt, fun k => ?_⟩
  obtain ⟨i, j, c, c', hc, -, hcJ, hc'J, hnc⟩ := T.noncomm
  have h := ggCartan_orbit_apply_eq_zero hp2 T.isWeyl T.isCartan T.three_le_card T.pairing
    ((ggAutomizer L Bs).map (ggLin (p := p) T.model))
    (fun k => ggLin (p := p) T.model (T.simple k)) T.simple_apply
    (fun k => ⟨T.simple k, T.simple_mem k, rfl⟩) f (i₀ := i)
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact T.apply_conj_coroot_eq_zero hp2 hNT htA htc hfy hLt hc hcJ hc'J hnc hu) k 1
    (Subgroup.one_mem _)
  simpa using h

theorem ggLin_sub_mem_span {u : MulAut ↥Bs} (hu : u ∈ ggAutomizer L Bs) (w : T.V) :
    ggLin (p := p) T.model u w - w ∈ Submodule.span (ZMod p) (Set.range T.coroot) := by
  rw [T.automizer_eq] at hu
  revert w
  refine Subgroup.closure_induction (p := fun u _ => ∀ w : T.V, ggLin (p := p) T.model u w - w ∈
    Submodule.span (ZMod p) (Set.range T.coroot)) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨i, rfl⟩ w
    rw [T.simple_apply, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro w
    simp
  · intro u v _ _ hu hv w
    have h := add_mem (hu (ggLin (p := p) T.model v w)) (hv w)
    rwa [sub_add_sub_cancel, ← LinearEquiv.mul_apply, ← map_mul] at h
  · intro u _ hu w
    have h := Submodule.neg_mem _ (hu (ggLin (p := p) T.model u⁻¹ w))
    rwa [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, neg_sub] at h

theorem mem_ggFixedSubmodule_of_commute (hp2 : p ≠ 2)
    (hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs) {t : MulAut ↥Bs}
    (htc : ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) {y : T.V}
    {f : Module.Dual (ZMod p) T.V} (hfy : f y = 2)
    (hLt : ggLin (p := p) T.model t = reflection hfy) (hf : ∀ k, f (T.coroot k) = 0) :
    y ∈ ggFixedSubmodule (p := p) T.model (ggAutNormalClosure L J Bs) := by
  rw [mem_ggFixedSubmodule_iff]
  intro φ hφ
  have hH := T.ggLin_sub_mem_span (ggAutNormalClosure_le_ggAutomizer hJL hφ) y
  have hcomm : reflection hfy * ggLin (p := p) T.model φ =
      ggLin (p := p) T.model φ * reflection hfy := by
    rw [← hLt, ← map_mul, ← map_mul, htc φ hφ]
  have h1 := congrArg (fun S : T.V ≃ₗ[ZMod p] T.V => S y) hcomm
  simp only [LinearEquiv.mul_apply, reflection_apply_self, map_neg] at h1
  rw [reflection_apply] at h1
  have hfφ : f (ggLin (p := p) T.model φ y) = 2 := by
    have h2 := apply_eq_zero_of_mem_span_range hf hH
    rwa [map_sub, hfy, sub_eq_zero] at h2
  rw [hfφ] at h1
  have h3 : (2 : ZMod p) • ggLin (p := p) T.model φ y = (2 : ZMod p) • y := by
    linear_combination (norm := module) h1
  exact smul_right_injective T.V (zmod_two_ne_zero hp2) h3

include T in
theorem unique [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs) {t t' : MulAut ↥Bs}
    (ht : GGIsReflection p t) (htA : t ∈ ggAutomizer ⊤ Bs)
    (htc : ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t)
    (ht' : GGIsReflection p t') (htA' : t' ∈ ggAutomizer ⊤ Bs)
    (htc' : ∀ φ ∈ ggAutNormalClosure L J Bs, t' * φ = φ * t') : t = t' := by
  by_contra hne
  obtain ⟨y, f, hfy, hLt, hf⟩ := T.exists_vanishing hp2 hNT ht htA htc
  obtain ⟨y', g, hgy, hLt', hg⟩ := T.exists_vanishing hp2 hNT ht' htA' htc'
  obtain ⟨hyy, hfg⟩ := ggReflection_linearIndependent_of_noTransvection hp2 hNT T.model
    (mem_ggAutomizer_iff.mp htA) (mem_ggAutomizer_iff.mp htA') hne hfy hgy hLt hLt'
  haveI : Finite T.V := Finite.of_equiv ↥Bs (Additive.ofMul.trans T.model.toEquiv)
  rcases T.tbHyp with hcodim | hline
  · exact not_linearIndependent_pair_of_vanishing_of_codim_le _ hcodim
      (fun _ => apply_eq_zero_of_mem_span_range hf) (fun _ => apply_eq_zero_of_mem_span_range hg)
      hfg
  · exact not_linearIndependent_pair_of_mem _ hline
      (T.mem_ggFixedSubmodule_of_commute hp2 hJL htc hfy hLt hf)
      (T.mem_ggFixedSubmodule_of_commute hp2 hJL htc' hgy hLt' hg) hyy

theorem ggWeylReflectionGroup [Finite G] (hp2 : p ≠ 2)
    (hli : LinearIndependent (ZMod p) T.coroot) :
    GGWeylReflectionGroup p (ggAutomizer L Bs) := by
  have hα : ∀ i, T.root i (T.coroot i) = 2 := T.root_coroot_self
  have hlin : ∀ i, ggLin (p := p) T.model (T.simple i) = reflection (hα i) := fun i =>
    ggLin_eq_reflection T.model (hα i) (T.simple_apply i)
  have hlinL := isLiftable_reflection_of_intCartan T.isCartan T.coroot T.root hα T.pairing
  have hφL : T.coxeter.IsLiftable T.simple := by
    intro i j
    apply ggLin_injective (p := p) T.model
    rw [map_pow, map_mul, hlin, hlin, map_one]
    exact hlinL i j
  rw [T.automizer_eq]
  refine ggWeylReflectionGroup_of_lift T.isWeyl T.simple hφL
    (fun i => ggIsReflection_of_eq_reflection hp2 T.model (hα i) (hlin i)) ?_
  have hinjL := ggCartanFaithfulInputFixed_holds p Fact.out hp2 T.Λ T.coxeter T.cartan T.isWeyl
    T.isCartan T.V T.coroot T.root hα T.pairing hli
  have hcomp : (ggLin (p := p) T.model).comp (T.coxeter.toCoxeterSystem.lift ⟨T.simple, hφL⟩) =
      T.coxeter.toCoxeterSystem.lift ⟨_, hlinL⟩ := by
    refine T.coxeter.toCoxeterSystem.ext_simple fun i => ?_
    rw [MonoidHom.comp_apply, CoxeterSystem.lift_apply_simple, CoxeterSystem.lift_apply_simple,
      hlin]
  intro w₁ w₂ hw
  apply hinjL
  rw [← hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, hw]

end GGExcReflTBData

theorem ggExcReflInput_of_tb (hTB : GGExcReflTBInput) : GGExcReflInput := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs :=
    ggAutomizer_mono Bs (hHyp.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left)
  obtain ⟨T⟩ := hTB G p B Bs x L D J hHyp hq hN hW
  by_cases hex : ∃ t : MulAut ↥Bs, GGIsReflection p t ∧ t ∈ ggAutomizer ⊤ Bs ∧
      ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t
  · obtain ⟨ρ, hρ, hρA, hρc⟩ := hex
    exact ⟨ρ, fun t ht htA htc => T.unique hp2 hHyp.2.2.2.1 hJL ht htA htc hρ hρA hρc⟩
  · exact ⟨1, fun t ht htA htc => absurd ⟨t, ht, htA, htc⟩ hex⟩

end CFSG.StandardType

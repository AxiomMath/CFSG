module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.LieType.Universal.SpinOmega.Reflections
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.JRFacts
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

namespace RootCentOmega

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup
  finrank_commSpace_reflection)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_self_charTwo [CharP K 2] (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem eichler_mul_self [CharP K 2] (u w : V) : eichler Q u w * eichler Q u w = 1 := by
  by_cases hw : polar Q u w = 0
  · rw [eichler_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul, eichler_zero_right]
  · rw [eichler_of_polar_ne_zero hw, one_mul]

theorem mem_ggOTwoPrime_of_mul_self {G : Type*} [Group G] {Y : Subgroup G} {y : G} (hy : y ∈ Y)
    (h : y * y = 1) : y ∈ ggOTwoPrime Y :=
  Subgroup.subset_closure ⟨hy, 1, by rw [pow_one, pow_two, h]⟩

theorem reflect_mul_reflect_comm {a b : V} (hab : polar Q a b = 0) :
    reflect Q a * reflect Q b = reflect Q b * reflect Q a := by
  by_cases ha : Q a = 0
  · rw [reflect_of_map_eq_zero ha, one_mul, mul_one]
  by_cases hb : Q b = 0
  · rw [reflect_of_map_eq_zero hb, one_mul, mul_one]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply ha, reflect_apply hb,
    reflect_apply ha, reflect_apply hb, polar_sub_right, polar_sub_right, polar_smul_right_eq,
    polar_smul_right_eq, hab, polar_comm Q b a, hab, mul_zero, mul_zero, sub_zero, sub_zero]
  abel

theorem reflect_apply_mem {W : Submodule K V} {a c : V} (ha : a ∈ W) (hc : c ∈ W) :
    reflect Q c a ∈ W := by
  by_cases h : Q c = 0
  · rw [reflect_of_map_eq_zero h]
    exact ha
  · rw [reflect_apply h]
    exact W.sub_mem ha (W.smul_mem _ hc)

theorem eichler_apply_mem {W : Submodule K V} {u w x : V} (hu : u ∈ W) (hw : w ∈ W)
    (hx : x ∈ W) : eichler Q u w x ∈ W := by
  obtain ⟨a, b, h⟩ := eichler_apply_eq_add (Q := Q) u w x
  rw [h]
  exact W.add_mem (W.add_mem hx (W.smul_mem _ hw)) (W.smul_mem _ hu)

variable (Q) in
@[expose] def eichlerSet (W : Submodule K V) : Set (V ≃ₗ[K] V) :=
  {g | ∃ u ∈ W, ∃ w ∈ W, eichler Q u w = g}

variable (Q) in
@[expose] def reflSet (W : Submodule K V) : Set (V ≃ₗ[K] V) :=
  {g | ∃ a ∈ W, reflect Q a = g}

variable (Q) in
@[expose] def evenSet (W : Submodule K V) : Set (V ≃ₗ[K] V) :=
  {g | ∃ a ∈ W, ∃ b ∈ W, Q a ≠ 0 ∧ Q b ≠ 0 ∧ reflect Q a * reflect Q b = g}

variable (Q) in
@[expose] def evenSub (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure (eichlerSet Q W ∪ evenSet Q W)

theorem reflect_conj_mem_evenSub {W : Submodule K V} {c : V} (hc : c ∈ W) {g : V ≃ₗ[K] V}
    (hg : g ∈ evenSub Q W) : reflect Q c * g * reflect Q c ∈ evenSub Q W := by
  have hcO := reflect_mem_orthogonalGroup Q c
  have hrr := reflect_mul_self Q c
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨u, hu, w, hw, rfl⟩ | ⟨a, ha, b, hb, hQa, hQb, rfl⟩
    · refine Subgroup.subset_closure (Or.inl ⟨reflect Q c u, reflect_apply_mem hu hc,
        reflect Q c w, reflect_apply_mem hw hc, ?_⟩)
      rw [← eichler_conj hcO, reflect_inv]
    · refine Subgroup.subset_closure (Or.inr ⟨reflect Q c a, reflect_apply_mem ha hc,
        reflect Q c b, reflect_apply_mem hb hc, by rwa [map_of_mem hcO],
        by rwa [map_of_mem hcO], ?_⟩)
      rw [← reflect_conj hcO, ← reflect_conj hcO, reflect_inv]
      calc reflect Q c * reflect Q a * reflect Q c * (reflect Q c * reflect Q b * reflect Q c)
          = reflect Q c * reflect Q a * (reflect Q c * reflect Q c) * reflect Q b *
              reflect Q c := by group
        _ = _ := by rw [hrr, mul_one]; group
  | one => rw [mul_one, hrr]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : reflect Q c * (x * y) * reflect Q c =
        reflect Q c * x * reflect Q c * (reflect Q c * y * reflect Q c) := by
      calc reflect Q c * (x * y) * reflect Q c
          = reflect Q c * x * (reflect Q c * reflect Q c) * y * reflect Q c := by
            rw [hrr]; group
        _ = _ := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : reflect Q c * x⁻¹ * reflect Q c = (reflect Q c * x * reflect Q c)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, reflect_inv]
      group
    rw [e]
    exact inv_mem hx

theorem mem_evenSub_or_of_mem_closure {W : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.closure (reflSet Q W ∪ eichlerSet Q W)) :
    g ∈ evenSub Q W ∨ ∃ a ∈ W, Q a ≠ 0 ∧ g * reflect Q a ∈ evenSub Q W := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨a, ha, rfl⟩ | hE
    · by_cases hQa : Q a = 0
      · left
        rw [reflect_of_map_eq_zero hQa]
        exact Subgroup.one_mem _
      · right
        exact ⟨a, ha, hQa, by rw [reflect_mul_self]; exact Subgroup.one_mem _⟩
    · exact Or.inl (Subgroup.subset_closure (Or.inl hE))
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul x y _ _ hx hy =>
    rcases hx with hx | ⟨a, ha, hQa, hxa⟩ <;> rcases hy with hy | ⟨b, hb, hQb, hyb⟩
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr ⟨b, hb, hQb, by rw [mul_assoc]; exact mul_mem hx hyb⟩
    · refine Or.inr ⟨a, ha, hQa, ?_⟩
      have e : x * y * reflect Q a = x * reflect Q a * (reflect Q a * y * reflect Q a) := by
        calc x * y * reflect Q a = x * (reflect Q a * reflect Q a) * y * reflect Q a := by
              rw [reflect_mul_self]; group
          _ = _ := by group
      rw [e]
      exact mul_mem hxa (reflect_conj_mem_evenSub ha hy)
    · left
      have e : x * y = x * reflect Q a * (reflect Q a * (y * reflect Q b) * reflect Q a) *
          (reflect Q a * reflect Q b) := by
        calc x * y = x * (reflect Q a * reflect Q a) * y *
              (reflect Q b * (reflect Q a * reflect Q a) * reflect Q b) := by
              rw [reflect_mul_self Q a, mul_one, mul_one, reflect_mul_self Q b]; group
          _ = _ := by group
      rw [e]
      exact mul_mem (mul_mem hxa (reflect_conj_mem_evenSub ha hyb))
        (Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hQa, hQb, rfl⟩))
  | inv x _ hx =>
    rcases hx with hx | ⟨a, ha, hQa, hxa⟩
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨a, ha, hQa, ?_⟩
      have e : x⁻¹ * reflect Q a = reflect Q a * (x * reflect Q a)⁻¹ * reflect Q a := by
        rw [mul_inv_rev, reflect_inv, ← mul_assoc, reflect_mul_self, one_mul]
      rw [e]
      exact reflect_conj_mem_evenSub ha (inv_mem hxa)

theorem exists_extend_of_mem_elementaryGroup {W : Submodule K V} {g' : W ≃ₗ[K] W}
    (hg' : g' ∈ elementaryGroup (Q.restrict W)) :
    ∃ g ∈ Subgroup.closure (eichlerSet Q W), (∀ x : W, g x = g' x) ∧
      ∀ z, (∀ x ∈ W, polar Q z x = 0) → g z = z := by
  induction hg' using Subgroup.closure_induction with
  | mem g' hg' =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hg'
    have hu' : Q u = 0 := hu
    have hw' : polar Q u w = 0 := by rwa [polar_restrict] at hw
    refine ⟨eichler Q u w, Subgroup.subset_closure ⟨u, u.2, w, w.2, rfl⟩, fun x => ?_,
      fun z hz => eichler_apply_of_polar_eq_zero (hz u u.2) (hz w w.2)⟩
    rw [eichler_apply hu' hw', eichler_apply hu hw]
    simp [polar_restrict]
  | one => exact ⟨1, Subgroup.one_mem _, fun x => rfl, fun z _ => rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    obtain ⟨h, hh, hhx, hhz⟩ := ihb
    refine ⟨g * h, mul_mem hg hh, fun x => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhx, hgx]
    · rw [LinearEquiv.mul_apply, hhz z hz, hgz z hz]
  | inv a _ iha =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    refine ⟨g⁻¹, inv_mem hg, fun x => ?_, fun z hz => ?_⟩
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgx, LinearEquiv.apply_inv_apply']
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgz z hz]

theorem exists_extend_of_mem_closure {W : Submodule K V} {g' : W ≃ₗ[K] W}
    (hg' : g' ∈ Subgroup.closure (Set.range (reflect (Q.restrict W)) ∪
      (elementaryGroup (Q.restrict W) : Set (W ≃ₗ[K] W)))) :
    ∃ g ∈ Subgroup.closure (reflSet Q W ∪ eichlerSet Q W), (∀ x : W, g x = g' x) ∧
      ∀ z, (∀ x ∈ W, polar Q z x = 0) → g z = z := by
  induction hg' using Subgroup.closure_induction with
  | mem g' hg' =>
    rcases hg' with ⟨a, rfl⟩ | hE
    · refine ⟨reflect Q a, Subgroup.subset_closure (Or.inl ⟨a, a.2, rfl⟩), fun x => ?_,
        fun z hz => reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hz a a.2)⟩
      by_cases ha : Q a = 0
      · have ha' : Q.restrict W a = 0 := ha
        rw [reflect_of_map_eq_zero ha, reflect_of_map_eq_zero ha']
        rfl
      · have ha' : Q.restrict W a ≠ 0 := ha
        rw [reflect_apply ha, reflect_apply ha']
        simp [polar_restrict]
    · obtain ⟨g, hg, hgx, hgz⟩ := exists_extend_of_mem_elementaryGroup hE
      exact ⟨g, Subgroup.closure_mono Set.subset_union_right hg, hgx, hgz⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun x => rfl, fun z _ => rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    obtain ⟨h, hh, hhx, hhz⟩ := ihb
    refine ⟨g * h, mul_mem hg hh, fun x => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhx, hgx]
    · rw [LinearEquiv.mul_apply, hhz z hz, hgz z hz]
  | inv a _ iha =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    refine ⟨g⁻¹, inv_mem hg, fun x => ?_, fun z hz => ?_⟩
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgx, LinearEquiv.apply_inv_apply']
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgz z hz]

section TwoPairs

variable {P₁ P₂ : HypPair Q}

theorem mem_perpTwo {x : V} : x ∈ P₁.perp ⊓ P₂.perp ↔
    (polar Q P₁.e x = 0 ∧ polar Q P₁.f x = 0) ∧ (polar Q P₂.e x = 0 ∧ polar Q P₂.f x = 0) := by
  rw [Submodule.mem_inf, HypPair.mem_perp, HypPair.mem_perp]

theorem apply_mem_perpTwo {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h1 : g P₁.e = P₁.e) (h2 : g P₁.f = P₁.f) (h3 : g P₂.e = P₂.e) (h4 : g P₂.f = P₂.f)
    {x : V} (hx : x ∈ P₁.perp ⊓ P₂.perp) : g x ∈ P₁.perp ⊓ P₂.perp := by
  have key : ∀ v, g v = v → polar Q v (g x) = polar Q v x := fun v hv => by
    conv_lhs => rw [← hv]
    exact polar_map_of_mem hgO v x
  rw [mem_perpTwo] at hx ⊢
  rw [key _ h1, key _ h2, key _ h3, key _ h4]
  exact hx

theorem inv_apply_eq_of_apply_eq {g : V ≃ₗ[K] V} {v : V} (h : g v = v) : g⁻¹ v = v := by
  apply g.injective
  rw [LinearEquiv.apply_inv_apply', h]

theorem eq_of_eq_on_perpTwo (h₁₂ : P₁.Orth P₂) {g h : V ≃ₗ[K] V} (h1 : g P₁.e = h P₁.e)
    (h2 : g P₁.f = h P₁.f) (h3 : g P₂.e = h P₂.e) (h4 : g P₂.f = h P₂.f)
    (hW : ∀ x ∈ P₁.perp ⊓ P₂.perp, g x = h x) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have he₂ : P₂.e ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₂.ee, h₁₂.fe⟩
  have hf₂ : P₂.f ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₂.ef, h₁₂.ff⟩
  have hyP : P₁.proj v ∈ P₁.perp := P₁.proj_mem_perp v
  have hw : P₂.proj (P₁.proj v) ∈ P₁.perp ⊓ P₂.perp := by
    refine ⟨?_, P₂.proj_mem_perp _⟩
    rw [HypPair.proj]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hyP (Submodule.smul_mem _ _ he₂))
      (Submodule.smul_mem _ _ hf₂)
  have hv : v = polar Q v P₁.f • P₁.e + polar Q v P₁.e • P₁.f +
      (polar Q (P₁.proj v) P₂.f • P₂.e + polar Q (P₁.proj v) P₂.e • P₂.f +
        P₂.proj (P₁.proj v)) := by
    rw [← P₂.eq_add_proj (P₁.proj v)]
    exact P₁.eq_add_proj v
  rw [hv]
  simp only [map_add, map_smul, h1, h2, h3, h4, hW _ hw]

end TwoPairs

section Pairing

variable [CharP K 2]

theorem exists_anisotropic_perp {W : Submodule K V} (hW : PolarNondegOn Q W)
    (h3 : ∀ a b : V, ∃ x ∈ W, x ≠ 0 ∧ polar Q a x = 0 ∧ polar Q b x = 0) {a b : V}
    (ha : a ∈ W) (hb : b ∈ W) (hab : polar Q a b ≠ 0) :
    ∃ c ∈ W, Q c ≠ 0 ∧ polar Q a c = 0 ∧ polar Q b c = 0 := by
  obtain ⟨x, hxW, hx0, hax, hbx⟩ := h3 a b
  obtain ⟨y, hyW, hxy⟩ := hW.exists_polar_ne_zero hxW hx0
  set y' := y - (polar Q b y / polar Q a b) • a - (polar Q a y / polar Q a b) • b with hy'
  have hba : polar Q b a = polar Q a b := polar_comm Q b a
  have hy'W : y' ∈ W := W.sub_mem (W.sub_mem hyW (W.smul_mem _ ha)) (W.smul_mem _ hb)
  have hay' : polar Q a y' = 0 := by
    rw [hy', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_charTwo, mul_zero, sub_zero, div_mul_cancel₀ _ hab, sub_self]
  have hby' : polar Q b y' = 0 := by
    rw [hy', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_charTwo, mul_zero, sub_zero, hba, div_mul_cancel₀ _ hab, sub_self]
  have hxy' : polar Q x y' = polar Q x y := by
    rw [hy', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q x a, hax, polar_comm Q x b, hbx, mul_zero, mul_zero, sub_zero, sub_zero]
  by_cases hQx : Q x = 0
  · by_cases hQy : Q y' = 0
    · refine ⟨x + y', W.add_mem hxW hy'W, ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_add Q x y', hQx, hQy, zero_add, zero_add, hxy']
        exact hxy
      · rw [polar_add_right, hax, hay', add_zero]
      · rw [polar_add_right, hbx, hby', add_zero]
    · exact ⟨y', hy'W, hQy, hay', hby'⟩
  · exact ⟨x, hxW, hQx, hax, hbx⟩

end Pairing

theorem exists_ne_zero_perp_of_three_le [FiniteDimensional K V] {W : Submodule K V}
    (hW3 : 3 ≤ Module.finrank K W) (a b : V) :
    ∃ x ∈ W, x ≠ 0 ∧ polar Q a x = 0 ∧ polar Q b x = 0 := by
  let f : W →ₗ[K] K × K :=
    LinearMap.prod ((polarBilin Q a).comp W.subtype) ((polarBilin Q b).comp W.subtype)
  have hlt : Module.finrank K (K × K) < Module.finrank K W := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  have hfx := LinearMap.mem_ker.mp hx
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), congrArg Prod.fst hfx, congrArg Prod.snd hfx⟩

theorem three_le_finrank_of_hypPair [FiniteDimensional K V] {W : Submodule K V} (P : HypPair Q)
    (he : P.e ∈ W) (hf : P.f ∈ W) {x : V} (hx : x ∈ W) (hxP : x ∈ P.perp) (hx0 : x ≠ 0) :
    3 ≤ Module.finrank K W := by
  have hxe : polar Q x P.e = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.mp hxP).1
  have hxf : polar Q x P.f = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.mp hxP).2
  have hli : LinearIndependent K ![(⟨P.e, he⟩ : W), ⟨P.f, hf⟩, ⟨x, hx⟩] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • P.e + g 1 • P.f + g 2 • x = 0 := by
      have := congrArg Subtype.val hg
      simpa [Fin.sum_univ_three] using this
    have h0 : g 0 = 0 := by
      have := congrArg (fun v => polar Q v P.f) hg'
      simpa [polar_add_left, polar_smul_left, P.polar_ef, P.polar_ff, hxf] using this
    have h1 : g 1 = 0 := by
      have := congrArg (fun v => polar Q v P.e) hg'
      simpa [polar_add_left, polar_smul_left, P.polar_fe, P.polar_ee, hxe] using this
    have h2 : g 2 = 0 := by
      rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hg'
      exact (smul_eq_zero.mp hg').resolve_right hx0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  simpa using hli.fintype_card_le_finrank

section Centralizer

variable {P₁ P₂ : HypPair Q}

theorem mem_centralizer_of_fix {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : g P₁.e = P₁.e) (h3 : g P₂.e = P₂.e) :
    g ∈ centralizer {eichler Q P₁.e P₂.e} := by
  rw [mem_centralizer_singleton_iff]
  have h := eichler_conj hgO P₁.e P₂.e
  rw [h1, h3] at h
  calc g * eichler Q P₁.e P₂.e = g * eichler Q P₁.e P₂.e * g⁻¹ * g := by group
    _ = eichler Q P₁.e P₂.e * g := by rw [h]

theorem reflect_mem_centralizer {a : V} (ha : a ∈ P₁.perp ⊓ P₂.perp) :
    reflect Q a ∈ centralizer {eichler Q P₁.e P₂.e} :=
  mem_centralizer_of_fix (reflect_mem_orthogonalGroup Q a)
    (reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact (mem_perpTwo.mp ha).1.1))
    (reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact (mem_perpTwo.mp ha).2.1))

variable [CharP K 2]

theorem rootPairSub_le_ggOTwoPrime (h₁₂ : P₁.Orth P₂) :
    CFSG.SeitzReduction.OmegaPilot.rootPairSub Q P₁.e P₂.e ≤
      ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  have hC := CFSG.SeitzReduction.OmegaPilot.rootPairSub_le_centralizer P₁.Q_e P₂.Q_e h₁₂.ee
  have key : ∀ u, rootGroup Q u ≤ centralizer {eichler Q P₁.e P₂.e} →
      rootGroup Q u ≤ ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
    intro u hu g hg
    refine mem_ggOTwoPrime_of_mul_self ⟨hu hg, rootGroup_le_elementaryGroup Q u hg⟩ ?_
    obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
    exact eichler_mul_self u w
  exact sup_le
    (key _ ((CFSG.SeitzReduction.OmegaPilot.rootGroup_le_rootPairSub_left _ _).trans hC))
    (key _ ((CFSG.SeitzReduction.OmegaPilot.rootGroup_le_rootPairSub_right _ _).trans hC))

variable [Finite K] (hQ : (polarBilin Q).Nondegenerate) (h₁₂ : P₁.Orth P₂)

include hQ h₁₂ in
theorem reflect_mul_reflect_mem_elementaryGroup {a c : V} (ha : Q a ≠ 0) (hc : Q c ≠ 0) :
    reflect Q a * reflect Q c ∈ elementaryGroup Q := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q a / Q c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hs
    exact hs.elim ha hc
  refine CFSG.LieType.Universal.Spin.reflect_mul_reflect_mem_of_eq_sq_mul hQ h₁₂ hc hs0 ?_
  rw [pow_two, ← hs, div_mul_cancel₀ _ hc]

include hQ h₁₂ in
theorem reflect_mul_reflect_mem_ggOTwoPrime_of_polar {a c : V} (ha : a ∈ P₁.perp ⊓ P₂.perp)
    (hc : c ∈ P₁.perp ⊓ P₂.perp) (hQa : Q a ≠ 0) (hQc : Q c ≠ 0) (hac : polar Q a c = 0) :
    reflect Q a * reflect Q c ∈
      ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  refine mem_ggOTwoPrime_of_mul_self ⟨mul_mem (reflect_mem_centralizer ha)
    (reflect_mem_centralizer hc), reflect_mul_reflect_mem_elementaryGroup hQ h₁₂ hQa hQc⟩ ?_
  calc reflect Q a * reflect Q c * (reflect Q a * reflect Q c)
      = reflect Q a * (reflect Q c * reflect Q a) * reflect Q c := by group
    _ = 1 := by
      rw [← reflect_mul_reflect_comm hac, ← mul_assoc, reflect_mul_self, one_mul,
        reflect_mul_self]

include hQ h₁₂ in
theorem reflect_mul_reflect_mem_ggOTwoPrime [FiniteDimensional K V]
    (hW3 : 3 ≤ Module.finrank K (P₁.perp ⊓ P₂.perp : Submodule K V)) {a b : V}
    (ha : a ∈ P₁.perp ⊓ P₂.perp) (hb : b ∈ P₁.perp ⊓ P₂.perp) (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) :
    reflect Q a * reflect Q b ∈
      ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  by_cases hab : polar Q a b = 0
  · exact reflect_mul_reflect_mem_ggOTwoPrime_of_polar hQ h₁₂ ha hb hQa hQb hab
  have hWnd : PolarNondegOn Q (P₁.perp ⊓ P₂.perp) :=
    (HypPair.polarNondegOn_perp hQ P₁).inf_perp P₂ (HypPair.mem_perp.mpr ⟨h₁₂.ee, h₁₂.fe⟩)
      (HypPair.mem_perp.mpr ⟨h₁₂.ef, h₁₂.ff⟩)
  obtain ⟨c, hcW, hQc, hac, hbc⟩ :=
    exists_anisotropic_perp hWnd (exists_ne_zero_perp_of_three_le hW3) ha hb hab
  have e : reflect Q a * reflect Q b = reflect Q a * reflect Q c * (reflect Q c * reflect Q b) := by
    rw [mul_assoc, ← mul_assoc (reflect Q c), reflect_mul_self, one_mul]
  rw [e]
  exact mul_mem (reflect_mul_reflect_mem_ggOTwoPrime_of_polar hQ h₁₂ ha hcW hQa hQc hac)
    (reflect_mul_reflect_mem_ggOTwoPrime_of_polar hQ h₁₂ hcW hb hQc hQb
      (by rw [polar_comm]; exact hbc))

include hQ h₁₂ in
theorem evenSub_le_ggOTwoPrime [FiniteDimensional K V]
    (hW3 : 3 ≤ Module.finrank K (P₁.perp ⊓ P₂.perp : Submodule K V)) :
    evenSub Q (P₁.perp ⊓ P₂.perp) ≤
      ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  rw [evenSub, Subgroup.closure_le]
  rintro g (⟨u, hu, w, hw, rfl⟩ | ⟨a, ha, b, hb, hQa, hQb, rfl⟩)
  · refine mem_ggOTwoPrime_of_mul_self ⟨?_, eichler_mem_elementaryGroup Q u w⟩
      (eichler_mul_self u w)
    exact mem_centralizer_of_fix (eichler_mem_orthogonalGroup Q u w)
      (eichler_apply_of_polar_eq_zero (mem_perpTwo.mp hu).1.1 (mem_perpTwo.mp hw).1.1)
      (eichler_apply_of_polar_eq_zero (mem_perpTwo.mp hu).2.1 (mem_perpTwo.mp hw).2.1)
  · exact reflect_mul_reflect_mem_ggOTwoPrime hQ h₁₂ hW3 ha hb hQa hQb

end Centralizer

@[expose] def restrictPair {W : Submodule K V} (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    HypPair (Q.restrict W) where
  e := ⟨P.e, he⟩
  f := ⟨P.f, hf⟩
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := by rw [polar_restrict]; exact P.polar_ef

theorem orth_restrictPair {W : Submodule K V} {P P' : HypPair Q} (h : P.Orth P') (he : P.e ∈ W)
    (hf : P.f ∈ W) (he' : P'.e ∈ W) (hf' : P'.f ∈ W) :
    (restrictPair P he hf).Orth (restrictPair P' he' hf') where
  ee := by rw [polar_restrict]; exact h.ee
  ef := by rw [polar_restrict]; exact h.ef
  fe := by rw [polar_restrict]; exact h.fe
  ff := by rw [polar_restrict]; exact h.ff

section Main

variable [Finite K] [CharP K 2] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
  {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)

include hQ h₁₂ in
theorem mem_ggOTwoPrime_of_fix (hE : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hW3 : 3 ≤ Module.finrank K (P₁.perp ⊓ P₂.perp : Submodule K V)) {P : ℕ → HypPair Q}
    {r : ℕ} (hr : 1 ≤ r)
    (hPW : ∀ m, (P m).e ∈ P₁.perp ⊓ P₂.perp ∧ (P m).f ∈ P₁.perp ⊓ P₂.perp)
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, x ∈ (P m).perp) → Q x = 0 → x = 0)
    (hA' : ∀ x ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, x ∈ (P m).perp) → x ≠ 0 →
      ∀ y ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, y ∈ (P m).perp) → polar Q x y = 0 →
        ∃ c : K, y = c • x)
    {g : V ≃ₗ[K] V} (hgE : g ∈ elementaryGroup Q) (h1 : g P₁.e = P₁.e) (h2 : g P₁.f = P₁.f)
    (h3 : g P₂.e = P₂.e) (h4 : g P₂.f = P₂.f) :
    g ∈ ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  set W := P₁.perp ⊓ P₂.perp with hWdef
  have hgO := elementaryGroup_le_orthogonalGroup Q hgE
  have hWnd : PolarNondegOn Q W :=
    (HypPair.polarNondegOn_perp hQ P₁).inf_perp P₂ (HypPair.mem_perp.mpr ⟨h₁₂.ee, h₁₂.fe⟩)
      (HypPair.mem_perp.mpr ⟨h₁₂.ef, h₁₂.ff⟩)
  let P' : ℕ → HypPair (Q.restrict W) := fun m => restrictPair (P m) (hPW m).1 (hPW m).2
  have hP' : ∀ i j, i < r → j < r → i ≠ j → (P' i).Orth (P' j) := fun i j hi hj hij =>
    orth_restrictPair (hP i j hi hj hij) _ _ _ _
  have htail : ∀ x : W, x ∈ tailSpace P' r ↔ ∀ m < r, (x : V) ∈ (P m).perp := by
    intro x
    rw [mem_tailSpace]
    refine forall₂_congr fun m _ => ?_
    rw [HypPair.mem_perp, polar_restrict, polar_restrict]
    rfl
  have hAR : ∀ x ∈ tailSpace P' r, Q.restrict W x = 0 → x = 0 := fun x hx hQx =>
    Subtype.ext (hA x x.2 ((htail x).mp hx) hQx)
  have hA'R : ∀ x ∈ tailSpace P' r, x ≠ 0 → ∀ y ∈ tailSpace P' r,
      polar (Q.restrict W) x y = 0 → ∃ c : K, y = c • x := by
    intro x hx hx0 y hy hxy
    obtain ⟨c, hc⟩ := hA' x x.2 ((htail x).mp hx) (fun h => hx0 (Subtype.ext h)) y y.2
      ((htail y).mp hy) (by rwa [polar_restrict] at hxy)
    exact ⟨c, Subtype.ext hc⟩
  have hgW : ∀ x ∈ W, g x ∈ W := fun x hx => apply_mem_perpTwo hgO h1 h2 h3 h4 hx
  have hgW' : ∀ x ∈ W, g.symm x ∈ W := fun x hx =>
    apply_mem_perpTwo (inv_mem hgO) (inv_apply_eq_of_apply_eq h1) (inv_apply_eq_of_apply_eq h2)
      (inv_apply_eq_of_apply_eq h3) (inv_apply_eq_of_apply_eq h4) hx
  set g' := CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv W g hgW hgW' with hg'
  have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    exact map_of_mem hgO x
  have hcl := orthogonalGroup_le_closure_of_two_eq_zero hP'
    (nondegenerate_polarBilin_restrict hWnd) CharTwo.two_eq_zero hAR hA'R hr hg'O
  obtain ⟨g₀, hg₀, hg₀x, hg₀z⟩ := exists_extend_of_mem_closure hcl
  have hz : ∀ v, (∀ x ∈ W, polar Q v x = 0) → g v = v → g₀ v = g v := fun v hv hgv => by
    rw [hgv]
    exact hg₀z v hv
  have heq : g₀ = g := eq_of_eq_on_perpTwo h₁₂
    (hz _ (fun x hx => (mem_perpTwo.mp hx).1.1) h1) (hz _ (fun x hx => (mem_perpTwo.mp hx).1.2) h2)
    (hz _ (fun x hx => (mem_perpTwo.mp hx).2.1) h3) (hz _ (fun x hx => (mem_perpTwo.mp hx).2.2) h4)
    (fun x hx => hg₀x ⟨x, hx⟩)
  rw [← heq]
  rcases mem_evenSub_or_of_mem_closure hg₀ with h | ⟨a, ha, hQa, h⟩
  · exact evenSub_le_ggOTwoPrime hQ h₁₂ hW3 h
  · exfalso
    have hN : g₀ * reflect Q a ∈ elementaryGroup Q :=
      (ggOTwoPrime_le _ (evenSub_le_ggOTwoPrime hQ h₁₂ hW3 h)).2
    have hrE : reflect Q a ∈ omegaGroup Q hQ := by
      have e : reflect Q a = g₀⁻¹ * (g₀ * reflect Q a) := by group
      rw [e]
      exact mul_mem (inv_mem (hE (by rw [heq]; exact hgE))) (hE hN)
    let _ : Invertible (Q a) := invertibleOfNonzero hQa
    have hev := (mem_omegaGroup.mp hrE).2
    rw [reflect_eq_reflection, finrank_commSpace_reflection hQ a] at hev
    exact Nat.not_even_one hev

include hQ h₁₂ in
theorem centralizer_le_ggOTwoPrime (hE : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hW3 : 3 ≤ Module.finrank K (P₁.perp ⊓ P₂.perp : Submodule K V)) {P : ℕ → HypPair Q}
    {r : ℕ} (hr : 1 ≤ r)
    (hPW : ∀ m, (P m).e ∈ P₁.perp ⊓ P₂.perp ∧ (P m).f ∈ P₁.perp ⊓ P₂.perp)
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, x ∈ (P m).perp) → Q x = 0 → x = 0)
    (hA' : ∀ x ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, x ∈ (P m).perp) → x ≠ 0 →
      ∀ y ∈ P₁.perp ⊓ P₂.perp, (∀ m < r, y ∈ (P m).perp) → polar Q x y = 0 →
        ∃ c : K, y = c • x) :
    centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q ≤
      ggOTwoPrime (centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q) := by
  rintro g ⟨hgC, hgE⟩
  obtain ⟨m, q, g'', rfl, hm, hq, hg''E, h1, h2, h3, h4⟩ :=
    CFSG.SeitzReduction.OmegaPilot.exists_factor_of_commute h₁₂ (elementaryGroup Q)
      (elementaryGroup_le_orthogonalGroup Q) (eichler_mem_elementaryGroup Q) hgE
      (mem_centralizer_singleton_iff.mp hgC)
  exact mul_mem (mul_mem (rootPairSub_le_ggOTwoPrime h₁₂ hm.1.1)
    (rootPairSub_le_ggOTwoPrime h₁₂ hq.1.2))
    (mem_ggOTwoPrime_of_fix hQ h₁₂ hE hW3 hr hPW hP hA hA' hg''E h1 h2 h3 h4)

end Main

end RootCentOmega

end CFSG.StandardType

module

public import CFSG.RankThree.PartOne.LIT.McSlA
public import CFSG.RankThree.PartOne.LIT.McSlB

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

theorem IsFrame.ext_dual {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {f g : Module.Dual (ZMod p) V} (hU : ∀ y ∈ U, f y = g y) (hL : ∀ l ∈ L, f l = g l) :
    f = g :=
  LinearMap.ext_on_codisjoint hF.1.codisjoint hU hL

theorem IsFrame.isAplus_comp_projL {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) {a : V}
    (haU : a ∈ U) (ha0 : a ≠ 0) {g : Module.Dual (ZMod p) V} (hg : TrIn H a g) :
    IsAplus H U (g ∘ₗ hF.projL) := by
  have hvanU : ∀ y ∈ U, (g ∘ₗ hF.projL) y = 0 := fun y hy => by
    rw [LinearMap.comp_apply, hF.projL_of_mem_U hy, map_zero]
  refine ⟨hvanU, fun u hu => ?_⟩
  have hgU : TrIn H a (g ∘ₗ hF.projU) := by
    refine hF.2.2.2 a haU _ (fun l hl => ?_) ?_
    · rw [LinearMap.comp_apply, hF.projU_of_mem_L hl, map_zero]
    · rw [LinearMap.comp_apply, hF.projU_of_mem haU]
      exact hg.1
  have hsub : g ∘ₗ hF.projL = g - g ∘ₗ hF.projU := LinearMap.ext fun z => by
    have := congrArg g (hF.projU_add_projL z)
    rw [map_add] at this
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← this]
    abel
  exact hF.trIn_center_of_vanish haU hu ha0 hvanU (by rw [hsub]; exact hg.sub hgU)

private theorem exists_ne_zero_of_vanish_on_L {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {f : Module.Dual (ZMod p) V} (hf0 : f ≠ 0) (hfL : ∀ l ∈ L, f l = 0) :
    ∃ y ∈ U, f y ≠ 0 := by
  by_contra hno
  push Not at hno
  exact hf0 (hF.ext_dual H (fun y hy => by rw [hno y hy, LinearMap.zero_apply])
    (fun l hl => by rw [hfL l hl, LinearMap.zero_apply]))

theorem exists_isAplus_of_two_axes {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) {a : V}
    (haU : a ∈ U) (ha0 : a ≠ 0) {f f' : Module.Dual (ZMod p) V} (hf0 : f ≠ 0) (hf : TrIn H a f)
    (hf' : TrIn H a f') (hind : ∀ t : ZMod p, f' ≠ t • f) :
    ∃ ψ, IsAplus H U ψ ∧ ψ ≠ 0 := by
  have key : ∀ g : Module.Dual (ZMod p) V, TrIn H a g → ¬ (∀ l ∈ L, g l = 0) →
      ∃ ψ, IsAplus H U ψ ∧ ψ ≠ 0 := by
    intro g hg hgL
    refine ⟨g ∘ₗ hF.projL, hF.isAplus_comp_projL H haU ha0 hg, fun h0 => hgL fun l hl => ?_⟩
    have := LinearMap.congr_fun h0 l
    rwa [LinearMap.comp_apply, hF.projL_of_mem hl, LinearMap.zero_apply] at this
  by_cases hfL : ∀ l ∈ L, f l = 0
  · by_cases hf'L : ∀ l ∈ L, f' l = 0
    · exfalso
      obtain ⟨t, ht⟩ := eq_smul_of_vanish_on_plane hF.2.1 haU ha0 hf'.1 hf.1
        (exists_ne_zero_of_vanish_on_L H hF hf0 hfL)
      refine hind t (hF.ext_dual H (fun y hy => ?_) (fun l hl => ?_))
      · rw [ht y hy, LinearMap.smul_apply, smul_eq_mul]
      · rw [hf'L l hl, LinearMap.smul_apply, hfL l hl, smul_zero]
    · exact key f' hf' hf'L
  · exact key f hf hfL

theorem eq_comb_of_vanish_on_U {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {ψ lam χ : Module.Dual (ZMod p) V} (hψU : ∀ y ∈ U, ψ y = 0) (hlamU : ∀ y ∈ U, lam y = 0)
    (hχU : ∀ y ∈ U, χ y = 0) (hψ0 : ψ ≠ 0) (hind : ∀ t : ZMod p, lam ≠ t • ψ) :
    ∃ α β : ZMod p, χ = α • ψ + β • lam := by
  obtain ⟨m, hmL, hm0, hψm⟩ := exists_ne_zero_ker_of_finrank_two hF.2.2.1 ψ
  have hψL : ∃ y ∈ L, ψ y ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hψ0 (hF.ext_dual H (fun y hy => ?_) (fun l hl => ?_))
    · rw [hψU y hy, LinearMap.zero_apply]
    · rw [hno l hl, LinearMap.zero_apply]
  have hlamm : lam m ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := eq_smul_of_vanish_on_plane hF.2.2.1 hmL hm0 h0 hψm hψL
    refine hind t (hF.ext_dual H (fun y hy => ?_) (fun l hl => ?_))
    · rw [hlamU y hy, LinearMap.smul_apply, hψU y hy, smul_zero]
    · rw [LinearMap.smul_apply, smul_eq_mul]
      exact ht l hl
  obtain ⟨t, ht⟩ := eq_smul_of_vanish_on_plane hF.2.2.1 hmL hm0
    (f := χ - (χ m / lam m) • lam) (by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hlamm,
        sub_self]) hψm hψL
  refine ⟨t, χ m / lam m, hF.ext_dual H (fun y hy => ?_) (fun l hl => ?_)⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, hχU y hy, hψU y hy, hlamU y hy,
      smul_zero, add_zero]
  · have := ht l hl
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at this
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination this

theorem fullCenter_of_aplus_pair {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {ψ lam : Module.Dual (ZMod p) V} (hψ : IsAplus H U ψ) (hlam : IsAplus H U lam)
    (hψ0 : ψ ≠ 0) (hind : ∀ t : ZMod p, lam ≠ t • ψ) {u : V} (hu : u ∈ U) (hu0 : u ≠ 0) :
    FullCenter H u := by
  refine ⟨hu0, fun f hfu => ?_⟩
  have h1 : TrIn H u (f ∘ₗ hF.projU) := by
    refine hF.2.2.2 u hu _ (fun l hl => ?_) ?_
    · rw [LinearMap.comp_apply, hF.projU_of_mem_L hl, map_zero]
    · rw [LinearMap.comp_apply, hF.projU_of_mem hu]
      exact hfu
  obtain ⟨α, β, hab⟩ := eq_comb_of_vanish_on_U H hF (χ := f ∘ₗ hF.projL) hψ.1 hlam.1
    (fun y hy => by rw [LinearMap.comp_apply, hF.projL_of_mem_U hy, map_zero]) hψ0 hind
  have h2 : TrIn H u (f ∘ₗ hF.projL) := by
    rw [hab]
    exact ((hψ.2 u hu).smul α).add ((hlam.2 u hu).smul β)
  have hsum : f = f ∘ₗ hF.projU + f ∘ₗ hF.projL := LinearMap.ext fun z => by
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add,
      hF.projU_add_projL]
  rw [hsum]
  exact h1.add h2

theorem exists_fullCenter_of_not_hasUniqueAxes [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hnu : ¬ HasUniqueAxes H) : ∃ c, FullCenter H c := by
  unfold HasUniqueAxes at hnu
  push Not at hnu
  obtain ⟨a, f, f', ha, hf, hf', hf0, hind⟩ := hnu
  obtain ⟨b, g, φ, hφ, hg, hφb, hga⟩ := exists_partner H hirr hgen ha hf0 hf
  have hF := isFrame_of_reciprocal H hdim hφ hg hφb hga
  have haU : a ∈ Submodule.span (ZMod p) {a, b} := Submodule.subset_span (Set.mem_insert _ _)
  obtain ⟨ψ, hψ, hψ0⟩ := exists_isAplus_of_two_axes H hF haU ha hf0 hf hf' hind
  by_cases hone : ∀ lam, IsAplus H (Submodule.span (ZMod p) {a, b}) lam → ∃ t : ZMod p, lam = t • ψ
  · obtain ⟨l, hl, hψl⟩ := exists_isAminus_of_isAplus H hirr hgen hF hψ hψ0 hone
    exact exists_fullCenter_of_aplus_aminus H hdim hirr hgen hF hψ.1 hψ.2 hl.1 hl.2 hψl
  · push Not at hone
    obtain ⟨lam, hlam, hind'⟩ := hone
    exact ⟨a, fullCenter_of_aplus_pair H hF hψ hlam hψ0 hind' haU ha⟩

end CFSG.RankThree.PartOne.LIT

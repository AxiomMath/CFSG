module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16e_star_equiv_aux {M A₁ A₂ : Type*} [Group M] [Group A₁] [Group A₂] (f₁ : M →* A₁)
    (f₂ : M →* A₂) (h : f₁.ker = f₂.ker) :
    ∃ ρ : f₁.range ≃* f₂.range, ∀ (m : M) (h₁ : f₁ m ∈ f₁.range) (h₂ : f₂ m ∈ f₂.range),
      ρ ⟨f₁ m, h₁⟩ = ⟨f₂ m, h₂⟩ := by
  refine ⟨((QuotientGroup.quotientKerEquivRange f₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans (QuotientGroup.quotientKerEquivRange f₂), ?_⟩
  intro m h₁ h₂
  have : (QuotientGroup.quotientKerEquivRange f₁).symm ⟨f₁ m, h₁⟩ = (m : M ⧸ f₁.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MulEquiv.trans_apply, this]
  rfl

variable {G : Type} [Group G] [Finite G]

theorem s16e_star_equiv (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    ∃ ρ : ↥(Mbar D.M V₀ V hV) ≃* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
      (∀ (x : G) (hx : x ∈ D.M) (h₀ : x ∈ stabTil V₀ V)
        (h₁ : x ∈ stabTil (v1Sub D.M V₀ V hV L) V),
        ρ ⟨actTil V₀ V hV ⟨x, h₀⟩, actTil_mem_barSub V₀ V hV hx h₀⟩ =
          ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, h₁⟩,
            actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hx h₁⟩) ∧
      ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map ρ.toMonoidHom =
        (lStar D.M V₀ V hV L).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h.hyp125.pairFacts.le_normalizer₀
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h.hyp125 hV
  have hs₀ : D.M ≤ stabTil V₀ V := le_stabTil hM hM₀
  have hs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁
  have hker : (barHom V₀ V hV hs₀).ker = (barHom (v1Sub D.M V₀ V hV L) V hV hs₁).ker := by
    rw [ker_barHom V₀ V hV hM hs₀, ker_barHom (v1Sub D.M V₀ V hV L) V hV hM hs₁,
      fifteen_two_cent D h1217 h hV]
  obtain ⟨ρ₀, hρ₀⟩ := s16e_star_equiv_aux _ _ hker
  have hr₀ : (barHom V₀ V hV hs₀).range = Mbar D.M V₀ V hV := range_barHom V₀ V hV hs₀
  have hr₁ : (barHom (v1Sub D.M V₀ V hV L) V hV hs₁).range =
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV := range_barHom _ V hV hs₁
  let ρ : ↥(Mbar D.M V₀ V hV) ≃* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    ((MulEquiv.subgroupCongr hr₀.symm).trans ρ₀).trans (MulEquiv.subgroupCongr hr₁)
  have hcompat : ∀ (x : G) (hx : x ∈ D.M) (h₀ : x ∈ stabTil V₀ V)
      (h₁ : x ∈ stabTil (v1Sub D.M V₀ V hV L) V),
      ρ ⟨actTil V₀ V hV ⟨x, h₀⟩, actTil_mem_barSub V₀ V hV hx h₀⟩ =
        ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, h₁⟩,
          actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hx h₁⟩ := by
    intro x hx h₀ h₁
    have h := hρ₀ ⟨x, hx⟩ ⟨⟨x, hx⟩, rfl⟩ ⟨⟨x, hx⟩, rfl⟩
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  refine ⟨ρ, hcompat, ?_⟩
  ext ψ
  constructor
  · intro hψ
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hψ
    obtain ⟨g, hgL, hgφ⟩ := (mem_barSub V₀ V hV L (φ : MulAut (Vtil V₀ V hV))).1
      (Subgroup.mem_subgroupOf.1 hφ)
    have hgM : (g : G) ∈ D.M := h.le hgL
    have h₁ : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := hs₁ hgM
    have hφeq : φ = ⟨actTil V₀ V hV ⟨(g : G), g.2⟩, actTil_mem_barSub V₀ V hV hgM g.2⟩ :=
      Subtype.ext hgφ.symm
    have hρφ : ρ φ = ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩,
        actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hgM h₁⟩ := by
      rw [hφeq]
      exact hcompat (g : G) hgM g.2 h₁
    change ρ φ ∈ (lStar D.M V₀ V hV L).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
    rw [Subgroup.mem_subgroupOf, hρφ]
    exact (mem_barSub _ V hV L _).2 ⟨⟨(g : G), h₁⟩, hgL, rfl⟩
  · intro hψ
    obtain ⟨g, hgL, hgψ⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L
      (ψ : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))).1 (Subgroup.mem_subgroupOf.1 hψ)
    have hgM : (g : G) ∈ D.M := h.le hgL
    have h₀ : (g : G) ∈ stabTil V₀ V := hs₀ hgM
    have hmem : actTil V₀ V hV ⟨(g : G), h₀⟩ ∈ lBar V₀ V hV L :=
      (mem_barSub V₀ V hV L _).2 ⟨⟨(g : G), h₀⟩, hgL, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨actTil V₀ V hV ⟨(g : G), h₀⟩,
      actTil_mem_barSub V₀ V hV hgM h₀⟩, Subgroup.mem_subgroupOf.2 hmem, ?_⟩
    apply Subtype.ext
    have := hcompat (g : G) hgM h₀ g.2
    have h2 := congrArg Subtype.val this
    rw [← hgψ]
    exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

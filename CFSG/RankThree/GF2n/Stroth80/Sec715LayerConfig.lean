module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

@[expose] def IsLayerConfigC (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) :
    Prop :=
  ∃ (M₃ M₄ : Submodule K (wvQ hS t)) (N₄ N₃ : Submodule K ↥(deltaSub hS t)),
    IsCompl M₃ M₄ ∧ IsCompl N₄ N₃ ∧ IsIrrSub (deltaAct hS ht) N₄ ∧
      IsIrrSub (deltaAct hS ht) N₃ ∧
    (∀ T : ↥(deltaSub hS t) →ₗ[K] ↥(deltaSub hS t),
      (∀ x f, T (deltaAct hS ht x f) = deltaAct hS ht x (T f)) →
        (∀ f ∈ N₄, T f ∈ N₄) ∧ ∀ f ∈ N₃, T f ∈ N₃) ∧
    (∀ w w' : ↥(S714.wsub hS t), (Submodule.Quotient.mk w : wvQ hS t) ∈ M₃ →
      (Submodule.Quotient.mk w' : wvQ hS t) ∈ M₄ → M₀.B (w : M₀.E) (w' : M₀.E) = 0) ∧
    (∀ (w : ↥(S714.wsub hS t)) (f : ↥(deltaSub hS t)),
      ((Submodule.Quotient.mk w : wvQ hS t) ∈ M₃ → f ∈ N₃ →
        (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w = 0) ∧
      ((Submodule.Quotient.mk w : wvQ hS t) ∈ M₄ → f ∈ N₄ →
        (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w = 0)) ∧
    (∀ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)) (h : Mbar M Q) (hh : h ∈ bar M Q (hc.CN t)),
      (⟨S714.delta hS t g (S714.mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ :
        ↥(deltaSub hS t)) ∈ N₄ →
      (⟨S714.delta hS t h (S714.mem_bar_H0_of_CN hh), delta_mem_deltaSub hS hh⟩ :
        ↥(deltaSub hS t)) ∈ N₃ → g * h = h * g) ∧
    ∀ f ∈ N₄, ∀ f' ∈ N₃, f ≠ 0 → f' ≠ 0 →
      5 ≤ Module.finrank K
        (LinearMap.range ((f + f' : ↥(deltaSub hS t)) : ↥(S714.wsub hS t) →ₗ[K] M₀.E))

end CFSG.RankThree.GF2n.Stroth80.S715L

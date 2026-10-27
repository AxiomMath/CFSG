module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrAt
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBNbr
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2NbrDatum.IsE6 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) : Prop :=
  ∃ e : Fin 6 ≃ N.Λ, N.coxeter = CoxeterMatrix.E₆.reindex e

@[expose] def GGQ2NbrDatum.IsD6Fork {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) (b : N.Λ) : Prop :=
  ∃ e : Fin 6 ≃ N.Λ, N.coxeter = (ggCoxeterMatrixD 6).reindex e ∧ (b = e 4 ∨ b = e 5)

@[expose] def GGQ2NbrDatum.Pos {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) : Prop :=
  LinearIndependent (ZMod p) N.coroot ∨ finrank (ZMod p) N.V = Fintype.card N.Λ + 1

@[expose] def GGQ2NbrDatum.NormAt {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) (y : G) : Prop :=
  ∀ u : ↥Bs, (u : G) = y →
    (∀ v : N.V, (∀ g ∈ (ggAutomizer K Bs).map (ggLin (p := p) N.model), g v = v) ↔
      v ∈ Submodule.span (ZMod p) {N.model (Additive.ofMul u)}) →
    N.model (Additive.ofMul u) ∉ Submodule.span (ZMod p) (Set.range N.coroot) →
    ∀ φ ∈ ggAutomizer ⊤ Bs,
      ggLin (p := p) N.model φ (N.model (Additive.ofMul u)) ∈
        Submodule.span (ZMod p) {N.model (Additive.ofMul u)} →
      ∃ (π : N.Λ ≃ N.Λ) (μ : N.Λ → ZMod p) (c : ZMod p), c ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
        (∀ i j, μ i * (N.cartan i j : ZMod p) = μ j * (N.cartan (π i) (π j) : ZMod p)) ∧
        ∃ w ∈ (ggAutomizer K Bs).map (ggLin (p := p) N.model), ∀ i : N.Λ,
          ggLin (p := p) N.model φ (N.coroot i) = c • μ i • w (N.coroot (π i))

abbrev GGQ2PosSel : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (Bs : Subgroup G) (y : G)
    (J K : Subgroup G), Prop

@[expose] def GGQ2SelE6 : GGQ2PosSel := fun _ _ _ p _ Bs _ _ K =>
  ∃ N : GGQ2NbrDatum p Bs K, N.IsE6 ∧ N.Pos

@[expose] def GGQ2SelD6 : GGQ2PosSel := fun _ _ _ p _ Bs y J K =>
  ∃ (N : GGQ2NbrDatum p Bs K) (b : N.Λ), N.IsD6Fork b ∧
    ggAutomizer J Bs = Subgroup.closure (N.simple '' {k | k ≠ b}) ∧ N.Pos ∧ N.NormAt y

@[expose] def GGQ2SelRest : GGQ2PosSel := fun G _ _ p _ Bs y J K =>
  ¬ GGQ2SelD6 G p Bs y J K ∧ ¬ GGQ2SelE6 G p Bs y J K

@[expose] def GGQ2GammaNbrPosInLOn (S : GGQ2PosSel) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    S G p Bs y J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2_posInL_of_cells (hr : GGQ2GammaNbrPosInLOn GGQ2SelRest)
    (hd : GGQ2GammaNbrPosInLOn GGQ2SelD6) (he : GGQ2GammaNbrPosInLOn GGQ2SelE6) :
    GGQ2GammaNbrPosAt GGQ2PosInL := by
  intro G _ _ p B Bs x L D J hS hp hI hx _ y K hnb hnr hM u hu
  by_cases h6 : GGQ2SelD6 G p Bs y J K
  · exact hd hS hp hI hx hnb hnr hM h6 hu
  · by_cases hE : GGQ2SelE6 G p Bs y J K
    · exact he hS hp hI hx hnb hnr hM hE hu
    · exact hr hS hp hI hx hnb hnr hM ⟨h6, hE⟩ hu

end CFSG.StandardType

end

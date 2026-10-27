module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S4Stmt
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Notation

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def Star (α α' : Vtx X) : Prop :=
  IsCritical X α α' ∧ Vv X α ≤ Qv X (geo X α' α 2)

@[expose] def critR0 (α α' : Vtx X) : Subgroup X.Universal := ⁅Vv X α, ZM X α'⁆

end Notation

section PUNotation

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] noncomputable def Wnab (α ρ : Vtx (puAmalgam hTM)) :
    Subgroup (puAmalgam hTM).Universal :=
  ⨆ μ ∈ {μ | (puAmalgam hTM).treeGraph.Adj ρ μ ∧ α ∈ nablaSet hTM L μ}, Vv (puAmalgam hTM) μ

@[expose] def Concl431A (q : ℕ) (α α' : Vtx (puAmalgam hTM)) : Prop :=
  critR0 (puAmalgam hTM) α α' = Usup (puAmalgam hTM) α' (geo (puAmalgam hTM) α' α 1) ∧
    Nat.card ↥(critR0 (puAmalgam hTM) α α') = q ^ 2 ∧
    Nat.card ↥(critR (puAmalgam hTM) α α') = q ∧
    IsC1 hTM L q α (Vv (puAmalgam hTM) α) (ZM (puAmalgam hTM) α) ∧
    (∀ δ ∈ nablaSet hTM L α,
      Vcirc hTM L α ≤ conjCl (stab (puAmalgam hTM) α) (ZM (puAmalgam hTM) δ)) ∧
    6 ≤ critDist (puAmalgam hTM)

@[expose] def Concl431B (q : ℕ) (α α' : Vtx (puAmalgam hTM)) : Prop :=
  q ^ 2 ≤ Nat.card ↥⁅Vv (puAmalgam hTM) α, Vcirc hTM L (geo (puAmalgam hTM) α' α 2)⁆ ∧
    q ^ 2 ≤ Nat.card ↥(Hloc hTM L α) ∧
    ∀ δ ∈ nablaSet hTM L α, ⁅ZM (puAmalgam hTM) δ, Qv (puAmalgam hTM) α⁆ =
      Usup (puAmalgam hTM) δ (geo (puAmalgam hTM) α δ 1)

@[expose] def Concl432 (α : Vtx (puAmalgam hTM)) : Prop :=
  ⁅Vv (puAmalgam hTM) α, Qv (puAmalgam hTM) α⁆ ≤ Dloc hTM L α ∧
    ∀ δ ∈ nablaSet hTM L α,
      Hloc hTM L α = ⁅ZM (puAmalgam hTM) δ, Qv (puAmalgam hTM) α⁆ ∧
        ⁅ZM (puAmalgam hTM) δ, Qv (puAmalgam hTM) α⁆ =
          Usup (puAmalgam hTM) δ (geo (puAmalgam hTM) α δ 1)

@[expose] def Concl434 : Prop :=
  ∀ β δ ℓ : Vtx (puAmalgam hTM), ¬ IsMVtx (puAmalgam hTM) β →
    (puAmalgam hTM).treeGraph.Adj β δ → (puAmalgam hTM).treeGraph.Adj β ℓ →
    ¬ Uloc hTM L δ ⊓ ZM (puAmalgam hTM) ℓ ≤ stabCenter (puAmalgam hTM) ℓ →
    ZM (puAmalgam hTM) δ = ZM (puAmalgam hTM) ℓ

@[expose] def Concl436 (α α' : Vtx (puAmalgam hTM)) : Prop :=
  ¬ critR0 (puAmalgam hTM) α α' ≤ stabCenter (puAmalgam hTM) (geo (puAmalgam hTM) α' α 4) →
    geo (puAmalgam hTM) α' α 4 ∈ nablaSet hTM L (geo (puAmalgam hTM) α' α 2) ∧
      ∀ ρ, (puAmalgam hTM).treeGraph.Adj α ρ →
        Gab (puAmalgam hTM) α ρ ⊔ ZM (puAmalgam hTM) α' = stab (puAmalgam hTM) α →
        Wnab hTM L α ρ ≤ Qv (puAmalgam hTM) (geo (puAmalgam hTM) α' α 4)

end PUNotation

section Steps

@[expose] def Hyp40 {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
    {F : Type} [Field F] [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  PUMin M T L ∧ 2 < critDist (puAmalgam h.le) ∧ IsSL3FullVia M T L φ

@[expose] def S4CFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ μ δ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ δ →
      ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ →
      (ZM (puAmalgam h.le) δ).relIndex
          (⁅Vv (puAmalgam h.le) δ, ZM (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) δ) ≤
        Fintype.card F →
      IsC1 h.le L (Fintype.card F) δ (Vv (puAmalgam h.le) δ) (ZM (puAmalgam h.le) δ)

@[expose] def S4CFFc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ μ δ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ δ →
      ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ →
      ∀ N : Subgroup (puAmalgam h.le).Universal, ZM (puAmalgam h.le) δ ≤ N →
        N ≤ Vv (puAmalgam h.le) δ → ⁅N, ZM (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) δ →
        N.relIndex (Vv (puAmalgam h.le) δ) ≤ Fintype.card F →
        IsC1 h.le L (Fintype.card F) δ (Vv (puAmalgam h.le) δ) (ZM (puAmalgam h.le) δ)

@[expose] def S431A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' →
      Concl431A h.le L (Fintype.card F) α α'

@[expose] def S431B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' →
      Concl431B h.le L (Fintype.card F) α α'

@[expose] def S432 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' → Concl432 h.le L α

@[expose] def S43b4Ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    critDist (puAmalgam h.le) = 4 → ∀ α α' : Vtx (puAmalgam h.le), Star (puAmalgam h.le) α α' →
      ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α

@[expose] def S43b4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    critDist (puAmalgam h.le) = 4 → ∀ α α' : Vtx (puAmalgam h.le), ¬ Star (puAmalgam h.le) α α'

@[expose] def S43b6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) → ∀ α α' : Vtx (puAmalgam h.le), ¬ Star (puAmalgam h.le) α α'

@[expose] def S43End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    ∀ α α' : Vtx (puAmalgam h.le), ¬ Star (puAmalgam h.le) α α'

end Steps

end CFSG.Quasithin.MS93.S4A

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s43_of (hEnd : S4A.S43End) : S43 := by
  intro G _ _ M T L h hmin hb hfull α α' hc hle
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  exact hEnd G M T L h F inferInstance inferInstance φ ⟨hmin, hb, hφ⟩ α α' ⟨hc, hle⟩

theorem S4A.s43End_of_parts (h4 : S4A.S43b4) (h6 : S4A.S43b6) : S4A.S43End := by
  intro G _ _ M T L h F _ _ φ hH α α'
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hb := hH.2.1
  by_cases hb4 : critDist (puAmalgam h.le) = 4
  · exact h4 G M T L h F inferInstance inferInstance φ hH hb4 α α'
  · exact h6 G M T L h F inferInstance inferInstance φ hH (by omega) α α'

theorem s43_of_parts (h4 : S4A.S43b4) (h6 : S4A.S43b6) : S43 :=
  s43_of (S4A.s43End_of_parts h4 h6)

end CFSG.Quasithin.MS93

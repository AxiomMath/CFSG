module

public import CFSG.Quasithin.MS93.Sec2Two

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93
open scoped commutatorElement

section Module

universe w

variable {U₀ : Type w} [Group U₀]

@[expose] def NatHyp (G₀ L Q : Subgroup U₀) : Prop :=
  ∀ (Y : Type w) [CommGroup Y] [Finite Y], (∀ y : Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 6 →
    ∀ ρ : ↥G₀ →* MulAut Y, (∀ q : ↥G₀, (q : U₀) ∈ Q → ρ q = 1) →
      (∃ l : ↥G₀, (l : U₀) ∈ L ∧ ρ l ≠ 1) →
        (∀ W : Subgroup Y, (∀ l : ↥G₀, (l : U₀) ∈ L → ∀ w ∈ W, ρ l w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∃ y₀ : Y, y₀ ≠ 1 ∧ (Subgroup.closure {x | ∃ l : ↥G₀, (l : U₀) ∈ L ∧ ρ l y₀ = y₀ ∧
          ∃ y : Y, x = ρ l y * y⁻¹}).index ≤ 2

end Module

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B]

@[expose] noncomputable def offJoin (X : GoldAmalgam A C B) (γ ρ : Vtx X) :
    Subgroup X.Universal :=
  (⨆ (ε : Vtx X) (_ : IsCritical X γ ε ∧ geo X γ ε 1 = ρ), ZM X ε) ⊔ Qv X γ

structure G2Hyp (X : GoldAmalgam A C B) (Lt Ut Wt : Vtx X → Subgroup X.Universal) : Prop where
  h20 : Hyp20 X
  cent : CentHyp X
  b4 : critDist X = 4
  fin : ∀ γ, IsMVtx X γ → Finite ↥(stab X γ)
  lt_le : ∀ γ, IsMVtx X γ → Lt γ ≤ stab X γ
  lt_nor : ∀ γ, IsMVtx X γ → stab X γ ≤ Subgroup.normalizer (Lt γ : Set X.Universal)
  lt_perf : ∀ γ, IsMVtx X γ → ⁅Lt γ, Lt γ⁆ = Lt γ
  lt_sup : ∀ γ ρ, IsMVtx X γ → X.treeGraph.Adj γ ρ → stab X γ = Lt γ ⊔ Qv X ρ
  lt_gen : ∀ γ ρ, IsMVtx X γ → X.treeGraph.Adj γ ρ → ∀ x ∈ Qv X ρ, x ∉ Qv X γ →
    Lt γ ≤ Subgroup.closure {y | ∃ k ∈ stab X γ, k * x * k⁻¹ = y}
  ut_le : ∀ γ, IsMVtx X γ → Ut γ ≤ ZM X γ
  ut_nor : ∀ γ, IsMVtx X γ → stab X γ ≤ Subgroup.normalizer (Ut γ : Set X.Universal)
  wt_eq : ∀ γ, IsMVtx X γ → Wt γ = Ut γ ⊓ Subgroup.centralizer (Lt γ : Set X.Universal)
  zm_comm : ∀ γ, IsMVtx X γ → ⁅ZM X γ, stab X γ⁆ ≤ Ut γ
  xm_eq : ∀ γ, IsMVtx X γ → XM X γ = ZM X γ
  off_cent : ∀ γ γ', IsCritical X γ γ' → ∀ y ∈ Qv X (geo X γ γ' 1),
    (∀ z ∈ ZM X γ', ⁅y, z⁆ ∈ Qv X γ) → y ∈ ZM X γ' ⊔ Qv X γ
  off_fix : ∀ γ γ', IsCritical X γ γ' → ∀ y ∈ Qv X (geo X γ γ' 1),
    (∀ r ∈ ⁅ZM X γ, ZM X γ'⁆, ⁅r, y⁆ ∈ Wt γ) → y ∈ ZM X γ' ⊔ Qv X γ
  r_le : ∀ γ γ', IsCritical X γ γ' → ⁅ZM X γ, ZM X γ'⁆ ≤ Ut γ
  w_le_r : ∀ γ γ', IsCritical X γ γ' → Wt γ ≤ ⁅ZM X γ, ZM X γ'⁆
  r_eq : ∀ γ γ', IsCritical X γ γ' → ∀ u ∈ Ut γ, (∀ z ∈ ZM X γ', ⁅u, z⁆ ∈ Wt γ) →
    u ∈ ⁅ZM X γ, ZM X γ'⁆
  r_card : ∀ γ γ', IsCritical X γ γ' → 2 < Nat.card ↥⁅ZM X γ, ZM X γ'⁆
  off_idx : ∀ γ γ', IsCritical X γ γ' → (Qv X γ).relIndex (ZM X γ') ≤ 8
  two_gen : ∀ γ γ', IsCritical X γ γ' → ∃ g₁ ∈ stab X γ, ∃ g₂ ∈ stab X γ,
    Lt γ ≤ (ZM X γ').map (MulAut.conj g₁).toMonoidHom ⊔
      (ZM X γ').map (MulAut.conj g₂).toMonoidHom ⊔ Qv X γ
  a_nor : ∀ γ γ', IsCritical X γ γ' → ∀ g ∈ stab X (geo X γ γ' 2), ∀ u ∈ Ut γ,
    (∀ t ∈ Qv X (geo X γ γ' 1), ⁅u, t⁆ ∈ Wt γ) →
      g * u * g⁻¹ ∈ Ut γ ∧ ∀ t ∈ Qv X (geo X γ γ' 1), ⁅g * u * g⁻¹, t⁆ ∈ Wt γ
  a_cent : ∀ γ γ', IsCritical X γ γ' → ∀ u ∈ Ut γ,
    (∀ t ∈ Qv X (geo X γ γ' 1), ⁅u, t⁆ ∈ Wt γ) →
      u ∈ Subgroup.centralizer (Lt (geo X γ γ' 2) : Set X.Universal)
  comm_off : ∀ γ ρ, IsMVtx X γ → X.treeGraph.Adj γ ρ → ∃ D : Subgroup X.Universal,
    Qv X γ ≤ D ∧ D ≤ Qv X ρ ∧ (Qv X γ).relIndex D ≤ 2 ∧
      ∀ x ∈ offJoin X γ ρ, ∀ y ∈ offJoin X γ ρ, ⁅x, y⁆ ∈ D
  hV : ∀ ε ε', IsCritical X ε ε' → ¬ Vv X ε ≤ Qv X (geo X ε' ε 2)
  nat : ∀ γ, IsMVtx X γ → NatHyp (stab X γ) (Lt γ) (Qv X γ)

end CFSG.Quasithin.MS93.S38G

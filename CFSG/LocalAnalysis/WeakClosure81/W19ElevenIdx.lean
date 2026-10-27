module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenZ
public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenSyl
public import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem eq_one_of_conj_mem (c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2)
    {P₁ P₂ L₁ L₂ : Subgroup G} (hP₁ : Nat.card P₁ = p) (hP₂ : Nat.card P₂ = p) (hne : P₁ ≠ P₂)
    (hP₁X : P₁ ≤ X) (hP₂X : P₂ ≤ X) (hP₁L : P₁ ≤ L₁) (hP₂L : P₂ ≤ L₂) {n w : G}
    (hn : n ∈ normalizer (Z193 D V : Set G)) (hnM : n ∉ D.M) (hw : w ∈ Z193 D V)
    (hwL₁ : ∀ l ∈ L₁, l * w = w * l) (hwL₂ : ∀ l ∈ L₂, l * w = w * l)
    (hnw : n * w * n⁻¹ ∈ Z193 D V) (hnwL₁ : ∀ l ∈ L₁, l * (n * w * n⁻¹) = n * w * n⁻¹ * l) :
    w = 1 := by
  by_contra hw1
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hsq : w ^ 2 = 1 := c.isElemAbelian_Z193.2 w hw
  have hord : orderOf w = 2 := orderOf_eq_prime hsq hw1
  have hD1 : Subgroup.zpowers w ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.1 h)
  have hD2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hYX : P₁ ⊔ P₂ ≤ X := sup_le hP₁X hP₂X
  have hYnc : ¬ IsCyclic ↥(P₁ ⊔ P₂) := not_isCyclic_sup_of_ne hP₁ hP₂ hne
  have hcn : ∀ y : G, y * w = w * y → y ∈ normalizer (Subgroup.zpowers w : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem_fin fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : y * w * y⁻¹ = w := by rw [hy]; group
    rw [← conj_zpow, this]
    exact Subgroup.zpow_mem_zpowers w k
  have hXD : P₁ ⊔ P₂ ≤ normalizer (Subgroup.zpowers w : Set G) := by
    have hc : P₁ ⊔ P₂ ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hwL₁ y (hP₁L hy)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hwL₂ y (hP₂L hy)
    intro y hy
    exact hcn y (Subgroup.mem_centralizer_singleton_iff.1 (hc hy))
  have hnormD : normalizer (Subgroup.zpowers w : Set G) ≤ D.M :=
    normalizer_le_of_uniqueMax (c.hyp.uniqueMax (P₁ ⊔ P₂) hYX hYnc) hD1 hD2 hXD
  have hcentM : ∀ y : G, y * w = w * y → y ∈ D.M := fun y hy => hnormD (hcn y hy)
  have hL₁M : L₁ ≤ conjSubgroup D.M n⁻¹ := by
    intro l hl
    rw [mem_conjSubgroup_iff]
    apply hcentM
    have h := hnwL₁ l hl
    calc n⁻¹ * l * n⁻¹⁻¹ * w = n⁻¹ * (l * (n * w * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * w * n⁻¹ * l) * n := by rw [h]
      _ = w * (n⁻¹ * l * n⁻¹⁻¹) := by group
  have hnM' : n⁻¹ ∉ D.M := fun h => hnM (by simpa using D.M.inv_mem h)
  have hV₀M : V₀ ≤ conjSubgroup D.M n⁻¹ := by
    intro v hv
    rw [mem_conjSubgroup_iff]
    have hvZ : v ∈ Z193 D V := c.V₀_le_Z193 h2 hv
    have h3 : n⁻¹ * v * n⁻¹⁻¹ ∈ Z193 D V :=
      (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (Z193 D V : Set G)).inv_mem hn) v).1 hvZ
    exact D.sylowM.le (c.Z193_le_T h3)
  have hbot := c.hyp.inf_eq_bot n⁻¹ hnM' hV₀M
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₁
    exact c.hyp.prime.one_lt.ne hP₁
  have hle : P₁ ≤ X ⊓ conjSubgroup D.M n⁻¹ := le_inf hP₁X (hP₁L.trans hL₁M)
  rw [hbot] at hle
  exact hP₁ne (le_bot_iff.1 hle)

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end

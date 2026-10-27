module

public import CFSG.GroupTheory.SteinbergBSSolvableSignalizer

public section

namespace CFSG.RankThree.Theta

open Subgroup

theorem completion_centralizers {p : ℕ} {A : Type*} [Group A] {G : Type*} [Group G]
    {α : A →* MulAut G} {θ : A → Subgroup G}
    (hd : CFSG.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum p A G α θ)
    (hcomplete :
      let Θ : Subgroup G := ⨆ (a : A) (_ : a ≠ 1), θ a
      (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧
        Nat.Coprime p (Nat.card Θ) ∧ ∀ a : A, a ≠ 1 → ∀ g ∈ Θ, α a g = g → g ∈ θ a) :
    let Θ : Subgroup G := ⨆ (a : A) (_ : a ≠ 1), θ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧
      Nat.Coprime p (Nat.card Θ) ∧ ∀ a : A, a ≠ 1 → ∀ g : G, (g ∈ Θ ∧ α a g = g ↔ g ∈ θ a) := by
  intro Θ
  obtain ⟨hinv, hsolv, hcop, hle⟩ := hcomplete
  refine ⟨hinv, hsolv, hcop, fun a ha g => ⟨fun h => hle a ha g h.1 h.2, fun hg => ?_⟩⟩
  exact ⟨(le_iSup_of_le a (le_iSup_of_le ha le_rfl) : θ a ≤ Θ) hg, hd.le_fixed a ha g hg⟩

end CFSG.RankThree.Theta

module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.K1327.Comp
public import CFSG.RankThree.PartOne.K1327.Psl2

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commute_of_member {p : ℕ} (hp : p.Prime) {K R V : Subgroup G} {g : ℕ} {b c : G}
    (hKm : StatedClassicalModel ↥K .PSL 2 2 g) (hKq : IsQuasisimple ↥K)
    (hKz : Subgroup.center ↥K = ⊥) (hKb : K ∈ thetaComponentsAt p b) (hRK : R ≤ K)
    (hR1 : R ≠ ⊥) (hcK : c ∈ K) (hcR : ∀ x ∈ R, c * x = x * c) (hcp : c ^ p = 1)
    (hVc : ∀ v ∈ V, c * v * c⁻¹ ∈ V) (hcop : ¬ p ∣ Nat.card V) {u : G} (huV : u ∈ V)
    (hub : u * b = b * u) (huR : ∀ x ∈ R, u * x = x * u) : Commute u c := by
  obtain ⟨hKY, hKmem⟩ := mem_thetaComponentsAt_iff.1 hKb
  set Y := Subgroup.centralizer ({b} : Set G) with hY
  have hX : IsComponent (K.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKY).symm hKq, hKmem.2.1⟩
  have huY : u ∈ Y := by
    rw [hY, Subgroup.mem_centralizer_singleton_iff]
    exact hub
  have huK := normalizes_of_component hKY hX hRK hR1 hKz huY huR
  obtain ⟨x₀, hx₀R, hx₀1⟩ : ∃ x₀ ∈ R, x₀ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one R with h | h
    · exact absurd h hR1
    · exact h
  have hT : ∀ a ∈ K, ∀ a' ∈ K, (∀ x ∈ R, a * x = x * a) → (∀ x ∈ R, a' * x = x * a') →
      a * a' = a' * a := by
    intro a ha a' ha' h1 h2
    have hx1 : (⟨x₀, hRK hx₀R⟩ : ↥K) ≠ 1 := fun h => hx₀1 (congrArg Subtype.val h)
    have e1 : (⟨a, ha⟩ : ↥K) * ⟨x₀, hRK hx₀R⟩ = ⟨x₀, hRK hx₀R⟩ * ⟨a, ha⟩ :=
      Subtype.ext (h1 x₀ hx₀R)
    have e2 : (⟨a', ha'⟩ : ↥K) * ⟨x₀, hRK hx₀R⟩ = ⟨x₀, hRK hx₀R⟩ * ⟨a', ha'⟩ :=
      Subtype.ext (h2 x₀ hx₀R)
    exact congrArg Subtype.val (psl_two_centralizer_comm hKm hx1 e1 e2)
  exact commute_of_component hp hT hcK hcR hcp hVc hcop huV huK huR

end CFSG.RankThree.PartOne.K1327

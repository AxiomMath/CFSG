module

public import CFSG.Quasithin.EmptyFaithful.S146zYOutPSL
public import CFSG.Quasithin.EmptyFaithful.S146zYOutJ1
public import CFSG.Quasithin.Vol2.F134Suzuki

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

theorem outAbelian_a38 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
    CFSG.IsComponent L → A38Types ↥L → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  intro A _ _ L _ _ hL a ha b hb
  rcases hL with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, -, hpsl⟩
  · exact CFSG.Quasithin.F134.commutator_mem_sup_centralizer L
      (outer_comm_of_statedPSL2 Nat.prime_two hn) ha hb
  · exact CFSG.Quasithin.F134.commutator_mem_of_suzukiModel hn ha hb
  · obtain ⟨e⟩ := hJ
    exact CFSG.Quasithin.F134.commutator_mem_sup_centralizer L (outer_comm_of_carrierJ1 e) ha hb
  · exact CFSG.Quasithin.F134.commutator_mem_sup_centralizer L
      (outer_comm_of_statedPSL2 hp hpsl) ha hb

end CFSG.Quasithin.S146zY

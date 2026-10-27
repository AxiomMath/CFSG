module

public import CFSG.Quasithin.EmptyFaithful.S146zYJGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.F134 CFSG.Walter.J1Props

theorem j1_no_five :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (y : A),
      IsSporadic .J1 ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) → y ∈ B → orderOf y = 5 → False := by
  rintro A _ _ L B U y ⟨e⟩ hUB hBL hU hB hyB hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε : ↥L ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hyL : y ∈ L := hBL hyB
  have hUw : IsPGroup 2 ((U.subgroupOf L).map ε.toMonoidHom) :=
    (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _
  have hUwi : ¬ 2 ∣ ((U.subgroupOf L).map ε.toMonoidHom).index := by
    have := Subgroup.index_map_equiv (U.subgroupOf L) ε
    erw [this]
    exact hU.2.2
  have hBw : ∀ q : ℕ, q.Prime → q ∣ Nat.card ((B.subgroupOf L).map ε.toMonoidHom) →
      q = 2 ∨ q = 5 := by
    intro q hq hqB
    refine hB q hq ?_
    rwa [← Nat.card_congr ((B.subgroupOf L).equivMapOfInjective _ ε.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv] at hqB
  have hyw : orderOf (ε ⟨y, hyL⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  exact janko_no_five jankoHyp₀ card_walterJ1' hUw hUwi
    (Subgroup.map_mono (Subgroup.subgroupOf_mono L hUB)) hBw
    ((mem_map_subgroupOf_iff' ε ⟨y, hyL⟩).2 hyB) hyw

end CFSG.Quasithin.S146zY

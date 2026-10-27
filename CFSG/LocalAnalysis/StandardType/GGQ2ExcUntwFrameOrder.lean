module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGF4TwoNTFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two9
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley
open CFSG.Open (IsElemAbelian)

private theorem excUntwFrameOrder_card_tE_range
    {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]
    (F : TableBExcTwo.OrthFrame τ d) :
    Nat.card ((TableBExcTwoTB.tE K F).range : Subgroup (adjointGroup τ K)) = 3 ^ (d + 1) := by
  let e : Multiplicative (Fin (d + 1) → ZMod 3) ≃ (TableBExcTwoTB.tE K F).range :=
    (MonoidHom.ofInjective (TableBExcTwoTB.tE_injective (K := K) F)).toEquiv
  rw [← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem excUntwFrameOrder_card_tE_range_F4
    {K : Type} [Field K] [CharP K 2] :
    Nat.card ((TableBF4TwoTB.tE K).range : Subgroup (adjointGroup .F4 K)) = 3 ^ 4 := by
  let e : Multiplicative (Fin 4 → ZMod 3) ≃ (TableBF4TwoTB.tE K).range :=
    (MonoidHom.ofInjective (TableBF4TwoTB.tE_injective (K := K))).toEquiv
  rw [← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem excUntwFrameOrder_F4_holds :
    ExcUntwFrameOrder .F4 4 4 := by
  intro K _ _ hK E hE hSC hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  obtain ⟨c, hc⟩ := F4TwoNonToral.exists_conj_frame_of_card_F4 K hK E hE hcard
  rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact excUntwFrameOrder_card_tE_range_F4 (K := K)

theorem excUntwFrameOrder_E6_holds :
    ExcUntwFrameOrder .E6 4 4 := by
  intro K _ _ hK E hE hSC hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  exact le_antisymm
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two.card_le_of_isElemAbelian_E6_three
      (by rw [hK]) hE) hcard

theorem excUntwFrameOrder_E7_holds :
    ExcUntwFrameOrder .E7 6 7 := by
  intro K _ _ hK E hE hSC hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_half_E7 hK hE hcard hSC
  rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simpa using excUntwFrameOrder_card_tE_range (K := K) (F := TableBExcTwo.frameE7)

theorem excUntwFrameOrder_E8_holds :
    ExcUntwFrameOrder .E8 7 8 := by
  intro K _ _ hK E hE hSC hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_half_E8 hK hE hcard hSC
  rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simpa using excUntwFrameOrder_card_tE_range (K := K) (F := TableBExcTwo.frameE8)

theorem excUntwTorusLift_E7_holds :
    ExcUntwTorusLift .E7 6 := by
  intro K _ _ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  exact TableBExcTwo.ggTorusLift_of_frame (K := K) (F := TableBExcTwo.frameE7)

theorem excUntwTorusLift_E8_holds :
    ExcUntwTorusLift .E8 7 := by
  intro K _ _ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hK)
  exact TableBExcTwo.ggTorusLift_of_frame (K := K) (F := TableBExcTwo.frameE8)

end CFSG.StandardType.GGQ2Frame.ExcPlacement

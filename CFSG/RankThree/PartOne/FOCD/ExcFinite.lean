module

public import CFSG.RankThree.PartOne.FOCD.OrdLemma
public import CFSG.RankThree.PartOne.FOCD.Suzuki
public import CFSG.RankThree.PartOne.FOC.Cases
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.ClassicalInvolution.Orders.Ree
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.FOC.Equiv

public section

namespace CFSG.RankThree.PartOne.FOCD

open CFSG CFSG.Blueprint CFSG.Open CFSG.LieType.Ree CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Census3 (IsoLie)

open TauCeti (LieTypeIndex PrimePower)


@[expose] def FieldInnerIdx (d : LieTypeIndex) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → IsoLie T d → FieldInnerT p T

theorem fieldInnerExc_of_idx (h : ∀ d : LieTypeIndex, ExcListedIndex d → FieldInnerIdx d) :
    FieldInnerExc := by
  intro T _ _ p hp hp5 hs hnab ⟨d, hd, hiso⟩
  exact h d hd T p hp hp5 hs hnab hiso

theorem fieldInnerT_of_card {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {N : ℕ} (hN : Nat.card T = N) (hdvd : N ∣ N71)
    (h31 : ¬ 31 ∣ N) : FieldInnerT p T :=
  fieldInnerT_of_dvd_N71 hp hp5 (hN ▸ hdvd) fun _ => hN ▸ h31

section Suzuki

theorem fieldInnerT_of_suzukiModel {T : Type} [Group T] [Finite T]
    {f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hnab : ∃ x y : T, x * y ≠ y * x)
    (hS : SuzukiModel T 2 f) : FieldInnerT p T := by
  obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  refine FieldInnerT.of_mulEquiv e hp ?_
  obtain ⟨hfin, -, hsS⟩ := suzuki_simple ha hK
  have hnab' : ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact fieldInnerT_of_comp (center_eq_bot_of_nonab hsS hnab')
    (innerComp_of_noCompOf fun _ => noCompOf_suzuki ha hK hp hp5) (outerComp_suzuki ha hK hp hp5)

theorem fieldInnerIdx_suzuki (m : ℕ) : FieldInnerIdx (.suzuki m) := by
  intro T _ _ p hp hp5 _ hnab hiso
  exact fieldInnerT_of_suzukiModel hp hp5 hnab (CTP.suzukiModel_of_isoLie m hiso)

end Suzuki

section Orders


theorem fieldInnerIdx_tits : FieldInnerIdx .tits := by
  intro T _ _ p hp hp5 _ _ hiso
  have hcard := S12K.card_of_reeTitsModel_Tits (CTP.reeTitsModel_tits hiso)
  refine fieldInnerT_of_card hp hp5 hcard ?_ ?_
  · unfold ordTits N71 primes71
    rw [Nat.dvd_iff_mod_eq_zero]
    decide +kernel
  · unfold ordTits
    decide +kernel

theorem fieldInnerIdx_reeG2_one : FieldInnerIdx (.reeG2 1) := by
  intro T _ _ p hp hp5 _ _ hiso
  obtain ⟨-, a, -, hfa, hcard⟩ :=
    ClassicalInvolution.card_of_reeTitsModel_twistedG2 (CTP.reeTitsModel_reeG2 1 hiso)
  refine fieldInnerT_of_card hp hp5 hcard ?_ ?_
  · unfold ordRee N71 primes71
    rw [Nat.dvd_iff_mod_eq_zero]
    decide +kernel
  · unfold ordRee
    decide +kernel

theorem fieldInnerIdx_F4
    (q : PrimePower) (hq2 : q.p = 2) (hq1 : q.exponent = 1) : FieldInnerIdx (.F4 q) := by
  intro T _ _ p hp hp5 _ _ hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq2 e0
  rw [hq2, hq1] at hmodel
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmodel
  refine fieldInnerT_of_card hp hp5 hcard ?_ ?_
  · unfold ordF4 N71 primes71
    rw [Nat.dvd_iff_mod_eq_zero]
    decide +kernel
  · unfold ordF4
    decide +kernel

end Orders

end CFSG.RankThree.PartOne.FOCD

module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.KFacts.K72L3Group
import CFSG.Quasithin.Vol2.F134Basic
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.RankThree.PartTwo.Sec17.G1724J2
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import Certificates.Data.ExceptionalSL3
import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem rowOfK9_of_card_dvd {X : Type} [Group X] {M : ℕ} (hX : Nat.card X ∣ M)
    (h : ¬ 604800 ∣ M) : RowOfK9 X :=
  rowOfK9_of_not_dvd fun h' => h (h'.trans hX)

theorem rowOfK9_of_lieOrder (hb : LieOrderBridge) {X : Type} [Group X]
    (idx : TauCeti.ValidLieTypeIndex)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (h : ¬ 604800 ∣ lieOrderFormula idx.1) : RowOfK9 X := by
  intro S _ _ hs hna ⟨eS⟩
  obtain ⟨eX⟩ := hX
  have hS : Nat.card S = lieOrderFormula idx.1 := hb idx S ⟨eS.trans eX⟩
  exact rowOfK9_of_not_dvd (X := S) (by rwa [hS]) S hs hna ⟨MulEquiv.refl S⟩

section Classical

open CFSG.RankThree.PartTwo.Sec4.RonanK429

theorem k9_nine_SL3 (e : ℕ) (he : 1 ≤ e) (he3 : e ≤ 3) :
    RowOfK9 (projSL 3 (GaloisField 3 e)) := by
  refine rowOfK9_of_not_dvd ?_
  rw [RowV.card_projSL_three_char_three he]
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  all_goals decide +kernel

theorem k9_nine_SU3 (e : ℕ) (he : 1 ≤ e) (he3 : e ≤ 3) : RowOfK9 (projSU 3 3 e) := by
  refine rowOfK9_of_not_dvd ?_
  rw [RowV.card_projSU_three_char_three he]
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  all_goals decide +kernel

theorem k9_nine_SL4 : RowOfK9 (projSL 4 (GaloisField 3 1)) :=
  rowOfK9_of_card_dvd (M := 3 ^ 6 * 16640) RowV.card_projSL_four_three_dvd (by decide +kernel)

theorem k9_nine_SU4 : RowOfK9 (projSU 4 3 1) :=
  rowOfK9_of_not_dvd (by rw [CFSG.PGLModel.card_projSU_four_three]; decide +kernel)

end Classical

private theorem not_dvd_lieOrderFormula_reeG2_one :
    ¬ 604800 ∣ lieOrderFormula (TauCeti.LieTypeIndex.reeG2 1) := by
  have h : lieOrderFormula (TauCeti.LieTypeIndex.reeG2 1) = 10073444472 := by
    simp only [lieOrderFormula, CFSG.Open.orderRee]
    norm_num
  rw [h]
  norm_num

private theorem not_dvd_lieOrderFormula_g2_three :
    ¬ 604800 ∣ lieOrderFormula g2ThreeIndex.1 := by
  have h : lieOrderFormula g2ThreeIndex.1 = 4245696 := by
    simp only [g2ThreeIndex, lieOrderFormula, CFSG.Open.orderG2, TauCeti.PrimePower.card_def]
    norm_num
  rw [h]
  norm_num

theorem k9_three_of_bridge (hb : LieOrderBridge) (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid) :
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group :=
  rowOfK9_of_lieOrder hb ⟨.reeG2 1, hr⟩ ⟨MulEquiv.refl _⟩ not_dvd_lieOrderFormula_reeG2_one

theorem k9_nine_G2_of_bridge (hb : LieOrderBridge) :
    RowOfK9 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group :=
  rowOfK9_of_lieOrder hb g2ThreeIndex ⟨MulEquiv.refl _⟩ not_dvd_lieOrderFormula_g2_three

theorem isCyclic_sylow_quotient {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ R : Sylow p G, IsCyclic R) {P : Subgroup G} (N : Subgroup P) [N.Normal] :
    ∀ R : Sylow p (P ⧸ N), IsCyclic R := fun R =>
  Quasithin.F134.isCyclic_of_isPGroup_of_surjective (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (KFacts.isCyclic_sylow_subgroup P h) R R.isPGroup'

theorem isEmpty_quotEquiv_j2_of_isCyclic_sylow_five
    (h5 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Blueprint.NativeSporadic.J2))
    {S : Type} [Group S] [Finite S] (hS : ∀ R : Sylow 5 S, IsCyclic R) (P : Subgroup S)
    (N : Subgroup P) [N.Normal] : IsEmpty (P ⧸ N ≃* Blueprint.NativeSporadic.J2) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨fun e => ?_⟩
  haveI : Finite Blueprint.NativeSporadic.J2 := Finite.of_equiv _ e.toEquiv
  have hcyc : ∀ R : Sylow 5 Blueprint.NativeSporadic.J2, IsCyclic R := fun R =>
    Quasithin.F134.isCyclic_of_isPGroup_of_surjective (f := e.toMonoidHom) e.surjective
      (isCyclic_sylow_quotient hS N) R R.isPGroup'
  obtain ⟨T⟩ : Nonempty (Sylow 5 Blueprint.NativeSporadic.J2) := inferInstance
  exact absurd h5 (not_le.mpr (Nat.lt_succ_of_le
    (CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow (by norm_num) T (hcyc T))))

private theorem card_projSL_two_three_one : Nat.card (projSL 2 (GaloisField 3 1)) = 12 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr (projSLEquivPSL (GaloisField 3 1)).toEquiv,
    CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := 3) (m := 1) (by norm_num)
      one_ne_zero]
  norm_num

theorem isCyclic_sylow_five_projSL_two_three {e : ℕ} (he : 2 ≤ e) :
    ∀ R : Sylow 5 (projSL 2 (GaloisField 3 e)), IsCyclic R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 3 e) = 3 ^ e := GaloisField.card 3 e (by omega)
  have h7 : 7 ≤ Nat.card (GaloisField 3 e) := by
    rw [hK]
    calc 7 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hcop : Nat.Coprime 5 (Nat.card (GaloisField 3 e)) := by
    rw [hK]
    exact Nat.Coprime.pow_right e ((Nat.coprime_primes (by norm_num) Nat.prime_three).mpr
      (by norm_num))
  have hPSL := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
    (GaloisField 3 e) hK h7 5 (by norm_num) hcop
  intro R
  exact Quasithin.F134.isCyclic_of_isPGroup_of_surjective
    (f := (projSLEquivPSL (GaloisField 3 e)).symm.toMonoidHom)
    (MulEquiv.surjective _) hPSL R R.isPGroup'

theorem rowOfK9_projSL_two_three_of_pRank
    (h5 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Blueprint.NativeSporadic.J2))
    (e : ℕ) (he : 1 ≤ e) : RowOfK9 (projSL 2 (GaloisField 3 e)) := by
  rcases Nat.lt_or_ge e 2 with h1 | h2
  · obtain rfl : e = 1 := by omega
    exact rowOfK9_of_not_dvd (by rw [card_projSL_two_three_one]; norm_num)
  · intro S _ _ _ _ ⟨eS⟩ σ _ _ P _ _ _ N _
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI : Finite (projSL 2 (GaloisField 3 e)) := Finite.of_equiv S eS.toEquiv
    have hS : ∀ R : Sylow 5 S, IsCyclic R := fun R =>
      Quasithin.F134.isCyclic_of_isPGroup_of_surjective (f := eS.symm.toMonoidHom)
        eS.symm.surjective (isCyclic_sylow_five_projSL_two_three h2) R R.isPGroup'
    exact isEmpty_quotEquiv_j2_of_isCyclic_sylow_five h5 hS P N

theorem rowOfK9_projSL_two_three
    (e : ℕ) (he : 1 ≤ e) :
    RowOfK9 (projSL 2 (GaloisField 3 e)) :=
  rowOfK9_projSL_two_three_of_pRank Sec17.G1724.two_le_pRank_five_J2 e he

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

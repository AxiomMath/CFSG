module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
import CFSG.LocalAnalysis.GLTheoremA.CatA.LieOrderGrid
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd443520

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

structure K150Facts (J : Type) [Group J] : Prop where
  simple : IsSimpleGroup J
  center : Subgroup.center J = ⊥
  three_dvd : 3 ∣ Nat.card J
  card_gt : 720 < Nat.card J
  not_chev : ∀ q : ℕ, ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q J

theorem K150Facts.exists_noncomm {J : Type} [Group J] (hF : K150Facts J) :
    ∃ a b : J, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hall : ∀ a : J, a = 1 := fun a => by
    have ha : a ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun g => h g a
    rw [hF.center, Subgroup.mem_bot] at ha
    exact ha
  have : Subsingleton J := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have h1 := Nat.card_of_subsingleton (1 : J)
  have := hF.card_gt
  omega

theorem k150_center_eq_bot_of_not_prime {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Q :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hp (Group.is_simple_iff_prime_card.mp inferInstance)

set_option maxRecDepth 100000 in
theorem k150_lieOrderFormula_ne_2520 {d : TauCeti.LieTypeIndex} (hd : d.Valid) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d ≠ 2520 :=
  CFSG.LocalAnalysis.GLTheoremA.LieGrid.lieOrderFormula_ne_of_grid [2, 3, 5, 7] 2520
    (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hd

theorem k150_not_isChevSimple_of_card (hb : LieOrderBridge) {T : Type} [Group T] {N : ℕ}
    (hN0 : N ≠ 0) (hc : Nat.card T = N)
    (hN : ∀ d : TauCeti.LieTypeIndex, d.Valid →
      CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d ≠ N)
    (h60 : N ≠ 60) (h360 : N ≠ 360) (h8 : N ≠ 20160) (q : ℕ) :
    ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; exact hN0)
  exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_not_lieOrder hb hc hN
    h60 h360 h8 q

theorem k150_card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem k150Facts_a7 (hb : LieOrderBridge) : K150Facts (alternatingGroup (Fin 7)) := by
  have hc := k150_card_alternating_seven
  refine ⟨alternatingGroup.isSimpleGroup (by simp), alternatingGroup.center_eq_bot (by simp),
    by rw [hc]; norm_num, by rw [hc]; norm_num, fun q => ?_⟩
  exact k150_not_isChevSimple_of_card hb (by norm_num) hc
    (fun d hd => k150_lieOrderFormula_ne_2520 hd) (by norm_num) (by norm_num) (by norm_num) q

theorem k150Facts_m22 (hb : LieOrderBridge) :
    K150Facts CFSG.Blueprint.NativeSporadic.M22 := by
  have hc := CFSG.Sporadic.Mathieu.card_M22
  have hsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  refine ⟨hsimple, k150_center_eq_bot_of_not_prime (by rw [hc]; norm_num),
    by rw [hc]; norm_num, by rw [hc]; norm_num, fun q => ?_⟩
  exact k150_not_isChevSimple_of_card hb (by norm_num) hc
    (fun d hd => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.OrderDvd443520.lieOrderFormula_ne_443520
      hd) (by norm_num) (by norm_num) (by norm_num) q

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

module

public import CFSG.RankThree.PartTwo.Sec13.KF135Core
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF2
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.RankThree.PartTwo.KFacts.KS21FusionL44
import CFSG.RankThree.PartTwo.KFacts.KS21FusionSp64
import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.Quasithin.Background.A318POutMore
import CFSG.Adapters.RankThreeOutcomesReverse
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.Fam8

open CFSG.RankThree.PartTwo.Sec13.F135Last
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  primePowerTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_pow_dvd_of_factors {p k : ℕ} (l : List (ℕ × ℕ)) (hl : ∀ y ∈ l, y.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hchk : ∀ y ∈ l, 7 ≤ y.1 → y.2 < k) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hk : 1 ≤ k) : ¬ p ^ k ∣ (l.map fun y => y.1 ^ y.2).prod := by
  intro hd
  obtain ⟨y, hy, rfl, hky⟩ :=
    CFSG.ComponentClassification.GSThmB.QPUSpor.exists_of_prime_pow_dvd_prod hp hk hl hnd hd
  have := hchk y hy hp7
  omega

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem list42_of_fam8 (hF : Fam8 S) : Sec4.Census.List42 S :=
  (list42_iff S).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hF))))))))

theorem false_of_factors (h : KF135Hyp S p P x u V) (hOut : KFactOutP)
    (hL : Sec4.Census.List42 S) (l : List (ℕ × ℕ)) (hl : ∀ y ∈ l, y.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hcard : Nat.card S = (l.map fun y => y.1 ^ y.2).prod)
    (hchk : ∀ y ∈ l, 7 ≤ y.1 → y.2 < 2) : False :=
  h.false_of_not_sq_dvd_card hOut hL
    (hcard ▸ not_pow_dvd_of_factors l hl hnd hchk h.prime h.seven_le (by norm_num))

theorem false_of_factors_outer (h : KF135Hyp S p P x u V)
    (hout : ¬ p ∣ Nat.card (Outer S)) (l : List (ℕ × ℕ)) (hl : ∀ y ∈ l, y.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hcard : Nat.card S = (l.map fun y => y.1 ^ y.2).prod)
    (hchk : ∀ y ∈ l, 7 ≤ y.1 → y.2 < 3) : False :=
  not_pow_dvd_of_factors l hl hnd hchk h.prime h.seven_le (by norm_num)
    (hcard ▸ h.cube_dvd_card_of_not_dvd_outer hout)

theorem not_dvd_of_dvd_54 (h : KF135Hyp S p P x u V) {m : ℕ} (hm : m ∣ 54) : ¬ p ∣ m :=
  fun hd => not_pow_dvd_of_factors (k := 1) [(2, 1), (3, 3)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide) (by decide)
    h.prime h.seven_le le_rfl (by rw [pow_one]; exact hd.trans hm)

section Rows

variable (h : KF135Hyp S p P x u V)
include h

theorem l52_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projSL 5 (GaloisField 2 1)) : False :=
  false_of_factors h hOut hL [(2, 10), (3, 2), (5, 1), (7, 1), (31, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr (φ.trans (Sec4.Item434SmallTwoOther.slEquivProjSL
      (by norm_num : 1 ≤ 5)).symm).toEquiv).trans
      (Sec4.Item434SmallTwoOther.L52.card_SL5.trans (by decide)))
    (by decide)

theorem u52_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S) (φ : S ≃* projSU 5 2 1) :
    False :=
  false_of_factors h hOut hL [(2, 10), (3, 5), (5, 1), (11, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSU_five_two_gf2.trans (by decide)))
    (by decide)

theorem not_dvd_outer_projSL_two {n : ℕ} (hn : 3 ≤ n) (φ : S ≃* projSL n (GaloisField 2 1)) :
    ¬ p ∣ Nat.card (Outer S) := by
  have hm : CFSG.Open.StatedClassicalModel S .PSL n 2 1 :=
    CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL
      ⟨Nat.prime_two, le_rfl, by omega, fun he => by simp at he; omega,
        fun he => by simp at he⟩ φ
  have := h.seven_le
  exact CFSG.Quasithin.A318P.not_dvd_outer_psl_binary hn hm h.prime (by omega)

theorem l62_false (φ : S ≃* projSL 6 (GaloisField 2 1)) : False :=
  false_of_factors_outer h (not_dvd_outer_projSL_two h (by norm_num) φ)
    [(2, 15), (3, 4), (5, 1), (7, 2), (31, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSL_six_two_gf2.trans (by decide)))
    (by decide)

theorem u62_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S) (φ : S ≃* projSU 6 2 1) :
    False :=
  false_of_factors h hOut hL [(2, 15), (3, 6), (5, 1), (7, 1), (11, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSU_six_two_gf2.trans (by decide)))
    (by decide)

theorem l72_false (φ : S ≃* projSL 7 (GaloisField 2 1)) : False :=
  false_of_factors_outer h (not_dvd_outer_projSL_two h (by norm_num) φ)
    [(2, 21), (3, 4), (5, 1), (7, 2), (31, 1), (127, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSL_seven_two_gf2.trans (by decide)))
    (by decide)

theorem sp62_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projSp 3 (GaloisField 2 1)) : False :=
  false_of_factors h hOut hL [(2, 9), (3, 4), (5, 1), (7, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSp_three_two_gf2.trans (by decide)))
    (by decide)

theorem sp82_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projSp 4 (GaloisField 2 1)) : False :=
  false_of_factors h hOut hL [(2, 16), (3, 5), (5, 2), (7, 1), (17, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projSp_four_two_gf2.trans (by decide)))
    (by decide)

theorem o8p_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projOmegaPlus 4 (GaloisField 2 1)) : False :=
  false_of_factors h hOut hL [(2, 12), (3, 5), (5, 2), (7, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.RonanEps.card_projOmegaPlus_four_two_gf2.trans (by decide)))
    (by decide)

theorem o8m_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S) {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (φ : S ≃* projOmegaMinus 3 (GaloisField 2 1) b c) : False :=
  false_of_factors h hOut hL [(2, 12), (3, 4), (5, 1), (7, 1), (17, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      ((Sec4.RonanEps.card_projOmegaMinus_four_two_gf2 hbc).trans (by decide)))
    (by decide)

theorem l44_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projSL 4 (GaloisField 2 2)) : False :=
  false_of_factors h hOut hL [(2, 12), (3, 4), (5, 2), (7, 1), (17, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr (φ.trans KFacts.KS21.L44.equivSL).toEquiv).trans
      (KFacts.KS21.L44.card_M_eq.trans (by decide)))
    (by decide)

theorem sp64_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S)
    (φ : S ≃* projSp 3 (GaloisField 2 2)) : False :=
  false_of_factors h hOut hL [(2, 18), (3, 4), (5, 3), (7, 1), (13, 1), (17, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr (φ.trans KFacts.KS21.Sp64.equivSp).toEquiv).trans
      (KFacts.KS21.Sp64.card_Sp_eq.trans (by decide)))
    (by decide)

theorem u54_false (hOut : KFactOutP) (hL : Sec4.Census.List42 S) (φ : S ≃* projSU 5 2 2) :
    False :=
  false_of_factors h hOut hL [(2, 20), (3, 2), (5, 4), (13, 1), (17, 1), (41, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr φ.toEquiv).trans
      (Sec4.Item434SmallTwoOther.U54.card_U54.trans (by decide)))
    (by decide)

theorem u58_false (φ : S ≃* projSU 5 2 3) : False := by
  have hout : ¬ p ∣ Nat.card (Outer S) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
    exact not_dvd_of_dvd_54 h (by
      have := Sec4.card_outer_projSU_dvd 5 2 3 (by norm_num) (by norm_num) (by norm_num)
      norm_num at this
      exact this)
  exact false_of_factors_outer h hout
    [(2, 30), (3, 9), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (331, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    ((Nat.card_congr (φ.trans KFacts.KS21.U58.equivSUI).toEquiv).trans
      (KFacts.KS21.U58.card_SUI.trans (by decide)))
    (by decide)

end Rows

section F4


open CFSG.Blueprint.Chevalley CFSG.LieType.Ree in
theorem f42_false (h : KF135Hyp S p P x u V)
    (φ : S ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : False := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 primePowerTwo f4TwoIndex.2 rfl φ
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
  have hK2 : Nat.card K = 2 := hK
  have hK' : Nat.card K = 2 ^ 1 := hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (le_refl 1) K hK'
  have hout2 : Nat.card (Outer S) = 2 := by
    have h1 : Nat.card (Outer S) = Nat.card (Outer (adjointGroup ReeTag.F4.tag K)) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    have h2 : Nat.card (Outer (adjointGroup ReeTag.F4.tag K)) =
        Nat.card (Multiplicative (ZMod (2 * 1))) :=
      Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)).toEquiv
    have hc : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      simp
    rw [h1, h2, hc]
  have hcard : Nat.card S = 3311126603366400 := by
    have h1 := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK2] at h1
    exact (Nat.card_congr e.toEquiv).trans (h1.trans (by norm_num [CFSG.Open.ordF4]))
  exact false_of_factors_outer h (not_dvd_of_dvd_54 h (by rw [hout2]; norm_num))
    [(2, 24), (3, 6), (5, 2), (7, 2), (13, 1), (17, 1)]
    (by simp only [List.forall_mem_cons, List.forall_mem_nil]; norm_num) (by decide)
    (hcard.trans (by decide)) (by decide)

theorem _root_.CFSG.RankThree.PartTwo.Sec13.KF135Proof.kF135At_fam8 (hOut : KFactOutP) :
    KF135At Fam8 := by
  intro S _ _ p P x u V hF h
  have hL := list42_of_fam8 hF
  rcases hF with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ |
    ⟨b, c, hbc, ⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (l52_false h hOut hL φ).elim
  · exact (u52_false h hOut hL φ).elim
  · exact (l62_false h φ).elim
  · exact (u62_false h hOut hL φ).elim
  · exact (l72_false h φ).elim
  · exact (sp62_false h hOut hL φ).elim
  · exact (sp82_false h hOut hL φ).elim
  · exact (o8p_false h hOut hL φ).elim
  · exact (o8m_false h hOut hL hbc φ).elim
  · exact (l44_false h hOut hL φ).elim
  · exact (sp64_false h hOut hL φ).elim
  · exact (u54_false h hOut hL φ).elim
  · exact (u58_false h φ).elim
  · exact (f42_false h φ).elim

end F4

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.Fam8

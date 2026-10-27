module

public import CFSG.RankThree.PartTwo.Sec15.ThmCDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG.RankThree.PerfectCover CFSG.Open

private theorem thmcm2_card_center_dvd_griess {S Q : Type} [Group S] [Group Q]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv, ← hker, ← hmap]
  exact Subgroup.card_map_dvd (H := hopfMultiplier S) (hopfLift q hq hker.le)

theorem twoMultLeTwo_of_not_four_dvd {S : Type} [Group S]
    (h : ¬ 4 ∣ Nat.card (griessHopfMultiplier S)) : TwoMultLeTwo S := by
  intro E _ _ hE hφ Z hZ hZ2
  obtain ⟨φ⟩ := hφ
  have hd := thmcm2_card_center_dvd_griess hE φ
  have hZd : Nat.card ↥Z ∣ Nat.card ↥(Subgroup.center E) := Subgroup.card_dvd_of_le hZ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  by_contra hgt
  rw [hk] at hgt
  have hk2 : 2 ≤ k := by
    by_contra hlt
    exact hgt (by interval_cases k <;> norm_num)
  have h4 : 4 ∣ Nat.card ↥Z := by
    rw [hk]
    exact Dvd.dvd.trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
  exact h (h4.trans (hZd.trans hd))

private theorem thmcm2_of_card {S : Type} [Group S] {m : ℕ} (hm : ¬ 4 ∣ m)
    (h : Nat.card (griessHopfMultiplier S) = m) : TwoMultLeTwo S :=
  twoMultLeTwo_of_not_four_dvd (h ▸ hm)

theorem twoMultLeTwo_alternatingGroup_seven :
    TwoMultLeTwo ↥(alternatingGroup (Fin 7)) :=
  thmcm2_of_card (m := 6) (by norm_num)
    ((Nat.card_congr (hopfMultiplierEquivGriess (alternatingGroup (Fin 7))).toEquiv).trans
      (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2)

theorem twoMultLeTwo_alternatingGroup_ten : TwoMultLeTwo ↥(alternatingGroup (Fin 10)) :=
  thmcm2_of_card (m := 2) (by norm_num)
    ((Nat.card_congr (hopfMultiplierEquivGriess (alternatingGroup (Fin 10))).toEquiv).trans
      (CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)))

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover in
theorem twoMultLeTwo_ON :
    TwoMultLeTwo CFSG.Blueprint.NativeSporadic.ON := by
  refine twoMultLeTwo_of_not_four_dvd ?_
  obtain ⟨h0, h3⟩ := card_hopfMultiplier_nativeON_le_three
  rw [Nat.card_congr (hopfMultiplierEquivGriess CFSG.Blueprint.NativeSporadic.ON).toEquiv]
  intro h4
  have h5 := Nat.le_of_dvd h0 h4
  omega

private theorem thmcm2_card_table {t : StatedLieTag} {n p f g : ℕ}
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (g, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) = g := by
  have hz : ∀ a : ℕ, Nat.card (Multiplicative (ZMod a)) = a := fun a =>
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod a)
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hg, he]
  simp only [Nat.card_prod, hz]
  omega

private theorem thmcm2_of_table {S : Type} [Group S] {t : StatedLieTag} {n p f g : ℕ}
    (e : Nonempty (griessHopfMultiplier S ≃*
      CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f))
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (g, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) (hg3 : g ∣ 3) :
    TwoMultLeTwo S := by
  obtain ⟨e⟩ := e
  refine twoMultLeTwo_of_not_four_dvd ?_
  rw [Nat.card_congr e.toEquiv, thmcm2_card_table hg he]
  intro h4
  have h43 := h4.trans hg3
  omega

private theorem thmcm2_eight_le {m : ℕ} (hm : 3 ≤ m) : 8 ≤ 2 ^ m :=
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

private theorem thmcm2_exceptional_psl {m : ℕ} (hm : 3 ≤ m) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 m = (1, 1) := by
  rw [CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSL Nat.prime_two
    (by omega)]
  have h8 := thmcm2_eight_le hm
  have hne2 : 2 ^ m ≠ 2 := by omega
  have hne4 : 2 ^ m ≠ 4 := by omega
  simp [CFSG.Open.griessPSLExceptional, hne2, hne4]

theorem twoMultLeTwo_L3Seven
    (hp7 : Fact (Nat.Prime 7)) :
    TwoMultLeTwo (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) := by
  have hadm : StatedLieAdmissible .PSL 3 7 1 :=
    ⟨hp7.out, le_refl 1, by norm_num, by simp, by simp⟩
  have hmodel : StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))
      .PSL 3 7 1 := by
    refine ⟨hadm, GaloisField 7 1, inferInstance, inferInstance, ?_,
      ⟨CFSG.PGLModel.projSLEquivStatedProj 3 _⟩⟩
    rw [GaloisField.card 7 1 one_ne_zero]
  obtain ⟨-, he⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hmodel
  refine thmcm2_of_table he (g := Nat.gcd 3 (7 ^ 1 - 1)) ?_ ?_ (Nat.gcd_dvd_left _ _)
  · unfold CFSG.Blueprint.Multiplier.genericOrders
    rfl
  · unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    decide

theorem twoMultLeTwo_L3Pi
    {m : ℕ} (hm : 3 ≤ m)
    {S : Type} [Group S] (h : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi S 2 m) :
    TwoMultLeTwo S := by
  have h8 := thmcm2_eight_le hm
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hadm : StatedLieAdmissible .PSL 3 2 m :=
      ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
    have hmodel : StatedClassicalModel S .PSL 3 2 m := by
      refine ⟨hadm, GaloisField 2 m, inferInstance, inferInstance, ?_,
        ⟨φ.trans (CFSG.PGLModel.projSLEquivStatedProj 3 _)⟩⟩
      rw [GaloisField.card 2 m (by omega)]
    obtain ⟨-, he⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hmodel
    refine thmcm2_of_table he (g := Nat.gcd 3 (2 ^ m - 1)) ?_ (thmcm2_exceptional_psl hm)
      (Nat.gcd_dvd_left _ _)
    unfold CFSG.Blueprint.Multiplier.genericOrders
    rfl
  · have hadm : StatedLieAdmissible .PSU 3 2 m := by
      refine ⟨Nat.prime_two, by omega, le_refl 3, fun h => ?_⟩
      have := congrArg Prod.snd h
      simp only at this
      omega
    have hmodel : StatedClassicalModel S .PSU 3 2 m := by
      refine ⟨hadm, GaloisField 2 (2 * m), inferInstance, inferInstance, ?_,
        ⟨φ.trans (CFSG.PGLModel.projSUEquivStatedProj 3 2 m)⟩⟩
      rw [GaloisField.card 2 (2 * m) (by omega), mul_comm, pow_mul]
    obtain ⟨-, he⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmodel
      (by decide)
    refine thmcm2_of_table he (g := Nat.gcd 3 (2 ^ m + 1)) ?_
      (CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSU_odd (by decide))
      (Nat.gcd_dvd_left _ _)
    unfold CFSG.Blueprint.Multiplier.genericOrders
    rfl

theorem kFactM2_of_certificates :
    KFactM2 :=
  ⟨twoMultLeTwo_ON, twoMultLeTwo_alternatingGroup_seven,
    ⟨⟨by norm_num⟩, twoMultLeTwo_L3Seven ⟨by norm_num⟩⟩, twoMultLeTwo_alternatingGroup_ten,
    fun _ hm _ _ h => twoMultLeTwo_L3Pi hm h⟩

end CFSG.RankThree.PartTwo.Sec15.ThmC

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
import CFSG.Quasithin.Background.A3Structure314Radical
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p21k_map_solvableRadical_eq_center {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    (CFSG.solvableRadical ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Subgroup.center (Bar2 L) := by
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  exact CFSG.Quasithin.A314.map_solvableRadical_eq_center inferInstance
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq)

theorem uc22p21k_barInf_equiv {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    Nonempty (BarInf L ≃* Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  exact CFSG.Quasithin.A314.solvableRadical_quotient_equiv inferInstance
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq)

theorem uc22p21k_barInf_equiv_of_calC {M L : Subgroup G} (hL : L ∈ calC M) :
    Nonempty (BarInf L ≃* Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
  uc22p21k_barInf_equiv hL.2.2

theorem uc22p21k_barInf_equiv_of_center_bot {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hc : Subgroup.center (Bar2 L) = ⊥) : Nonempty (BarInf L ≃* Bar2 L) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)⟩

theorem uc22p21k_quotCenter_equiv {X : Type} [Group X] (hc : Subgroup.center X = ⊥) :
    Nonempty ((X ⧸ Subgroup.center X) ≃* X) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot⟩

theorem uc22p21k_card_quot_center {X : Type} [Group X] (hc : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
  obtain ⟨e⟩ := uc22p21k_quotCenter_equiv hc
  exact Nat.card_congr e.toEquiv

theorem uc22p21k_center_eq_bot {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
    haveI : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton (X ⧸ Subgroup.center X) :=
      (QuotientGroup.quotientMulEquivOfEq h).injective.subsingleton
    exact not_subsingleton (X ⧸ Subgroup.center X) inferInstance

theorem uc22p21k_dvd_of_mul_eq {A g P S T d : ℕ} (hg : 0 < g) (h : A * g = P * (S * T))
    (hS : d ∣ S) (hT : g ∣ T) : d ∣ A := by
  obtain ⟨a, rfl⟩ := hS
  obtain ⟨b, rfl⟩ := hT
  have h2 : A * g = (P * d * a * b) * g := by rw [h]; ring
  have h3 := Nat.eq_of_mul_eq_mul_right hg h2
  exact ⟨P * a * b, by rw [h3]; ring⟩

theorem uc22p21k_ordBC_two_mul_gcd (q : ℕ) :
    ordBC 2 q * Nat.gcd 2 (q - 1) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have hprod : ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right ((Nat.gcd_dvd_right 2 _).trans
      (Nat.sub_one_dvd_pow_sub_one q 2)) _) _
  unfold ordBC
  rw [show 2 * 2 = 4 from rfl, hprod]
  exact Nat.div_mul_cancel hdvd

theorem uc22p21k_ordTwistedA_two_mul_gcd (q : ℕ) (hq : 1 ≤ q) :
    ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num),
      CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq even_two,
      CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide)]
  have hdvd : Nat.gcd 3 (q + 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    simp only [one_pow] at this
    exact (Nat.gcd_dvd_right 3 _).trans this
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 from rfl, show (2 + 1 : ℕ) = 3 from rfl]
  rw [hprod]
  exact Nat.div_mul_cancel hdvd

theorem uc22p21k_three_dvd_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  exact Nat.sub_one_dvd_pow_sub_one 4 n

theorem uc22p21k_three_dvd_ordBC_two (n : ℕ) : 3 ∣ ordBC 2 (2 ^ n) :=
  uc22p21k_dvd_of_mul_eq (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (uc22p21k_ordBC_two_mul_gcd (2 ^ n)) (uc22p21k_three_dvd_sq_sub_one n)
    ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 4))

theorem uc22p21k_three_dvd_ordTwistedA_two (n : ℕ) : 3 ∣ ordTwistedA 2 (2 ^ n) := by
  refine uc22p21k_dvd_of_mul_eq (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (uc22p21k_ordTwistedA_two_mul_gcd (2 ^ n) Nat.one_le_two_pow)
    (uc22p21k_three_dvd_sq_sub_one n) ((Nat.gcd_dvd_right _ _).trans ?_)
  simpa only [one_pow] using Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (by decide : Odd 3)

@[expose] def SpU3Quot (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, IsSp4 (X ⧸ Subgroup.center X) n) ∨ (∃ n : ℕ, IsU3 (X ⧸ Subgroup.center X) n)

theorem uc22p21k_three_dvd_card_quot {X : Type} [Group X] (h : SpU3Quot X) :
    3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · rw [show Nat.card (X ⧸ Subgroup.center X) = ordBC 2 (2 ^ n) from
      hn.card_eq_lieOrd (by norm_num)]
    exact uc22p21k_three_dvd_ordBC_two n
  · rw [show Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n) from
      hn.card_eq_lieOrd (by norm_num)]
    exact uc22p21k_three_dvd_ordTwistedA_two n

theorem uc22p21k_not_isSz {X : Type} [Group X] (h : SpU3Quot X) (m : ℕ) : ¬ IsSz X m := fun hSz =>
  CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
    ((uc22p21k_three_dvd_card_quot h).trans (Subgroup.card_quotient_dvd_card _))

theorem uc22p21k_not_isL2 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) (h : SpU3Quot X)
    (m : ℕ) : ¬ IsL2 X m := by
  intro hL2
  haveI : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2
  have hcard := uc22p21k_card_quot_center (uc22p21k_center_eq_bot hq)
  have hX : Nat.card X = ordA 1 (2 ^ m) := hL2.card_eq_lieOrd (by norm_num)
  have hm : 1 ≤ m := hL2.admissible.2.1
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hY : Nat.card (X ⧸ Subgroup.center X) = ordBC 2 (2 ^ n) :=
      hn.card_eq_lieOrd (by norm_num)
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two le_rfl hm hn.admissible.2.1
      (hX.symm.trans (hcard.symm.trans hY))
  · have hY : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n) :=
      hn.card_eq_lieOrd (by norm_num)
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA le_rfl hm le_rfl hn.admissible.2.1
      (hX.symm.trans (hcard.symm.trans hY))

@[expose] def J1NotSp4SU3 : Prop :=
  ∀ (X : Type) [Group X], IsJ1 X →
    Subgroup.center X = ⊥ ∧ (∀ n : ℕ, ¬ IsSp4 X n) ∧ (∀ n : ℕ, ¬ IsSU3 X n)

theorem uc22p21k_spU3Quot_of_shape {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (h : (∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n)) : SpU3Quot (Bar2 L) := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
    exact Or.inl ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv e hn⟩
  · exact Or.inr ⟨n, hn.2⟩

theorem uc22p21k_shape_not_list (hJ : J1NotSp4SU3) {M L : Subgroup G} (hL : L ∈ calC M)
    (hshape : (∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n)) :
    (∀ m : ℕ, ¬ IsL2 (Bar2 L) m) ∧ (∀ m : ℕ, ¬ IsSz (Bar2 L) m) ∧ ¬ IsJ1 (Bar2 L) := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hY : SpU3Quot (Bar2 L) := uc22p21k_spU3Quot_of_shape hq hshape
  refine ⟨uc22p21k_not_isL2 hq hY, uc22p21k_not_isSz hY, fun hj => ?_⟩
  obtain ⟨hZ, hsp, hsu⟩ := hJ (Bar2 L) hj
  rcases hshape with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hq hZ
    exact hsp n (CFSG.Blueprint.LieModel.of_mulEquiv e hn)
  · exact hsu n hn

theorem uc22p21k_spU3NotList (hJ : J1NotSp4SU3) (D : Data G) : SpU3NotList D :=
  fun _ hL hshape => uc22p21k_shape_not_list hJ hL hshape

end CFSG.LocalAnalysis.UniquenessCase.UC22

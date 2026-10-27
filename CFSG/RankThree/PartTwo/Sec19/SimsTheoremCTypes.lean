module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316Leaves
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge
import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard
import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallHeart

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

theorem card_quot_eq_of_surjective {L : Subgroup G} {T : Type*} [Group T] (α : L →* T)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 L) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card T :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem card_tildeU_eq_of_surjective {L : Subgroup G} {A : Type*} [AddGroup A]
    (β : blockU L →* Multiplicative A) (hβ : Function.Surjective β)
    (hker : β.ker = (blockZ L).subgroupOf (blockU L)) : Nat.card (tildeU L) = Nat.card A :=
  (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective β hβ)).toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_quot_of_isAltNaturalType {L : Subgroup G} {n : ℕ} (h : IsAltNaturalType L n) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact card_quot_eq_of_surjective α hα hker

theorem card_quot_of_isOmegaPlusType {L : Subgroup G} {m : ℕ} (h : IsOmegaPlusType L m) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (omegaPlusTwo m) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact card_quot_eq_of_surjective α hα hker

theorem card_quot_of_isOmegaMinusType {L : Subgroup G} {m : ℕ} (h : IsOmegaMinusType L m) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (omegaMinusTwo m) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact card_quot_eq_of_surjective α hα hker

theorem card_alternatingGroup_fin {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_alternatingGroup_fin_of_le_one {n : ℕ} (hn : n ≤ 1) :
    Nat.card (alternatingGroup (Fin n)) = 1 := by
  haveI : Subsingleton (alternatingGroup (Fin n)) := alternatingGroup_fin_subsingleton n (by omega)
  exact Nat.card_unique

theorem card_quot_of_isA7FourType {L : Subgroup G} (h : IsA7FourType L) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = 2520 := by
  obtain ⟨⟨α, hα, hker⟩, -⟩ := h
  rw [card_quot_eq_of_surjective α hα hker, card_alternatingGroup_fin (by norm_num)]
  decide

theorem card_quot_of_isA6Z3Type [Finite G] {L : Subgroup G} (h : IsA6Z3Type L) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = 1080 := by
  obtain ⟨⟨α, hα, -, hcard⟩, -⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
    card_alternatingGroup_fin (by norm_num), hcard] at h1
  have h6 : Nat.factorial 6 / 2 = 360 := by decide
  rw [h6] at h1
  have hpos : 0 < Nat.card (CFSG.pCore 2 L) := Nat.card_pos
  have : Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card (CFSG.pCore 2 L) =
      1080 * Nat.card (CFSG.pCore 2 L) := by
    rw [← h2, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem card_evenWeightOnes_even {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    Nat.card (evenWeightOnes n) = 2 := by
  have hmem : allOnes n ∈ evenWeight n := by
    show ∑ _i : Fin n, (1 : ZMod 2) = 0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_eq_zero_iff_even).mpr he
  let a : evenWeight n := ⟨allOnes n, hmem⟩
  have ha : (0 : evenWeight n) ≠ a := by
    intro h
    have := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
    exact zero_ne_one this
  have hset : ((evenWeightOnes n : AddSubgroup (evenWeight n)) : Set (evenWeight n)) = {0, a} := by
    ext z
    rw [SetLike.mem_coe, SimsItem316Small.mem_evenWeightOnes, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair ha]

theorem card_evenWeightOnes_odd {n : ℕ} (ho : Odd n) : Nat.card (evenWeightOnes n) = 1 := by
  have hbot : evenWeightOnes n = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [SimsItem316Small.mem_evenWeightOnes] at hz
    rcases hz with h | h
    · exact (AddSubgroup.mem_bot).mpr (Subtype.ext h)
    · exfalso
      have hz := z.2
      have hs : ∑ i, (z : Fin n → ZMod 2) i = 0 := hz
      rw [h] at hs
      simp only [allOnes, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at hs
      exact (Nat.not_even_iff_odd.mpr ho) ((ZMod.natCast_eq_zero_iff_even).mp hs)
  rw [hbot]
  exact Nat.card_unique

theorem card_altHeart_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    Nat.card (altHeart n) = 2 ^ (n - 2) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes n)
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight n (by omega),
    card_evenWeightOnes_even (by omega) he] at h
  have : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

theorem card_altHeart_odd {n : ℕ} (ho : Odd n) : Nat.card (altHeart n) = 2 ^ (n - 1) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes n)
  have hn : 1 ≤ n := by obtain ⟨k, rfl⟩ := ho; omega
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight n hn,
    card_evenWeightOnes_odd ho, mul_one] at h
  exact h.symm

@[expose] def IsFType (J : Subgroup G) : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ IsAltNaturalType J n) ∨ IsA7FourType J ∨
    (∃ m : ℕ, 3 ≤ m ∧ IsOmegaPlusType J m) ∨ (∃ m : ℕ, 2 ≤ m ∧ IsOmegaMinusType J m) ∨
      IsA6Z3Type J

theorem four_dvd_factorial_div_two {n : ℕ} (hn : 4 ≤ n) : 4 ∣ n.factorial / 2 := by
  have h24 : Nat.factorial 4 ∣ n.factorial := Nat.factorial_dvd_factorial hn
  have h8 : 8 ∣ n.factorial := dvd_trans (by decide) h24
  obtain ⟨k, hk⟩ := h8
  rw [hk, show 8 * k = 2 * (4 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 4 k

theorem two_le_mul_sub_one {m : ℕ} (hm : 3 ≤ m) : 6 ≤ m * (m - 1) :=
  le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul hm (by omega))

theorem two_le_succ_mul {m : ℕ} (hm : 2 ≤ m) : 6 ≤ (m + 1) * m :=
  le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul (by omega) hm)

theorem IsFType.four_dvd_card_quot [Finite G] {J : Subgroup G} (h : IsFType J) :
    4 ∣ Nat.card (J ⧸ CFSG.pCore 2 J) := by
  rcases h with ⟨n, hn, hA⟩ | hA | ⟨m, hm, hO⟩ | ⟨m, hm, hO⟩ | hA
  · rw [card_quot_of_isAltNaturalType hA, card_alternatingGroup_fin (by omega)]
    exact four_dvd_factorial_div_two (by omega)
  · rw [card_quot_of_isA7FourType hA]
    decide
  · rw [card_quot_of_isOmegaPlusType hO]
    obtain ⟨s, -, hs⟩ := exists_card_omegaPlusTwo hm
    rw [hs]
    have h4 : (4 : ℕ) ∣ 2 ^ (m * (m - 1)) := by
      have := pow_dvd_pow 2 (le_trans (by norm_num : 2 ≤ 6) (two_le_mul_sub_one hm))
      simpa using this
    exact Dvd.dvd.mul_right h4 s
  · rw [card_quot_of_isOmegaMinusType hO]
    obtain ⟨s, -, hs⟩ := exists_card_omegaMinusTwo hm
    rw [hs]
    have h4 : (4 : ℕ) ∣ 2 ^ ((m + 1) * m) := by
      have := pow_dvd_pow 2 (le_trans (by norm_num : 2 ≤ 6) (two_le_succ_mul hm))
      simpa using this
    exact Dvd.dvd.mul_right h4 s
  · rw [card_quot_of_isA6Z3Type hA]
    decide

theorem not_prime_of_four_dvd {k : ℕ} (h : 4 ∣ k) : ¬ k.Prime := by
  intro hp
  have h2 : 2 ∣ k := dvd_trans (by norm_num) h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  rw [← this] at h
  norm_num at h

theorem isQuasisimple_of_isFType [Finite G] {L : Subgroup G} (hS : IsShort L) (h : IsFType L) :
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) :=
  hS.quasisimple_or_prime.resolve_right (not_prime_of_four_dvd h.four_dvd_card_quot)

theorem not_isQuasisimple_of_isAltNaturalType_four {L : Subgroup G} (hA : IsAltNaturalType L 4)
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) : False := by
  obtain ⟨α, hα, hker, -⟩ := hA
  let e : (L ⧸ CFSG.pCore 2 L) ≃* alternatingGroup (Fin 4) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hperf : commutator (L ⧸ CFSG.pCore 2 L) = ⊤ := hq.1.commutator_eq_top
  have htop : commutator (alternatingGroup (Fin 4)) = ⊤ := by
    have h1 := congrArg (Subgroup.map e.toMonoidHom) hperf
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective] at h1
    rw [_root_.commutator_def]
    exact h1
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have hk := alternatingGroup.kleinFour_card_of_card_eq_four h4
  rw [alternatingGroup.kleinFour_eq_commutator h4, htop, Subgroup.card_top,
    card_alternatingGroup_fin (by norm_num)] at hk
  revert hk
  decide

theorem six_le_of_isAltNaturalType_even [Finite G] {L : Subgroup G} {n : ℕ} (hS : IsShort L)
    (hA : IsAltNaturalType L n) (he : Even n) : 6 ≤ n := by
  have hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) := by
    rcases hS.quasisimple_or_prime with hq | hp
    · exact hq
    · exfalso
      rw [card_quot_of_isAltNaturalType hA] at hp
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · rw [card_alternatingGroup_fin_of_le_one (by omega)] at hp
        exact Nat.not_prime_one hp
      · rw [card_alternatingGroup_fin hge] at hp
        rcases Nat.lt_or_ge n 4 with hlt4 | hge4
        · have h2 : n = 2 := by obtain ⟨k, hk⟩ := he; omega
          subst h2
          exact Nat.not_prime_one hp
        · exact not_prime_of_four_dvd (four_dvd_factorial_div_two hge4) hp
  have h3 := three_le_of_isAltNaturalType hq hA
  by_contra hlt
  have h4 : n = 4 := by obtain ⟨k, hk⟩ := he; omega
  subst h4
  exact not_isQuasisimple_of_isAltNaturalType_four hA hq

theorem isFType_of_isSolomonTypes [Finite G] {L : Subgroup G} (hS : IsShort L)
    (h : IsSolomonTypes L) : IsFType L := by
  rcases h with ⟨n, he, hA⟩ | h7
  · exact Or.inl ⟨n, six_le_of_isAltNaturalType_even hS hA he, hA⟩
  · exact Or.inr (Or.inl h7)

theorem isFType_of_isHaradaHallTypes {L : Subgroup G} (h : IsHaradaHallTypes L) : IsFType L := by
  rcases h with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | h6
  · exact Or.inr (Or.inr (Or.inl ⟨m, by omega, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

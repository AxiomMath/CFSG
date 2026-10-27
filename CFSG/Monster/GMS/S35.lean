module

public import CFSG.Monster.GMS.S347
public import CFSG.Monster.GMS.S342

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Defs

variable {G : Type*} [Group G]

inductive GMSType
  | twoA
  | twoB
  | threeA
  | threeC
  | fourA
  | fourB
  | fiveA
  | sixA
  deriving DecidableEq

@[expose] def typeSet (a z₀ x : G) : GMSType → Set G
  | .twoA => twoANbr a x
  | .twoB => twoBNbr a z₀ x
  | .fourA => fourANbr a z₀ x
  | .fourB => fourBNbr a x
  | .sixA => sixANbr a x
  | .threeA => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 0}
  | .threeC => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 1}
  | .fiveA => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 2}

@[expose] def gammaNbr (a z₀ x : G) : Set G := insert x (⋃ K, typeSet a z₀ x K)

@[expose] def perpSet (a x : G) : Set G := insert x (twoANbr a x)

@[expose] def IsLine (a : G) (l : Set G) : Prop :=
  ∃ x y : G, l = {x, y, x * y} ∧ IsConj a x ∧ IsConj a y ∧ IsConj a (x * y)

@[expose] def IsLineOfType (a z₀ b : G) (l : Set G) (K K' K'' : GMSType) : Prop :=
  ∃ x y : G, l = {x, y, x * y} ∧ IsConj a (x * y) ∧ x ∈ typeSet a z₀ b K ∧
    y ∈ typeSet a z₀ b K' ∧ x * y ∈ typeSet a z₀ b K''

theorem isConj_of_mem_typeSet {a z₀ x y : G} {K : GMSType} (h : y ∈ typeSet a z₀ x K) :
    IsConj a y := by
  cases K <;> first
    | exact h.1.1
    | exact h.1

theorem commute_of_mul_self {p b : G} (hp : p * p = 1) (hb : b * b = 1)
    (hpb : (p * b) * (p * b) = 1) : p * b = b * p := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : p * b = (p * b)⁻¹ := eq_inv_of_mul_eq_one_left hpb
  rw [h1, mul_inv_rev, hpi, hbi]

end Defs


section Cover

variable {G : Type*} [Group G]

@[expose] def GammaCover (a z₀ : G) : Prop :=
  ∀ x y : G, IsConj a x → IsConj a y → y ∈ gammaNbr a z₀ x

@[expose] def OddPairsCommonTwoB (a z₀ : G) : Prop :=
  ∀ x y : G, IsConj a x → IsConj a y → y ≠ x → Odd (orderOf (x * y)) → y ∈ oddNbr a z₀ x

end Cover

section OneSix

variable {G : Type} [Group G] {d₀ : B}

theorem even_orderOf_of_mem_twoANbr {a z₀ : G} (hnc : ¬ IsConj a z₀) (ha2 : orderOf a = 2)
    (hz2 : orderOf z₀ = 2) {x b : G} (hxA : IsConj a x) (hb : b ∈ twoANbr a x)
    (hab : b ∈ twoBNbr a z₀ a) : Even (orderOf (a * x)) := by
  by_contra hodd
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha2
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hxA).symm.trans ha2)
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hb.1).symm.trans ha2)
  have hab2 : (a * b) * (a * b) = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hab.2).symm.trans hz2)
  have hxb2 : (x * b) * (x * b) = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hb.2).symm.trans ha2)
  have hab' : a * b = b * a := commute_of_mul_self haa hbb hab2
  have hxb' : x * b = b * x := commute_of_mul_self hxx hbb hxb2
  set g := (a * x) ^ k with hg
  have hga : g * a * g⁻¹ = x := by
    rw [hg, (conj_pow_mul_self haa hxx k).1]
    have h1 : (a * x) ^ (2 * k) * (a * x) = 1 := by
      rw [← pow_succ, ← hk, pow_orderOf_eq_one]
    have h2 : (a * x) ^ (2 * k) = (a * x)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right haa,
      mul_assoc, haa, mul_one]
  have hgb : g * b = b * g := by
    have hc : Commute (a * x) b :=
      Commute.mul_left (show Commute a b from hab') (show Commute x b from hxb')
    exact (hc.pow_left k).eq
  have hconj : g * (a * b) * g⁻¹ = x * b := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = x * b := by rw [hga, hgb, mul_assoc, mul_inv_cancel, mul_one]
  exact hnc (hb.2.trans ((isConj_iff.mpr ⟨g, hconj⟩).symm.trans hab.2.symm))

theorem exists_orderOf_eq_two_pow
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x w : G} (hxA : IsConj a x)
    (hw : IsConj z₀ w) (haw : a * w = w * a) (hwa : IsConj a (a * w))
    (hxw : x ∈ Subgroup.centralizer ({w} : Set G)) : ∃ k, orderOf (a * x) = 2 ^ k := by
  have haQ : a ∈ leechQ w := mem_leechQ_of_isConj_mul hSLS hTV hL hG (IsConj.refl a) hw haw hwa
  have hxx : x * x = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hxA).symm.trans hG.1.1)
  have hsq : (a * x) ^ 2 ∈ leechQ w := by
    have h1 : x * a * x⁻¹ ∈ leechQ w := conj_mem_leechQ hxw haQ
    have e : (a * x) ^ 2 = a * (x * a * x⁻¹) := by
      rw [pow_two, inv_eq_of_mul_eq_one_right hxx]; group
    rw [e]
    exact mul_mem haQ h1
  have hp : IsPGroup 2 ↥(leechQ w) := IsPGroup.of_card (hG.2.of_isConj hw).card_leechQ
  obtain ⟨m, hm⟩ := hp ⟨(a * x) ^ 2, hsq⟩
  have hm' : (a * x) ^ (2 ^ (m + 1)) = 1 := by
    have := congrArg Subtype.val hm
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have hdvd : orderOf (a * x) ∣ 2 ^ (m + 1) := orderOf_dvd_of_pow_eq_one hm'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩


theorem gammaCover_of_oddPairsCommonTwoB
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) (hT3 : BabyTableIII) (hT4B : BabyTableIV)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    (hodd : OddPairsCommonTwoB a z₀) : GammaCover a z₀ := by
  intro x y hx hy
  by_cases hyx : y = x
  · exact Or.inl hyx
  refine Or.inr (Set.mem_iUnion.2 ?_)
  rcases Nat.even_or_odd (orderOf (x * y)) with hev | hod
  · rcases table7_cases hSLS hTV hL hT3 hT4B hG hx hy hev with h | h | h | h | h
    · exact ⟨.twoA, h⟩
    · exact ⟨.twoB, h⟩
    · exact ⟨.fourA, h⟩
    · exact ⟨.fourB, h⟩
    · exact ⟨.sixA, h⟩
  · have hmem := hodd x y hx hy hyx hod
    obtain ⟨k, hk, -⟩ := s348_type hSLS hTV hL hLO hT4 hG hx hmem
    match k, hk with
    | 0, hk => exact ⟨.threeA, hmem, hk⟩
    | 1, hk => exact ⟨.threeC, hmem, hk⟩
    | 2, hk => exact ⟨.fiveA, hmem, hk⟩

end OneSix

end CFSG.Monster.GMS

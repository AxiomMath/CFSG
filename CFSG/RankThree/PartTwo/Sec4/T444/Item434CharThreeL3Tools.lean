module

public import CFSG.LocalAnalysis.SectionRank.OddCover.LinearThree
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open scoped MatrixGroups

section Heis

variable {K : Type} [Field K]

@[expose] def uSL (a b c : K) : SL(3, K) :=
  ⟨CFSG.SectionRank.OddCover.u3Mat a b c, CFSG.SectionRank.OddCover.det_u3Mat a b c⟩

theorem coe_uSL (a b c : K) :
    ((uSL a b c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = CFSG.SectionRank.OddCover.u3Mat a b c :=
  rfl

theorem uSL_mul (a b c a' b' c' : K) :
    uSL a b c * uSL a' b' c' = uSL (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (CFSG.SectionRank.OddCover.u3Mat_mul a b c a' b' c')

theorem uSL_zero : uSL (0 : K) 0 0 = 1 :=
  Subtype.ext CFSG.SectionRank.OddCover.u3Mat_zero

theorem uSL_inv (a b c : K) : (uSL a b c)⁻¹ = uSL (-a) (-b) (a * b - c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [uSL_mul, ← uSL_zero]
  congr 1 <;> ring

theorem uSL_inj {a b c a' b' c' : K} (h : uSL a b c = uSL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_uSL] at h'
  exact ⟨by simpa [CFSG.SectionRank.OddCover.u3Mat] using congrFun (congrFun h' 0) 1,
    by simpa [CFSG.SectionRank.OddCover.u3Mat] using congrFun (congrFun h' 1) 2,
    by simpa [CFSG.SectionRank.OddCover.u3Mat] using congrFun (congrFun h' 0) 2⟩

theorem uSL_pow_three [CharP K 3] (a b c : K) : uSL a b c ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [pow_three, uSL_mul, uSL_mul, ← uSL_zero]
  have e1 : a + (a + a) = 0 := by linear_combination a * h3
  have e2 : b + (b + b) = 0 := by linear_combination b * h3
  have e3 : c + (c + c + a * b) + a * (b + b) = 0 := by linear_combination (c + a * b) * h3
  rw [e1, e2, e3]

theorem uSL_commute_iff (a b c a' b' c' : K) :
    uSL a b c * uSL a' b' c' = uSL a' b' c' * uSL a b c ↔ a * b' = a' * b := by
  rw [uSL_mul, uSL_mul]
  constructor
  · intro h
    obtain ⟨-, -, h3⟩ := uSL_inj h
    linear_combination h3
  · intro h
    have e1 : a + a' = a' + a := add_comm _ _
    have e2 : b + b' = b' + b := add_comm _ _
    have e3 : c + c' + a * b' = c' + c + a' * b := by linear_combination h
    rw [e1, e2, e3]

variable (K) in
@[expose] def heis : Subgroup SL(3, K) where
  carrier := {g | ∃ a b c : K, g = uSL a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uSL_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, uSL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, uSL_inv a b c⟩

theorem card_heis [Finite K] : Nat.card (heis K) = Nat.card K ^ 3 := by
  let φ : K × K × K → heis K := fun v => ⟨uSL v.1 v.2.1 v.2.2, _, _, _, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uSL_inj (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, hg⟩ := g.2
      exact ⟨(a, b, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod]
  ring

@[expose] def lineSub (a₀ b₀ : K) : Subgroup SL(3, K) where
  carrier := {g | ∃ s c : K, g = uSL (s * a₀) (s * b₀) c}
  mul_mem' := by
    rintro _ _ ⟨s, c, rfl⟩ ⟨t, d, rfl⟩
    refine ⟨s + t, c + d + s * a₀ * (t * b₀), ?_⟩
    rw [uSL_mul]
    congr 1 <;> ring
  one_mem' := ⟨0, 0, by rw [zero_mul, zero_mul, uSL_zero]⟩
  inv_mem' := by
    rintro _ ⟨s, c, rfl⟩
    refine ⟨-s, s * a₀ * (s * b₀) - c, ?_⟩
    rw [uSL_inv]
    congr 1 <;> ring

theorem lineSub_le_heis (a₀ b₀ : K) : lineSub a₀ b₀ ≤ heis K := by
  rintro _ ⟨s, c, rfl⟩
  exact ⟨_, _, _, rfl⟩

theorem lineSub_commute {a₀ b₀ : K} {x y : SL(3, K)} (hx : x ∈ lineSub a₀ b₀)
    (hy : y ∈ lineSub a₀ b₀) : x * y = y * x := by
  obtain ⟨s, c, rfl⟩ := hx
  obtain ⟨t, d, rfl⟩ := hy
  rw [uSL_commute_iff]
  ring

theorem isElemAbelian_lineSub [CharP K 3] (a₀ b₀ : K) :
    CFSG.Assembly.IsElemAbelian 3 (lineSub a₀ b₀) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (lineSub_commute x.2 y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨s, c, rfl⟩ := hx
  exact uSL_pow_three _ _ _

theorem card_lineSub [Finite K] {a₀ b₀ : K} (h : a₀ ≠ 0 ∨ b₀ ≠ 0) :
    Nat.card (lineSub a₀ b₀) = Nat.card K ^ 2 := by
  let φ : K × K → lineSub a₀ b₀ := fun v => ⟨uSL (v.1 * a₀) (v.1 * b₀) v.2, v.1, v.2, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun v w hvw => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uSL_inj (congrArg Subtype.val hvw)
      have hs : v.1 = w.1 := by
        rcases h with ha | hb
        · exact mul_right_cancel₀ ha h1
        · exact mul_right_cancel₀ hb h2
      exact Prod.ext hs h3
    · obtain ⟨s, c, hg⟩ := g.2
      exact ⟨(s, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, sq]

theorem exists_le_lineSub {P : Subgroup SL(3, K)} (hP : P ≤ heis K)
    (hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ a₀ b₀ : K, (a₀ ≠ 0 ∨ b₀ ≠ 0) ∧ P ≤ lineSub a₀ b₀ := by
  by_cases hZ : ∀ x ∈ P, ∃ c : K, x = uSL 0 0 c
  · refine ⟨1, 0, Or.inl one_ne_zero, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := hZ x hx
    exact ⟨0, c, by rw [zero_mul, zero_mul]⟩
  push Not at hZ
  obtain ⟨x, hxP, hxZ⟩ := hZ
  obtain ⟨a, b, c, rfl⟩ := hP hxP
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hab
    push Not at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact hxZ c rfl
  refine ⟨a, b, hab, fun y hy => ?_⟩
  obtain ⟨a', b', c', rfl⟩ := hP hy
  have hcomm := (uSL_commute_iff a b c a' b' c').mp (hc _ hxP _ hy)
  rcases hab with ha | hb
  · refine ⟨a' / a, c', ?_⟩
    have e1 : a' / a * a = a' := div_mul_cancel₀ a' ha
    have e2 : a' / a * b = b' := by
      rw [div_mul_eq_mul_div, div_eq_iff ha]
      linear_combination -hcomm
    rw [e1, e2]
  · refine ⟨b' / b, c', ?_⟩
    have e1 : b' / b * a = a' := by
      rw [div_mul_eq_mul_div, div_eq_iff hb]
      linear_combination hcomm
    have e2 : b' / b * b = b' := div_mul_cancel₀ b' hb
    rw [e1, e2]

end Heis

section CharThree

variable (K : Type) [Field K] [CharP K 3]

theorem eq_one_of_pow_three_eq_one {K : Type} [Field K] [CharP K 3] {r : K} (hr : r ^ 3 = 1) :
    r = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h : (r - 1) ^ 3 = 0 := by linear_combination hr - (r ^ 2 - r) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem center_SL_three_eq_bot : Subgroup.center SL(3, K) = ⊥ :=
  Sec4.center_specialLinearGroup_eq_bot fun _ hr => eq_one_of_pow_three_eq_one hr

@[expose] noncomputable def slEquivProjectiveSL :
    SL(3, K) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
  ((QuotientGroup.quotientMulEquivOfEq (show
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K = ⊥ by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      center_SL_three_eq_bot])).trans QuotientGroup.quotientBot).symm

@[expose] noncomputable def slEquivProjSL : SL(3, K) ≃* CFSG.Assembly.RankThreeEven.projSL 3 K :=
  (slEquivProjectiveSL K).trans (Sec4.projSLEquivProjectiveSL 3 K).symm

end CharThree

section Galois

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

variable {e : ℕ}

theorem card_outer_SL_three_dvd (he : 1 ≤ e) :
    Nat.card (Outer SL(3, GaloisField 3 e)) ∣ 2 * e := by
  have h := higher_linear_outer_order_divides_field_gcd_bound
    Nat.prime_three he le_rfl (GaloisField.card 3 e (by omega))
  have hg : Nat.gcd 3 (3 ^ e - 1) = 1 := by
    rw [← Nat.Coprime]
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have h1 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    have h2 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [hg, mul_one] at h
  rwa [Nat.card_congr (equivalence (slEquivProjectiveSL (GaloisField 3 e))).toEquiv]

theorem factorization_card_SL_three (he : e ≠ 0) :
    (Nat.card SL(3, GaloisField 3 e)).factorization 3 = 3 * e := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    GaloisField.card 3 e he, show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num), show 3 * (3 - 1) / 2 = 3 by norm_num]
  set m := ((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 - 1) with hm_def
  have hm : ¬ 3 ∣ m := by
    intro h3
    have h1 : 3 ∣ (3 ^ e) ^ 2 := dvd_pow (dvd_pow_self 3 he) two_ne_zero
    have h1' : 3 ∣ (3 ^ e) ^ 3 := dvd_pow (dvd_pow_self 3 he) (by norm_num)
    have h2 : 1 ≤ (3 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h2' : 1 ≤ (3 ^ e) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h <;> omega
  rw [show (3 ^ e) ^ 3 * m = 3 ^ (3 * e) * m by rw [← pow_mul, mul_comm e 3]]
  exact Item434AltPerm.factorization_three_pow_mul (3 * e) hm

end Galois

end CFSG.RankThree.PartTwo.Sec4.Item434CharThree

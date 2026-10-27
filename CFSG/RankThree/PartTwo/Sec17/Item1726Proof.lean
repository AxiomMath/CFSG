module

import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

section OmegaTwo

variable {G : Type*} [Group G]

theorem mul_pow_of_commutator_central {x y z : G} (hyx : y * x = x * y * z)
    (hzx : z * x = x * z) (hzy : z * y = y * z) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * z ^ (∑ i ∈ Finset.range n, i) := by
  have hz : ∀ m : ℕ, y ^ m * x = x * y ^ m * z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * x = y * (y ^ m * x) := by rw [pow_succ', mul_assoc]
        _ = y * (x * y ^ m * z ^ m) := by rw [ih]
        _ = (y * x) * y ^ m * z ^ m := by group
        _ = x * y * z * y ^ m * z ^ m := by rw [hyx]
        _ = x * y * (z * y ^ m) * z ^ m := by group
        _ = x * y * (y ^ m * z) * z ^ m := by
            rw [(Commute.pow_right (show Commute z y from hzy) m).eq]
        _ = x * y ^ (m + 1) * z ^ (m + 1) := by rw [pow_succ', pow_succ']; group
  induction n with
  | zero => simp
  | succ n ih =>
    set t := ∑ i ∈ Finset.range n, i with ht
    have hzxt : Commute (z ^ t) x := Commute.pow_left hzx _
    have hzyt : Commute (z ^ (n + t)) y := Commute.pow_left hzy _
    rw [Finset.sum_range_succ, ← ht]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * z ^ t * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * (z ^ t * x) * y := by group
      _ = x ^ n * y ^ n * (x * z ^ t) * y := by rw [hzxt.eq]
      _ = x ^ n * (y ^ n * x) * z ^ t * y := by group
      _ = x ^ n * (x * y ^ n * z ^ n) * z ^ t * y := by rw [hz n]
      _ = x ^ (n + 1) * y ^ n * z ^ (n + t) * y := by rw [pow_succ, pow_add]; group
      _ = x ^ (n + 1) * y ^ n * (z ^ (n + t) * y) := by group
      _ = x ^ (n + 1) * y ^ n * (y * z ^ (n + t)) := by rw [hzyt.eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * z ^ (t + n) := by rw [pow_succ, add_comm n t]; group

theorem dvd_sum_range_id {p : ℕ} (hp : Odd p) : p ∣ ∑ i ∈ Finset.range p, i := by
  have h := Finset.sum_range_id_mul_two p
  have h2 : p ∣ (∑ i ∈ Finset.range p, i) * 2 := h ▸ Dvd.intro _ rfl
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hp.not_two_dvd_nat))
    h2

@[expose] def omegaOneZTwo (p : ℕ) (hp : Odd p) (Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Q ∧ x ^ p = 1 ∧
    ∀ g ∈ Q, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.centralizer (Q : Set G)}
  mul_mem' := by
    rintro x y ⟨hxQ, hxp, hxc⟩ ⟨hyQ, hyp, hyc⟩
    refine ⟨Q.mul_mem hxQ hyQ, ?_, fun g hg => ?_⟩
    ·
      set z := y⁻¹ * x⁻¹ * y * x with hz
      have hzC : z ∈ Subgroup.centralizer (Q : Set G) := by
        have hc := hxc y⁻¹ (Q.inv_mem hyQ)
        rw [inv_inv] at hc
        have hcx : x * (x * y⁻¹ * x⁻¹ * y) = (x * y⁻¹ * x⁻¹ * y) * x :=
          (Subgroup.mem_centralizer_iff.mp hc x hxQ)
        have e : z = x⁻¹ * (x * y⁻¹ * x⁻¹ * y) * x := by rw [hz]; group
        rw [e, mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hc
      have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hzC x hxQ).symm
      have hzy : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hzC y hyQ).symm
      have hyx : y * x = x * y * z := by rw [hz]; group
      have hzp : z ^ p = 1 := by
        have hxz : y⁻¹ * x * y⁻¹⁻¹ = x * z⁻¹ := by rw [hz]; group
        have h1 : (y⁻¹ * x * y⁻¹⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
        rw [hxz, (Commute.inv_right (show Commute x z from hzx.symm)).mul_pow, hxp, one_mul,
          inv_pow] at h1
        exact inv_eq_one.mp h1
      rw [mul_pow_of_commutator_central hyx hzx hzy p, hxp, hyp, one_mul, one_mul]
      obtain ⟨k, hk⟩ := dvd_sum_range_id hp
      rw [hk, pow_mul, hzp, one_pow]
    ·
      have h1 := hyc g hg
      have h2 := hxc g hg
      have e : x * y * g * (x * y)⁻¹ * g⁻¹ =
          x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ * (x * g * x⁻¹ * g⁻¹) := by group
      rw [e]
      have hc : x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ = y * g * y⁻¹ * g⁻¹ := by
        rw [Subgroup.mem_centralizer_iff.mp h1 x hxQ, mul_inv_cancel_right]
      rw [hc]
      exact Subgroup.mul_mem _ h1 h2
  one_mem' := ⟨Q.one_mem, one_pow p, fun g _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxQ, hxp, hxc⟩
    refine ⟨Q.inv_mem hxQ, by rw [inv_pow, hxp, inv_one], fun g hg => ?_⟩
    have h1 := Subgroup.inv_mem _ (hxc g hg)
    have e : (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ := by group
    rw [e] at h1
    have hcx : x * (g * x * g⁻¹ * x⁻¹) = (g * x * g⁻¹ * x⁻¹) * x :=
      Subgroup.mem_centralizer_iff.mp h1 x hxQ
    have e2 : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ = x⁻¹ * (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e2, mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
    exact h1

end OmegaTwo

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G} {s : G}

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian p F)
    (hEF : E ≤ F) : CFSG.Assembly.IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

theorem inf_zpowers_eq_bot_of_prime {H : Subgroup G} {x : G} (hp : p.Prime) (hx : orderOf x = p)
    (hxH : x ∉ H) : H ⊓ Subgroup.zpowers x = ⊥ := by
  have hdvd : Nat.card (H ⊓ Subgroup.zpowers x : Subgroup G) ∣ p := by
    rw [← hx, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hxH
    have heq : H ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hx])
    exact (heq ▸ inf_le_left : Subgroup.zpowers x ≤ H) (Subgroup.mem_zpowers x)

theorem Sec17Y1.not_card_cube (h : Sec17Y1 G A c L Y₀ Y₁ S p P) {E : Subgroup G}
    (hEY : E ≤ Y₁) (hE : CFSG.Assembly.IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : CFSG.Open.pCoreOf 2 Y₁ ≠ ⊥ := h.mem_y1Star.prop.1.1.2
  set X := Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₁ : Subgroup G) : Set G) with hXdef
  have hX : CFSG.Assembly.IsTwoLocal X :=
    ⟨_, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₁, rfl⟩
  have hYX : Y₁ ≤ X :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₁)
  have hbdd : BddAbove {k | ∃ E' : Subgroup G, E' ≤ X ∧ CFSG.Assembly.IsElemAbelian p E' ∧
      Nat.card E' = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E', -, -, hk⟩
    have h1 : k < p ^ k := Nat.lt_pow_self h.p_prime.one_lt
    have h2 : Nat.card E' ≤ Nat.card G := Subgroup.card_le_card_group E'
    change k ≤ Nat.card G
    omega
  have h1 : 3 ≤ CFSG.Assembly.pRank p X := le_csSup hbdd ⟨E, hEY.trans hYX, hE, hcard⟩
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank h.p_prime.one_lt hX
  have h3 := h.localRank_lt p h.p_prime h.three_lt_p
  omega

omit [Finite G] in
theorem yI_one (Y₁ : Subgroup G) (w : G) : yI Y₁ w 1 = Y₁ := by
  simp only [yI, Nat.sub_self, pow_zero]
  exact map_conj_one Y₁

end Data

end CFSG.RankThree.PartTwo.Sec17

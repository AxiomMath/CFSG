module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LieType.Ree

open Polynomial CFSG.Blueprint

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem isPGroup_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : IsPGroup 2 (suzukiU a K) := by
  have hcard : Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 :=
    (suzuki_unipotent_structure (a := a) (K := K) hK).2.1
  refine IsPGroup.of_card (n := (2 * a + 1) * 2) ?_
  rw [hcard, pow_mul]

theorem not_dvd_index_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 2 ∣ (suzukiU a K).index := by
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hcard : Nat.card (suzukiU a K) = q ^ 2 := by
    rw [hq]
    exact (suzuki_unipotent_structure (a := a) (K := K) hK).2.1
  have hq1 : 1 ≤ q := by
    rw [hq]
    have := pow_pos (by norm_num : 0 < 2) (2 * a + 1)
    omega
  have hindex : (suzukiU a K).index = (q - 1) * (q ^ 2 + 1) := by
    have h := (suzukiU a K).card_mul_index
    rw [hcard] at h
    have hG : Nat.card (suzukiGroup a K) = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      simpa [hq] using suzuki_order (a := a) (K := K) hK
    rw [hG, mul_assoc] at h
    exact Nat.mul_left_cancel (pow_pos (by omega : 0 < q) 2) h
  have hq_even : Even q := by
    rw [hq]
    exact Even.pow_of_ne_zero even_two (by omega)
  have hq_sub : Odd (q - 1) := Nat.Even.sub_odd hq1 hq_even odd_one
  have hq2 : Odd (q ^ 2 + 1) := (hq_even.pow_of_ne_zero (by norm_num : 2 ≠ 0)).add_one
  have hidx : Odd (suzukiU a K).index := by
    rw [hindex, Nat.odd_mul]
    exact ⟨hq_sub, hq2⟩
  exact hidx.not_two_dvd_nat

noncomputable def suzukiUSylow
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Sylow 2 (suzukiGroup a K) :=
  (isPGroup_suzukiU hK).toSylow (not_dvd_index_suzukiU hK)

theorem suzuki_center_suzukiU
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center (suzukiU a K) = (suzukiZ0 a K).subgroupOf (suzukiU a K) := by
  obtain ⟨-, -, -, -, -, hcent, -, -, -⟩ :=
    suzuki_unipotent_structure (a := a) (K := K) hK
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff (a := a) (K := K) hK).1 z.2
    by_cases hu : u = 0
    · rw [mem_suzukiZ0_iff (a := a) (K := K) hK]
      exact ⟨v, by simpa [hu] using huv⟩
    · exfalso
      have hθ_lt : 2 ^ (a + 1) < Nat.card K := by
        rw [hK]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hdeg : (Polynomial.X ^ 2 ^ (a + 1) - Polynomial.X : K[X]).natDegree <
          Cardinal.mk K := by
        rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq (K' := K) (p := 2) (n := a + 1)
          (by omega) (by norm_num)]
        rw [← Nat.cast_card (α := K)]
        exact_mod_cast hθ_lt
      obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
        (Polynomial.X ^ 2 ^ (a + 1) - Polynomial.X : K[X])
        (FiniteField.X_pow_card_pow_sub_X_ne_zero (K' := K) (p := 2) (n := a + 1)
          (by omega) (by norm_num)) hdeg
      have ht' : t ^ 2 ^ (a + 1) - t ≠ 0 := by
        simpa [Polynomial.eval_sub, Polynomial.eval_pow] using ht
      have ht_ne : t ^ 2 ^ (a + 1) ≠ t := sub_ne_zero.mp ht'
      let c : K := u * t
      have hcomm : (z : suzukiGroup a K) * suzukiSElt a K c 0 =
          suzukiSElt a K c 0 * (z : suzukiGroup a K) := by
        have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz
          (⟨suzukiSElt a K c 0, suzukiSElt_mem_suzukiU a K c 0⟩ : suzukiU a K))
        simpa using h.symm
      have hprod : suzukiSElt a K u v * suzukiSElt a K c 0 =
          suzukiSElt a K c 0 * suzukiSElt a K u v := by
        simpa [← huv] using hcomm
      rw [suzukiSElt_mul (a := a) (K := K) hK u v c 0,
        suzukiSElt_mul (a := a) (K := K) hK c 0 u v] at hprod
      have hsecond : v + u ^ 2 ^ (a + 1) * c = v + c ^ 2 ^ (a + 1) * u := by
        simpa using (suzukiSElt_inj.1 hprod).2
      have heq : u ^ 2 ^ (a + 1) * c = c ^ 2 ^ (a + 1) * u := add_left_cancel hsecond
      have heq' : u ^ 2 ^ (a + 1) * (u * t) = (u * t) ^ 2 ^ (a + 1) * u := by
        simpa [c] using heq
      have hpow : u ^ (2 ^ (a + 1) + 1) * t =
          u ^ (2 ^ (a + 1) + 1) * t ^ 2 ^ (a + 1) := by
        rw [pow_succ, mul_assoc, heq', mul_pow]
        ring
      have ht_eq : t = t ^ 2 ^ (a + 1) :=
        mul_left_cancel₀ (pow_ne_zero _ hu) hpow
      exact ht_ne ht_eq.symm
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent (z : suzukiGroup a K) (Subgroup.mem_subgroupOf.mp hz)
      (g : suzukiGroup a K) g.2).symm

end CFSG.LieType.Ree

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Open

theorem card_center_sylow_of_isSzGp
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsSzGp Y n) (P : Sylow 2 Y) :
    Nat.card (Subgroup.center (P : Subgroup Y)) = 2 ^ n := by
  unfold IsSzGp CFSG.Blueprint.SuzukiModel at hY
  obtain ⟨-, a, ha, K, hKfield, hKfin, hn, hKcard, ⟨e⟩⟩ := hY
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by
    rw [hKcard, hn]
  have hcenterU : Nat.card (Subgroup.center (suzukiU a K)) = 2 ^ n := by
    have hZ0card : Nat.card (suzukiZ0 a K) = Nat.card K := by
      rw [← SetLike.coe_sort_coe, coe_suzukiZ0 (a := a) (K := K) hK,
        Nat.card_range_of_injective (fun x y h => (suzukiSElt_inj.1 h).2)]
    have hZ0sub : Nat.card ((suzukiZ0 a K).subgroupOf (suzukiU a K)) = Nat.card K := by
      rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (suzukiZ0_le_suzukiU (a := a) (K := K))).toEquiv]
      exact hZ0card
    rw [suzuki_center_suzukiU (a := a) (K := K) ha hK]
    exact hZ0sub.trans hKcard
  have hcenterQ (Q : Sylow 2 (suzukiGroup a K)) :
      Nat.card (Subgroup.center (Q : Subgroup (suzukiGroup a K))) =
        Nat.card (Subgroup.center (suzukiU a K)) := by
    haveI : Finite (Subgroup (suzukiGroup a K)) :=
      Finite.of_injective (fun H : Subgroup (suzukiGroup a K) =>
        (H : Set (suzukiGroup a K))) SetLike.coe_injective
    haveI : Finite (Sylow 2 (suzukiGroup a K)) :=
      Finite.of_injective (fun Q : Sylow 2 (suzukiGroup a K) =>
        (Q : Subgroup (suzukiGroup a K))) (fun _ _ h => Sylow.ext h)
    have hUsylow : ((suzukiUSylow hK : Sylow 2 (suzukiGroup a K)) :
        Subgroup (suzukiGroup a K)) = suzukiU a K := rfl
    calc Nat.card (Subgroup.center (Q : Subgroup (suzukiGroup a K)))
        = Nat.card (Subgroup.center ((suzukiUSylow hK : Sylow 2 (suzukiGroup a K)) :
            Subgroup (suzukiGroup a K))) :=
          (Nat.card_congr
            (Subgroup.centerCongr (Sylow.equiv (suzukiUSylow hK) Q)).toEquiv).symm
      _ = Nat.card (Subgroup.center (suzukiU a K)) := by rw [hUsylow]
  let Q : Sylow 2 (suzukiGroup a K) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hQcoe : (Q : Subgroup (suzukiGroup a K)) =
      (P : Subgroup Y).map (e : Y →* suzukiGroup a K) :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  have hcenterP : Nat.card (Subgroup.center (P : Subgroup Y)) =
      Nat.card (Subgroup.center (Q : Subgroup (suzukiGroup a K))) := by
    rw [hQcoe]
    exact Nat.card_congr
      (Subgroup.centerCongr (MulEquiv.subgroupMap e (P : Subgroup Y))).toEquiv
  exact hcenterP.trans ((hcenterQ Q).trans hcenterU)


theorem w3Lem85TwoGap1_of_PSU3
    (hU3 : ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), IsPSUGp Y 3 n →
      ∀ A : Subgroup (MulAut Y), IsElemAbelian 2 A → Nat.card A ≤ 2 ^ (n + 1)) :
    W3Lem85TwoGap1 :=
  ⟨hU3, fun Y _ _ n hY P => card_center_sylow_of_isSzGp hY P⟩

end CFSG.LocalAnalysis.WeakClosure81

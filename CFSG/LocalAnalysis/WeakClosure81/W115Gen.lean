module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22ReducibleMBound
import CFSG.Mathlib.Arithmetic.TwoPowModThree
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Elem
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Quasithin.H13.A5.M22Hat
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
    (card_modEq_fixSub card_modEq_subgroup)

private theorem w115_rkIdx_finset_inf_le {ι : Type*} {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (s : Finset ι) (A : ι → Subgroup W) :
    rkIdx (s.inf A) ≤ ∑ i ∈ s, rkIdx (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [rkIdx]
  | insert a s ha ih =>
      rw [Finset.inf_insert, Finset.sum_insert ha]
      exact le_trans (rkIdx_inf_le hW (A a) (s.inf A)) (add_le_add le_rfl ih)

theorem w115_fixV_eq_bot_of_isIrrOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L ⊤ ⊥) (hL : L ≠ ⊥) : fixV L = ⊥ := by
  rcases hirr.2.2.2 (fixV L) (fun g hg u hu => by rw [hu g hg]; exact hu) bot_le le_top with h | h
  · exact h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext w
    have : w ∈ fixV L := by rw [h]; trivial
    exact this g hg

theorem w115_rk_le_four_mul {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : fixV L = ⊥) {s : MulAut W} (c : Fin 4 → MulAut W)
    (hc : ∀ i, ∃ g : MulAut W, c i = g * s * g⁻¹)
    (hgen : L ≤ Subgroup.closure (Set.range c)) :
    rk W ≤ 4 * rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  have hle : (Finset.univ : Finset (Fin 4)).inf (fun i => fixV (Subgroup.zpowers (c i))) ≤
      fixV (Subgroup.closure (Set.range c)) := by
    intro w hw
    rw [mem_fixV]
    intro x hx
    have hci : ∀ i : Fin 4, c i w = w := fun i =>
      mem_fixV_zpowers_iff_apply.mp
        ((show (Finset.univ : Finset (Fin 4)).inf
            (fun j => fixV (Subgroup.zpowers (c j))) ≤ fixV (Subgroup.zpowers (c i)) from
          Finset.inf_le (Finset.mem_univ i)) hw)
    induction hx using Subgroup.closure_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hci i
    | one => rfl
    | mul y z hy hz ihy ihz => rw [MulAut.mul_apply, ihz, ihy]
    | inv y hy ihy => simpa [ihy] using MulAut.inv_apply_self W y w
  have hbot : (Finset.univ : Finset (Fin 4)).inf
      (fun i => fixV (Subgroup.zpowers (c i))) = ⊥ := by
    refine le_bot_iff.mp (le_trans hle ?_)
    rw [← hL]
    exact CFSG.Quasithin.B1.fixV_le_fixV hgen
  have hbound := w115_rkIdx_finset_inf_le (ι := Fin 4) hW Finset.univ
    (fun i => fixV (Subgroup.zpowers (c i)))
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 4)), rkIdx (fixV (Subgroup.zpowers (c i))) =
      4 * rkIdx (fixV (Subgroup.zpowers s)) := by
    have hAi : ∀ i : Fin 4, rkIdx (fixV (Subgroup.zpowers (c i))) =
        rkIdx (fixV (Subgroup.zpowers s)) := by
      intro i
      obtain ⟨g, hg⟩ := hc i
      rw [hg]
      exact rkIdx_fixV_conj g s
    calc ∑ i ∈ (Finset.univ : Finset (Fin 4)), rkIdx (fixV (Subgroup.zpowers (c i)))
        = ∑ _i ∈ (Finset.univ : Finset (Fin 4)), rkIdx (fixV (Subgroup.zpowers s)) :=
          Finset.sum_congr rfl fun i _ => hAi i
      _ = 4 * rkIdx (fixV (Subgroup.zpowers s)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hrk : rk W = rkIdx ((Finset.univ : Finset (Fin 4)).inf
      (fun i => fixV (Subgroup.zpowers (c i)))) := by
    rw [hbot]
    have h := rk_add_rkIdx (H := (⊥ : Subgroup W))
    rw [rk_bot, zero_add] at h
    exact h.symm
  rw [hrk]
  exact le_trans hbound (le_of_eq hsum)

theorem w115_rkIdx_fixV_prod_four_le {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (a b c d : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (a * b * c * d))) ≤
      rkIdx (fixV (Subgroup.zpowers a)) + rkIdx (fixV (Subgroup.zpowers b)) +
      rkIdx (fixV (Subgroup.zpowers c)) + rkIdx (fixV (Subgroup.zpowers d)) := by
  have h1 := rkIdx_fixV_mul_le hW (a * b * c) d
  have h2 := rkIdx_fixV_mul_le hW (a * b) c
  have h3 := rkIdx_fixV_mul_le hW a b
  omega

theorem w115_ten_le_rk {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {y : MulAut W} (hy : 11 ∣ orderOf y) : 10 ≤ rk W := by
  have h10 := ten_le_rkIdx_of_eleven hW (y := y) hy
  have h := rk_add_rkIdx (H := fixV (Subgroup.zpowers y))
  omega

theorem w115_even_rkIdx_fixV_of_commute {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {z s : MulAut W} (hz : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hzs : z * s = s * z) :
    Even (rkIdx (fixV (Subgroup.zpowers s))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ (3 ^ 1) = 1 := by simpa using hz
  have hbotz : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.fixSub z = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hfpf w hw
  set K : Subgroup W := fixV (Subgroup.zpowers s) with hK
  have hzK : ∀ w ∈ K, z w ∈ K := by
    intro w hw
    rw [hK, mem_fixV_zpowers_iff_apply] at hw ⊢
    rw [← MulAut.mul_apply, ← hzs, MulAut.mul_apply, hw]
  have hmodW : Nat.card W ≡ 1 [MOD 3] := by
    have h := card_modEq_fixSub (W := W) (p := 3) (n := 1) (α := z) hz3
    rw [hbotz, Subgroup.card_bot] at h
    exact h
  have hmodK : Nat.card K ≡ 1 [MOD 3] := by
    have h := card_modEq_subgroup (W := W) (p := 3) (n := 1) (α := z) hz3 K hzK
    have hbot : K ⊓ CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.fixSub z = ⊥ := by
      rw [hbotz, inf_bot_eq]
    rw [hbot, Subgroup.card_bot] at h
    exact h
  have hcardK : Nat.card K = 2 ^ rk K := card_eq_two_pow hW K
  have hcardW : Nat.card W = 2 ^ rk W := card_eq_two_pow_rk hW
  have hevenW : Even (rk W) := by
    have h : 2 ^ rk W % 3 = 1 := by
      have hh := hmodW
      rw [hcardW] at hh
      change 2 ^ rk W % 3 = 1 % 3 at hh
      simpa using hh
    rcases Nat.even_or_odd (rk W) with h' | h'
    · exact h'
    · rw [CFSG.two_pow_mod_three_of_odd h'] at h
      norm_num at h
  have hevenK : Even (rk K) := by
    have h : 2 ^ rk K % 3 = 1 := by
      have hh := hmodK
      rw [hcardK] at hh
      change 2 ^ rk K % 3 = 1 % 3 at hh
      simpa using hh
    rcases Nat.even_or_odd (rk K) with h' | h'
    · exact h'
    · rw [CFSG.two_pow_mod_three_of_odd h'] at h
      norm_num at h
  have hsub : rkIdx K = rk W - rk K := by
    have h := rk_add_rkIdx K
    omega
  rw [hsub]
  obtain ⟨i, hi⟩ := hevenW
  obtain ⟨j, hj⟩ := hevenK
  refine ⟨i - j, ?_⟩
  omega

theorem w115_rk_le_two_mul_rkIdx_of_inv {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {z s : MulAut W} (hz : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hsz : s * z * s⁻¹ = z⁻¹) :
    rk W ≤ 2 * rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  set K : Subgroup W := fixV (Subgroup.zpowers s) with hK
  set K' : Subgroup W := K.map z.toMonoidHom with hK'
  have hsz' : ∀ u : W, s (z u) = z⁻¹ (s u) := by
    intro u
    have h := congrArg (fun f : MulAut W => f (s u)) hsz
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h
  have hdisj : K ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨hwK, hwK'⟩ := Subgroup.mem_inf.mp hw
    rw [hK'] at hwK'
    obtain ⟨u, huK, rfl⟩ := Subgroup.mem_map.mp hwK'
    have hsw : s (z u) = z u := mem_fixV_zpowers_iff_apply.mp (by rwa [hK] at hwK)
    have hsu : s u = u := mem_fixV_zpowers_iff_apply.mp (by rwa [hK] at huK)
    have hzu : z u = z⁻¹ u := by rw [← hsw, hsz', hsu]
    have hz2 : z (z u) = u := by rw [hzu, MulAut.apply_inv_self]
    have hzu' : z u = u := by
      have h := congrArg (fun f : MulAut W => f u) hz
      simp only [MulAut.one_apply] at h
      have h3 : (z ^ 3) u = z ((z * z) u) := by
        rw [show z ^ 3 = z * (z * z) by rw [pow_succ', pow_succ, pow_one]]
        rfl
      rw [h3, MulAut.mul_apply, hz2] at h
      exact h
    rw [hfpf u hzu', map_one]
  have hcard : Nat.card ↥(K ⊔ K') * Nat.card ↥(K ⊓ K') = Nat.card K * Nat.card K' :=
    card_sup_mul_card_inf K K'
  rw [hdisj, Subgroup.card_bot, mul_one] at hcard
  have hcardK' : Nat.card K' = Nat.card K := by
    rw [hK']
    exact Subgroup.card_map_of_injective z.injective
  have hsq : 2 ^ (rk K + rk K) ≤ 2 ^ rk W := by
    calc 2 ^ (rk K + rk K) = 2 ^ rk K * 2 ^ rk K := by rw [pow_add]
      _ = Nat.card K * Nat.card K := by rw [card_eq_two_pow hW K]
      _ = Nat.card K * Nat.card K' := by rw [hcardK']
      _ = Nat.card ↥(K ⊔ K') := hcard.symm
      _ ≤ Nat.card W := Subgroup.card_le_card_group _
      _ = 2 ^ rk W := card_eq_two_pow_rk hW
  have h2k : rk K + rk K ≤ rk W := (Nat.pow_le_pow_iff_right (by norm_num)).mp hsq
  have hsub : rk K + rkIdx K = rk W := rk_add_rkIdx K
  omega

theorem w116_card_cover {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) (hSp : IsSpor (X ⧸ Subgroup.center X) .M22) :
    Nat.card X = 3 * 443520 := by
  obtain ⟨e⟩ := hSp
  have hcard : Nat.card (X ⧸ Subgroup.center X) = 443520 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.Census.card_m22_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hcard, hZ,
    Nat.mul_comm]

theorem w116_ten_le_rk {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hSp : IsSpor (↥L ⧸ Subgroup.center ↥L) .M22) : 10 ≤ rk W := by
  have hcard : Nat.card ↥L = 3 * 443520 := w116_card_cover hZ hSp
  have h11 : 11 ∣ Nat.card ↥L := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 11 h11
  have hx' : orderOf (x : MulAut W) = 11 := by rw [Subgroup.orderOf_coe, hx]
  exact w115_ten_le_rk hW (y := (x : MulAut W)) (by rw [hx'])

end CFSG.LocalAnalysis.WeakClosure81.W115

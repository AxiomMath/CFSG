module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreSmall
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

private theorem card_center_quotient_of_R891List897
    {Y : Type} [Group Y] (hY : R891List897 Y) :
    Nat.card (Y ⧸ center Y) = 360 ∨
      Nat.card (Y ⧸ center Y) = 20160 ∨
      Nat.card (Y ⧸ center Y) = 460815505920 := by
  rcases hY with ⟨-, -, ⟨e⟩⟩ | ⟨-, -, hL⟩ | ⟨-, -, ⟨e⟩⟩
  · exact Or.inl ((Nat.card_congr e.toEquiv).trans (by rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl : Nat.card (alternatingGroup (Fin 6)) = 360))
  · apply Or.inr ∘ Or.inl
    apply CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
    exact hL.statedClassicalModel (by decide)
  · exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON_eq))

private theorem factorization_two_center_quotient_le_nine_of_R891List897
    {Y : Type} [Group Y] (hY : R891List897 Y) :
    (Nat.card (Y ⧸ center Y)).factorization 2 ≤ 9 := by
  rcases card_center_quotient_of_R891List897 hY with h | h | h
  · rw [h, show 360 = 2 ^ 3 * 45 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    norm_num
  · rw [h, show 20160 = 2 ^ 6 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
    norm_num
  · rw [h, show 460815505920 = 2 ^ 9 * 900030285 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 900030285)]

private theorem two_pow_three_mul_dvd_card_of_R891SL3Two
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : R891SL3Two X n) :
    2 ^ (3 * n) ∣ Nat.card X := by
  have hcard := R891Core.primeCore_sl3Two hX
  have hdvd : (2 : ℤ) ^ (3 * n) ∣ (Nat.card X : ℤ) := by
    rw [hcard]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  exact_mod_cast hdvd

private theorem le_of_two_pow_three_mul_dvd_of_factorization_le
    {N n m : ℕ} (hN : N ≠ 0) (hpow : 2 ^ (3 * n) ∣ N)
    (hval : N.factorization 2 ≤ 3 * m) : n ≤ m := by
  have h := (Nat.factorization_le_iff_dvd (by positivity : 2 ^ (3 * n) ≠ 0) hN).mpr hpow
  have h2 := h 2
  rw [Nat.factorization_pow_self Nat.prime_two] at h2
  omega

open Subgroup

private theorem pPrimeCore_eq_bot_of_R891SL3Two_of_two_le
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : R891SL3Two X n) (hn : 2 ≤ n) :
    CFSG.pPrimeCore 3 X = ⊥ := by
  rcases hX with ⟨hn1, -⟩ | ⟨-, -, hTC⟩ | ⟨-, -, hTC⟩
  · omega
  all_goals
    have hZ : IsPGroup 3 (center X) := by
      apply IsPGroup.of_card (n := 1)
      simpa using hTC.2.1
    have h3 : 3 ∣ Nat.card X := by
      have hd := Subgroup.card_subgroup_dvd_card (center X)
      rwa [hTC.2.1] at hd
    let : Group.IsPerfect X := ⟨hTC.1.1⟩
    have h3Q : 3 ∣ Nat.card (X ⧸ center X) := by
      by_contra hnd
      exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support
        (by decide) hnd h3
    exact CFSG.gLAPPrimeCore_eq_bot_of_quasisimple_of_isPGroup_center
      (by decide) hTC.1 hZ h3Q

private theorem prime_eq_seven_or_thirteen_or_seventy_three_of_R891_congruences
    {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hn3 : n ≤ 3)
    (hdiv : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p])
    (hndiv : ¬ (2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p]) :
    (n = 1 ∧ p = 7) ∨ (n = 2 ∧ p = 13) ∨ (n = 3 ∧ p = 73) := by
  have hnCases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hnCases with rfl | rfl | rfl
  · have hdvd : p ∣ 7 := by
      have h := Int.modEq_iff_dvd.mp hdiv
      norm_num [R891Pi] at h
      exact_mod_cast h
    have heq : p = 7 := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd).resolve_left hp.ne_one
    exact Or.inl ⟨rfl, heq⟩
  · have hdvd : p ∣ 65 := by
      have h := Int.modEq_iff_dvd.mp hdiv
      norm_num [R891Pi] at h
      exact_mod_cast h
    have h5 : p ≠ 5 := by
      intro h
      subst h
      norm_num [R891Pi, Int.ModEq] at hndiv
    have heq : p = 13 := by
      have hm : p ∣ 5 * 13 := by simpa using hdvd
      rcases hp.dvd_mul.mp hm with h | h
      · have := ((Nat.dvd_prime Nat.prime_five).mp h).resolve_left hp.ne_one
        exact False.elim (h5 this)
      · exact ((Nat.dvd_prime (by decide : Nat.Prime 13)).mp h).resolve_left hp.ne_one
    exact Or.inr (Or.inl ⟨rfl, heq⟩)
  · have hdvd : p ∣ 511 := by
      have h := Int.modEq_iff_dvd.mp hdiv
      norm_num [R891Pi] at h
      exact_mod_cast h
    have h7 : p ≠ 7 := by
      intro h
      subst h
      norm_num [R891Pi, Int.ModEq] at hndiv
    have heq : p = 73 := by
      have hm : p ∣ 7 * 73 := by simpa using hdvd
      rcases hp.dvd_mul.mp hm with h | h
      · have := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp h).resolve_left hp.ne_one
        exact False.elim (h7 this)
      · exact ((Nat.dvd_prime (by decide : Nat.Prime 73)).mp h).resolve_left hp.ne_one
    exact Or.inr (Or.inr ⟨rfl, heq⟩)

theorem prime_cases_of_R891Cong
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {n : ℕ} (hcong : R891Cong D n) (hn : 1 ≤ n) (hn3 : n ≤ 3)
    {p : ℕ} (hp : p ∈ D.sig) :
    (n = 1 ∧ p = 7) ∨ (n = 2 ∧ p = 13) ∨ (n = 3 ∧ p = 73) :=
  prime_eq_seven_or_thirteen_or_seventy_three_of_R891_congruences
    (D.sig_prime p hp).1 hn hn3 (hcong p hp).1 (hcong p hp).2

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

private theorem R891X_le_R891Y_of_R891YSet
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L S R : Subgroup G} {n : ℕ}
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hy : R891YSet D L S n R Ys) (hn : 2 ≤ n) :
    R891X L (R891Z L S) n ≤ R891Y (R891H L S) (R891Z L S) Ys := by
  have hn1 : n ≠ 1 := by omega
  have hXH : R891X L (R891Z L S) n ≤ R891H L S := by
    rw [R891X, if_neg hn1, CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hXperfect : Group.IsPerfect (R891X L (R891Z L S) n) := by
    rw [R891X, if_neg hn1, CFSG.LocalAnalysis.UniquenessCase.UC22.F08.DerInf8]
    exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect _
  let P : Subgroup G :=
    (Ys.comap (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))).map
      (R891H L S).subtype
  have hXP : R891X L (R891Z L S) n ≤ P := by
    intro x hx
    refine ⟨⟨x, hXH hx⟩, ?_, rfl⟩
    change QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)) ⟨x, hXH hx⟩ ∈ Ys
    exact hy.xLeLarge hn ⟨⟨x, hXH hx⟩, hx, rfl⟩
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
    _ P hXperfect hXP

private theorem card_Bar2_dvd_card_map_quotient_pPrimeCore_of_le
    {G : Type} [Group G] [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (hcore : CFSG.pPrimeCore 3 (Bar2 X) = ⊥) :
    Nat.card (Bar2 X) ∣ Nat.card ((X.subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y))) := by
  let π : X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  let φ : X →* (Y ⧸ CFSG.pPrimeCore 3 Y) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y)).comp (Subgroup.inclusion hXY)
  let N : Subgroup X := (CFSG.pPrimeCore 3 Y).comap (Subgroup.inclusion hXY)
  have hNnormal : N.Normal := (CFSG.pPrimeCore_normal (p := 3)).comap _
  have hNcop : Nat.Coprime 3 (Nat.card N) :=
    (CFSG.coprime_card_pPrimeCore 3 Y).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hXY))
  have hNmap : N.map π = ⊥ := by
    have hn : (N.map π).Normal := hNnormal.map π (QuotientGroup.mk'_surjective _)
    have hc : Nat.Coprime 3 (Nat.card (N.map π)) :=
      hNcop.coprime_dvd_right (Subgroup.card_map_dvd _ _)
    exact le_bot_iff.mp ((CFSG.le_pPrimeCore_of_normal_coprime hn hc).trans hcore.le)
  have hφker : φ.ker = N := by
    ext x
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 Y) (Subgroup.inclusion hXY x) = 1 ↔
      Subgroup.inclusion hXY x ∈ CFSG.pPrimeCore 3 Y
    exact QuotientGroup.eq_one_iff _
  have hker : φ.ker ≤ π.ker := by
    rw [hφker, ← Subgroup.map_eq_bot_iff]
    exact hNmap
  let f : (X ⧸ φ.ker) →* Bar2 X := QuotientGroup.lift φ.ker π hker
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) y
    exact ⟨QuotientGroup.mk' φ.ker x, rfl⟩
  have hdvd : Nat.card (Bar2 X) ∣ Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_dvd_of_surjective hf
  have hrange : φ.range = (X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rwa [hrange] at hdvd

private theorem odd_card_center_of_R891List897 {Y : Type} [Group Y]
    (hY : R891List897 Y) : Odd (Nat.card (center Y)) := by
  have hcard : Nat.card (center Y) = 3 := by
    rcases hY with ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩ <;> exact hc
  rw [hcard]
  decide

private theorem two_pow_three_mul_dvd_card_center_quotient_R891Ybar
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L S R : Subgroup G} {n : ℕ}
    (hx : R891XShape D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hy : R891YSet D L S n R Ys)
    (hZodd : Odd (Nat.card (center (R891Ybar (R891H L S) (R891Z L S) Ys))))
    (hn : 2 ≤ n) :
    2 ^ (3 * n) ∣ Nat.card (R891Ybar (R891H L S) (R891Z L S) Ys ⧸
      center (R891Ybar (R891H L S) (R891Z L S) Ys)) := by
  have hXY := R891X_le_R891Y_of_R891YSet hy hn
  have hpow : 2 ^ (3 * n) ∣ Nat.card (R891Ybar (R891H L S) (R891Z L S) Ys) :=
    (two_pow_three_mul_dvd_card_of_R891SL3Two hx.xShape).trans
      ((card_Bar2_dvd_card_map_quotient_pPrimeCore_of_le hXY
        (pPrimeCore_eq_bot_of_R891SL3Two_of_two_le hx.xShape hn)).trans
          (Subgroup.card_subgroup_dvd_card _))
  have hcop : Nat.Coprime (2 ^ (3 * n))
      (Nat.card (center (R891Ybar (R891H L S) (R891Z L S) Ys))) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hZodd.not_two_dvd_nat).pow_left _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (R891Ybar (R891H L S) (R891Z L S) Ys))] at hpow
  exact hcop.dvd_of_dvd_mul_right hpow

private theorem le_of_R891XShape_of_R891YSet_of_factorization_le
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L S R : Subgroup G} {n m : ℕ}
    (hx : R891XShape D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hy : R891YSet D L S n R Ys) (hm : 1 ≤ m)
    (hZodd : Odd (Nat.card (center (R891Ybar (R891H L S) (R891Z L S) Ys))))
    (hval : (Nat.card (R891Ybar (R891H L S) (R891Z L S) Ys ⧸
      center (R891Ybar (R891H L S) (R891Z L S) Ys))).factorization 2 ≤ 3 * m) : n ≤ m := by
  by_cases hn : 2 ≤ n
  · exact le_of_two_pow_three_mul_dvd_of_factorization_le Nat.card_pos.ne'
      (two_pow_three_mul_dvd_card_center_quotient_R891Ybar hx hy hZodd hn) hval
  · omega

theorem le_three_of_R891XShape_of_R891YSet
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L S R : Subgroup G} {n : ℕ}
    (hx : R891XShape D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hy : R891YSet D L S n R Ys)
    (hlist : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) : n ≤ 3 := by
  exact le_of_R891XShape_of_R891YSet_of_factorization_le hx hy (by omega)
    (odd_card_center_of_R891List897 hlist)
    (by simpa using factorization_two_center_quotient_le_nine_of_R891List897 hlist)

theorem prime_cases_of_R891XShape_of_R891YSet
    {G : Type} [Group G] [Finite G] {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L S R : Subgroup G} {n : ℕ}
    (hx : R891XShape D L S n R) (hcong : R891Cong D n)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hy : R891YSet D L S n R Ys)
    (hlist : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys))
    {p : ℕ} (hp : p ∈ D.sig) :
    (n = 1 ∧ p = 7) ∨ (n = 2 ∧ p = 13) ∨ (n = 3 ∧ p = 73) := by
  have hn1 : 1 ≤ n := by
    rcases hx.xShape with ⟨hn, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;> omega
  exact prime_cases_of_R891Cong hcong hn1
    (le_three_of_R891XShape_of_R891YSet hx hy hlist) hp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

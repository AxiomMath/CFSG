module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddBorel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddEigen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSimple
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem orderOf_dvd_orderOf_of_conj_pow {Q : Type} [Group Q] {q k : ℕ} {a b : Q}
    (ha : orderOf a = q) (hab : b * a * b⁻¹ = a ^ k) : orderOf (k : ZMod q) ∣ orderOf b := by
  have hbj : ∀ j : ℕ, b ^ j * a * (b ^ j)⁻¹ = a ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc b ^ (j + 1) * a * (b ^ (j + 1))⁻¹ = b * (b ^ j * a * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = a ^ (k ^ (j + 1)) := by rw [ih, ← conj_pow, hab, ← pow_mul, pow_succ']
  refine orderOf_dvd_of_pow_eq_one ?_
  have h1 := hbj (orderOf b)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : a ^ (k ^ orderOf b) = a ^ 1 := by rw [← h1, pow_one]
  rw [pow_eq_pow_iff_modEq, ha] at h2
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ q).mpr h2
  push_cast at h3
  exact h3

theorem eq_eleven_of_isSpor_J1 {Q : Type} [Group Q] (hQ : IsSpor Q .J1) {q k : ℕ}
    (hq : q.Prime) (hq7 : 7 < q) {a b : Q} (ha : orderOf a = q) (hab : b * a * b⁻¹ = a ^ k)
    (hk : orderOf (k : ZMod q) = (q - 1) / 2) : q = 11 := by
  obtain ⟨e⟩ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hQ
  have hcard : Nat.card Q = 175560 :=
    (Nat.card_congr (e.trans CFSG.Walter.walterJ1EquivNative.symm).toEquiv).trans
      CFSG.Walter.J1Props.card_walterJ1
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hq1 : q ∣ 175560 := by
    rw [← hcard, ← ha]
    exact orderOf_dvd_natCard a
  have h9 : (q - 1) / 2 ∣ 175560 := by
    rw [← hk, ← hcard]
    exact (orderOf_dvd_orderOf_of_conj_pow ha hab).trans (orderOf_dvd_natCard b)
  have hq1' : q ∣ 2 ^ 3 * (3 * (5 * (7 * (11 * 19)))) := by
    norm_num
    exact hq1
  rcases (Nat.Prime.dvd_mul hq).mp hq1' with h | h
  · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)
    omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · have h19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
    subst h19
    exact absurd h9 (by decide)

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem lieChar_or_J1 (S : Slice D L D₃ Y H q) (hq : 7 < q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hK32 : UCK.K32) :
    (∃ f : ℕ, LieModel (F09.Lbar9 Y H) .PSL 2 q f ∨
        (q ^ f % 3 = 2 ∧ LieModel (F09.Lbar9 Y H) .PSL 3 q f) ∨
        (q ^ f % 3 = 1 ∧ LieModel (F09.Lbar9 Y H) .PSU 3 q f)) ∨
      (q = 11 ∧ IsSpor (F09.Lbar9 Y H) .J1) := by
  classical
  have hqp := S.prime
  haveI : Fact q.Prime := ⟨hqp⟩
  obtain ⟨a, b, k, ha, hab, hk⟩ := S.exists_conj_pow_lbar9
  have hk3 : 3 < orderOf (k : ZMod q) := by
    have := hqp.eq_two_or_odd
    rw [hk]
    omega
  have hK : CFSG.Open.IsKGroup (F09.Lbar9 Y H) := CFSG.Open.IsKGroup.subgroup
    ((CFSG.Open.IsKProper.isKGroup D.standing.kProper H S.H_ne_top).quotient _) _
  have hnab : ∃ x y : F09.Lbar9 Y H, x * y ≠ y * x := by
    refine ⟨a, b, fun h => ?_⟩
    have h1 : a ^ k = a ^ 1 := by rw [← hab, ← h, mul_inv_cancel_right, pow_one]
    rw [pow_eq_pow_iff_modEq, ha] at h1
    have h2 : (k : ZMod q) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff k 1 q).mpr h1
      rwa [Nat.cast_one] at this
    rw [h2, orderOf_one] at hk3
    omega
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (F09.Lbar9 Y H)) = 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine le_antisymm (F09.pRank_three_le_one_of_not_hasE9 (F09.not_hasE9_Lbar9 hyp)) ?_
    have hnp : ¬ IsPGroup 3 (F09.Lbar9 Y H) := fun h3 => by
      obtain ⟨n, hn⟩ := h3 a
      have h1 : q ∣ 3 ^ n := ha ▸ orderOf_dvd_of_pow_eq_one hn
      have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp (hqp.dvd_of_dvd_pow h1)
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
      (F09.three_dvd_card_of_not_isPGroup (F09.pPrimeCore_Lbar9 hyp.2.1.1) hnp)
    have hx3 : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
    exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := zpowers x) (by norm_num) le_top
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hx3) (k := 1) (by rw [hx3, pow_one])
  rcases hK32 (F09.Lbar9 Y H) hK (S.isSimpleGroup_Lbar9 hyp) hnab hrank with
    ⟨p, f, hL⟩ | ⟨p, f, hpf, hL⟩ | ⟨p, f, hpf, hU⟩ | hJ
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl ⟨f, Or.inl hL⟩
    · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
        CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
      have := orderOf_le_of_conj_of_mulEquiv le_rfl e hp hqp hpq hcard (by norm_num)
        (by omega) ha hab
      omega
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl ⟨f, Or.inr (Or.inl ⟨hpf, hL⟩)⟩
    · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
        CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
      have := orderOf_le_of_conj_of_mulEquiv le_rfl e hp hqp hpq hcard (by norm_num)
        (by omega) ha hab
      omega
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl ⟨f, Or.inr (Or.inr ⟨hpf, hU⟩)⟩
    · obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ :=
        CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide)
      rw [← pow_mul] at hcard
      have := orderOf_le_of_conj_of_mulEquiv (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 _ K) e
        hp hqp hpq hcard (by norm_num) (by omega) ha hab
      omega
  · exact Or.inr ⟨eq_eleven_of_isSpor_J1 hJ hqp hq ha hab hk, hJ⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

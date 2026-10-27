module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem card_fix_congr_uc6 {S T : Type} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    Nat.card {s : S // α s = s} = Nat.card {t : T // MulAut.congr e α t = t} := by
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv fun s => ?_
  show α s = s ↔ e (α (e.symm (e s))) = e s
  rw [MulEquiv.symm_apply_apply, e.injective.eq_iff]

theorem card_fix_conj_uc6 {T : Type} [Group T] (c β : MulAut T) :
    Nat.card {t : T // (c * β * c⁻¹) t = t} = Nat.card {t : T // β t = t} := by
  symm
  apply Nat.card_congr
  refine c.toEquiv.subtypeEquiv fun t => ?_
  show β t = t ↔ (c * β * c⁻¹) (c t) = c t
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  exact c.injective.eq_iff.symm

theorem card_eqLocus_uc6 {T : Type} [Group T] (f : MulAut T) :
    Nat.card ↥(f.toMonoidHom.eqLocus (MonoidHom.id T)) = Nat.card {t : T // f t = t} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

section


theorem kSz_holds : KSz := by
  intro S _ _ hK hs hnc hcop α hα
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    by_contra h
    push_neg at h
    exact hnc ⟨⟨fun a b => h a b⟩⟩
  have hcat : CFSG.Assembly.InCatalog S := by
    have := hK.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.topEquiv (G := S)).toMonoidHom
      (Subgroup.topEquiv (G := S)).surjective
    exact this
  have h3 : ¬ 3 ∣ Nat.card S := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop h
    omega
  obtain ⟨f, -, a, ha, K, _, _, hf, hKc, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat h3
  have hKc' : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hKc
  set α' : MulAut (suzukiGroup a K) := MulAut.congr e α with hα'
  have hα'3 : orderOf α' = 3 := by
    rw [hα', ← hα]
    exact orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α
  have hnin : α' ∉ inner (suzukiGroup a K) := by
    intro hin
    have h1 : α' ^ 3 = 1 := by rw [← hα'3]; exact pow_orderOf_eq_one α'
    have := CFSG.RankThree.PartTwo.Sec6.BThreeCensus.eq_one_of_mem_inner_of_pow_three ha hKc' h1 hin
    rw [this, orderOf_one] at hα'3
    omega
  obtain ⟨σ, h, b, k, _, _, -, hab, hkc, hconj, ⟨eFix⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hKc' 3 Nat.prime_three
      (by norm_num) α' hα'3 hnin
  have hC : Nat.card {s : S // α s = s} =
      (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) := by
    rw [card_fix_congr_uc6 e α, ← hα', ← card_fix_conj_uc6 (MulAut.conj h) α', hconj, ← card_eqLocus_uc6,
      Nat.card_congr eFix.toEquiv]
    exact suzuki_order hkc
  have hS : Nat.card S =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact suzuki_order hKc'
  set q0 := 2 ^ (2 * b + 1) with hq0
  have hq : 2 ^ (2 * a + 1) = q0 ^ 3 := by rw [← hab, pow_mul]
  have hq0two : 2 ≤ q0 := by
    rw [hq0]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨t, ht⟩ : ∃ t, q0 = t + 1 := ⟨q0 - 1, by omega⟩
  have hfac : q0 ^ 3 - 1 = (q0 - 1) * (q0 ^ 2 + q0 + 1) := by
    rw [ht, Nat.add_sub_cancel]
    have : (t + 1) ^ 3 = t * ((t + 1) ^ 2 + (t + 1) + 1) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  have hN : q0 ^ 2 + q0 + 1 ≠ 1 := by
    intro h1
    have : 0 < q0 ^ 2 := by positivity
    omega
  obtain ⟨r, hr, hrN⟩ := Nat.exists_prime_and_dvd hN
  have hodd : ¬ 2 ∣ q0 ^ 2 + q0 + 1 := by
    have he : Even (q0 * (q0 + 1)) := Nat.even_mul_succ_self q0
    have : q0 ^ 2 + q0 + 1 = q0 * (q0 + 1) + 1 := by ring
    rw [this]
    intro h2
    obtain ⟨c, hc⟩ := he
    omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hodd hrN
  have hrS : r ∣ Nat.card S := by
    rw [hS, hq, hfac]
    exact ((hrN.mul_left (q0 - 1)).mul_left _).mul_right _
  refine ⟨r, hr, hr2, fun hdiv => ?_⟩
  have hSpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card S).factorization r ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd hr hSpos hrS).ne'
  have hrC : r ∣ Nat.card {s : S // α s = s} := (dvd_pow_self r hv).trans hdiv
  rw [hC] at hrC
  have hr_two : ∀ {x : ℕ}, r ∣ x → x = q0 → False := by
    intro x hx hxq
    rw [hxq, hq0] at hx
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hx))
  rcases (Nat.Prime.dvd_mul hr).1 hrC with h12 | h3'
  · rcases (Nat.Prime.dvd_mul hr).1 h12 with h1 | h2
    · exact hr_two (hr.dvd_of_dvd_pow h1) rfl
    · have h3r : r ∣ 3 := by
        have : q0 ^ 2 + q0 + 1 = (q0 - 1) * (q0 + 2) + 3 := by
          rw [ht, Nat.add_sub_cancel]
          ring
        rw [this] at hrN
        exact (Nat.dvd_add_right (h2.mul_right _)).1 hrN
      have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3r
      exact h3 (hr3 ▸ hrS)
  · have hrq : r ∣ q0 := by
      have : q0 ^ 2 + q0 + 1 = (q0 ^ 2 + 1) + q0 := by ring
      rw [this] at hrN
      exact (Nat.dvd_add_right h3').1 hrN
    exact hr_two hrq rfl

end

end CFSG.LocalAnalysis.UniquenessCase.UCK

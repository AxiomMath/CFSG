module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylGL
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22LT

public section

open Matrix

namespace CFSG.Quasithin.KGC31

open CFSG.Assembly.LowTwoRank

theorem lieSyl_not_dvd_of_ne {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ) :
    ¬ ℓ ∣ p :=
  fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm

theorem lieSyl_not_dvd_pow {ℓ x : ℕ} (hℓ : ℓ.Prime) (hx : ¬ ℓ ∣ x) (k : ℕ) : ¬ ℓ ∣ x ^ k :=
  fun h => hx (hℓ.dvd_of_dvd_pow h)

theorem lieSyl_two_pow_add_one_ne (a : ℕ) : 2 ^ a + 1 ≠ 11 := by
  rcases a with _ | _ | _ | _ | a
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [pow_succ, pow_succ, pow_succ, pow_succ]
    omega

theorem lieSyl_two_pow_ne_twelve (b : ℕ) : 2 ^ b ≠ 12 := by
  rcases b with _ | _ | _ | _ | b
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [pow_succ, pow_succ, pow_succ, pow_succ]
    omega

theorem lieSyl_card_fin_three_factorial : (Fintype.card (Fin 3)).factorial = 6 := by
  rw [Fintype.card_fin]
  decide

theorem lieSyl_card_fin_four_factorial : (Fintype.card (Fin 4)).factorial = 24 := by
  rw [Fintype.card_fin]
  decide

theorem lieSyl_card_sum_two : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
  simp [Fintype.card_sum]

theorem lieSyl_card_sum_two_factorial : (Fintype.card (Fin 2 ⊕ Fin 2)).factorial = 24 := by
  rw [lieSyl_card_sum_two]
  decide

theorem sylowAutBoundAll_of_mulEquiv {ℓ m : ℕ} [Fact ℓ.Prime] {G N : Type*} [Group G] [Finite G]
    [Group N] (e : G ≃* N) (h : SylowAutBoundAll ℓ m G) : SylowAutBoundAll ℓ m N :=
  SylowAutBoundAll.of_surjective e.toMonoidHom e.surjective h

theorem sylowAutBoundAll_statedProj {K ι : Type} [Field K] [Finite K] [Fintype ι] [DecidableEq ι]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hn : Fintype.card ι < ℓ) (hK : ¬ ℓ ∣ Nat.card K)
    (H : Subgroup (GL ι K)) :
    SylowAutBoundAll ℓ (Fintype.card ι).factorial (StatedProj H) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hG : SylowAutBoundAll ℓ (Fintype.card ι).factorial (GL ι K) :=
    sylowAutBoundAll_GL_of_fintype hℓ hn hK
  have hH : SylowAutBoundAll ℓ (Fintype.card ι).factorial H :=
    SylowAutBoundAll.of_injective H.subtype (Subgroup.subtype_injective H) hG
  exact SylowAutBoundAll.of_surjective (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H))
    (QuotientGroup.mk'_surjective _) hH

theorem sylowAutBound_of_statedProj_mulEquiv {S : Type} [Group S] [Finite S] {K ι : Type}
    [Field K] [Finite K] [Fintype ι] [DecidableEq ι] {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hn : Fintype.card ι < ℓ) (hK : ¬ ℓ ∣ Nat.card K) (H : Subgroup (GL ι K))
    (hdvd : (Fintype.card ι).factorial ∣ m) (e : S ≃* StatedProj H) :
    SylowAutBound ℓ m S := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h1 : SylowAutBoundAll ℓ (Fintype.card ι).factorial (StatedProj H) :=
    sylowAutBoundAll_statedProj hℓ hn hK H
  have h2 : SylowAutBoundAll ℓ (Fintype.card ι).factorial S :=
    sylowAutBoundAll_of_mulEquiv e.symm h1
  exact sylowAutBound_iff_all.2 (h2.mono hdvd)

theorem lieSyl_psl3 {S : Type} [Group S] [Finite S] {ℓ p f m : ℕ} (hℓ : ℓ.Prime)
    (hn : 3 < ℓ) (hne : p ≠ ℓ) (hdvd : 6 ∣ m) (hmod : StatedClassicalModel S .PSL 3 p f) :
    SylowAutBound ℓ m S := by
  obtain ⟨⟨hpp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmod
  have hK : ¬ ℓ ∣ Nat.card K := by
    rw [hcard]
    exact lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_of_ne hℓ hpp hne) f
  have hn' : Fintype.card (Fin 3) < ℓ := by
    rw [Fintype.card_fin]
    exact hn
  have hdvd' : (Fintype.card (Fin 3)).factorial ∣ m := by
    rw [lieSyl_card_fin_three_factorial]
    exact hdvd
  exact sylowAutBound_of_statedProj_mulEquiv hℓ hn' hK (StatedSL 3 K) hdvd' e

theorem lieSyl_psu3 {S : Type} [Group S] [Finite S] {ℓ p f m : ℕ} (hℓ : ℓ.Prime)
    (hn : 3 < ℓ) (hne : p ≠ ℓ) (hdvd : 6 ∣ m) (hmod : StatedClassicalModel S .PSU 3 p f) :
    SylowAutBound ℓ m S := by
  obtain ⟨⟨hpp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmod
  have hK : ¬ ℓ ∣ Nat.card K := by
    rw [hcard]
    exact lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_of_ne hℓ hpp hne) f) 2
  have hn' : Fintype.card (Fin 3) < ℓ := by
    rw [Fintype.card_fin]
    exact hn
  have hdvd' : (Fintype.card (Fin 3)).factorial ∣ m := by
    rw [lieSyl_card_fin_three_factorial]
    exact hdvd
  exact sylowAutBound_of_statedProj_mulEquiv hℓ hn' hK (StatedSU 3 (p ^ f) K) hdvd' e

theorem lieSyl_psp2 {S : Type} [Group S] [Finite S] {ℓ p f m : ℕ} (hℓ : ℓ.Prime)
    (hn : 4 < ℓ) (hne : p ≠ ℓ) (hdvd : 24 ∣ m) (hmod : StatedClassicalModel S .PSp 2 p f) :
    SylowAutBound ℓ m S := by
  obtain ⟨⟨hpp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmod
  have hK : ¬ ℓ ∣ Nat.card K := by
    rw [hcard]
    exact lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_of_ne hℓ hpp hne) f
  have hn' : Fintype.card (Fin 2 ⊕ Fin 2) < ℓ := by
    rw [lieSyl_card_sum_two]
    exact hn
  have hdvd' : (Fintype.card (Fin 2 ⊕ Fin 2)).factorial ∣ m := by
    rw [lieSyl_card_sum_two_factorial]
    exact hdvd
  exact sylowAutBound_of_statedProj_mulEquiv hℓ hn' hK (StatedSp 2 K) hdvd' e

theorem lieSyl_psl4 {S : Type} [Group S] [Finite S] {ℓ p f m : ℕ} (hℓ : ℓ.Prime)
    (hn : 4 < ℓ) (hne : p ≠ ℓ) (hdvd : 24 ∣ m) (hmod : StatedClassicalModel S .PSL 4 p f) :
    SylowAutBound ℓ m S := by
  obtain ⟨⟨hpp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmod
  have hK : ¬ ℓ ∣ Nat.card K := by
    rw [hcard]
    exact lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_of_ne hℓ hpp hne) f
  have hn' : Fintype.card (Fin 4) < ℓ := by
    rw [Fintype.card_fin]
    exact hn
  have hdvd' : (Fintype.card (Fin 4)).factorial ∣ m := by
    rw [lieSyl_card_fin_four_factorial]
    exact hdvd
  exact sylowAutBound_of_statedProj_mulEquiv hℓ hn' hK (StatedSL 4 K) hdvd' e

theorem lieSyl_psu4 {S : Type} [Group S] [Finite S] {ℓ p f m : ℕ} (hℓ : ℓ.Prime)
    (hn : 4 < ℓ) (hne : p ≠ ℓ) (hdvd : 24 ∣ m) (hmod : StatedClassicalModel S .PSU 4 p f) :
    SylowAutBound ℓ m S := by
  obtain ⟨⟨hpp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmod
  have hK : ¬ ℓ ∣ Nat.card K := by
    rw [hcard]
    exact lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_pow hℓ (lieSyl_not_dvd_of_ne hℓ hpp hne) f) 2
  have hn' : Fintype.card (Fin 4) < ℓ := by
    rw [Fintype.card_fin]
    exact hn
  have hdvd' : (Fintype.card (Fin 4)).factorial ∣ m := by
    rw [lieSyl_card_fin_four_factorial]
    exact hdvd
  exact sylowAutBound_of_statedProj_mulEquiv hℓ hn' hK (StatedSU 4 (p ^ f) K) hdvd' e

theorem ltqtk_conj_psl3_psu3 :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p ≠ 2 → (f = 1 ∨ f = 2) →
      (StatedClassicalModel S .PSL 3 p f ∨ StatedClassicalModel S .PSU 3 p f) →
      (p ≠ 11 → SylowAutBound 11 6 S) ∧ (p = 11 → SylowAutBound 5 6 S) := by
  rintro S _ _ p f _ _ (h | h)
  · exact ⟨fun hp => lieSyl_psl3 (by norm_num) (by norm_num) hp (dvd_refl 6) h,
      fun hp => lieSyl_psl3 (by norm_num) (by norm_num) (by omega) (dvd_refl 6) h⟩
  · exact ⟨fun hp => lieSyl_psu3 (by norm_num) (by norm_num) hp (dvd_refl 6) h,
      fun hp => lieSyl_psu3 (by norm_num) (by norm_num) (by omega) (dvd_refl 6) h⟩

theorem ltqtk_conj_psp2 :
    ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → p ≠ 11 →
      StatedClassicalModel S .PSp 2 p 1 → SylowAutBound 11 24 S := by
  rintro S _ _ p _ hp hmod
  exact lieSyl_psp2 (by norm_num) (by norm_num) hp (dvd_refl 24) hmod

theorem ltqtk_conj_psl4 :
    ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → (∃ a : ℕ, p = 2 ^ a + 1) →
      StatedClassicalModel S .PSL 4 p 1 → SylowAutBound 11 24 S := by
  rintro S _ _ p _ ⟨a, ha⟩ hmod
  have hne : p ≠ 11 := fun h => lieSyl_two_pow_add_one_ne a (ha.symm.trans h)
  exact lieSyl_psl4 (by norm_num) (by norm_num) hne (dvd_refl 24) hmod

theorem ltqtk_conj_psu4 :
    ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → (∃ b : ℕ, p + 1 = 2 ^ b) →
      StatedClassicalModel S .PSU 4 p 1 → SylowAutBound 11 24 S := by
  rintro S _ _ p _ ⟨b, hb⟩ hmod
  have hne : p ≠ 11 := fun h => lieSyl_two_pow_ne_twelve b (by omega)
  exact lieSyl_psu4 (by norm_num) (by norm_num) hne (dvd_refl 24) hmod

theorem ltqtk_conj_char2 :
    ∀ (S : Type) [Group S] [Finite S] (f : ℕ),
      (StatedClassicalModel S .PSL 3 2 f ∨ StatedClassicalModel S .PSU 3 2 f ∨
        StatedClassicalModel S .PSp 2 2 f ∨ StatedClassicalModel S .PSU 4 2 f) →
      SylowAutBound 11 1152 S := by
  rintro S _ _ f (h | h | h | h)
  · exact lieSyl_psl3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact lieSyl_psu3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact lieSyl_psp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact lieSyl_psu4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

end CFSG.Quasithin.KGC31

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin.KGC31 CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ltqtk_of_exc
    (hG2 : ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → p ≠ 11 →
      ChevalleyExceptionalModel S .G2 p 1 → SylowAutBound 11 24 S)
    (hExc : LieSylow11Exc) : LTQTK := by
  unfold LTQTK
  refine ⟨ltqtk_conj_psl3_psu3, ?_, ltqtk_conj_psl4, ltqtk_conj_psu4, ltqtk_conj_char2, hExc⟩
  rintro S _ _ p hp2 hp11 (h | h)
  · exact ltqtk_conj_psp2 S p hp2 hp11 h
  · exact hG2 S p hp2 hp11 h

end CFSG.Quasithin.H13.Ch4

end

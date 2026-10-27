module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpCartan
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZGeneric

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s2122np_eq_sup_of_mul {E A B : Subgroup G}
    (hAE : A ≤ E) (hBE : B ≤ E) (hmul : (E : Set G) = (A : Set G) * (B : Set G)) :
    E = A ⊔ B := by
  refine le_antisymm ?_ (sup_le hAE hBE)
  intro x hx
  have hx' : x ∈ (A : Set G) * (B : Set G) := hmul ▸ hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hx'
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hc)

private theorem uc22s2122np_card_eq_p_of_ne {p i : ℕ} (hp : p.Prime) (hi2 : i ≤ 2)
    {E : Subgroup G} (hEc : Nat.card E ∣ p ^ 2) (hcard : Nat.card E = p ^ i) {b : G}
    (hb1 : b ≠ 1) {X : Subgroup G} (hXE : X ≤ E) (hne : X ≠ E) (hbX : b ∈ X) :
    Nat.card X = p := by
  have hXdvdp : Nat.card X ∣ p ^ 2 := (Subgroup.card_dvd_of_le hXE).trans hEc
  obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp).1 hXdvdp
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    rw [Subgroup.eq_bot_of_card_eq X hj] at hbX
    exact hb1 (Subgroup.mem_bot.1 hbX)
  have hjne2 : j ≠ 2 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hXE
      (by rw [hcard, hj]; exact Nat.pow_le_pow_right hp.pos hi2))
  have hj1 : j = 1 := by omega
  rw [hj1, pow_one] at hj
  exact hj

private theorem uc22s2122np_false_of_card_sq {p : ℕ} (hp : p.Prime) {E A B : Subgroup G}
    (hEsup : E = A ⊔ B) {b : G} (hbA : b ∈ A) (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hcard : Nat.card E = p ^ 2) (hAcard : Nat.card A = p) (hBcard : Nat.card B = p) :
    False := by
  have hbord : orderOf b = p := by
    have hdvd := Subgroup.orderOf_dvd_natCard A hbA
    rw [hAcard] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.1 h1) hb1
    · exact hp'
  have hAzb : A = zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbA)
      (by rw [Nat.card_zpowers, hbord, hAcard])).symm
  have hBzb : B = zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbB)
      (by rw [Nat.card_zpowers, hbord, hBcard])).symm
  have hEcard : Nat.card E = p := by
    rw [hEsup, hAzb, hBzb, sup_idem, Nat.card_zpowers, hbord]
  rw [hcard] at hEcard
  have hlt : p < p ^ 2 := by
    simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)
  omega

theorem uc22s2122np_eq_or_eq_of_mul {p : ℕ} (hp : p.Prime) {E A B : Subgroup G}
    (hEc : Nat.card E ∣ p ^ 2) (hAE : A ≤ E) (hBE : B ≤ E)
    (hmul : (E : Set G) = (A : Set G) * (B : Set G)) {b : G} (hbA : b ∈ A) (hbB : b ∈ B)
    (hb1 : b ≠ 1) : A = E ∨ B = E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hEsup : E = A ⊔ B := uc22s2122np_eq_sup_of_mul hAE hBE hmul
  obtain ⟨i, hi2, hcard⟩ := (Nat.dvd_prime_pow hp).1 hEc
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have hbE : b ∈ E := hAE hbA
    rw [Subgroup.eq_bot_of_card_eq E hcard] at hbE
    exact hb1 (Subgroup.mem_bot.1 hbE)
  have hi : i = 1 ∨ i = 2 := by omega
  rcases hi with hi1 | hi2'
  · have hEp : Nat.card E = p := hcard.trans (by rw [hi1, pow_one])
    by_cases hAE' : A = E
    · exact Or.inl hAE'
    · have hAcard : Nat.card A = p :=
        uc22s2122np_card_eq_p_of_ne hp hi2 hEc hcard hb1 hAE hAE' hbA
      exact absurd (Subgroup.eq_of_le_of_card_ge hAE (by rw [hEp, hAcard])) hAE'
  · have hcard2 : Nat.card E = p ^ 2 := hcard.trans (by rw [hi2'])
    by_cases hAE' : A = E
    · exact Or.inl hAE'
    by_cases hBE' : B = E
    · exact Or.inr hBE'
    exfalso
    exact uc22s2122np_false_of_card_sq hp hEsup hbA hbB hb1 hcard2
      (uc22s2122np_card_eq_p_of_ne hp hi2 hEc hcard hb1 hAE hAE' hbA)
      (uc22s2122np_card_eq_p_of_ne hp hi2 hEc hcard hb1 hBE hBE' hbB)

private theorem uc22s2122np_card_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E T : Subgroup G} (hEp : IsPGroup p E) (hT : IsPGroup 2 T) :
    Nat.Coprime (Nat.card E) (Nat.card T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hEp.exists_card_eq
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [ha, hk]
  exact (Nat.Coprime.pow_left a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)).pow_right k

private theorem uc22s2122np_solvable_of_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E T : Subgroup G} (hEp : IsPGroup p E) (hT : IsPGroup 2 T)
    (hcard : Nat.card ↥(E ⊔ T : Subgroup G) = Nat.card E * Nat.card T) :
    Group.IsSolvable ↥(E ⊔ T : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsupp : ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ Nat.card ↥(E ⊔ T : Subgroup G) → ℓ = p ∨ ℓ = 2 := by
    intro ℓ hℓ hdvd
    rw [hcard] at hdvd
    obtain ⟨a, ha⟩ := hEp.exists_card_eq
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [ha, hk] at hdvd
    rcases hℓ.dvd_mul.1 hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h))
  exact CFSG.SignalizerFunctorTheorem.Glauberman.isSolvable_of_prime_support hp Nat.prime_two
    hp2 hsupp

private theorem uc22s2122np_setup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E T : Subgroup G} (hEp : IsPGroup p E) (hT : IsPGroup 2 T)
    (hET : ((E ⊔ T : Subgroup G) : Set G) = (E : Set G) * (T : Set G)) :
    E ⊓ T = ⊥ ∧ Group.IsSolvable ↥(E ⊔ T : Subgroup G) ∧ Odd (Nat.card E) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTE : E ⊓ T = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (uc22s2122np_card_coprime hp hp2 hEp hT)
  have hcard : Nat.card ↥(E ⊔ T : Subgroup G) = Nat.card E * Nat.card T :=
    CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul hET hTE
  refine ⟨hTE, uc22s2122np_solvable_of_mul hp hp2 hEp hT hcard, ?_⟩
  obtain ⟨a, ha⟩ := hEp.exists_card_eq
  rw [ha]
  exact (hp.odd_of_ne_two hp2).pow

private theorem uc22s2122np_inter_mul {E X T : Subgroup G}
    (hET : ((E ⊔ T : Subgroup G) : Set G) = (E : Set G) * (T : Set G))
    (hZY : (X ⊔ T : Subgroup G) ≤ E ⊔ T) :
    ((X ⊔ T : Subgroup G) : Set G) = ((E ⊓ (X ⊔ T) : Subgroup G) : Set G) * (T : Set G) := by
  have hTZ : T ≤ (X ⊔ T : Subgroup G) := le_sup_right
  have h1 := CFSG.Quasithin.H23P4.inf_mul_eq_mul_inf (H := E) (K := T) (I := X ⊔ T) hTZ
  have h2 : ((E : Set G) * (T : Set G)) ∩ ((X ⊔ T : Subgroup G) : Set G) =
      ((X ⊔ T : Subgroup G) : Set G) := by
    rw [← hET]
    exact Set.inter_eq_right.2 hZY
  rw [← h2, ← h1]

private theorem uc22s2122np_isHall_inter {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E X T : Subgroup G} (hEp : IsPGroup p E) (hEc : Nat.card E ∣ p ^ 2)
    (hT : IsPGroup 2 T)
    (hAZ : ((X ⊔ T : Subgroup G) : Set G) = ((E ⊓ (X ⊔ T) : Subgroup G) : Set G) * (T : Set G))
    (hAT : (E ⊓ (X ⊔ T) : Subgroup G) ⊓ T = ⊥) :
    IsHallOddIn (E ⊓ (X ⊔ T)) (X ⊔ T) ∧ IsMulCommutative ↥(E ⊓ (X ⊔ T)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAdvd : Nat.card (E ⊓ (X ⊔ T) : Subgroup G) ∣ p ^ 2 :=
    (Subgroup.card_dvd_of_le inf_le_left).trans hEc
  obtain ⟨a, ha⟩ := (hEp.to_le inf_le_left : IsPGroup p (E ⊓ (X ⊔ T) : Subgroup G)).exists_card_eq
  obtain ⟨t, ht⟩ := hT.exists_card_eq
  have hAodd : Odd (Nat.card (E ⊓ (X ⊔ T) : Subgroup G)) := by
    rw [ha]
    exact (hp.odd_of_ne_two hp2).pow
  have hZindex : ((E ⊓ (X ⊔ T) : Subgroup G).subgroupOf (X ⊔ T)).index = 2 ^ t := by
    change (E ⊓ (X ⊔ T)).relIndex (X ⊔ T) = 2 ^ t
    rw [CFSG.Quasithin.H23P4.relIndex_eq_card_of_coe_eq_mul inf_le_right hAZ hAT, ht]
  have hAcomm : IsMulCommutative ↥(E ⊓ (X ⊔ T) : Subgroup G) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    exact Subtype.ext
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.commute_of_card_dvd_sq
        (hEp.to_le inf_le_left) hAdvd (x : G) x.2 (y : G) y.2)
  exact ⟨⟨inf_le_right, hAodd, ⟨t, hZindex⟩⟩, hAcomm⟩

private theorem uc22s2122np_pRank_le_two_of_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A Z T : Subgroup G} (hAp : IsPGroup p A) (hAdvd : Nat.card A ∣ p ^ 2)
    (hAZ : (Z : Set G) = (A : Set G) * (T : Set G)) (hAT : A ⊓ T = ⊥)
    (hT : IsPGroup 2 T) :
    ∀ r ∈ piSet Z, r ≠ 2 → CFSG.Open.pRank r Z ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  obtain ⟨t, ht⟩ := hT.exists_card_eq
  intro r hr hr2
  have hrp : r = p := by
    have hdvd : r ∣ Nat.card Z := hr.2
    rw [CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul hAZ hAT, ha, ht] at hdvd
    rcases hr.1.dvd_mul.1 hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hr.1 hp).1 (hr.1.dvd_of_dvd_pow h)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_two).1
        (hr.1.dvd_of_dvd_pow h)) hr2
  rw [hrp]
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := Z) (k := 2) ?_
  intro F hFZ hFel
  obtain ⟨j, hj⟩ := hFel.isPGroup.exists_card_eq
  have hFdvd : Nat.card F ∣ Nat.card Z := Subgroup.card_dvd_of_le hFZ
  rw [CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul hAZ hAT, ha, ht] at hFdvd
  have hcop2 : Nat.Coprime (p ^ j) (2 ^ t) :=
    (Nat.Coprime.pow_left j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)).pow_right t
  have hjp : p ^ j ∣ p ^ a := hcop2.dvd_of_dvd_mul_right (hj ▸ hFdvd)
  have hja : j ≤ a :=
    (Nat.pow_le_pow_iff_right hp.one_lt).1 (Nat.le_of_dvd (pow_pos hp.pos a) hjp)
  have ha2 : a ≤ 2 := by
    have hdvd : p ^ a ∣ p ^ 2 := by
      rw [← ha]
      exact hAdvd
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (Nat.le_of_dvd (pow_pos hp.pos 2) hdvd)
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos (by omega)

private theorem uc22s2122np_uniqueMax {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E X : Subgroup G} (hEp : IsPGroup p E) (hEc : Nat.card E ∣ p ^ 2)
    (hET : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G))
    (hYs : Group.IsSolvable ↥(E ⊔ D.T : Subgroup G)) (hXE : X ≤ E)
    (hXc : Nat.card X = p) (hXU : X ∈ uniqueSet D.M) :
    UniqueMax D.M (X ⊔ D.T) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hTE : E ⊓ D.T = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime
      (uc22s2122np_card_coprime hp hp2 hEp D.sylowM.isPGroup)
  have hZY : (X ⊔ D.T : Subgroup G) ≤ E ⊔ D.T := sup_le (hXE.trans le_sup_left) le_sup_right
  have hAZ := uc22s2122np_inter_mul hET hZY
  have hAT : (E ⊓ (X ⊔ D.T) : Subgroup G) ⊓ D.T = ⊥ := by
    have h1 : (E ⊓ (X ⊔ D.T) : Subgroup G) ⊓ D.T ≤ E ⊓ D.T :=
      inf_le_inf_right _ inf_le_left
    rw [hTE] at h1
    exact le_bot_iff.1 h1
  obtain ⟨hHall, hAcomm⟩ :=
    uc22s2122np_isHall_inter hp hp2 hEp hEc D.sylowM.isPGroup hAZ hAT
  have hrk := uc22s2122np_pRank_le_two_of_mul hp hp2 (hEp.to_le inf_le_left)
    ((Subgroup.card_dvd_of_le inf_le_left).trans hEc) hAZ hAT D.sylowM.isPGroup
  have hZsolv : Group.IsSolvable ↥(X ⊔ D.T : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hZY)
      (Subgroup.inclusion_injective hZY)
  have hXp : (Nat.card X).Prime := by rw [hXc]; exact hp
  have hX2 : Nat.card X ≠ 2 := by rw [hXc]; exact hp2
  exact (h211 h1930 c X hXp hX2 hZsolv ⟨E ⊓ (X ⊔ D.T), hHall, hAcomm⟩ hrk hXU).1

private theorem uc22s2122np_false_of_le_hSet {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hEp : IsPGroup p E) (hEc : Nat.card E ∣ p ^ 2)
    (hET : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G))
    (hYs : Group.IsSolvable ↥(E ⊔ D.T : Subgroup G)) {X : Subgroup G} (hXE : X ≤ E)
    (hXc : Nat.card X = p) (hXU : X ∈ uniqueSet D.M) (hEH : E ≤ H) : False := by
  have hU := uc22s2122np_uniqueMax h211 h1930 c hp hp2 hEp hEc hET hYs hXE hXc hXU
  exact uc22s21rn_not_le_of_uniqueMax D hH hU (sup_le (hXE.trans hEH) hH.1)

theorem uc22s2122np_false_of_permutes {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E X : Subgroup G}
    (hEM : E ≤ D.M) (hEp : IsPGroup p E) (hEc : Nat.card E ∣ p ^ 2)
    (hET : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G))
    {b : G} (hbE : b ∈ E) (hbL0 : b ∈ c.L0) (hb1 : b ≠ 1)
    (hXE : X ≤ E) (hXc : Nat.card X = p) (hXU : X ∈ uniqueSet D.M) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTE, hYs, hoddE⟩ := uc22s2122np_setup hp hp2 hEp D.sylowM.isPGroup hET
  have hTY : D.T ≤ E ⊔ D.T := le_sup_right
  have hYM : E ⊔ D.T ≤ D.M := sup_le hEM D.sylowM.le
  have hEfac : (E : Set G) =
      ((E ⊓ H₁ : Subgroup G) : Set G) * ((E ⊓ H₂ : Subgroup G) : Set G) :=
    uc22s21rhp_cartan_eq_mul D hH₁ hH₂ hfX hYM hTY hYs le_sup_left hET hoddE
  have hbH₁ : b ∈ H₁ := (Subgroup.mem_inf.1 (hL0 hbL0)).1
  have hbH₂ : b ∈ H₂ := (Subgroup.mem_inf.1 (hL0 hbL0)).2
  have hfac : E ≤ H₁ ∨ E ≤ H₂ := by
    rcases uc22s2122np_eq_or_eq_of_mul (E := E) (A := E ⊓ H₁) (B := E ⊓ H₂) hp hEc
      (fun x hx => hx.1) (fun x hx => hx.1) hEfac ⟨hbE, hbH₁⟩ ⟨hbE, hbH₂⟩ hb1 with h | h
    · exact Or.inl (h ▸ inf_le_right)
    · exact Or.inr (h ▸ inf_le_right)
  rcases hfac with h | h
  · exact uc22s2122np_false_of_le_hSet h211 h1930 c hH₁ hp hp2 hEp hEc hET hYs hXE hXc hXU h
  · exact uc22s2122np_false_of_le_hSet h211 h1930 c hH₂ hp hp2 hEp hEc hET hYs hXE hXc hXU h

end CFSG.LocalAnalysis.UniquenessCase.UC22

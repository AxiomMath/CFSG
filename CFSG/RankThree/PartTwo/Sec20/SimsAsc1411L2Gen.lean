module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2GenExc
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2GenNT
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Field

variable {K : Type} [Field K]

private theorem excl1411_of_word1411_prime {G : Type*} [Group G] {α : MulAut G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ p ∣ 2 ^ e - 1)
    (hW : ∃ x₁ x₂ x₃ : G, p ∣ orderOf (word1411 α x₁ x₂ x₃)) : Excl1411 α := by
  obtain ⟨x₁, x₂, x₃, hx⟩ := hW
  exact Or.inr (Or.inl ⟨x₁, x₂, x₃, p, 1, hp, hp2, le_rfl, by simpa using h8, by simpa using hx⟩)

theorem excl1411_pglAction_of_involution [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 9 < p ^ f)
    {g : PGL2 K} (hg1 : g ≠ 1) (hg2 : g * g = 1) : Excl1411 (pglAction K g) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  by_cases hgen : ∃ n, Odd n ∧ ¬ n ∣ 105 ∧ (n ∣ Nat.card K - 1 ∨ n ∣ Nat.card K + 1)
  · obtain ⟨n, hn, hn105, hnq⟩ := hgen
    obtain ⟨y, hy⟩ := exists_inverted_dvd_orderOf hK ⟨p, f, hp, hpodd, hf, hK⟩
      (by rw [hK]; omega) hg1 hg2 hn hnq
    exact excl1411_of_odd_not_dvd_105 hn hn105 hy
  have hmem := mem_of_forall_odd_dvd_dvd_105 (hK ▸ hpodd.pow)
    (fun n hn hd => by_contra fun h => hgen ⟨n, hn, h, Or.inl hd⟩)
    (fun n hn hd => by_contra fun h => hgen ⟨n, hn, h, Or.inr hd⟩)
  have key : ∀ r : ℕ, r.Prime → p ^ f = r → p = r ∧ f = 1 := fun r hr h =>
    (Nat.Prime.pow_eq_iff hr).mp h
  rw [hK] at hmem
  obtain ⟨hex, hf1⟩ : (p = 11 ∨ p = 13 ∨ p = 29 ∨ p = 31 ∨ p = 41) ∧ f = 1 := by
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact ⟨Or.inl (key 11 (by norm_num) h).1, (key 11 (by norm_num) h).2⟩
    · exact ⟨Or.inr (Or.inl (key 13 (by norm_num) h).1), (key 13 (by norm_num) h).2⟩
    ·
      exfalso
      have hdvd : p ∣ 3 * 5 := by
        rw [show 3 * 5 = 15 by norm_num, ← h]
        exact dvd_pow_self p (by omega)
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h5
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5
        have h35 : 3 ∣ 5 ^ f := ⟨5, by omega⟩
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h35) (by norm_num)
    · exact ⟨Or.inr (Or.inr (Or.inl (key 29 (by norm_num) h).1)), (key 29 (by norm_num) h).2⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (key 31 (by norm_num) h).1))),
        (key 31 (by norm_num) h).2⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (key 41 (by norm_num) h).1))),
        (key 41 (by norm_num) h).2⟩
  subst hf1
  have hp105 : ¬ p ∣ 105 := by
    rcases hex with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hconj : ∀ ν : Kˣ, ¬ IsSquare (ν : K) →
      Excl1411 (pglAction K (ProjGenLinGroup.mk (swapGL ν))) → Excl1411 (pglAction K g) := by
    intro ν hν hE
    obtain ⟨h, hh⟩ := exists_conj_swap_of_involution hK2 ν hν hg2 hg1
    have e : ∀ g' : PGL2 K, h * g * h⁻¹ = g' → Excl1411 (pglAction K g') →
        Excl1411 (pglAction K g) := by
      rintro g' rfl hE'
      refine Excl1411.of_conj (pglAction K h) ?_
      rwa [map_mul, map_mul, map_inv] at hE'
    rcases hh with hh | hh
    · exact e _ hh (excl1411_pglAction_swapGL_one hp2 hp105)
    · exact e _ hh hE
  by_cases h31 : p = 31
  · subst h31
    have hν : ¬ IsSquare ((-1 : Kˣ) : K) := by
      have := Fintype.ofFinite K
      rw [Units.val_neg, Units.val_one, FiniteField.isSquare_neg_one_iff,
        ← Nat.card_eq_fintype_card, hK]
      norm_num
    exact hconj (-1) hν (Or.inr (Or.inr (Or.inr
      (exists_sixteen_dvd_orderOf_L2_31 (by exact_mod_cast CharP.cast_eq_zero K 31)))))
  · have h15 : (15 : K) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff K p 15).mp (by exact_mod_cast h0)
      rcases hex with rfl | rfl | rfl | rfl | rfl <;> norm_num at this
    obtain ⟨ν, hν, hν1⟩ := exists_not_isSquare_sq_ne_one hK2 h15
    refine hconj ν hν (excl1411_of_word1411_prime hp hp2 ?_
      (exists_word1411_pglAction_swapGL_dvd ν hν1))
    intro e he1 he8
    rcases hex with rfl | rfl | rfl | rfl | rfl
    · interval_cases e <;> norm_num
    · interval_cases e <;> norm_num
    · interval_cases e <;> norm_num
    · exact absurd rfl h31
    · interval_cases e <;> norm_num

theorem excl1411_psl2FieldAut [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h25 : p ^ f ≠ 25) (h49 : p ^ f ≠ 49)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) : Excl1411 (psl2FieldAut K σ) := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm, rfl, hσx⟩ := exists_eq_two_mul_of_orderOf_ringEquiv_eq_two hp hK hσ
  by_cases hp57 : p = 5 ∨ p = 7
  ·
    have hm2 : 2 ≤ m := by
      by_contra hlt
      obtain rfl : m = 1 := by omega
      rcases hp57 with rfl | rfl
      · exact h25 (by norm_num)
      · exact h49 (by norm_num)
    obtain ⟨n, hn, hnr, hn105⟩ := exists_odd_dvd_pow_add_one_not_dvd_105 hp57 hm2
    have hr : 2 ≤ p ^ m := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    obtain ⟨x, hx⟩ := exists_field_split_dvd_orderOf σ hr (by rw [hK, pow_mul']) hσx hn hnr
    exact excl1411_of_odd_not_dvd_105 hn hn105 hx
  ·
    push Not at hp57
    have hp105 : ¬ p ∣ 105 := by
      intro hd
      rcases eq_of_dvd_105 hd with h | h | h | h | h | h | h | h <;> subst h
      · exact absurd hp (by norm_num)
      · exact hp3 rfl
      · exact hp57.1 rfl
      · exact hp57.2 rfl
      all_goals exact absurd hp (by norm_num)
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
      by_contra hall
      push Not at hall
      have h1 : σ = 1 := RingEquiv.ext hall
      rw [h1, orderOf_one] at hσ
      exact absurd hσ (by norm_num)
    obtain ⟨x, hx⟩ := exists_field_unipotent_dvd_orderOf σ hb
    exact excl1411_of_odd_not_dvd_105 (hp.odd_of_ne_two hp2) hp105 hx

theorem excl1411_psl2_odd [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 9 < p ^ f)
    (α : MulAut (PSL2 K)) (hα : orderOf α = 2) : Excl1411 α := by
  by_cases h25 : p ^ f = 25
  · obtain ⟨x₁, x₂, x₃, hx⟩ := exists_word1411_L2_25 (by rw [hK, h25]) α hα
    exact Or.inr (Or.inl ⟨x₁, x₂, x₃, 13, 1, by norm_num, by norm_num, le_rfl,
      fun e he1 he8 => by interval_cases e <;> norm_num, by rwa [pow_one]⟩)
  by_cases h49 : p ^ f = 49
  · obtain ⟨x₁, x₂, x₃, hx⟩ := exists_word1411_L2_49 (by rw [hK, h49]) α hα
    exact Or.inr (Or.inl ⟨x₁, x₂, x₃, 5, 2, by norm_num, by norm_num, by norm_num,
      fun e he1 he8 => by interval_cases e <;> norm_num, hx⟩)
  rcases eq_pglAction_or_eq_conj_psl2FieldAut α hα with ⟨g, hg1, hg2, rfl⟩ | ⟨σ, hσ, β, rfl⟩
  · exact excl1411_pglAction_of_involution hK hp2 hp3 hq hg1 hg2
  · exact (excl1411_psl2FieldAut hK hp2 hp3 h25 h49 hσ).conj β

end Field

theorem noSmall1411_L2_odd {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    (h : Hyp1411 X L S) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 9 < p ^ f)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p f))) :
    NoSmall1411 X L S := by
  obtain ⟨e⟩ := hL
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  set ε := e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p f)) with hε
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
    have := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p f) le_rfl
      (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega))
    exact e.isSimpleGroup
  have hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥ := by
    have e1 := Subgroup.map_center_eq ε
    rw [psl2_center_eq_bot] at e1
    exact (Subgroup.map_eq_bot_iff_of_injective _ ε.injective).mp e1
  refine noSmall1411_of_forall_excl h hsimp hZ fun α hα => Excl1411.of_congr ε ?_
  exact excl1411_psl2_odd hcard hp2 hp3 hq _ (by rw [MulEquiv.orderOf_eq]; exact hα)

end CFSG.RankThree.PartTwo.Sec20

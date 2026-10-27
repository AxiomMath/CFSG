module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3SylowOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3SylowCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3SylowDiag
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s16k_z3_odd_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup S16kGL6} (hE1 : IsElemAbelian p E) {x : S16kGL6} (hx : x ∈ E) :
    Odd (orderOf x) := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hE1.2 x hx)
  rcases hp.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
  · rw [h]; exact odd_one
  · rw [h]; exact hp.odd_of_ne_two hp2

private theorem s16k_z3_le_cent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup S16kGL6} (hH : H ≤ Subgroup.normalizer (s16kScal : Set S16kGL6))
    {E : Subgroup S16kGL6} (hEH : E ≤ H) (hE1 : IsElemAbelian p E) :
    E ≤ Subgroup.centralizer (s16kScal : Set S16kGL6) := by
  intro x hx
  exact s16k_z3_odd_cent (hH (hEH hx)) (s16k_z3_odd_orderOf hp hp2 hE1 hx)

private theorem s16k_z3_prime_dvd_181440 {p : ℕ} (hp : p.Prime) (h : p ∣ 181440) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h237 : p ∣ 2 ^ 6 ∨ p ∣ 3 ^ 4 ∨ p ∣ 5 ∨ p ∣ 7 := by
    have hf : 181440 = 2 ^ 6 * 3 ^ 4 * 5 * 7 := by norm_num
    rw [hf] at h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hpq {q : ℕ} (hq : q.Prime) (h : p ∣ q) : p = q := by
    rcases (Nat.dvd_prime hq).mp h with h1 | h1
    · exact absurd h1 hp.ne_one
    · exact h1
  rcases h237 with h | h | h | h
  · exact Or.inl (hpq (by norm_num) (hp.dvd_of_dvd_pow h))
  · exact Or.inr (Or.inl (hpq (by norm_num) (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr (Or.inl (hpq (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (hpq (by norm_num) h)))

private theorem s16k_z3_sq_not_dvd_181440 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 181440 := by
  intro h
  have hdvd : p ∣ 181440 := (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h
  rcases s16k_z3_prime_dvd_181440 hp hdvd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at h
  · norm_num at h

private theorem s16k_z3_pow_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (h : p ^ n ∣ 181440) : p ^ n ≤ p := by
  by_cases hn : n = 0
  · rw [hn, pow_zero]; exact hp.one_le
  · by_cases hn1 : n = 1
    · rw [hn1, pow_one]
    · have hn2 : 2 ≤ n := by omega
      exfalso
      exact s16k_z3_sq_not_dvd_181440 hp hp2 hp3 ((pow_dvd_pow p hn2).trans h)

theorem s16k_z3_pRank_le {H : Subgroup S16kGL6}
    (hH : H ≤ Subgroup.normalizer (s16kScal : Set S16kGL6)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p H ≤ if p = 3 then 3 else 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEH hE1
  have hEcent : E ≤ Subgroup.centralizer (s16kScal : Set S16kGL6) :=
    s16k_z3_le_cent hp hp2 hH hEH hE1
  have hdiv : Nat.card E ∣ 181440 :=
    (Subgroup.card_dvd_of_le hEcent).trans s16k_z3_cent_card_dvd
  by_cases hp3 : p = 3
  · rw [if_pos hp3, hp3]
    have hE1' : IsElemAbelian 3 E := hp3 ▸ hE1
    obtain ⟨c, hc, hcD⟩ := s16k_z3_elem3_diag hEcent hE1'
    calc Nat.card E = Nat.card (E.map (MulAut.conj c).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
      _ ≤ Nat.card s16kDiag := Subgroup.card_le_of_le hcD
      _ = 27 := s16k_diag_card
      _ = 3 ^ 3 := by norm_num
  · rw [if_neg hp3, pow_one]
    haveI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p ↥E := fun x => ⟨1, by
      show x ^ p ^ 1 = 1
      rw [pow_one]
      exact Subtype.ext (by simpa using hE1.2 (x : S16kGL6) x.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥E)).mp hpg
    have hpn : p ^ n ∣ 181440 := hn ▸ hdiv
    rw [hn]
    exact s16k_z3_pow_le_of_dvd hp hp2 hp3 hpn

theorem s16k_z3_e27_conj {E : Subgroup S16kGL6}
    (hE : E ≤ Subgroup.normalizer (s16kScal : Set S16kGL6)) (hE1 : IsElemAbelian 3 E)
    (hE2 : Nat.card E = 3 ^ 3) :
    ∃ n ∈ Subgroup.normalizer (s16kScal : Set S16kGL6),
      E = s16kDiag.map (MulAut.conj n).toMonoidHom := by
  have hEcent : E ≤ Subgroup.centralizer (s16kScal : Set S16kGL6) :=
    s16k_z3_le_cent (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) hE
      (le_refl E) hE1
  obtain ⟨c, hc, hcD⟩ := s16k_z3_elem3_diag hEcent hE1
  have hcard : Nat.card (E.map (MulAut.conj c).toMonoidHom) = Nat.card s16kDiag := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hE2, s16k_diag_card]
    norm_num
  have hEq : E.map (MulAut.conj c).toMonoidHom = s16kDiag :=
    Subgroup.eq_of_le_of_card_ge hcD (le_of_eq hcard.symm)
  refine ⟨c⁻¹, (Subgroup.normalizer (s16kScal : Set S16kGL6)).inv_mem
    (Subgroup.centralizer_le_normalizer _ hc), ?_⟩
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id S16kGL6 := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    group
  have hmap := congrArg (fun K : Subgroup S16kGL6 =>
    K.map (MulAut.conj c⁻¹).toMonoidHom) hEq
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
  exact hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowAlt8
public import CFSG.Quasithin.Background.GoldschmidtM12SylowFam
public import CFSG.Quasithin.Background.GoldschmidtM12SylowL2
public import CFSG.Quasithin.Background.GoldschmidtM12SylowL3
public import CFSG.Quasithin.Background.GoldschmidtM12SylowSz8
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace M12Sylow

section Certificates


theorem excl64_or_of_sqtkSimpleList {S : Type} [Group S] [Finite S]
    (h : CFSG.Milestones.SQTKSimpleList S) :
    Excl64 S ∨ Nonempty (S ≃* ↥NativeSporadic.M12) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSL 3 p 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSU 3 p 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSL 2 p 2) := by
  rcases h with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hmodel⟩ | (hchar | htits) | ⟨n, hn, hmodel⟩ |
    ⟨s, hs, ⟨e⟩⟩
  ·
    left
    by_cases h8 : n = 8
    · subst h8
      exact Excl64.of_equiv excl64_alternating_eight e
    · exact Excl64.of_equiv (excl64_alternating hn5 (by omega)) e
  ·
    rcases hmodel with ⟨f, hf, hmod⟩ | h3 | h3
    · rcases hf with rfl | rfl
      · exact Or.inl (excl64_psl_two_odd_prime hp hp2 hmod)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hmod⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, h3⟩)))
  ·
    left
    obtain ⟨f, hf⟩ := hchar
    rcases hf with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hodd, hf, h⟩ |
      ⟨hodd, hf, h⟩
    · exact excl64_psl_two_even hf h
    · by_cases h1 : f = 1
      · subst h1
        exact excl64_psl_three_two h
      · by_cases h2 : f = 2
        · subst h2
          exact excl64_psl_three_four h
        · exact excl64_of_psl_char_two (n := 3) h (by norm_num; omega)
    · by_cases h2 : f = 2
      · subst h2
        exact excl64_psu_three_four h
      · exact excl64_of_psu_char_two (n := 3) h (by norm_num; omega)
    · exact excl64_of_psp_char_two (n := 2) h (by norm_num; omega)
    · exact excl64_of_g2 hf h
    · exact excl64_of_trialityD4 hf h
    · exact excl64_of_twistedF4 h
    · by_cases h3 : f = 3
      · subst h3
        exact excl64_suzuki_eight h
      · exact excl64_of_suzuki (by obtain ⟨k, hk⟩ := hodd; omega) h
  ·
    exact Or.inl (excl64_of_tits htits)
  ·
    left
    rcases hn with rfl | rfl
    · obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨by decide, hmodel⟩)
      exact Excl64.of_equiv excl64_alternating_eight e
    · exact excl64_of_psl_char_two (n := 5) (f := 1) hmodel (by norm_num)
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (excl64_m11 (e : S ≃* ↥NativeSporadic.M11))
    · exact Or.inr (Or.inl ⟨(e : S ≃* ↥NativeSporadic.M12)⟩)
    · exact Or.inl (excl64_m22 (e : S ≃* ↥NativeSporadic.M22))
    · exact Or.inl (excl64_m23 (e : S ≃* ↥NativeSporadic.M23))
    · exact Or.inl (excl64_of_sporadic_large (Or.inl rfl) e)
    · exact Or.inl (excl64_j1 (e : S ≃* NativeSporadic.J1))
    · exact Or.inl (excl64_j2 (e : S ≃* NativeSporadic.J2))
    · exact Or.inl (excl64_of_sporadic_large (Or.inr (Or.inl rfl)) e)
    · exact Or.inl (excl64_of_sporadic_large (Or.inr (Or.inr (Or.inl rfl))) e)
    · exact Or.inl (excl64_of_sporadic_large (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e)
    · exact Or.inl (excl64_of_sporadic_large (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) e)

end Certificates

end M12Sylow

end CFSG.Quasithin.F6

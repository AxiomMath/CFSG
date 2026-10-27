module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s21_15Two_of_s21_15N {D : Data G} {Ch : Choice2011 G} (hsig : D.sig.Nonempty)
    (h15 : S21_15N D Ch) : S21_15Two D Ch := by
  intro h1930 c L hL n hLS hne
  obtain ⟨s, hso, hs1, hsn⟩ := uc22p2213c_exists_odd hLS
  have hs3 : 3 ≤ s := by obtain ⟨j, rfl⟩ := hso; omega
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (n := 2 ^ s - 1) (by
    have : 2 ^ 3 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
    omega)
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr (fun h => Or.inl h.1)
  obtain ⟨A, hA, hAL⟩ := uc22ine229_exists_sub hLS' hsn hr hrs
  obtain ⟨p, hp⟩ := hsig
  exact (h15 h1930 c L hL n hLS' hne s hso hsn r hr hrs p hp A hA hAL).2.1

end CFSG.LocalAnalysis.UniquenessCase.UC22

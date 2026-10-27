module

public import CFSG.Quasithin.Background.F7TwoInvL2Even
public import CFSG.Quasithin.Background.F7TwoInvL2Odd

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank

theorem invAutGen_of_statedPSL2 {L : Type} [Group L] {p f : ℕ}
    (h : StatedClassicalModel L .PSL 2 p f) :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  by_cases hp2 : p = 2
  · subst hp2
    exact invAutGen_of_statedPSL2_two h
  · obtain ⟨hp, -, h4, K, _, _, hK, ⟨e⟩⟩ := exists_psl2_of_statedClassicalModel h
    have : Fact p.Prime := ⟨hp⟩
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact invAutGen_of_mulEquiv_forall e (invAutGen_psl2_odd hp2 hK h5)

end CFSG.Quasithin.F7Two

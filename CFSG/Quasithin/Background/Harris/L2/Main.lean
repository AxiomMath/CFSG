module

public import CFSG.Quasithin.Background.Harris.L2.Cases
public import CFSG.Quasithin.Background.Harris.L2.Numerics
public import CFSG.Quasithin.Background.Harris.L2.Rank

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem oneCompFor_famL2_of_cases (h6 : Case6Input) (h7 : Case7Input) (h16 : Case16Input) :
    OneCompFor FamL2 := by
  rintro V _ _ _ Γ A L m hs ⟨-, f, hf, hmodel⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_sl2 hmodel
  let _inst : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  obtain ⟨d, J, hd1, hDcard, hJne, hJn, hshift, hdimD, hdim⟩ :=
    exists_descent_data (by omega) hFcard φ hs.L_irr
  have hmf := m_le_of_sl2 hs hf φ
  have hbound : d * 2 ^ J.card ≤ 2 * f + 2 := by
    have := hs.bound
    rw [hdim] at this
    omega
  rcases l2_numerics hf hd1 hJne hJn hshift hbound with ⟨hJ1, rfl⟩ | ⟨hJ2, rfl⟩ |
    ⟨hJ3, rfl, rfl⟩
  · have h := h6 V Γ A L m d hs hf φ hmf hDcard (by rw [hdimD, hJ1]; rfl)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · have h := h7 V Γ A L m d hs hd1 φ hmf hDcard (by rw [hdimD, hJ2]; rfl)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · have h := h16 V Γ A L m hs φ hmf hDcard (by rw [hdimD, hJ3]; rfl)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))

end CFSG.Quasithin.G11.Harris.L2

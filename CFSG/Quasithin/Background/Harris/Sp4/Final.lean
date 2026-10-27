module

public import CFSG.Quasithin.Background.Harris.Sp4.Main

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

theorem oneCompFor_famSp4 : OneCompFor FamSp4 := by
  rintro V _ _ _ Γ A L m hs ⟨-, f, hf, hmodel⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_antiSp hmodel
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (case9_holds hs hf φ))))))))))

end CFSG.Quasithin.G11.Harris.Sp4

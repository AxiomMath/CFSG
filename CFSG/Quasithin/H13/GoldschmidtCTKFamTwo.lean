module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoLin
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoSp
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoG2
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoD4
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoF4
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoTits

public section

namespace CFSG.Quasithin.H13.CTK

theorem exclA5BlockFor_two : ExclA5BlockFor fun S _ => SQTKTwoFam S := by
  have h := exclA5BlockFor_bender.or (exclA5BlockFor_two_lin.or (exclA5BlockFor_two_sp.or
    (exclA5BlockFor_two_g2.or (exclA5BlockFor_two_d4.or
      (exclA5BlockFor_two_f4.or exclA5BlockFor_two_tits)))))
  refine ExclA5BlockFor.mono (fun S _ hS => ?_) h
  rcases hS with ⟨f, h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8⟩ | h9
  · exact Or.inl (Or.inl ⟨f, h1⟩)
  · exact Or.inr (Or.inl ⟨f, h2⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨f, h3⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨f, h4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h5⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h6⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h7⟩)))))
  · exact Or.inl (Or.inr (Or.inr ⟨f, h8⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h9)))))

end CFSG.Quasithin.H13.CTK

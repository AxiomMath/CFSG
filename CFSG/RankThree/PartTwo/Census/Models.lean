module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G]

theorem iiModel_of_projSU_five_two (e : G ≃* projSU 5 2 1) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inl ⟨e⟩)))

theorem iiModel_of_projSU_six_two (e : G ≃* projSU 6 2 1) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨e⟩))))

theorem iiModel_of_projSL_six_two (e : G ≃* projSL 6 (GaloisField 2 1)) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨e⟩)))))

theorem iiModel_of_projSL_seven_two (e : G ≃* projSL 7 (GaloisField 2 1)) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))

theorem iiModel_of_projSp_four_two (e : G ≃* projSp 4 (GaloisField 2 1)) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))

theorem iiModel_of_projOmegaPlus_four_two (e : G ≃* projOmegaPlus 4 (GaloisField 2 1)) :
    IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))))

theorem iiModel_of_projOmegaMinus_three_two {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* projOmegaMinus 3 (GaloisField 2 1) b c) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨b, c, hbc, ⟨e⟩⟩)))))))))

theorem iiModel_of_projSL_four_four (e : G ≃* projSL 4 (GaloisField 2 2)) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨e⟩))))))))))

theorem iiModel_of_projSp_three_four (e : G ≃* projSp 3 (GaloisField 2 2)) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨e⟩)))))))))))

theorem iiModel_of_projSU_five_eight (e : G ≃* projSU 5 2 3) : IIModel G :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨e⟩)))))))))))

end CFSG.RankThree.PartTwo.Census

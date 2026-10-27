
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

namespace A36A

open CFSG.SectionRank CFSG.Assembly.LowTwoRank

theorem a23List_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : A23List T) :
    A23List S := by
  rcases h with ⟨n, h5, h8, ⟨e'⟩⟩ | ⟨p, hp, hp2, h⟩ | (⟨f, hf⟩ | hT) | ⟨n, hn, h⟩ |
    ⟨s, hs, ⟨e'⟩⟩
  · exact Or.inl ⟨n, h5, h8, ⟨e.trans e'⟩⟩
  · refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    rcases h with ⟨f, hf, hm⟩ | hm | hm
    · exact Or.inl ⟨f, hf, statedClassicalModel_of_mulEquiv e hm⟩
    · exact Or.inr (Or.inl (statedClassicalModel_of_mulEquiv e hm))
    · exact Or.inr (Or.inr (statedClassicalModel_of_mulEquiv e hm))
  · refine Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩)))
    rcases hf with ⟨a, hm⟩ | ⟨a, hm⟩ | ⟨a, hm⟩ | ⟨a, hm⟩ | ⟨a, hm⟩ | ⟨a, hm⟩ | ⟨a, b, hm⟩ |
      ⟨a, b, hm⟩
    · exact Or.inl ⟨a, statedClassicalModel_of_mulEquiv e hm⟩
    · exact Or.inr (Or.inl ⟨a, statedClassicalModel_of_mulEquiv e hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, statedClassicalModel_of_mulEquiv e hm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, statedClassicalModel_of_mulEquiv e hm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, chevalleyExceptionalModel_of_mulEquiv e hm⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a, chevalleyExceptionalModel_of_mulEquiv e hm⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a, b, reeTitsModel_of_mulEquiv e hm⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨a, b, suzukiModel_of_mulEquiv e hm⟩))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (reeTitsModel_of_mulEquiv e hT))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, statedClassicalModel_of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, ⟨e.trans e'⟩⟩)))

end A36A

end CFSG.Quasithin

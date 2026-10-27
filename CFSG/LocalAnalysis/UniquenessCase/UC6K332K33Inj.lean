module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Lists

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)

variable {L : Type} [Group L]

theorem K33Models.of_isAlt_seven (h : UC22.IsAlt L 7) : K33Models L :=
  Or.inl (Or.inl h)

theorem K33Models.of_isAlt_six (h : UC22.IsAlt L 6) : K33Models L :=
  Or.inl (Or.inr h)

theorem K33Models.of_psl3_three_one (h : LieModel L .PSL 3 3 1) : K33Models L :=
  Or.inr (Or.inl (Or.inl h))

theorem K33Models.of_psu3_three_one (h : LieModel L .PSU 3 3 1) : K33Models L :=
  Or.inr (Or.inl (Or.inr h))

theorem K33Models.of_psl3 {p f : ℕ} (hq : p ^ f % 3 = 1) (h : LieModel L .PSL 3 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inl ⟨p, f, hq, h⟩)))

theorem K33Models.of_psu3 {p f : ℕ} (hq : p ^ f % 3 = 2) (h : LieModel L .PSU 3 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨p, f, hq, h⟩))))

theorem K33Models.of_psp4 {p f : ℕ} (h : LieModel L .PSp 2 p f) : K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩)))))

theorem K33Models.of_g2 {p f : ℕ} (h : LieModel L .G2 0 p f) : K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩))))))

theorem K33Models.of_trialityD4 {p f : ℕ} (h : LieModel L .trialityD4 0 p f) : K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩)))))))

theorem K33Models.of_twistedF4 {f : ℕ} (h : LieModel L .twistedF4 0 2 f) : K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩))))))))

theorem K33Models.of_tits (h : LieModel L .Tits 0 2 1) : K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem K33Models.of_psl4 {p f : ℕ} (hq : p ^ f % 3 = 2) (h : LieModel L .PSL 4 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨p, f, hq, h⟩))))))))))

theorem K33Models.of_psu4 {p f : ℕ} (hq : p ^ f % 3 = 1) (h : LieModel L .PSU 4 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨p, f, hq, h⟩)))))))))))

theorem K33Models.of_psl5 {p f : ℕ} (hq : p ^ f % 3 = 2) (h : LieModel L .PSL 5 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hq, h⟩))))))))))))

theorem K33Models.of_psu5 {p f : ℕ} (hq : p ^ f % 3 = 1) (h : LieModel L .PSU 5 p f) :
    K33Models L :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hq, h⟩))))))))))))

theorem K33Models.of_spor {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨
      s = .Ru ∨ s = .J4)
    (h : UC22.IsSpor L s) : K33Models L :=
  Or.inr (Or.inr (Or.inr ⟨s, hs, h⟩))

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

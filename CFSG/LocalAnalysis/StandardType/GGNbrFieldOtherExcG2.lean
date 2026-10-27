module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcHead
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcRowG2
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixG2
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Rows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFieldOtherG2Dvd_subfield {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherG2DvdLabel p lab) :
    p ∣ 2 ^ (lab.n / p) - 1 ∧ 2 ≤ lab.n / p := by
  obtain ⟨hdvd, -, hp5, hq⟩ := h
  have hq₀ : p ∣ 2 ^ (lab.n / p) - 1 := (ggFermat_dvd_two_pow_sub_one_iff hp hdvd).mp hq
  refine ⟨hq₀, ?_⟩
  have h1 : 1 ≤ lab.n / p := Nat.div_pos (Nat.le_of_dvd hlab.1 hdvd) hp.pos
  by_contra h2
  have he : lab.n / p = 1 := by omega
  rw [he] at hq₀
  exact absurd (Nat.le_of_dvd (by norm_num) hq₀) (by omega)

theorem ggFieldKLevel_G2Dvd
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherG2DvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  refine ggFieldKLevel_of_fixKnownRowTwo
    (S := fun p lab => p.Prime ∧ LargeEvenInLambda2 lab ∧ GGFieldOtherG2DvdLabel p lab)
    (Rw := fun p lab => lab.tag = .G2 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) ?_ ?_ ?_ ?_ ?_
    hpc hconj hcen hinn p lab hp hp2 hlab ⟨hp, hlab, hS⟩
  · rintro p lab ⟨hp, hlab, h⟩
    obtain ⟨hq₀, -⟩ := ggFieldOtherG2Dvd_subfield hp hlab h
    exact ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2⟩, ⟨h.2.1, h.2.2.1, hq₀⟩⟩
  · rintro p lab - ⟨hp, hlab, h⟩
    obtain ⟨-, h2⟩ := ggFieldOtherG2Dvd_subfield hp hlab h
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨-, ht, -, -⟩ := h
    dsimp only at ht h2 ⊢
    subst ht
    exact ⟨le_trans (by norm_num) h2, hlab.2.1, h2⟩
  · rintro p lab ⟨ht, -, -⟩
    refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'
  · rintro p lab hp hp2 hlab ⟨-, -, h⟩
    obtain ⟨-, h2⟩ := ggFieldOtherG2Dvd_subfield hp hlab h
    exact ggFieldFixKnown_G2 p lab hp hp2 hlab ⟨h.2.1, h2⟩
  · rintro p lab hp - hlab ⟨ht, hp5, hq⟩
    exact largeEvenLabelAll_rowPlainTwo_G2Dvd hp hp5 hlab ⟨ht, hq⟩

end CFSG.StandardType

end

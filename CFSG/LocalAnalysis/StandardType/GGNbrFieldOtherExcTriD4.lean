module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcHead
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Rows
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTriD4Fix
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTriD4Weyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFieldKLevel_triD4Dvd
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTriD4DvdLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo
    (Rw := fun p lab => lab.tag = .triD4 ∧ p ≠ 3 ∧ (p.Prime → p ∣ 2 ^ lab.n - 1))
    (fun _ _ ⟨hd, ht, hp3, hpq⟩ => ⟨hd, ⟨ht, hp3, fun _ => hpq⟩,
      ⟨ht, hp3, fun hp => (ggFermat_dvd_two_pow_sub_one_iff hp hd).mp hpq⟩⟩)
    (fun p lab hlab ⟨hd, ht, _, _⟩ => by
      obtain ⟨t, l, n⟩ := lab
      dsimp only at ht hd ⊢
      subst ht
      obtain ⟨hn1, hl⟩ := hlab
      exact ⟨Nat.div_pos (Nat.le_of_dvd hn1 hd) (Nat.pos_of_dvd_of_pos hd hn1), hl⟩)
    (fun _ _ ⟨ht, hp3, _⟩ =>
      ⟨fun ⟨h, _⟩ => (by rw [ht] at h; cases h), fun ⟨_, h⟩ => hp3 h⟩)
    (fun p lab hp hp2 hlab ⟨_, ht, hp3, _⟩ => ggFieldFixKnown_triD4 p lab hp hp2 hlab ⟨ht, hp3⟩)
    (fun p _ hp hp2 hlab ⟨ht, hp3, hpq⟩ => largeEvenLabelAll_rowPlainTwo_triD4 hp
      (by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by norm_num)
        omega)
      hlab ⟨ht, hpq hp⟩)
    hpc hconj hcen hinn

end CFSG.StandardType

end

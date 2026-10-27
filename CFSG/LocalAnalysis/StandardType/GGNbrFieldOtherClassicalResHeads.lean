module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResSp4Eight
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveFix
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherSp4EightLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 3

section Sp4Eight


theorem ggFieldKLevel_sp4Eight (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherSp4EightLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKX (Kp := fun _ k => ¬ 3 ∣ k) (S := GGFieldOtherSp4EightLabel)
    (fun _ _ _ hab hb ha => hb (ha.trans hab))
    (fun _ _ ⟨hBC, _⟩ => by
      refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases hBC with h'' | h'' <;> rw [h''] at h' <;>
        cases h')
    (fun p _ _ _ _ ⟨hBC, hl, hp, hn⟩ => by
      subst hp
      exact largeEvenLabelAll_rowKX_sp4Eight ⟨hBC, hl, hn⟩)
    (fun p _ _ _ _ ⟨hBC, hl, hp, hn⟩ => by
      subst hp
      exact largeEvenLabelAll_fixKX_sp4Eight ⟨hBC, hl, hn⟩)
    hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_sp4Eight (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherSp4EightLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_sp4Eight hpc hconj hcen hinn) hT

end Sp4Eight

@[expose] def GGFieldOtherU5FiveLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 4 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n + 1 ∧ 5 ∣ lab.n

theorem ggFieldOther_twA_not {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .twA) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'

section Unitary


theorem ggFieldKLevel_u5Five (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherU5FiveLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKX (Kp := fun _ k => k ∣ 5) (S := GGFieldOtherU5FiveLabel)
    (fun _ _ _ hab hb => hab.trans hb) (fun _ _ ⟨ht, _⟩ => ggFieldOther_twA_not ht)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd⟩ => by
      subst hp
      exact largeEvenLabelAll_rowKX_u5Five hlab ⟨ht, hl, hq, hd⟩)
    (fun p _ _ _ hlab ⟨ht, hl, hp, hq, hd⟩ => by
      subst hp
      exact largeEvenLabelAll_fixKX_u5Five hlab ⟨ht, hl, hq, hd⟩)
    hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_u5Five (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherU5FiveLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_u5Five hpc hconj hcen hinn) hT

end Unitary

end CFSG.StandardType

end

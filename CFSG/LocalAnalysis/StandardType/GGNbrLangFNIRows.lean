module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def KGFieldNotInnerInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    ¬ GGNbrLangT3Label p lab → S p lab → LargeEvenLabelAll lab (KGFieldNotInnerCont p)

theorem KGFieldNotInnerInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : KGFieldNotInnerInputOn S) :
    KGFieldNotInnerInputOn S' :=
  fun p lab hp hp2 hlab ht3 hS' => h p lab hp hp2 hlab ht3 (hS p lab hS')

theorem kgFieldNotInnerInput_of_on (h : KGFieldNotInnerInputOn fun _ _ => True) :
    KGFieldNotInnerInput :=
  fun p lab hp hp2 hlab ht3 => h p lab hp hp2 hlab ht3 trivial

@[expose] def kgfniFieldDegree (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .twA | .twD | .twE6 => 2
  | .triD4 => 3
  | _ => 1

inductive KGFNIFamily
  | linear | unitary | symplectic | orthogonal | g2 | f4 | e6 | e7 | e8 | triality | suzuki | ree
  | derived
  deriving DecidableEq

@[expose] def KGFNIFamily.tagCase : KGFNIFamily → LargeEvenLieTag → Prop
  | .linear, t => t = .A
  | .unitary, t => t = .twA
  | .symplectic, t => t = .B ∨ t = .C
  | .orthogonal, t => t = .D ∨ t = .twD
  | .g2, t => t = .G2
  | .f4, t => t = .F4
  | .e6, t => t = .E6 ∨ t = .twE6
  | .e7, t => t = .E7
  | .e8, t => t = .E8
  | .triality, t => t = .triD4
  | .suzuki, t => t = .twB2
  | .ree, t => t = .twF4
  | .derived, t => t = .B2der ∨ t = .G2der ∨ t = .twF4der

@[expose] def kgfniFamily : LargeEvenLieTag → KGFNIFamily
  | .A => .linear
  | .twA => .unitary
  | .B | .C => .symplectic
  | .D | .twD => .orthogonal
  | .G2 => .g2
  | .F4 => .f4
  | .E6 | .twE6 => .e6
  | .E7 => .e7
  | .E8 => .e8
  | .triD4 => .triality
  | .twB2 => .suzuki
  | .twF4 => .ree
  | .B2der | .G2der | .twF4der => .derived

theorem kgfniFamily_tagCase (t : LargeEvenLieTag) : (kgfniFamily t).tagCase t := by
  cases t <;> simp [kgfniFamily, KGFNIFamily.tagCase]

@[expose] def kgfniRow (fam : KGFNIFamily) (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  fam.tagCase lab.tag ∧ p ∣ lab.n

theorem kgFieldNotInnerInput_of_rows (Open : KGFNIFamily → Prop)
    (hopen : KGFieldNotInnerInputOn fun p lab => Open (kgfniFamily lab.tag) ∧ p ∣ lab.n)
    (hdone : ∀ fam, ¬ Open fam → KGFieldNotInnerInputOn (kgfniRow fam))
    (hvac : KGFieldNotInnerInputOn fun p lab => ¬ p ∣ lab.n) : KGFieldNotInnerInput := by
  intro p lab hp hp2 hlab ht3
  by_cases hdvd : p ∣ lab.n
  · by_cases ho : Open (kgfniFamily lab.tag)
    · exact hopen p lab hp hp2 hlab ht3 ⟨ho, hdvd⟩
    · exact hdone (kgfniFamily lab.tag) ho p lab hp hp2 hlab ht3
        ⟨kgfniFamily_tagCase lab.tag, hdvd⟩
  · exact hvac p lab hp hp2 hlab ht3 hdvd

theorem kgFieldNotInnerCont_of_fieldConj_exponent {R : Type} [Group R] [IsSimpleGroup R]
    {I F : Set (MulAut R)} {p e : ℕ} (hp : p.Prime)
    (hna : ∃ a b : R, a * b ≠ b * a) (hc : GGRawFieldConj p R I F)
    (hpow : ∀ f ∈ F, f ^ e = 1) (hcop : Nat.Coprime p e) :
    KGFieldNotInnerCont p R I F := by
  unfold KGFieldNotInnerCont
  intro α hα hαnot hαp
  obtain ⟨u, hu, f, hf, rfl⟩ := hα
  obtain ⟨f', hf', _, _, horder, _⟩ := hc inferInstance hna u hu f hf hαnot hαp
  have hpe : p ∣ e := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one (hpow f' hf')
  have hp1 : p = 1 := hcop.eq_one_of_dvd hpe
  exact absurd hp1 hp.ne_one

theorem kgfni_tag_of_fieldDegree_eq_three {lab : LargeEvenLabel} (h : kgfniFieldDegree lab = 3) :
    lab.tag = .triD4 := by
  cases ht : lab.tag <;> simp only [kgfniFieldDegree, ht] at h ⊢ <;>
    first | rfl | (exfalso; omega)

theorem kgfni_prime_dvd_fieldDegree {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hd : p ∣ kgfniFieldDegree lab) : p = 2 ∨ (p = 3 ∧ lab.tag = .triD4) := by
  have hdvd6 : p ∣ 6 := by
    refine dvd_trans hd ?_
    cases h : lab.tag <;> simp only [kgfniFieldDegree, h] <;> decide
  have hp23 : p = 2 ∨ p = 3 := by
    have h23 : p ∣ 2 * 3 := by simpa using hdvd6
    rcases hp.dvd_mul.mp h23 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  rcases hp23 with h2 | h3
  · exact Or.inl h2
  · subst h3
    refine Or.inr ⟨rfl, kgfni_tag_of_fieldDegree_eq_three ?_⟩
    have hpos : 0 < kgfniFieldDegree lab := by
      cases h : lab.tag <;> simp only [kgfniFieldDegree, h] <;> decide
    have hle : kgfniFieldDegree lab ≤ 3 := by
      cases h : lab.tag <;> simp only [kgfniFieldDegree, h] <;> decide
    have hge : 3 ≤ kgfniFieldDegree lab := Nat.le_of_dvd hpos hd
    omega

theorem kgfni_coprime_fieldDegree_of_not_t3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht3 : ¬ GGNbrLangT3Label p lab) (hpn : ¬ p ∣ lab.n) :
    Nat.Coprime p (kgfniFieldDegree lab * lab.n) := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  rcases hp.dvd_mul.mp h with hd | hn
  · rcases kgfni_prime_dvd_fieldDegree hp hd with h2 | ⟨h3, htag⟩
    · exact hp2 h2
    · exact ht3 ⟨htag, h3⟩
  · exact hpn hn

theorem kgfni_derived_n_eq_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : KGFNIFamily.tagCase .derived lab.tag) : lab.n = 1 := by
  rcases htag with h | h | h <;>
    (simp only [LargeEvenInLambda2, h] at hlab <;> exact hlab.2.2)

theorem kgFieldNotInnerInputOn_derived : KGFieldNotInnerInputOn (kgfniRow .derived) := by
  intro p lab hp hp2 hlab ht3 hrow
  obtain ⟨htag, hdvd⟩ := hrow
  rw [kgfni_derived_n_eq_one hlab htag] at hdvd
  exact absurd (Nat.eq_one_of_dvd_one hdvd) hp.ne_one

end CFSG.StandardType

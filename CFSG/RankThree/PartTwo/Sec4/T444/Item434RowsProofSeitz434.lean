module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzL2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzL3
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Families
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def IsLie42GenericSz (X : Type) [Group X] : Prop :=
  ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid), 2 ≤ m ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)

@[expose] def IsLie42GenericRest (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsoLThreePi X p e) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo X q) ∨
      Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      Nonempty (X ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (X ≃* projSU 4 p 1))) ∨
  (∃ n : ℕ, 4 ≤ n ∧ n ≠ 6 ∧
    (IsoLThreePi X 2 n ∨
      (3 ∣ n ∧ (Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 3 2 n))) ∨
      Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 4 ≤ q.exponent ∧ q.exponent ≠ 6 ∧ IsoGTwo X q) ∨
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    4 ≤ q.exponent ∧ q.exponent ≠ 6 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), 2 ≤ m ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group))

theorem pow_mod_three_cases {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
  have h0 : p ^ e % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  omega

theorem l3_cases {X : Type} [Group X] {p e : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e)
    (h : Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (X ≃* projSU 3 p e)) :
    IsoLThreePi X p e ∨ (3 ∣ e ∧ (Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
      Nonempty (X ≃* projSU 3 p e))) ∨ IsLie42GenericL3Vac X := by
  by_cases h3e : 3 ∣ e
  · rcases pow_mod_three_cases (e := e) hp.out hp3 with h1 | h2
    · rcases h with hL | hU
      · exact Or.inl (Or.inl ⟨h1, hL⟩)
      · exact Or.inr (Or.inl ⟨h3e, Or.inr hU⟩)
    · rcases h with hL | hU
      · exact Or.inr (Or.inl ⟨h3e, Or.inl hL⟩)
      · exact Or.inl (Or.inr ⟨h2, hU⟩)
  · rcases pow_mod_three_cases (e := e) hp.out hp3 with h1 | h2
    · rcases h with hL | hU
      · exact Or.inl (Or.inl ⟨h1, hL⟩)
      · exact Or.inr (Or.inr ⟨p, e, hp, hp3, he, h3e, Or.inr ⟨h1, hU⟩⟩)
    · rcases h with hL | hU
      · exact Or.inr (Or.inr ⟨p, e, hp, hp3, he, h3e, Or.inl ⟨h2, hL⟩⟩)
      · exact Or.inl (Or.inr ⟨h2, hU⟩)

theorem isLie42Generic_cases {X : Type} [Group X] (h : IsLie42Generic X) :
    IsLie42GenericL2 X ∨ IsLie42GenericSz X ∨ IsLie42GenericL3Vac X ∨ IsLie42GenericRest X := by
  rcases h with ⟨p, e, hp, hp3, he, h2⟩ | ⟨p, e, hp, hp3, he, he2, h3⟩ | h4 | h7
  · exact Or.inl (Or.inl ⟨p, e, hp, hp3, he, h2⟩)
  · rcases l3_cases (by omega) he h3 with hpi | ⟨h3e, -⟩ | hv
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, he2, hpi⟩)))
    · exact absurd (Nat.le_of_dvd (by omega) h3e) (by omega)
    · exact Or.inr (Or.inr (Or.inl hv))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases h7 with ⟨n, hn4, hn6, h2 | h3 | hu3 | hsp | hu4⟩ | hg2 | hd4 | hsz | hf4
    · exact Or.inl (Or.inr ⟨n, hn4, hn6, h2⟩)
    · rcases l3_cases (by norm_num) (by omega) (Or.inl h3) with hpi | h3e | hv
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn4, hn6, Or.inl hpi⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨n, hn4, hn6, Or.inr (Or.inl h3e)⟩)))))
      · exact Or.inr (Or.inr (Or.inl hv))
    · rcases l3_cases (by norm_num) (by omega) (Or.inr hu3) with hpi | h3e | hv
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn4, hn6, Or.inl hpi⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨n, hn4, hn6, Or.inr (Or.inl h3e)⟩)))))
      · exact Or.inr (Or.inr (Or.inl hv))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, hn4, hn6, Or.inr (Or.inr (Or.inl hsp))⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, hn4, hn6, Or.inr (Or.inr (Or.inr hu4))⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hg2))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd4)))))))
    · exact Or.inr (Or.inl hsz)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hf4)))))))

@[expose] def IsLie42GenericD4 (X : Type) [Group X] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    4 ≤ q.exponent ∧ q.exponent ≠ 6 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def Seitz434Rest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsLie42GenericRest (X ⧸ Subgroup.center X) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E →
      ((Nat.card E = 9 ∧ ¬ IsLie42GenericD4 (X ⧸ Subgroup.center X)) ∨
        (Nat.card E = 27 ∧ Subgroup.center X = ⊥)) →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

end CFSG.RankThree.PartTwo.Sec4

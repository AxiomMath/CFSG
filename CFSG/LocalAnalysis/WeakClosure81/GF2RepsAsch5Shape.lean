module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup InFGroup IsOmegaColl)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  (W4Lem4_10 W4Lem4_11 IsCoverL3OddOver IsCoverU3OddOver)
open CFSG.Blueprint (LieModel)

theorem isoInvPred_isAlt (n : ℕ) : IsoInvPred (fun X _ => IsAlt X n) :=
  fun _ _ _ _ ⟨e⟩ ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isoInvPred_lieModel (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ) :
    IsoInvPred (fun X _ => LieModel X t n p f) :=
  fun _ _ _ _ ⟨e⟩ h => CFSG.GH74.lieModel_of_mulEquiv e h

theorem isoInvPred_f6IsL2 (p e : ℕ) : IsoInvPred (fun X _ => F6.IsL2 p e X) :=
  fun _ _ _ _ ⟨e'⟩ h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e' h

theorem isoInvPred_or {P₁ P₂ : ∀ (X : Type) [Group X], Prop} (h₁ : IsoInvPred P₁)
    (h₂ : IsoInvPred P₂) : IsoInvPred (fun X _ => P₁ X ∨ P₂ X) :=
  fun X Y _ _ e h => h.elim (fun h => Or.inl (h₁ X Y e h)) (fun h => Or.inr (h₂ X Y e h))

theorem two_mul_card_isL2_odd {X : Type} [Group X] [Finite X] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : F6.IsL2 p e X) : 2 * Nat.card X = p ^ e * ((p ^ e) ^ 2 - 1) := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  have := CFSG.ComponentClassification.UnbalancingLocal.two_mul_card_psl_two_of_odd K hodd
  rw [Nat.card_congr e'.toEquiv, mul_comm, this, hcard]

theorem not_isAlt_five_of_isL2_odd {X : Type} [Group X] [Finite X] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : p ^ e ≠ 5) (h : F6.IsL2 p e X) : ¬ IsAlt X 5 := by
  rintro ⟨e'⟩
  have h60 : Nat.card X = 60 := by
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h2 := two_mul_card_isL2_odd hp hp2 h
  rw [h60] at h2
  generalize p ^ e = q at h2 hq
  have hq10 : q ≤ 10 := by
    by_contra hc
    have h1 : 121 ≤ q ^ 2 := by nlinarith
    have h2' : 120 ≤ q ^ 2 - 1 := by omega
    have h3 : q * 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul_left q h2'
    omega
  interval_cases q <;> first | exact hq rfl | (norm_num at h2) | omega

end CFSG.LocalAnalysis.WeakClosure81

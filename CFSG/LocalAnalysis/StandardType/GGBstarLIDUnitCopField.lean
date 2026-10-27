module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitField
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldUni

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGUnitCopFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1 ∧ p ∣ lab.n

theorem GGUnitCopFieldLabel.unitaryCoprime {p : ℕ} {lab : LargeEvenLabel}
    (h : GGUnitCopFieldLabel p lab) :
    lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1 :=
  ⟨h.1, h.2.2.1, h.2.2.2.1⟩

namespace LIDUC

theorem ggFieldInnR_mono_rank {p r r' : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : 0 < p) (h : GGFieldInnR p r R I) (hrr : r ≤ r') : GGFieldInnR p r' R I :=
  fun Eb Eh hEbI hEb hr h3 hV hle hEh hf =>
    h Eb Eh hEbI hEb ((Nat.pow_le_pow_right hp hrr).trans hr) h3 hV hle hEh hf

variable {K : Type} [Field K] [Finite K] {d n p : ℕ}

theorem ggFieldInnR_unitary_cop (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGFieldInnR p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases (show d = 4 ∨ 5 ≤ d by omega) with rfl | hd5
  · have hD : 4 / p + 1 < 3 := by
      have : 4 / p ≤ 4 / 3 := Nat.div_le_div_left hp3 (by norm_num)
      omega
    exact LIDTwDF.ggFieldInnR_unitary_toral hK hn (by norm_num)
      (fun he => absurd (congrArg Prod.fst he) (by norm_num)) hD hp hpq
  · refine ggFieldInnR_mono_rank hp.pos
      (TableBUD.ggFieldInnR_unitary_dvd hK hn hd5 hp hpq ?_) (by omega)
    rintro ⟨h6, h3⟩
    exact hpd (by rw [h6, h3]; norm_num)

theorem unitCopLabel_arith {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGUnitCopFieldLabel p lab) :
    1 ≤ lab.n ∧ 4 ≤ lab.rank + 1 ∧ ¬ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1 ∧
      (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
  obtain ⟨-, hl, hpn, hpd, -⟩ := h
  refine ⟨hlab.1, by omega, hpd, hpn, fun he => ?_⟩
  have := congrArg Prod.fst he
  simp only at this
  omega

theorem unitCopField_data_torus {R : Type} [Group R] {I : Set (MulAut R)}
    (h : (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I) :
    (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I := by
  obtain ⟨⟨r, hr, hlift, -⟩, hO⟩ := h
  exact ⟨⟨r, hr, hlift⟩, hO⟩

section Labels


theorem largeEvenLabelAll_unitCopField_data (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitCopFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I := by
  obtain ⟨hn, hd4, hpd, hpq, hdq⟩ := unitCopLabel_arith hlab h
  obtain ⟨ht, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd4 hpd hpq hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
    omega
  refine ⟨K, i1, i2, hK, hQ', ⟨ggUnitaryTorusRank p (l + 1), hr2,
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq, ?_⟩,
    InndiagSU.ggOutdiagOdd_unitary hK hn (by omega) (fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])) p⟩
  simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  exact ggFieldInnR_unitary_cop hK hn hd4 hp hpq hpd

end Labels

end LIDUC

section Holds


theorem ggBstarInnerDiagLInputOn_of_le_unitCopField {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitCopFieldLabel p lab) : GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  by_cases hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)
  · exact ggInnerDiagOnLab_bstar_of_fieldInn
      (fun _ _ hp hlab hs => (LIDUC.largeEvenLabelAll_unitCopField_data hp hlab
        (hS _ _ hs)).mono fun _ _ _ _ hP => hP.1) hC hM hinn
  · obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => S p lab)
      (P' := fun R _ I _ => (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I)
      (fun lab hlab hs => (LIDUC.largeEvenLabelAll_unitCopField_data hp hlab
        (hS p lab hs)).mono fun _ _ _ _ hP => LIDUC.unitCopField_data_torus hP)
      (fun _ _ _ _ _ _ hP => hP.1) hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r, hr2, hlift⟩, hOD⟩ :=
      largeEvenRawDatum_exists hraw
    have hnc := UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift
    obtain ⟨-, -, -, -, -, hβ, hS', hst⟩ := hC.1
    rcases ggInnLocal_or_delta hp hβ.2.1 hS' hnc hL θ hBN h3 hOD hst.2.1 with hU | hT₀
    · exact absurd hU hinn
    · exact ggInnerDiagOnLab_bstar_of_moved hC hnc hM hT₀

theorem ggBstarInnerDiagLInputOn_unitCopField_holds :
    GGBstarInnerDiagLInputOn GGUnitCopFieldLabel :=
  ggBstarInnerDiagLInputOn_of_le_unitCopField fun _ _ h => h

theorem ggBstarInnerDiagLInputOn_of_not_unitCopField {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGUnitCopFieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_unitCopField
    (S := fun p lab => S p lab ∧ GGUnitCopFieldLabel p lab) fun _ _ h => h.2
  have h' := hF.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGUnitCopFieldLabel p lab
    · exact Or.inl ⟨hlab, hl⟩
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

end Holds

end CFSG.StandardType

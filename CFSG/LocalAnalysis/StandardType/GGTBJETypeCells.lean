module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelJ
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggTBJE7Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7 ∧ GGLabPhiOneTwo p lab

theorem ggLabPhiOneTwo_dvd {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGLabPhiOneTwo p lab) : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  unfold GGLabPhiOneTwo at h
  have hfac : 4 ^ lab.n - 1 = (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by
    have h4 : (4 : ℕ) ^ lab.n = 2 ^ lab.n * 2 ^ lab.n := by
      rw [← mul_pow]
      norm_num
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ lab.n = k + 1 := ⟨2 ^ lab.n - 1, by
      have := Nat.one_le_two_pow (n := lab.n)
      omega⟩
    rw [h4, hk]
    simp only [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [hfac] at h
  exact (Nat.Prime.dvd_mul hp).mp h

@[expose] def ggTBJNoRowCand (_p _n : ℕ) (_labJ : LargeEvenLabel) : Prop := False

@[expose] def ggTBJE6RowCand (p n : ℕ) (labJ : LargeEvenLabel) : Prop :=
  labJ.tag = .D ∧ labJ.rank = 4 ∧ p = 3 ∧ 3 ∣ 2 ^ n - 1

@[expose] def ggTBJTwE6RowCand (p n : ℕ) (labJ : LargeEvenLabel) : Prop :=
  (labJ.tag = .D ∧ labJ.rank = 4 ∧ p = 3 ∧ 3 ∣ 2 ^ n + 1) ∨
    (labJ.tag = .triD4 ∧ p = 3 ∧ 3 ∣ 2 ^ n + 1) ∨
    (labJ.tag = .twA ∧ labJ.rank = 2 ∧ p = 3 ∧ labJ.n = 3 * n)

@[expose] def GGTBJETypeLeviL (τ : LargeEvenLieTag)
    (Cand : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = τ) p Bs L → GGResXDatum p Bs L →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨τ, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨τ, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n → ¬ Cand p n labJ →
          GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J

@[expose] def GGTBJETypeLeviK (τ : LargeEvenLieTag)
    (Cand : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = τ) p Bs K → GGResXDatum p Bs K →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨τ, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨τ, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n → ¬ Cand p n labJ →
          GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J

@[expose] def GGTBJETypeRowL (τ : LargeEvenLieTag)
    (Cand : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = τ) p Bs L → GGResXDatum p Bs L →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨τ, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨τ, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n → Cand p n labJ →
          GGResRowAt ggRowNonLevi p J L

@[expose] def GGTBJETypeRowK (τ : LargeEvenLieTag)
    (Cand : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = τ) p Bs K → GGResXDatum p Bs K →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨τ, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨τ, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n → Cand p n labJ →
          GGResRowAt ggRowNonLevi p J K

theorem ggTBJETypeRowL_noCand (τ : LargeEvenLieTag) : GGTBJETypeRowL τ ggTBJNoRowCand := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  exact hc.elim

theorem ggTBJETypeRowK_noCand (τ : LargeEvenLieTag) : GGTBJETypeRowK τ ggTBJNoRowCand := by
  intro G _ _ p B Bs x L D J y K hH hJK hp hK hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  exact hc.elim

@[expose] def GGTBJE6LeviL : Prop := GGTBJETypeLeviL .E6 ggTBJE6RowCand

@[expose] def GGTBJE6LeviK : Prop := GGTBJETypeLeviK .E6 ggTBJE6RowCand

@[expose] def GGTBJE6RowL : Prop := GGTBJETypeRowL .E6 ggTBJE6RowCand

@[expose] def GGTBJE6RowK : Prop := GGTBJETypeRowK .E6 ggTBJE6RowCand

@[expose] def GGTBJE7LeviL : Prop := GGTBJETypeLeviL .E7 ggTBJNoRowCand

@[expose] def GGTBJE7LeviK : Prop := GGTBJETypeLeviK .E7 ggTBJNoRowCand

@[expose] def GGTBJF4LeviL : Prop := GGTBJETypeLeviL .F4 ggTBJNoRowCand

@[expose] def GGTBJF4LeviK : Prop := GGTBJETypeLeviK .F4 ggTBJNoRowCand

@[expose] def GGTBJTwE6RowL : Prop := GGTBJETypeRowL .twE6 ggTBJTwE6RowCand

@[expose] def GGTBJTwE6RowK : Prop := GGTBJETypeRowK .twE6 ggTBJTwE6RowCand

section Dispatch

private theorem eType_rank_zero {τ : LargeEvenLieTag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .F4 ∨ τ = .twE6) {r n : ℕ}
    (h : LargeEvenInLambda2 (⟨τ, r, n⟩ : LargeEvenLabel)) : r = 0 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> exact h.2

theorem ggTBJLeftOnLab_eType {τ : LargeEvenLieTag}
    {Cand : ℕ → ℕ → LargeEvenLabel → Prop}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .F4 ∨ τ = .twE6) (hrow : GGTBJETypeRowL τ Cand)
    (hcell : GGTBJETypeLeviL τ Cand) :
    GGTBJLeftOnLab fun p lab => lab.tag = τ ∧ GGLabPhiOneTwo p lab := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hphi⟩ := hS
  have ht' : t = τ := ht
  subst ht'
  have hr : r = 0 := eType_rank_zero hτ hΛ
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hL' : GGInnerDiagOnLabel (fun _ lab => lab.tag = t) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hL
  by_cases hc : Cand p n labJ
  · exact Or.inr (Or.inr (hrow G p B Bs x L D J y K hH hL' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc))
  · exact (hcell G p B Bs x L D J y K hH hL' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc).imp id Or.inl

theorem ggTBJNbrOnLab_eType (hI3 : GGNbrSubcomponentInput) {τ : LargeEvenLieTag}
    {Cand : ℕ → ℕ → LargeEvenLabel → Prop}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .F4 ∨ τ = .twE6) (hrow : GGTBJETypeRowK τ Cand)
    (hcell : GGTBJETypeLeviK τ Cand) :
    GGTBJNbrOnLab fun p lab => lab.tag = τ ∧ GGLabPhiOneTwo p lab := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hphi⟩ := hS
  have ht' : t = τ := ht
  subst ht'
  have hr : r = 0 := eType_rank_zero hτ hΛ
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hK' : GGInnerDiagOnLabel (fun _ lab => lab.tag = t) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hK
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1
  by_cases hc : Cand p n labJ
  · exact Or.inr (Or.inr
      (hrow G p B Bs x L D J y K hH hJK hK' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc))
  · exact (hcell G p B Bs x L D J y K hH hJK hK' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc).imp
      id Or.inl

theorem ggTBJLeftOn_eTypeTag (hTCJ : GGTCJKnown) {τ : LargeEvenLieTag}
    {Cand : ℕ → ℕ → LargeEvenLabel → Prop}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .F4 ∨ τ = .twE6) (hrow : GGTBJETypeRowL τ Cand)
    (hcell : GGTBJETypeLeviL τ Cand) :
    GGTBJLeftOn fun p lab => lab.tag = τ ∧ GGLabPhiOneTwo p lab :=
  (ggTBJLeftOnLab_eType hτ hrow hcell).toLeftOn hTCJ

theorem ggTBJNbrOn_eTypeTag (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    {τ : LargeEvenLieTag} {Cand : ℕ → ℕ → LargeEvenLabel → Prop}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .F4 ∨ τ = .twE6) (hrow : GGTBJETypeRowK τ Cand)
    (hcell : GGTBJETypeLeviK τ Cand) :
    GGTBJNbrOn fun p lab => lab.tag = τ ∧ GGLabPhiOneTwo p lab :=
  (ggTBJNbrOnLab_eType hI3 hτ hrow hcell).toNbrOn hTCJ hI3

theorem ggTBJLeftOn_E6 (hTCJ : GGTCJKnown) (hRow : GGTBJE6RowL) (hLevi : GGTBJE6LeviL) :
    GGTBJLeftOn ggTBJE6Label :=
  ggTBJLeftOn_eTypeTag hTCJ (Or.inl rfl) hRow hLevi

theorem ggTBJNbrOn_E6 (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hRow : GGTBJE6RowK) (hLevi : GGTBJE6LeviK) : GGTBJNbrOn ggTBJE6Label :=
  ggTBJNbrOn_eTypeTag hTCJ hI3 (Or.inl rfl) hRow hLevi

theorem ggTBJLeftOn_E7 (hTCJ : GGTCJKnown) (hLevi : GGTBJE7LeviL) :
    GGTBJLeftOn ggTBJE7Label :=
  ggTBJLeftOn_eTypeTag hTCJ (Or.inr (Or.inl rfl)) (ggTBJETypeRowL_noCand .E7) hLevi

theorem ggTBJNbrOn_E7 (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hLevi : GGTBJE7LeviK) : GGTBJNbrOn ggTBJE7Label :=
  ggTBJNbrOn_eTypeTag hTCJ hI3 (Or.inr (Or.inl rfl)) (ggTBJETypeRowK_noCand .E7) hLevi

theorem ggTBJLeftOn_F4 (hTCJ : GGTCJKnown) (hLevi : GGTBJF4LeviL) :
    GGTBJLeftOn ggTBJF4Label :=
  ggTBJLeftOn_eTypeTag hTCJ (Or.inr (Or.inr (Or.inl rfl))) (ggTBJETypeRowL_noCand .F4) hLevi

theorem ggTBJNbrOn_F4 (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hLevi : GGTBJF4LeviK) : GGTBJNbrOn ggTBJF4Label :=
  ggTBJNbrOn_eTypeTag hTCJ hI3 (Or.inr (Or.inr (Or.inl rfl))) (ggTBJETypeRowK_noCand .F4) hLevi

end Dispatch

theorem GGTBJOrdinaryOutside.of_E6 {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hRL : GGTBJE6RowL) (hRK : GGTBJE6RowK)
    (hL : GGTBJE6LeviL) (hK : GGTBJE6LeviK)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJE6Label p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_E6 hTCJ hRL hL) (ggTBJNbrOn_E6 hTCJ hI3 hRK hK) h

theorem GGTBJOrdinaryOutside.of_E7 {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hL : GGTBJE7LeviL) (hK : GGTBJE7LeviK)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJE7Label p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_E7 hTCJ hL) (ggTBJNbrOn_E7 hTCJ hI3 hK) h

theorem GGTBJOrdinaryOutside.of_F4 {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hL : GGTBJF4LeviL) (hK : GGTBJF4LeviK)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJF4Label p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_F4 hTCJ hL) (ggTBJNbrOn_F4 hTCJ hI3 hK) h

end CFSG.StandardType

end

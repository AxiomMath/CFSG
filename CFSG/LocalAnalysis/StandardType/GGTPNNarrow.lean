module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrTablePNbrInputOn (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
      R p (Nat.card Bs) labJ labK →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

@[expose] def GGNbrTablePNbrInputOnL
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ labL labJ labK : LargeEvenLabel, LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ →
      LargeEvenInLambda2 labK → R p (Nat.card Bs) labL labJ labK →
      GGHasLabel labL (L ⧸ Subgroup.center L) → GGHasLabel labJ (J ⧸ Subgroup.center J) →
      GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

@[expose] def GGNbrTablePNbrInputI1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

theorem GGNbrTablePNbrInput.on' (h : GGNbrTablePNbrInput)
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : GGNbrTablePNbrInputOn R :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' _ hhJ hhK =>
    h G p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' hhJ hhK

theorem GGNbrTablePNbrInputOn.mono {R R' : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hR : ∀ p n a b, R p n a b → R' p n a b) (h : GGNbrTablePNbrInputOn R') :
    GGNbrTablePNbrInputOn R :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' hr hhJ hhK =>
    h G p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' (hR _ _ _ _ hr) hhJ hhK

theorem GGNbrTablePNbrInputOnL.mono
    {R R' : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop}
    (hR : ∀ p n l a b, R p n l a b → R' p n l a b) (h : GGNbrTablePNbrInputOnL R') :
    GGNbrTablePNbrInputOnL R :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn labL labJ labK hL' hJ hK' hr hhL hhJ hhK =>
    h G p B Bs x L D J y K hc hL hK hn labL labJ labK hL' hJ hK' (hR _ _ _ _ _ hr) hhL hhJ hhK

theorem GGNbrTablePNbrInput.onL' (h : GGNbrTablePNbrInput)
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop) :
    GGNbrTablePNbrInputOnL R :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn labL labJ labK _ hJ hK' _ _ hhJ hhK =>
    h G p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' hhJ hhK

theorem GGNbrTablePNbrInputOnL.toOn {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGNbrTablePNbrInputOnL fun p n _ a b => R p n a b) : GGNbrTablePNbrInputOn R := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' hr hhJ hhK
  obtain ⟨hperf, labL, hΛL, hraw⟩ := hL
  exact h G p B Bs x L D J y K hc ⟨hperf, labL, hΛL, hraw⟩ hK hn labL labJ labK hΛL hJ hK' hr
    (largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw) hhJ hhK

theorem GGNbrTablePNbrInputOn.toOnL {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGNbrTablePNbrInputOn R) : GGNbrTablePNbrInputOnL fun p n _ a b => R p n a b :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn _ labJ labK _ hJ hK' hr _ hhJ hhK =>
    h G p B Bs x L D J y K hc hL hK hn labJ labK hJ hK' hr hhJ hhK

theorem GGNbrTablePNbrInputOnL.union
    {R₁ R₂ : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop}
    (h₁ : GGNbrTablePNbrInputOnL R₁) (h₂ : GGNbrTablePNbrInputOnL R₂) :
    GGNbrTablePNbrInputOnL fun p n l a b => R₁ p n l a b ∨ R₂ p n l a b :=
  fun G _ _ p B Bs x L D J y K hc hL hK hn labL labJ labK hL' hJ hK' hr hhL hhJ hhK =>
    hr.elim
      (fun h => h₁ G p B Bs x L D J y K hc hL hK hn labL labJ labK hL' hJ hK' h hhL hhJ hhK)
      (fun h => h₂ G p B Bs x L D J y K hc hL hK hn labL labJ labK hL' hJ hK' h hhL hhJ hhK)

@[expose] def GGRegimeAm2 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => p = 3 ∧ labJ.tag = .A ∧ labJ.n = 1 ∧ 3 ≤ labJ.rank

@[expose] def GGRegimeFieldTwo : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ labK => 2 ≤ labJ.n ∧ labK.n = 1 ∧ ¬ (labK.tag = .A ∧ p = 3 ∧ 5 ≤ labK.rank)

@[expose] def GGRegimeA8Seven : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ _ labK => p = 7 ∧ labK = ⟨.A, 8, 1⟩

@[expose] def GGRegimeA2Eight : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => p = 7 ∧ labJ = ⟨.A, 2, 3⟩

@[expose] def GGRegimeA24 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => p = 3 ∧ labJ = ⟨.A, 2, 2⟩

@[expose] def GGRegimeBC : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun _ _ labJ _ => (labJ.tag = .B ∨ labJ.tag = .C) ∧ 3 ≤ labJ.rank

@[expose] def GGPairA24 (p : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  p = 3 ∧ labL = ⟨.A, 5, 1⟩ ∧ labJ = ⟨.A, 2, 2⟩

@[expose] def GGPairBC (_ : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  (labJ.tag = .B ∨ labJ.tag = .C) ∧ 3 ≤ labJ.rank ∧
    (labL.tag = .B ∨ labL.tag = .C) ∧ labL.rank = labJ.rank + 1 ∧ labL.n = labJ.n

@[expose] def GGPairTypeA (p : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  labL.tag = .A ∧ 3 ≤ labL.rank ∧ 2 ≤ labL.n ∧ p ∣ 2 ^ labL.n - 1 ∧
    labJ = ⟨.A, labL.rank - 1, labL.n⟩

@[expose] def GGPairI1 (p : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  GGPairA24 p labL labJ ∨ GGPairBC p labL labJ ∨ GGPairTypeA p labL labJ

@[expose] def GGRegimeTypeA : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => labJ.tag = .A ∧ 2 ≤ labJ.rank ∧ 2 ≤ labJ.n ∧ p ∣ 2 ^ labJ.n - 1

theorem GGPairA24.regime {p : ℕ} {labL labJ : LargeEvenLabel} (h : GGPairA24 p labL labJ)
    (n : ℕ) (labK : LargeEvenLabel) : GGRegimeA24 p n labJ labK := ⟨h.1, h.2.2⟩

theorem GGPairBC.regime {p : ℕ} {labL labJ : LargeEvenLabel} (h : GGPairBC p labL labJ)
    (n : ℕ) (labK : LargeEvenLabel) : GGRegimeBC p n labJ labK := ⟨h.1, h.2.1⟩

theorem GGPairTypeA.regime {p : ℕ} {labL labJ : LargeEvenLabel} (h : GGPairTypeA p labL labJ)
    (n : ℕ) (labK : LargeEvenLabel) : GGRegimeTypeA p n labJ labK := by
  obtain ⟨hA, hr, hn, hp, rfl⟩ := h
  exact ⟨rfl, by simp; omega, hn, hp⟩

@[expose] def GGRegimeA24L : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labL labJ _ => GGPairA24 p labL labJ

@[expose] def GGRegimeBCL : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labL labJ _ => GGPairBC p labL labJ

@[expose] def GGRegimeB36L : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labL _ _ => p = 3 ∧ n = 3 ^ 6 ∧ (labL.tag = .E6 ∨ labL.tag = .twE6)

@[expose] def GGRegimeTypeAL : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labL labJ _ => GGPairTypeA p labL labJ

@[expose] def GGRegimeA11 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labK => GGRegimeA8Seven p n labJ labK ∨ GGRegimeA2Eight p n labJ labK

@[expose] def GGRegimeNarrowL :
    ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n l a b => GGRegimeA24L p n l a b ∨ GGRegimeAm2 p n a b ∨ GGRegimeBCL p n l a b ∨
    GGRegimeB36L p n l a b ∨ GGRegimeFieldTwo p n a b ∨ GGRegimeA8Seven p n a b ∨
    GGRegimeA2Eight p n a b ∨ GGRegimeTypeAL p n l a b

@[expose] def GGNbrTablePNbrInputNarrow : Prop := GGNbrTablePNbrInputOnL GGRegimeNarrowL

theorem GGNbrTablePNbrInputNarrow.toA24L (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOnL GGRegimeA24L :=
  GGNbrTablePNbrInputOnL.mono (fun _ _ _ _ _ hr => Or.inl hr) h

theorem GGNbrTablePNbrInputNarrow.toBCL (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOnL GGRegimeBCL :=
  GGNbrTablePNbrInputOnL.mono (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inl hr))) h

theorem GGNbrTablePNbrInputNarrow.toB36L (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOnL GGRegimeB36L :=
  GGNbrTablePNbrInputOnL.mono (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inr (Or.inl hr)))) h

theorem GGNbrTablePNbrInputNarrow.toAm2 (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOn GGRegimeAm2 :=
  GGNbrTablePNbrInputOnL.toOn (GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => Or.inr (Or.inl hr)) h)

theorem GGNbrTablePNbrInputNarrow.toFieldTwo (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOn GGRegimeFieldTwo :=
  GGNbrTablePNbrInputOnL.toOn (GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))) h)

theorem GGNbrTablePNbrInputNarrow.toA8Seven (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOn GGRegimeA8Seven :=
  GGNbrTablePNbrInputOnL.toOn (GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))) h)

theorem GGNbrTablePNbrInputNarrow.toA2Eight (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOn GGRegimeA2Eight :=
  GGNbrTablePNbrInputOnL.toOn (GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))))) h)

theorem GGNbrTablePNbrInputNarrow.toTypeAL (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOnL GGRegimeTypeAL :=
  GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))) h

theorem GGNbrTablePNbrInputNarrow.toA11 (h : GGNbrTablePNbrInputNarrow) :
    GGNbrTablePNbrInputOn GGRegimeA11 :=
  GGNbrTablePNbrInputOnL.toOn (GGNbrTablePNbrInputOnL.mono
    (fun _ _ _ _ _ hr => hr.elim
      (fun h6 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
      (fun h7 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))) h)

theorem GGNbrTablePNbrInput.toNarrow (h : GGNbrTablePNbrInput) : GGNbrTablePNbrInputNarrow :=
  h.onL' _

theorem ggNbrTablePNbrInputNarrow_of_regimes
    (h1 : GGNbrTablePNbrInputOnL GGRegimeA24L) (h2 : GGNbrTablePNbrInputOn GGRegimeAm2)
    (h3 : GGNbrTablePNbrInputOnL GGRegimeBCL) (h4 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (h5 : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (h6 : GGNbrTablePNbrInputOn GGRegimeA8Seven)
    (h7 : GGNbrTablePNbrInputOn GGRegimeA2Eight) (h8 : GGNbrTablePNbrInputOnL GGRegimeTypeAL) :
    GGNbrTablePNbrInputNarrow :=
  h1.union (h2.toOnL.union (h3.union (h4.union (h5.toOnL.union (h6.toOnL.union
    (h7.toOnL.union h8))))))

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

@[expose] def SUmSmall (S : Type) [Group S] (m f : ℕ) : Prop :=
  m = 4 ∧ f = 1 ∧ (OddLieType S ∨ NativeSporadic.SporadicRep S)

@[expose] def SUmOvergroup (K : Type) [Group K] (τ : MulAut K) (m f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    (LieModel (K ⧸ center K) .PSL m 2 (2 * f) ∨ SUmSmall (K ⧸ center K) m f)

@[expose] def CatSUmAlternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)), 4 ≤ m →
      IsComponent D → LieModel (D ⧸ center D) .PSU m 2 f → False

@[expose] def CatSUmEvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f → False

@[expose] def CatSUmEvenOuterAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .PSL m 2 (2 * f)

@[expose] def CatSUmOddLieAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f → m = 4 ∧ f = 1

@[expose] def CatSUmSporadicAt (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D ∧
          Odd (Nat.card (center D))) ∨ FixedCentralizerTwoFree σ D) → m = 4 ∧ f = 1

@[expose] def CatSUmCovers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel (D' ⧸ center D') .PSU m 2 f ∧
          (Odd (Nat.card (center D)) → Odd (Nat.card (center D'))) ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D') ∧
          (τ ∈ (MulAut.conj : K →* MulAut K).range → FixedCentralizerTwoSmall τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoSmall (centerQuotientAut τ) D')

@[expose] def SUmCatalogueClausesAt (m : ℕ) : Prop :=
  CatSUmAlternating ∧ CatSUmEvenInner ∧ CatSUmEvenOuterAt m ∧ CatSUmOddLieAt m ∧
    CatSUmSporadicAt m ∧ CatSUmCovers

@[expose] def SUmOvergroupCatalogue : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → Catalog (K ⧸ center K) →
    ∀ τ : MulAut K, orderOf τ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), 4 ≤ m →
      IsComponent D → LieModel (D ⧸ center D) .PSU m 2 f → FixedCentralizerTwoFree τ D →
        SUmOvergroup K τ m f

theorem not_sumSmall_of_ne {S : Type} [Group S] {m f : ℕ} (hmf : (m, f) ≠ (4, 1)) :
    ¬ SUmSmall S m f := fun h => hmf (by rw [h.1, h.2.1])

theorem sum_simple_of_clauses {m : ℕ} (h : SUmCatalogueClausesAt m) {S : Type} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} (hm : 4 ≤ m) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoSmall σ D →
        Odd (Nat.card (center D)) → SUmSmall S m f) ∧
      (FixedCentralizerTwoFree σ D →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧
          (LieModel S .PSL m 2 (2 * f) ∨ SUmSmall S m f)) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  refine ⟨fun hin hsmall hZD => ?_, fun hodd => ?_⟩
  · rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ m f D hm hD hDm).elim
    · obtain ⟨h4, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact ⟨h4, h1, .inl ho⟩
    · exact (hEI S hS hna he σ hσ hin m f D hD hDm).elim
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ f D hD hDm (.inl ⟨hin, hsmall, hZD⟩)
      exact ⟨h4, h1, .inr hsp⟩
  · have hout := LinearPilot.not_mem_range_conj_of_twoFree hna hσ hodd
    refine ⟨hout, ?_⟩
    rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ m f D hm hD hDm).elim
    · obtain ⟨h4, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact .inr ⟨h4, h1, .inl ho⟩
    · exact .inl (hEO S hS hna he σ hσ hout f D hD hDm hodd)
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ f D hD hDm (.inr hodd)
      exact .inr ⟨h4, h1, .inr hsp⟩

theorem sum_inner_small_of_clauses {m : ℕ} (h : SUmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 4 ≤ m) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hZD : Odd (Nat.card (center D)))
    (hin : τ ∈ (MulAut.conj : K →* MulAut K).range) (hsmall : FixedCentralizerTwoSmall τ D) :
    SUmSmall (K ⧸ center K) m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, hZD', -, hsmall'⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨-, hs'⟩ := hsmall' hin hsmall
  exact (sum_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).1 (hinn hin) hs' (hZD' hZD)

theorem sum_not_inner_of_clauses {m : ℕ} (h : SUmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 4 ≤ m) (hmf : (m, f) ≠ (4, 1))
    (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hZD : Odd (Nat.card (center D)))
    (hsmall : FixedCentralizerTwoSmall τ D) : τ ∉ (MulAut.conj : K →* MulAut K).range :=
  fun hin => not_sumSmall_of_ne hmf
    (sum_inner_small_of_clauses h hK hcat τ hτ hm D hD hDm hZD hin hsmall)

theorem sum_overgroup_catalogue {m : ℕ} (h : SUmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 4 ≤ m) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    SUmOvergroup K τ m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, -, hodd', -⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨hout, hlist⟩ := (sum_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).2 hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, hlist⟩

theorem sum_overgroup_catalogue_of_ne {m : ℕ} (h : SUmCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (hm : 4 ≤ m) (hmf : (m, f) ≠ (4, 1))
    (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
      LieModel (K ⧸ center K) .PSL m 2 (2 * f) := by
  obtain ⟨hout, hZ, hlist⟩ := sum_overgroup_catalogue h hK hcat τ hτ hm D hD hDm hodd
  exact ⟨hout, hZ, hlist.resolve_right (not_sumSmall_of_ne hmf)⟩

theorem sumOvergroupCatalogue_of_clauses (h : ∀ m : ℕ, 4 ≤ m → SUmCatalogueClausesAt m) :
    SUmOvergroupCatalogue :=
  fun _ _ _ hK hcat τ hτ m _ D hm hD hDm hodd =>
    sum_overgroup_catalogue (h m hm) hK hcat τ hτ hm D hD hDm hodd

end CFSG.SeitzReduction.UnitaryPilot

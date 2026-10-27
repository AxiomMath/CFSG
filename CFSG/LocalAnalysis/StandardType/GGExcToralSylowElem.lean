module

public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowPDiv
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Defs

@[expose] def GGExcElemToralRestInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    p ∣ Nat.card K - 1 → p < excWeylBound τ → ∀ s : ↥(adjointGroup τ K), s ^ p = 1 →
      GGExcToral τ K (Subgroup.zpowers s)

@[expose] def GGE6ElemToralFiveInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 5 ∣ Nat.card K - 1 →
    ∀ s : ↥(adjointGroup .E6 K), s ^ 5 = 1 → GGExcToral .E6 K (Subgroup.zpowers s)

@[expose] def GGExcPDivNonToralNsInput (τ : Tag) : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 →
    ∀ a : adjointGroup τ (GaloisField 2 f), a ^ p = 1 →
      ¬ GGExcToral τ (GaloisField 2 f) (Subgroup.zpowers a) →
        ¬ GGExcHighNonsplit τ (GaloisField 2 f) (Subgroup.zpowers a) →
          ∀ X : Subgroup (adjointGroup τ (GaloisField 2 f)),
            IsComponentOf X (Subgroup.centralizer {a}) → p ∣ Nat.card X

@[expose] def GGE6PDivNonToralNsInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∧ p = 3 ∨ p ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
        ¬ GGE6InndiagHighNonsplit (GaloisField 2 f) (Subgroup.zpowers α) →
          ∀ X : Subgroup (adjointGroup .E6 (GaloisField 2 f)),
            IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → p ∣ Nat.card X

@[expose] def GGExcCentCompNonToralNsInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K - 1 → ∀ s : ↥(adjointGroup τ K), s ^ p = 1 →
      ¬ GGExcToral τ K (Subgroup.zpowers s) →
      ∀ C : Subgroup ↥(adjointGroup τ K),
        IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))) →
          GGNotExcThreeOrder (ggCQ C)

@[expose] def GGE6InndiagCompNonToralNsInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (¬ p ∣ Nat.card K - 1 ∨ p = 3) →
      ∀ α ∈ LayerSixE.inndiagAut .E6 K, α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α) →
      ∀ X : Subgroup ↥(adjointGroup .E6 K),
        IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → GGNotExcThreeOrder (ggCQ X)

end Defs

namespace ExcToralSylow

section Toral

variable {K : Type} [Field K]

theorem ggInndiagToral_map_conj {τ : Tag} {A₀ : Subgroup ↥(adjointGroup τ K)}
    (h : GGExcToral τ K A₀) :
    LayerSixE.GGInndiagToral τ K
      (A₀.map (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hc x hx)
  exact ⟨l, by rw [← conj_eq_rootDiagAutHom hl, map_mul, map_mul, map_inv]⟩

end Toral

section Elem

theorem ggExcToral_zpowers_of_elemToral {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (hT : GGExcElemToralRestInput τ) {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {s : ↥(adjointGroup τ K)}
    (hs : s ^ p = 1) : GGExcToral τ K (Subgroup.zpowers s) := by
  by_cases hb : excWeylBound τ ≤ p
  · exact ggExcToral_zpowers_of_splitCoprime (hτ.imp_right Or.inr) hp hpq hb hs
  · exact hT K p hp hp2 hpq (not_le.mp hb) s hs

theorem ggInndiagToral_E6_of_elemToral (hT : GGE6ElemToralFiveInput) {K : Type} [Field K]
    [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) {α : MulAut ↥(adjointGroup .E6 K)}
    (hαD : α ∈ LayerSixE.inndiagAut .E6 K) (hαp : α ^ p = 1) :
    LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α) := by
  have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  obtain ⟨x, rfl⟩ := mem_range_conj_of_inndiag_E6 hαD h3p hαp
  have hxp : x ^ p = 1 := mulAut_conj_injective_adjoint (by rw [map_pow, hαp, map_one])
  have hx : GGExcToral .E6 K (Subgroup.zpowers x) := by
    by_cases h7 : 7 ≤ p
    · exact ggExcToral_zpowers_of_splitCoprime (Or.inr (Or.inl rfl)) hp hpq h7 hxp
    · have h5 : p = 5 := by
        interval_cases p <;> first | rfl | omega | exact absurd hp (by norm_num)
      subst h5
      exact hT K hpq x hxp
  have h := ggInndiagToral_map_conj hx
  rwa [MonoidHom.map_zpowers] at h

end Elem

end ExcToralSylow

section Removal

theorem ggExcPDivNonToralRestInput_of_ns {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (hT : GGExcElemToralRestInput τ) (h : GGExcPDivNonToralNsInput τ) :
    GGExcPDivNonToralRestInput τ := by
  intro f hf p hp hp2 hpq a ha ht hn X hX
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hpq with h1 | h1
  · exact absurd (ExcToralSylow.ggExcToral_zpowers_of_elemToral hτ hT hp hp2
      (by rw [hK]; exact h1) ha) ht
  · exact h f hf p hp hp2 h1 a ha ht hn X hX

theorem ggE6PDivNonToralRestInput_of_ns (hT : GGE6ElemToralFiveInput)
    (h : GGE6PDivNonToralNsInput) : GGE6PDivNonToralRestInput := by
  intro f hf p hp hp2 hpq α hαD hαp ht hn X hX
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  by_cases hs : p ∣ 2 ^ f - 1 ∧ p ≠ 3
  · exact absurd (ExcToralSylow.ggInndiagToral_E6_of_elemToral hT hp hp2 hs.2
      (by rw [hK]; exact hs.1) hαD hαp) ht
  · refine h f hf p hp hp2 ?_ α hαD hαp ht hn X hX
    rcases hpq with h1 | h1
    · exact Or.inl ⟨h1, not_not.mp fun h3 => hs ⟨h1, h3⟩⟩
    · exact Or.inr h1

theorem ggExcCentCompNonToralInput_of_ns {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    (hT : GGExcElemToralRestInput τ) (h : GGExcCentCompNonToralNsInput τ) :
    GGExcCentCompNonToralInput τ := by
  intro K _ _ _ hK4 p hp hp2 s hs ht C hC
  by_cases hpq : p ∣ Nat.card K - 1
  · exact absurd (ExcToralSylow.ggExcToral_zpowers_of_elemToral hτ hT hp hp2 hpq hs) ht
  · exact h K hK4 p hp hp2 hpq s hs ht C hC

theorem ggE6InndiagCompNonToralInput_of_ns (hT : GGE6ElemToralFiveInput)
    (h : GGE6InndiagCompNonToralNsInput) : GGE6InndiagCompNonToralInput := by
  intro K _ _ _ hK4 p hp hp2 α hαD hαp ht X hX
  by_cases hs : p ∣ Nat.card K - 1 ∧ p ≠ 3
  · exact absurd (ExcToralSylow.ggInndiagToral_E6_of_elemToral hT hp hp2 hs.2 hs.1 hαD hαp) ht
  · exact h K hK4 p hp hp2 ((not_and_or.mp hs).imp_right not_not.mp) α hαD hαp ht X hX

@[expose] def GGExcElemToralRest : Prop :=
  GGExcElemToralRestInput .F4 ∧ GGE6ElemToralFiveInput ∧ GGExcElemToralRestInput .E7 ∧
    GGExcElemToralRestInput .E8

@[expose] def GGLayerPDivExcRestNs : Prop :=
  GGExcPDivNonToralNsInput .F4 ∧ GGE6PDivNonToralNsInput ∧ GGExcPDivNonToralNsInput .E7 ∧
    GGExcPDivNonToralNsInput .E8 ∧ GGTwE6PDivInput

theorem ggLayerPDivExcRest_of_ns (hT : GGExcElemToralRest) (h : GGLayerPDivExcRestNs) :
    GGLayerPDivExcRest :=
  ⟨ggExcPDivNonToralRestInput_of_ns (Or.inl rfl) hT.1 h.1,
    ggE6PDivNonToralRestInput_of_ns hT.2.1 h.2.1,
    ggExcPDivNonToralRestInput_of_ns (Or.inr (Or.inl rfl)) hT.2.2.1 h.2.2.1,
    ggExcPDivNonToralRestInput_of_ns (Or.inr (Or.inr rfl)) hT.2.2.2 h.2.2.2.1, h.2.2.2.2⟩

@[expose] def GGLayerNotExcThreeRestNs : Prop :=
  GGExcSmallCompOrderInput ∧ GGExcCentCompNonToralNsInput .F4 ∧
    GGExcCentCompNonToralNsInput .E7 ∧ GGExcCentCompNonToralNsInput .E8 ∧
    GGE6InndiagCompNonToralNsInput ∧ GGTwE6InndiagCompInput

theorem ggLayerNotExcThreeRest_of_ns (hT : GGExcElemToralRest) (h : GGLayerNotExcThreeRestNs) :
    GGLayerNotExcThreeRest :=
  ⟨h.1, ggExcCentCompNonToralInput_of_ns (Or.inl rfl) hT.1 h.2.1,
    ggExcCentCompNonToralInput_of_ns (Or.inr (Or.inl rfl)) hT.2.2.1 h.2.2.1,
    ggExcCentCompNonToralInput_of_ns (Or.inr (Or.inr rfl)) hT.2.2.2 h.2.2.2.1,
    ggE6InndiagCompNonToralInput_of_ns hT.2.1 h.2.2.2.2.1, h.2.2.2.2.2⟩

end Removal

end CFSG.StandardType

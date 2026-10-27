module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompPCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Kd

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
  {d : G}

theorem ggKd_eq_of_le_component {K : Subgroup G}
    (hK : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}))
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hJK : J ≤ K) : ggKd p B x L D J d = K := by
  have hKE := le_largeEvenLayer hK
  have hJE := hJK.trans hKE
  have hle : ggKd p B x L D J d ≤ K := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    have haK := largeEvenLayer_le_normalizer hK ha
    exact (Subgroup.mem_normalizer_iff.mp haK _).mp (hJK hj)
  rcases ggLe_center_or_eq_of_normalized hK.2.2 hle (hKE.trans layer_le_normalizer_ggKd) with h | h
  · exfalso
    apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ
    exact ((le_ggKd p B x L D J d).trans h).trans (Subgroup.centralizer_le hJK)
  · exact h

omit [Finite G] in
theorem isSubnormal_of_eq_sup_pPrimeCore {A X : Subgroup G} (hA : IsSubnormal A X) (hJA : J ≤ A)
    (hAeq : A = J ⊔ LargeEvenPPrimeCoreOf p A)
    (hc : LargeEvenPPrimeCoreOf p A ≤ Subgroup.centralizer (J : Set G)) : IsSubnormal J X := by
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := by
    rw [hAeq]
    exact sup_le Subgroup.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer _))
  exact IsSubnormal.step hJA ((Subgroup.normal_subgroupOf_iff_le_normalizer hJA).mpr hAN) hA

end Kd

section Inputs

@[expose] def GGSixJComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
      ∀ d ∈ D, d ≠ 1 → ∃ K : Subgroup G,
        IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) ∧ J ≤ K

@[expose] def GGSixKdPumpupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
      ∀ d ∈ D, d ≠ 1 →
        IsComponentOf (ggKd p B x L D J d) (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) →
        ¬ IsSubnormal (ggKd p B x L D J d) (Subgroup.centralizer {d}) →
          ggKd p B x L D J d = J ∧ ∃ A : Subgroup G,
            LargeEvenPComponent p (Subgroup.centralizer {d}) A ∧ J ≤ A ∧
              A = J ⊔ LargeEvenPPrimeCoreOf p A

@[expose] def GGSixPCompCentralizeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
      ∀ d ∈ D, d ≠ 1 → ∀ A : Subgroup G,
        LargeEvenPComponent p (Subgroup.centralizer {d}) A → J ≤ A →
        A = J ⊔ LargeEvenPPrimeCoreOf p A → Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) →
          LargeEvenPPrimeCoreOf p A ≤ Subgroup.centralizer (J : Set G)

theorem ggSixKdComponentInput_of_pumpup (hJK : GGSixJComponentInput) (hpu : GGSixKdPumpupInput)
    (hpc : GGSixPCompCentralizeInput) : GGSixKdComponentInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1
  obtain ⟨K, hK, hJK'⟩ := hJK G p B Bs x L D J t n f ψ hctx d hd hd1
  have hKd : ggKd p B x L D J d = K := ggKd_eq_of_le_component hK hctx.j_comp.2.2 hJK'
  have hKdc : IsComponentOf (ggKd p B x L D J d)
      (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) := hKd ▸ hK
  have hle : ggKd p B x L D J d ≤ Subgroup.centralizer {d} := hKdc.1.trans inf_le_right
  by_cases hsn : IsSubnormal (ggKd p B x L D J d) (Subgroup.centralizer {d})
  · exact ⟨hle, hsn, hKdc.2.2⟩
  · exfalso
    obtain ⟨hKJ, A, hA, hJA, hAeq⟩ :=
      hpu G p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1 hKdc hsn
    have hY : Odd (Nat.card (⁅J, LargeEvenPPrimeCoreOf p (Subgroup.centralizer {d})⁆ :
        Subgroup G)) := (hctx.stdType.2.2.2 D J hctx.stdSub).2 d hd hd1
    have hEodd := ggOdd_card_pPrimeCoreOf hctx.prime hA hctx.j_comp.2.2 hJA hAeq hZJ hY
    have hc := hpc G p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1 A hA hJA hAeq hEodd
    apply hsn
    rw [hKJ]
    exact isSubnormal_of_eq_sup_pPrimeCore hA.2.1 hJA hAeq hc

end Inputs

end CFSG.StandardType

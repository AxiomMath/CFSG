module

public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF429_C1 (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp : Subgroup E) : Prop :=
  f = 1 → Gp = ⊤ ∨ (κ = .D4tw ∧ Gp.index = 3 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) ∨
    ((κ = .U4 ∨ κ = .U5) ∧ Gp.index = 2 ∧ Nat.card E = Nat.card (MulAut ↥Gp))

@[expose] def burnsideF429_C2 (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (T : Subgroup E) : Prop :=
  let chart := hyp.toHypF_4_4g.chart
  (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
    (∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T) ∧
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      chart.IsFieldInv t ∨
        (chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f ∧
          chart.GraphFixedMarkingGoal t) ∨
        (chart.IsTypeIIIInv t ∧ ∃ s z : E,
          t = s * z ∧ chart.IsGraphInv s ∧
            chart.coordinatePayload.RankInvolution 1 z ∧ s * z = z * s ∧
            IsGenLie ↥(cenIn Gp s) .Sp4 2 f ∧ chart.GraphFixedMarkingGoal s ∧
            Subgroup.centralizer ({t} : Set E) =
              Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E))

@[expose] def burnsideF429_C3 (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop :=
  2 ≤ f → oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
    oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂)

@[expose] def burnsideF429_C4 {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop :=
  pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧
    pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂)

@[expose] def burnsideF429_C5 (κ : GLKind) {f : ℕ} {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (T : Subgroup E) : Prop :=
  let chart := hyp.toHypF_4_4g.chart
  (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) ∧
      pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂))) ∨
    (κ = .U4 ∧ ∃ D : Subgroup E, Gp ≤ D ∧ Gp.relIndex D = 2 ∧ (D ⊓ M₁) ⊔ (D ⊓ M₂) = D ∧
      ∃ t ∈ T, t ∈ D ∧ chart.IsGraphInv t ∧
        (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁))).relIndex (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T)) = 2 ∧
        (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂))).relIndex (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T)) = 2 ∧
        pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T) =
          pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) ⊔ Subgroup.zpowers t ∧
        pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T) =
          pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)) ⊔ Subgroup.zpowers t)

@[expose] def burnsideF429_C6 (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ T : Subgroup E) :
    Prop :=
  (thompsonJ T = thompsonJ (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      baum T = baum (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ∨ (f = 1 ∧ (κ = .U4 ∨ κ = .U5))

@[expose] def burnsideF429_C7 (κ : GLKind) {f : ℕ} {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (T : Subgroup E) : Prop :=
  let chart := hyp.toHypF_4_4g.chart
  ctr T = ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ⊓ Subgroup.centralizer (T : Set E) ∧
    (ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) ∨
      (κ = .L3 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = chart.longRoot) ∨
      (κ = .Sp4 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
        ctr (oPPrime 2 (Gp ⊓ M₁)) ⊔ ctr (oPPrime 2 (Gp ⊓ M₂)) ∧
        ctr (oPPrime 2 (Gp ⊓ M₁)) ⊓ ctr (oPPrime 2 (Gp ⊓ M₂)) = ⊥ ∧
        ctr (oPPrime 2 (Gp ⊓ M₁)) = chart.longRoot ∧
        ctr (oPPrime 2 (Gp ⊓ M₂)) = chart.shortRoot))

@[expose] def burnsideF429_C8 (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) :
    Prop :=
  ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤
      oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
        ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∧
    (Sp 2 Gp β ≤ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
          ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∨
      (f = 1 ∧ (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) ∧
        (Sp 2 Gp β ⊓ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
          ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β)))).relIndex (Sp 2 Gp β) = 2))

end CFSG.ASVolI

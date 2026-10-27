module

public import CFSG.Quasithin.Background.C118TwoSeeds
public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV omegaOne)
open CFSG.Quasithin (thompsonJ SeedData)
open CFSG.QuasithinUnique.Setup.Campbell (Ecore Fcore Vmod Zfix IsSeed)

namespace K339

theorem tripleE_eq_Fcore (H : Type) [Group H] [Finite H] : tripleE H = Fcore H := by
  change (CFSG.elemThompsonCenterTorsion ↥(CFSG.pCore 2 H) 2).map (CFSG.pCore 2 H).subtype = _
  rw [CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf,
    CFSG.Quasithin.BlueprintB2.omegaOneCenterOf_eq_centerTorsion]
  rfl

variable {H : Type} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] {P : Sylow 2 H}
  {ρ : H →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore H →* Multiplicative (Fin 2 → k)}

theorem Vmod_le_tripleV (h : IsSeed P ρ (Ecore H) ψ) : Vmod H ≤ tripleV H := by
  rw [← h.commutator_Hone_Fcore, ← tripleE_eq_Fcore]
  exact Subgroup.commutator_mono le_top le_rfl

theorem commutator_thompsonJ_tripleE (h : IsSeed P ρ (Ecore H) ψ) :
    ⁅thompsonJ (P : Subgroup H), tripleE H⁆ = Zfix P := by
  rw [tripleE_eq_Fcore]
  exact h.commutator_thompsonJ_Fcore

@[expose] def SeedAt {S : Type} [Group S] {H : Type} [Group H] (ι : S →* H) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k) (P : Sylow 2 H)
    (ρ : H →* Matrix.SpecialLinearGroup (Fin 2) k) (ψ : Ecore H →* Multiplicative (Fin 2 → k)),
    (P : Subgroup H) = ι.range ∧ IsSeed P ρ (Ecore H) ψ

variable {S : Type} [Group S] {ι : S →* H}

@[expose, reducible] noncomputable def seedOf (hι : Function.Injective ι) {k : Type} [Field k] [Finite k]
    {P : Sylow 2 H} (hP : (P : Subgroup H) = ι.range) {ρ : H →* Matrix.SpecialLinearGroup (Fin 2) k}
    {ψ : Ecore H →* Multiplicative (Fin 2 → k)} (h : IsSeed P ρ (Ecore H) ψ) : SeedData S where
  G := H
  k := k
  S := P
  e := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hP.symm)
  ρ := ρ
  ψ := ψ
  seed := h

variable (hι : Function.Injective ι) {k' : Type} [Field k'] [Finite k'] (hP : (P : Subgroup H) = ι.range)
  {ρ' : H →* Matrix.SpecialLinearGroup (Fin 2) k'} {ψ' : Ecore H →* Multiplicative (Fin 2 → k')}
  (h : IsSeed P ρ' (Ecore H) ψ')

theorem seedOf_f_apply (s : S) : (seedOf hι hP h).f s = ι s := rfl

theorem seedOf_Fh : (seedOf hι hP h).Fh = (Fcore H).comap ι :=
  Subgroup.ext fun _ => Iff.rfl

theorem seedOf_Vh : (seedOf hι hP h).Vh = (Vmod H).comap ι :=
  Subgroup.ext fun _ => Iff.rfl

end K339

@[expose] def SeedBridge : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    Subgroup.centralizer (CFSG.elemThompsonCenterTorsion S 2 : Set S) = ⊤ →
    ∀ (H : Type) [Group H] [Finite H] (ι : S →* H), InClassG S H ι →
      ⁅(⊤ : Subgroup H), (omegaOne 2 (Subgroup.center S)).map ι⁆ ≠ ⊥ → K339.SeedAt ι

@[expose] def K339Z : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    Subgroup.centralizer (CFSG.elemThompsonCenterTorsion S 2 : Set S) = ⊤ →
    ∀ (H₁ : Type) [Group H₁] [Finite H₁] (ι₁ : S →* H₁), InClassG S H₁ ι₁ →
    ∀ (H₂ : Type) [Group H₂] [Finite H₂] (ι₂ : S →* H₂), InClassG S H₂ ι₂ →
      ⁅(⊤ : Subgroup H₁), (omegaOne 2 (Subgroup.center S)).map ι₁⁆ ≠ ⊥ →
      ⁅(⊤ : Subgroup H₂), (omegaOne 2 (Subgroup.center S)).map ι₂⁆ ≠ ⊥ →
      (tripleE H₁).comap ι₁ = (tripleE H₂).comap ι₂ ∨
        ⁅(tripleV H₁).comap ι₁, (tripleV H₂).comap ι₂⁆ ≠ ⊥ ∨
        (⁅thompsonJ ι₁.range, tripleE H₁⁆.comap ι₁).map ι₂ ≤ Subgroup.center H₂

theorem k339Z_of_seedBridge (hK1 : SeedBridge) : K339Z := by
  intro S _ _ hS hSJ H₁ _ _ ι₁ hG₁ H₂ _ _ ι₂ hG₂ hZ₁ hZ₂
  obtain ⟨k₁, _, _, P₁, ρ₁, ψ₁, hP₁, h₁⟩ := hK1 S hS hSJ H₁ ι₁ hG₁ hZ₁
  obtain ⟨k₂, _, _, P₂, ρ₂, ψ₂, hP₂, h₂⟩ := hK1 S hS hSJ H₂ ι₂ hG₂ hZ₂
  rcases (K339.seedOf hG₁.injective hP₁ h₁).campbell_lemma23 (K339.seedOf hG₂.injective hP₂ h₂) with
    hF | hV | hZ
  · left
    rw [K339.seedOf_Fh, K339.seedOf_Fh] at hF
    rw [K339.tripleE_eq_Fcore, K339.tripleE_eq_Fcore]
    exact hF
  · right
    left
    rw [K339.seedOf_Vh, K339.seedOf_Vh] at hV
    intro hbot
    apply hV
    rw [eq_bot_iff, ← hbot]
    exact Subgroup.commutator_mono (Subgroup.comap_mono (K339.Vmod_le_tripleV h₁))
      (Subgroup.comap_mono (K339.Vmod_le_tripleV h₂))
  · right
    right
    rintro _ ⟨s, hs, rfl⟩
    have hs' : ι₁ s ∈ Zfix P₁ := by
      rw [← K339.commutator_thompsonJ_tripleE h₁, hP₁]
      exact hs
    exact hZ ⟨s, hs', rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

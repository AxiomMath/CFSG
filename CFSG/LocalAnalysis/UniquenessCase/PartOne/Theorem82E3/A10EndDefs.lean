module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def KFactE27Signalizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W = ⊥

namespace Ctx82E3

structure A10Frame (c : Ctx82E3 D) extends Case811Sylow c where
  qs : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L
  center : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)
  iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)
  sig : D.sig = {5}

namespace A10Frame

variable {c : Ctx82E3 D}

@[expose] noncomputable def deg (F : A10Frame c) (B : Subgroup G) : ℕ :=
  {i : Fin 10 | ∃ x : c.L, (x : G) ∈ B ∧
    (F.iso (QuotientGroup.mk (QuotientGroup.mk x : c.Lbar)) : Equiv.Perm (Fin 10)) i ≠ i}.ncard

end A10Frame

structure A10Facts {c : Ctx82E3 D} (F : A10Frame c) : Prop where
  normalizer_A1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 →
    Subgroup.normalizer (B : Set G) ≤ D.M
  normalizer_A : Subgroup.normalizer (F.A : Set G) ≤ D.M
  centralizer_three : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B ≠ 9 →
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G))
  gamma_two : ¬ CFSG.Open.rankThreeGamma 2 3 F.A ≤ D.M

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Stmt
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Aux
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise

section Hyps

variable {G : Type} [Group G]

@[expose] def Six6iiiImg (T M V : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    X ≤ Subgroup.normalizer (V : Set G) → Nat.card (autOn X V) = 3 →
      ∀ k : ℕ, IsChiefSeriesFrom X V V k → 3 ≤ k

@[expose] def NoThreeInCV (M V : Subgroup G) : Prop :=
  ∀ y ∈ M, (∀ v ∈ V, y * v * y⁻¹ = v) → orderOf y ≠ 3

@[expose] def KerNoThree (M H : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card (kerIn (H ⊓ M) H)

@[expose] def NoS5Shape (V H : Subgroup G) : Prop :=
  ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
    ¬ (∃ _ : (L.subgroupOf N).Normal,
        QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
          NaturalSn 5 H L N) ∧
    ¬ (∃ _ : (L.subgroupOf N).Normal,
        QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))
          (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) ∧ NaturalSnPair 5 H L N)

end Hyps

@[expose] def Lemma319SixGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V →
      ∀ A : Subgroup G, IsMinOffender T H V A →
        ∃ L₀ N₀ : Subgroup G, ∃ _ : IsChiefStep H (conjClosure V H) L₀ N₀,
          ∃ _ : ¬ IsCentralStep H L₀ N₀, ∃ χ₀ : ↥H →* ℤˣ,
            (∀ g : ↥H, (g : G) ∈ centralizerMod L₀ H N₀ → χ₀ g = 1) ∧
              ∃ a ∈ A, ∃ ha : a ∈ H, χ₀ ⟨a, ha⟩ = -1

@[expose] def Lemma319SixShapeD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V →
      ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
        ChiefFactorShape H L N

@[expose] def Lemma319SixPlusD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → 2 ≤ qMin M V h.reduced.2.2.1 → Six6iiiImg T M V →
      KerNoThree M H → NoS5Shape V H →
      (∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
          cSecIn H L N = pCoreOf 2 H) ∧
        ∃ φ : ↥H →* (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)),
          Function.Surjective φ ∧ φ.ker = (pCoreOf 2 H).subgroupOf H

end CFSG.Quasithin.H13.L319

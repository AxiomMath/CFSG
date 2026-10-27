module

public import CFSG.Walter.SimpleCase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

structure BenderCounterexample (G : Type) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  hasAbelianSylowTwo : HasAbelianSylowTwo G
  three_le_twoRank : 3 ≤ CFSG.Open.twoRank G
  isAStar : ∀ H : Subgroup G, H ≠ ⊤ → IsAStar H
  not_isTypeJR : ¬ IsTypeJR G
  not_stronglyEmbedded : ¬ ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M

theorem benderHyp_of_forall_not_benderCounterexample
    (h : ∀ (G : Type) [Group G] [Finite G], ¬ BenderCounterexample G) : BenderHyp := by
  intro G _ _ hs hnab hab hr hA
  by_contra hcon
  rw [not_or] at hcon
  exact h G ⟨hs, hnab, hab, hr, hA, hcon.1, hcon.2⟩

section Choices

variable {G : Type} [Group G] [Finite G]

@[expose] def HasFixedPointFreeCore (s : G) (H : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ qCoreOf H p ≠ ⊥ ∧
    qCoreOf H p ⊓ Subgroup.centralizer ({s} : Set G) = ⊥

@[expose] def benderM (s : G) : Set (Subgroup G) :=
  {H | IsCoatom H ∧ Subgroup.centralizer ({s} : Set G) ≤ H ∧
    (HasFixedPointFreeCore s H ∨
      ((∀ K : Subgroup G, IsCoatom K → Subgroup.centralizer ({s} : Set G) ≤ K →
          ¬ HasFixedPointFreeCore s K) ∧
        ∀ K : Subgroup G, IsCoatom K → Subgroup.centralizer ({s} : Set G) ≤ K →
          Nat.card (componentLayerOf K) ≤ Nat.card (componentLayerOf H)))}

@[expose] def benderABar (H : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ generalizedFittingSubgroupOf H ∧
    (U.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal ∧
    (2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) →
      Subgroup.normalizer (U : Set G) ≤ H) ∧
    (Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) = 1 →
      primesOfOrder (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G))) =
        primesOfOrder (generalizedFittingSubgroupOf H))}

end Choices

end CFSG.Walter

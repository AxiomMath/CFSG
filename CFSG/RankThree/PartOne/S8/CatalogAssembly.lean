module

public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (Catalog ExceptionalRep)
open CFSG.Blueprint.NativeSporadic (SporadicRep)
open CFSG.SectionRank (IsKGroupCat)
open scoped Pointwise

theorem componentLocalCoreOddConclusion_of_le_centralizer {G : Type*} [Group G] {p : ℕ}
    {E : Subgroup G} {t : G} {L : Subgroup G}
    (hset : ((localCoreProduct p E t : Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ :
        Subgroup G) : Set G) * (thetaT p E : Set G))
    (hle : localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) :
    ComponentLocalCoreOddConclusion p E t L := by
  refine ⟨hset, hle.trans (Subgroup.centralizer_le_normalizer _), ?_⟩
  have h1 : (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t) = 1 :=
    Subgroup.relIndex_eq_one.mpr hle
  show ¬ 2 ∣ (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t)
  rw [h1]
  omega

theorem not_mulEquiv_cyclic_of_nonabelian {T : Type} [Group T] {q : ℕ}
    (hT : ∃ a b : T, a * b ≠ b * a) (e : T ≃* Multiplicative (ZMod q)) : False := by
  obtain ⟨a, b, hab⟩ := hT
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem original_catalog_component_local_core_odd_action_of_families
    (hlin : OriginalLinearComponentLocalCoreOddAction)
    (hunit : OriginalUnitaryComponentLocalCoreOddAction)
    (hsymp : OriginalSymplecticOrthogonalComponentLocalCoreOddAction)
    (hspor : OriginalSporadicComponentLocalCoreOddAction)
    (hexc : OriginalExceptionalComponentLocalCoreOddAction)
    (hcop : OriginalCoprimeCatalogComponentLocalCoreCentralization)
    (halt : AlternatingComponentSelectedPrimeLocalCoreCentralization)
    (hprep : OriginalThetaFreeQuotientComponentActionPreparation) :
    OriginalCatalogComponentLocalCoreOddAction := by
  intro X _ _ hK hX p hp hp3 N _ hN hθ E hE hEc t ht ht1
  obtain ⟨-, hrankQ, -, -, hset, -, -, -, -, -, hcomp⟩ :=
    hprep X hK hX p hp hp3 N hN hθ E hE hEc t ht ht1
  refine ⟨hset, fun L hL => ?_⟩
  obtain ⟨hcat, hEL, hXL, hSL⟩ := hcomp L hL
  by_cases hpT : p ∣ Nat.card (L ⧸ Subgroup.center L)
  · have hSL' := hSL hpT
    by_cases hCE : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) = ⊥
    ·
      have hodd : ComponentLocalCoreOddConclusion p E t L := by
        rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hclass | hexcRep | hsporRep
        · exact (not_mulEquiv_cyclic_of_nonabelian hL.1.2.2 e).elim
        · exact componentLocalCoreOddConclusion_of_le_centralizer hset
            (halt (X ⧸ N) p hp hp3 hrankQ E hE hEc t ht ht1 L hL ⟨n, hn, ⟨e⟩⟩ hEL hSL').2.2.2.2
        · obtain ⟨c, n, ℓ, f, hmod⟩ := hclass
          have hℓ : ℓ.Prime := hmod.1.1
          cases c with
          | PSL =>
            exact hlin X hX p hp hp3 N hN E hE hEc t ht ht1 L hL ℓ n f hℓ hmod hpT hEL hSL'
          | PSU =>
            exact hunit X hX p hp hp3 N hN E hE hEc t ht ht1 L hL ℓ n f hℓ hmod hpT hEL hSL'
          | PSp =>
            exact hsymp X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .PSp (Or.inl rfl) ℓ n f hℓ
              hmod hpT hEL hSL'
          | POmegaOdd =>
            exact hsymp X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .POmegaOdd
              (Or.inr (Or.inl rfl)) ℓ n f hℓ hmod hpT hEL hSL'
          | POmegaPlus =>
            exact hsymp X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .POmegaPlus
              (Or.inr (Or.inr (Or.inl rfl))) ℓ n f hℓ hmod hpT hEL hSL'
          | POmegaMinus =>
            exact hsymp X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .POmegaMinus
              (Or.inr (Or.inr (Or.inr rfl))) ℓ n f hℓ hmod hpT hEL hSL'
          | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
          | twistedB2 | twistedG2 | twistedF4 | Tits => exact hmod.2.elim
        · exact hexc X hX p hp hp3 N hN E hE hEc t ht ht1 L hL hexcRep hpT hEL hSL'
        · exact hspor X hX p hp hp3 N hN E hE hEc t ht ht1 L hL hsporRep hEL hSL'
      refine ⟨hodd, fun h => ?_⟩
      rcases h with h | h
      · exact absurd hpT h
      · exact absurd hCE h
    ·
      obtain ⟨-, -, hD⟩ :=
        CFSG.RankThree.Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE
          hEc ht ht1 hL hXL hCE
      have hDC : localCoreProduct p E t ≤ Subgroup.centralizer (L : Set (X ⧸ N)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hD
      exact ⟨componentLocalCoreOddConclusion_of_le_centralizer hset hDC, fun _ => hDC⟩
  ·
    obtain ⟨-, -, -, -, -, hD⟩ :=
      hcop X hX p hp hp3 N hN E hE hEc t ht ht1 L hL hcat hpT hEL hXL
    exact ⟨componentLocalCoreOddConclusion_of_le_centralizer hset hD, fun _ => hD⟩

end CFSG.RankThree.PartOne

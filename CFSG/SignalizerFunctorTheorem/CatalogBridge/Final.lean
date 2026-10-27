module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Public
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Cyclic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Alternating
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Sporadic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldStated
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldSymplectic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinearTwo
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldOrthogonal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalley
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyG2
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldTriality
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyTwistedE6
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeWard
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldReeF4
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSuzukiMain
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalReeFinal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSmallReeBZero
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeBZero
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTrialityMain
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwistedE6Main
public import CFSG.SignalizerFunctorTheorem.NonLocal.TrialityTwo
public import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedE6Small
public import CFSG.SignalizerFunctorTheorem.NonLocal.Contract
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthContract
import CFSG.Sporadic.Schreier.TitsOuter

public section

open CFSG CFSG.Blueprint
open CFSG.Open (signalizerNearPSolvable signalizerFunctorEk IsElemAbelian)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

structure CatalogResidual :
    Prop where
  sporadicHS : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
    (NativeSporadic.Carrier .HS)) ≤ 2
  sporadicOuter : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple
  nlChevalley : SubfieldNonLocalizedChevalley

theorem catalog_hypothesisA
    (hres : CatalogResidual) {p : ℕ} (hp : p.Prime) :
    CatalogHypothesisA p := by
  intro X _ _ hsimple hnonab hcat hcop
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hp2 : p ≠ 2 := ne_two_of_coprime_card_of_simple_nonabelian hsimple hnonab hcop
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hclass | hexc | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact e.injective h1
  · exact hypothesisA_alternating hp hsimple hnonab hn e hcop
  · obtain ⟨t, n, ℓ, f, hm⟩ := hclass
    refine hypothesisA_of_near_or_fieldClauses hp hsimple hnonab hcop
      (pSubgroupsCyclic_classical hm hp hp2 hpX) ?_
    cases t with
    | PSL =>
      have hn2 : 2 ≤ n := hm.1.2.2.1
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · have : n = 2 := by omega
        subst this
        exact nearOrField_statedPSL2 hm hp hodd hpX
      · exact Or.inr (fieldClauses_statedPSL hm h3 hp hodd hpX NonLocal.subfieldNonLocalizedPSL)
    | PSU => exact nearOrField_statedPSU hm hp hodd hpX NonLocal.subfieldNonLocalizedPSU
    | PSp => exact Or.inr (fieldClauses_statedPSp hm hp hodd hpX NonLocal.subfieldNonLocalizedPSp)
    | POmegaOdd =>
      exact nearOrField_statedOrthogonal hsimple hnonab (Or.inl rfl) hm hp hp2 hpX
        NonLocal.subfieldNonLocalizedOrthogonal
    | POmegaPlus =>
      exact nearOrField_statedOrthogonal hsimple hnonab (Or.inr (Or.inl rfl)) hm hp hp2 hpX
        NonLocal.subfieldNonLocalizedOrthogonal
    | POmegaMinus =>
      exact nearOrField_statedOrthogonal hsimple hnonab (Or.inr (Or.inr rfl)) hm hp hp2 hpX
        NonLocal.subfieldNonLocalizedOrthogonal
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
    | twistedB2 | twistedG2 | twistedF4 | Tits => exact hm.2.elim
  · refine hypothesisA_of_near_or_fieldClauses hp hsimple hnonab hcop
      (pSubgroupsCyclic_exceptional hexc hp hp2 hpX) ?_
    rcases hexc with ⟨t, ℓ, f, ht, hm⟩ | ⟨t, ℓ, f, ht, hm⟩ | ⟨ℓ, f, hm⟩
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nearOrField_chevalleyG2 hsimple hnonab hm hp hp2 hpX hres.nlChevalley
      · exact nearOrField_chevalleyF4 hsimple hm hp hp2 hpX hres.nlChevalley
      · exact nearOrField_chevalleyE6 hsimple hnonab hm hp hp2 hpX hres.nlChevalley
      · exact nearOrField_chevalleyE7 hsimple hnonab hm hp hp2 hpX hres.nlChevalley
      · exact nearOrField_chevalleyE8 hsimple hm hp hp2 hpX hres.nlChevalley
      · exact nearOrField_chevalleyTwistedE6 hsimple hnonab hm hp hp2 hpX
          (subfieldNonLocalizedTwistedE6_of NonLocal.subfieldNonLocalizedTwistedE6Small)
      · exact nearOrField_chevalleyTrialityD4 hm hp hp2 hpX
          (subfieldNonLocalizedTriality_of NonLocal.subfieldNonLocalizedTrialityTwo)
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact nearOrField_reeG2 hm hp hp2 hpX
          (subfieldNonLocalizedSmallRee_of subfieldNonLocalizedSmallReeBZero) smallReeOuterIsField
      · exact nearOrField_reeF4 hm hp hp2 hpX
          (subfieldNonLocalizedLargeRee_of subfieldNonLocalizedLargeReeBZero)
      ·
        have h2 := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier X ℓ f hm).1
        have haut := not_dvd_card_mulAut_of_not_dvd_outer hp hpX
          ((NoOddOuter.of_isPGroup_two h2) p hp hp2 hpX)
        exact Or.inr fun ⟨g, hg⟩ => absurd (hg ▸ orderOf_dvd_natCard g) haut
    · exact nearOrField_suzuki hm hp hp2 hpX subfieldNonLocalizedSuzuki
  · exact hypothesisA_sporadic hres.sporadicHS hres.sporadicOuter hsimple hnonab hspor hp hcop

theorem signalizer_functor_theorem_catalog
    (hres : CatalogResidual)
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (A : Subgroup G) (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (Θ : Subgroup G → Subgroup G)
    (hcent : ∀ S ∈ signalizerFunctorEk p k A, Θ S ≤ Subgroup.centralizer (S : Set G))
    (hcop : ∀ S ∈ signalizerFunctorEk p k A, Nat.Coprime p (Nat.card (Θ S)))
    (hinv : ∀ S ∈ signalizerFunctorEk p k A, A ≤ Subgroup.normalizer (Θ S : Set G))
    (hbal : ∀ S ∈ signalizerFunctorEk p k A, ∀ S' ∈ signalizerFunctorEk p k A,
      Θ S ⊓ Subgroup.centralizer (S' : Set G) ≤ Θ S')
    (hK : ∀ S ∈ signalizerFunctorEk p k A, CFSG.SectionRank.IsKGroupCat ↥(Θ S)) :
    let W : Subgroup G := ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), Θ S
    (Nat.Coprime p (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G)) ∧
    (∀ S ∈ signalizerFunctorEk p k A, W ⊓ Subgroup.centralizer (S : Set G) = Θ S) ∧
    (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
      (∀ S ∈ signalizerFunctorEk p k A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ Θ S) →
      Y ≤ W) ∧
    ((∀ S ∈ signalizerFunctorEk p k A, Group.IsSolvable (Θ S)) → Group.IsSolvable W) :=
  signalizer_functor_theorem_of_catalogHypothesisA G p hp (catalog_hypothesisA hres hp) k hk A hA
    hrank Θ hcent hcop hinv hbal hK

end CFSG.SignalizerFunctorTheorem.CatalogBridge

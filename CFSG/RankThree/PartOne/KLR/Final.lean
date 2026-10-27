module

public import CFSG.RankThree.PartOne.KLR.Native
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.NoninnerFinal
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KF4.B2Frame
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.LargeReeOrder

section Final

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem solvOdd_of_sector (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) (E : Subgroup (ModGL ReeTag.F4.tag L))
    (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (m : ℕ)
    (hE : Nat.card E = m ^ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p)
    (V : Subgroup (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) [V.Normal]
    [Group.IsSolvable V] : Odd (Nat.card V) := by
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF m hE hp hpm
  exact odd_card_of_solvable_normal_centralizer D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => starRadFree D ha hK w hp hp3 hordb hbT) x hx V

end Final

theorem largeReeSolvOdd :
    LargeReeSolvOdd := by
  intro a ha K _ _ _ hK p hp hp3 x hx V hVn hVs
  classical
  have := hVn
  have := hVs
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hx ▸ orderOf_dvd_natCard x
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd6 : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1 → Odd (Nat.card V) := by
    intro h
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK hp hp3 h x hx
    have hodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) :=
      Nat.odd_iff.2 (by omega)
    exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card V)
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd with
    h1 | h2 | h3 | h4 | h5
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
    exact solvOdd_of_sector D ha hK wPhi1 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 h1) x hx V
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi2 D.isFrob
    exact solvOdd_of_sector D ha hK wPhi2 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp hp3 h2) x hx V
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
      exact solvOdd_of_sector D ha hK wPhi4p E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4p hK hp hp3 hpp) x hx V
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D.isFrob
      exact solvOdd_of_sector D ha hK wPhi4m E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4m hK hp hp3 hpm) x hx V
  · exact hodd6 (Or.inl h4)
  · exact hodd6 (Or.inr h5)

theorem largeRee_all_actors :
    LargeReeAllActorsActualComponentLocalCoreProductOddAction := by
  exact largeRee_all_actors_of_native_aux largeReeSolvOdd largeReeNoninnerCore

end CFSG.RankThree.PartOne.KLR

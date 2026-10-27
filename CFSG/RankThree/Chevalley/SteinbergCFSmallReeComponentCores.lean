module

public import CFSG.RankThree.Chevalley.SteinbergCFSmallReePlaneCore
public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.LieType.Ree.SmallReeModelSchreier

public noncomputable section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open scoped Pointwise

theorem exists_mulEquiv_reeGamma_G2_of_reeTitsModel {T : Type} [Group T] {ℓ f : ℕ}
    (hT : ReeTitsModel T .twistedG2 ℓ f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime), 1 ≤ a ∧
      Nat.card K = 3 ^ (2 * a + 1) ∧ Nonempty (T ≃* ReeTag.G2.reeGamma K a) := by
  obtain ⟨-, -, hℓ, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f hT
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e₀⟩⟩ := hT
  subst hℓ
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a' K hfa' hK ⟨e₀⟩
  exact ⟨a', K, inferInstance, inferInstance, inferInstance, by omega, by rw [hK, hfa'], ⟨e⟩⟩

theorem autThetaT_eq_map_thetaT_of_mem {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) {t : B} (htA : t ∈ A) (ht1 : t ≠ 1) :
    autThetaT p B (A.map B.subtype) = (thetaT p A).map B.subtype := by
  refine le_antisymm (fun x hx => ?_) (map_subtype_thetaT_le hp B A)
  simp only [autThetaT, Subgroup.mem_iInf] at hx
  have hxt := hx (t : M) (Subgroup.mem_map_of_mem _ htA) (fun h => ht1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B t] at hxt
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hxt
  refine Subgroup.mem_map_of_mem _ ?_
  simp only [thetaT, Subgroup.mem_iInf]
  intro b hbA hb1
  have h1 := hx (b : M) (Subgroup.mem_map_of_mem _ hbA) (fun h => hb1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B b] at h1
  obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 h1
  have hy : y' = y := Subtype.ext hyy'
  rwa [hy] at hy'

theorem planeLocalCoreOdd_smallRee (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : PlaneLocalCoreOdd p (ReeTag.G2.reeGamma K a) := by
  intro B hB A hAB hA hAcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, -, -, hW⟩ := small_Ree_plane_local_core_product_odd a ha K hK hp hp3 B hB
    (A.subgroupOf B) hE hEcard
  have hodd := (hW _ ht'E ht'1).2
  have hAE : (A.subgroupOf B).map B.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAB]
  have heq : autPlaneProduct p B A t = (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨t, hAB htA⟩ : B)} : Set B)), A.subgroupOf B⁆ ⊔
        thetaT p (A.subgroupOf B)).map B.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, map_subtype_theta_centralizer hp B,
      ← autThetaT_eq_map_thetaT_of_mem hp B (A.subgroupOf B) ht'E ht'1, hAE]
    rfl
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd.not_two_dvd_nat

theorem small_Ree_normalized_component_local_core_product_odd_image {H : Type} [Group H]
    [Finite H] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup H}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : H} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup H} (hL : IsComponent L) {ℓ f : ℕ}
    (hT : ReeTitsModel (L ⧸ center L) .twistedG2 ℓ f) (hEL : E ≤ normalizer (L : Set H))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)) ≤
      normalizer (L : Set H)) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ ⊔ thetaT p E :
        Subgroup H) : Set H) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ : Subgroup H) :
        Set H) * (thetaT p E : Set H) ∧
    ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ ⊔ thetaT p E ≤
      normalizer (L : Set H) ∧
    ¬ 2 ∣ (centralizer (L : Set H)).relIndex
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ ⊔ thetaT p E) ∧
    CFSG.Quasithin.twoPrimeResidual
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ ⊔
          thetaT p E) ≤ centralizer (L : Set H) ∧
    (E ⊓ centralizer (L : Set H) ≠ ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set H)) := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma_G2_of_reeTitsModel hT
  have hplane := (planeLocalCoreOdd_smallRee a ha K hK hp hp3).of_mulEquiv hp e
  exact component_local_core_odd_action_of_plane hp (by omega) hE hEcard ht ht1 hL hEL hSL hplane

end CFSG.RankThree.Chevalley

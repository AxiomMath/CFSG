module

public import CFSG.RankThree.PartTwo.Sec6.Item65UsedStatement
public import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.Sec6.Item65UsedLocal
import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

namespace Ctx65

variable {A L B E : Subgroup G} {a₀ : G} (h : Ctx65 G A L B E a₀)
include h

theorem commutator_theta_le_of_not_lt (h45 : Sec4.Item4_5)
    (hno : ∀ b ∈ B, b ≠ 1 → ∀ K ∈ thetaComponentsAt 3 b,
      ¬ inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K)
    {Z' : Subgroup G} (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hLK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Z', Z'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have heq := (lt_or_eq_of_le hLK).resolve_left (hno a haB ha1 K hK)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.B_le_A.trans (h.A_le_normalizer h45 haB ha1 K hK)
  have hBKC := le_thetaQuotCentralizer_of_residual_eq h.B_le_C (h.B_le_centralizer haB) hK hBK heq
  obtain ⟨a', ha'B, -, -, hCeq⟩ := exists_centralizer_eq_inf h.elemB h.cardB haB ha1
  have hZ'Ka : Z' ≤ K := hZ'K a haB ha1 K hK hLK
  have hZ'C : Z' ≤ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hZ'
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  have hle : K ⊓ Subgroup.centralizer ({a'} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    rw [hCeq]
    exact inf_le_inf_right _ hKa
  have hZ'le : Z' ≤ K ⊓ Subgroup.centralizer ({a'} : Set G) :=
    le_inf hZ'Ka (hZ'C.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha'B)))
  have hsn : (Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G))).IsSubnormal := by
    have heq' : Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G)) =
        (Z'.subgroupOf (Subgroup.centralizer (B : Set G))).comap (Subgroup.inclusion hle) := by
      ext m
      simp [Subgroup.mem_subgroupOf]
    rw [heq']
    exact (mem_thetaComponentsIn_iff.mp hZ').2.2.1.comap _
  exact commutator_theta_le_of_mem_thetaQuotCentralizer (isQuasisimple_of_mem_thetaComponentsAt hK)
    (h.elemB.2 a' ha'B) (hBKC ha'B) hZ'le hsn

end Ctx65

theorem rank3II_6_5Used_one (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hG : PartTwoStanding G) {A : Subgroup G} (hA : A ∈ partTwoS G) {L : Subgroup G}
    (hL : L ∈ thetaComponentFamily 3 A) {B : Subgroup G}
    (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBAL : B ≤ A ⊓ thetaQuotCentralizer L) {E : Subgroup G}
    (hE : E ∈ collectionIn (partTwoE G) (A ⊔ L)) (hBE : B ≤ E) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K := by
  by_contra hcon
  have hno : ∀ b ∈ B, b ≠ 1 → ∀ K ∈ thetaComponentsAt 3 b,
      ¬ inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K :=
    fun b hb hb1 K hK hlt => hcon ⟨b, hb, hb1, K, hK, hlt⟩
  obtain ⟨a₀, ha₀A, ha₀1, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have h : Ctx65 G A L B E a₀ := ⟨hG, hA, ha₀A, ha₀1, hLa₀, hBab, hB9, hBAL, hE, hBE,
    fun b hb hb1 K hK hlt => absurd hlt (hno b hb hb1 K hK)⟩
  obtain ⟨Z', hZ', hZZ', hEZ', hZ'K⟩ := h.exists_Z' h45 h48
  obtain ⟨R, Y, hR1, hR2, hER, hYp, hY1, hYZ', hZ'Y, hYR, -⟩ :=
    h.exists_R_Y h45 h48 h49 hZ' hZZ' hEZ' hZ'K
  exact h.false_of_R_Y_of_local h45 h48 h49 hZ' hZ'K
    (fun a haB ha1 K hK hLK => h.commutator_theta_le_of_not_lt h45 hno hZ' hZ'K haB ha1 hK hLK)
    hR1 hR2 hER hYp hY1 hYZ' hZ'Y hYR

theorem rank3II_6_5Used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) :
    Item6_5Used := by
  intro G _ _ hG A hA L hL B hBab hB9 hBAL
  exact ⟨fun E hE hBE => rank3II_6_5Used_one h45 h48 h49 hG hA hL hBab hB9 hBAL hE hBE,
    fun hno => rank3II_6_5_two h45 h48 hG hA hL hBab hB9 hBAL hno⟩

end CFSG.RankThree.PartTwo.Sec6

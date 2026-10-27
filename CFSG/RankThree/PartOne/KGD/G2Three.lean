module

public import CFSG.RankThree.PartOne.KGD.G2ThreeSplit
public import CFSG.RankThree.PartOne.KGD.G2ThreeCyclo
public import CFSG.RankThree.PartOne.KGD.G2ThreeQPlusI
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.NativeCyclicF4
public import CFSG.RankThree.SteinbergBRThreeG2Noninner
public import CFSG.RankThree.Chevalley.SteinbergBNG2OddNonthreeComponent

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank CFSG.RankThree.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Chevalley.SteinbergBN
open scoped Pointwise

theorem G2_three_outer_commutator_odd {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) :
    ¬ 2 ∣ Nat.card (commutator (Outer (adjointGroup .G2 K))) := by
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  exact KE.outer_commutator_odd_of_hom (fun a b => mul_comm a b) Θ hker

theorem localCoreTrivialOn_noninner_G2_three {f : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (adjointGroup .G2 K) =>
      α ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  refine localCoreTrivialOn_of_forall hp fun B hB α hα hαp => ?_
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α.1
  exact (three_G2_noninner_odd_prime_local_core_trivial hf hK hp (by omega) B hB α hα hαp x a
    a.2 hxa).2.2.2.2

theorem G2_three_prime_cases {f : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpC : p ∣ Nat.card (adjointGroup .G2 K)) :
    p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 ∨
      (∃ d : ℕ, (d : ℤ) = (Nat.card K : ℤ) ^ 2 + 1 * Nat.card K + 1 ∧ p ∣ d) ∨
      (∃ d : ℕ, (d : ℤ) = (Nat.card K : ℤ) ^ 2 + (-1) * Nat.card K + 1 ∧ p ∣ d) := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  rcases dvd_cyclotomic_factor_of_dvd_card_G2 Nat.prime_three hK hp (by omega) hpC with
    h | h | h | h
  · exact Or.inl (by rw [hK]; exact h)
  · exact Or.inr (Or.inl (by rw [hK]; exact h))
  · refine Or.inr (Or.inr (Or.inl ⟨(3 ^ f) ^ 2 + 3 ^ f + 1, ?_, h⟩))
    rw [hK]
    push_cast
    ring
  · have hle : 3 ^ f ≤ (3 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    refine Or.inr (Or.inr (Or.inr ⟨(3 ^ f) ^ 2 - 3 ^ f + 1, ?_, h⟩))
    rw [hK]
    push_cast [Nat.cast_sub hle]
    ring

theorem planeLocalCoreOdd_G2_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : PlaneLocalCoreOdd p (adjointGroup .G2 K) := by
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    rw [ringChar.eq K 3]
    norm_num
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hV : ∀ x : adjointGroup .G2 K, orderOf x = p →
      ∀ V : Subgroup (centralizer ({x} : Set (adjointGroup .G2 K))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
    intro x hxp
    have hpC : p ∣ Nat.card (adjointGroup .G2 K) := hxp ▸ orderOf_dvd_natCard x
    rcases G2_three_prime_cases K hK hp hp3 hpC with h | h | ⟨d, hd, hpd⟩ | ⟨d, hd, hpd⟩
    · exact solvable_normal_split K hKodd hp hp3 h x hxp
    · exact solvable_normal_qplus K hKodd hK2 hp hp3 h x hxp
    · exact solvable_normal_cyclotomic K hKodd 1 (Or.inr rfl) d hd hp hp3 hpd x hxp
    · exact solvable_normal_cyclotomic K hKodd (-1) (Or.inl rfl) d hd hp hp3 hpd x hxp
  have hI : ∀ B : Subgroup (MulAut (adjointGroup .G2 K)),
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .G2 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range →
        Odd (Nat.card ↥(autThetaT p B A)) := by
    intro B hB A hAB hA hAcard hAinn
    obtain ⟨P, -, hPcard, -, -⟩ := plane_comap_conj hinj hp hA hAcard hAinn
    have hpC : p ∣ Nat.card (adjointGroup .G2 K) :=
      (hPcard ▸ dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans
        (Subgroup.card_subgroup_dvd_card P)
    rcases G2_three_prime_cases K hK hp hp3 hpC with h | h | ⟨d, hd, hpd⟩ | ⟨d, hd, hpd⟩
    · rw [autThetaT_eq_bot_of_split K hKodd hp hp3 h B hB A hA hAcard hAinn, Subgroup.card_bot]
      exact odd_one
    · rw [autThetaT_eq_bot_of_qplus_three hf K hK hp hp3 h B hB A hA hAcard hAinn,
        Subgroup.card_bot]
      exact odd_one
    · exact (false_of_plane_cyclotomic K hKodd 1 (Or.inr rfl) d hd hp hp3 hpd A hA hAcard
        hAinn).elim
    · exact (false_of_plane_cyclotomic K hKodd (-1) (Or.inl rfl) d hd hp hp3 hpd A hA hAcard
        hAinn).elim
  exact KE.planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot hV
    (G2_three_outer_commutator_odd hf K hK) (localCoreTrivialOn_noninner_G2_three hf K hK hp hp3)
    hI

theorem g2_three_component {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {f : ℕ}
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 3 f) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) :
    ComponentLocalCoreOddConclusion p E t L ∧
      (E ⊓ centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤ centralizer (L : Set G)) := by
  obtain ⟨⟨-, hf1, -⟩, hmod⟩ := hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic Nat.prime_three hf1 hK
  exact KE.component_odd_conclusion_of_native hp (by omega) hE hEcard ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_G2_three hf1 K hK hp hp3)

end CFSG.RankThree.PartOne.KGD

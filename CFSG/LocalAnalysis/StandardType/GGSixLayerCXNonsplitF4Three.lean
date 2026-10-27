module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Basic
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenCyclotomicThree
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeSixActors
public import CFSG.RankThree.PartOne.D4RC.RxOrder
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.D4RC.RxIso
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.F4Weyl CFSG.RankThree.E6

namespace F4Nonsplit

theorem exists_card_eq_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem exists_frobenius_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ F : AlgebraicClosure K →+* AlgebraicClosure K, ∀ c, F c = c ^ Nat.card K := by
  obtain ⟨f, -, hf⟩ := exists_card_eq_two_pow K
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  exact ⟨iterateFrobenius (AlgebraicClosure K) 2 f, fun c => by rw [iterateFrobenius_def, hf]⟩

theorem pow_three_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := by
  zify [hq, Nat.one_le_pow 3 q hq]
  ring

theorem pow_three_add_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 3 + 1 = (q ^ 2 - q + 1) * (q + 1) := by
  have h : q ≤ q ^ 2 := by nlinarith
  zify [h]
  ring


theorem dvd_card_of_isComponentOf_phiThree {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1)
    {x₁ : adjointGroup .F4 K} (hx₁p : orderOf x₁ = p) {X : Subgroup (adjointGroup .F4 K)}
    (hX : IsComponentOf X (Subgroup.centralizer {x₁})) : p ∣ Nat.card X := by
  classical
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow K
  obtain ⟨F, hF⟩ := exists_frobenius_pow K
  have hεw : ((1 : ℤ) = 1 ∧ f4Coxeter ^ 4 = f4Coxeter ^ 4 ∧
      p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      ((1 : ℤ) = -1 ∧ f4Coxeter ^ 4 = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1) :=
    Or.inl ⟨rfl, rfl, hpd⟩
  obtain ⟨g, hg, hgn, x, hx, hxp, hx₁⟩ :=
    exists_lang_coordinate_three_six K (AlgebraicClosure K) F hF hεw hp hp3 hx₁p
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K (AlgebraicClosure K) F hF hεw hp hp3).2 g hg hgn
  by_cases hne : {α | IsRoot .F4 α ∧ torusRootChar x α = 1}.Nonempty
  swap
  · exact absurd hX (not_isComponentOf_of_commutator_eq_bot
      (F4_three_six_regular_actor K (AlgebraicClosure K) F hF hεw hp hp3 hg hgn hx hxp
        (Set.not_nonempty_iff_eq_empty.1 hne) hx₁).2)
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, hK₃⟩ := EvenF4Actors.exists_intermediateField_finrank K (AlgebraicClosure K) 3
  obtain ⟨-, a, -, hRS, hSa, -, -, -, -, -, -, -, -, x₀, hx₀, -, hR₀', hq₀, -⟩ :=
    even_F4_cyclotomic_three_nonregular_derived_centralizer K hK (AlgebraicClosure K) F hF hp hp3
      K₃ hK₃ _ g rfl hg hgn _ _ rfl rfl x hx hxp κ u δ hδ hu
      (fun z hz => by rw [huw z hz, one_smul]) _ _ rfl rfl _ _ _ rfl rfl rfl
  have hx₀₁ : x₀ = x₁ := Subtype.ext (baseChangeGL_injective (τ := .F4)
    (algebraMap K (AlgebraicClosure K)) (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup .F4 K).subtype) :=
    (baseChangeGL_injective (τ := .F4) (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : Nat.card ↥⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [← Subgroup.card_map_of_injective hι, hR₀',
      Subgroup.card_map_of_injective (MulAut.conj _).injective, hRS, hSa,
      Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective (baseChangeGL_injective (τ := .F4) _),
      Nat.card_congr (f4A2Equiv K κ).toEquiv,
      CFSG.RankThree.PartOne.D4RC.rcl_card_SL3_field K rfl hq2]
  refine dvd_card_of_isComponentOf_of_quasisimple hq₀ ?_ hX
  rw [hcard, pow_three_sub_one_eq _ (by omega)]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpd _) _

end F4Nonsplit

end CFSG.StandardType

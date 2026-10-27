module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.LieType.AlgebraicGroups.FiniteSubgroupConjugacyExtension
public import CFSG.LocalAnalysis.StandardType.GGE6RankFivePrimeField
import CFSG.LocalAnalysis.StandardType.GGFinModelEps
import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.StandardType.E6RankFive

open CFSG Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TableBExc.E6Three SCFourCover

theorem e6AdToral_of_card_ge
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {E : Subgroup (ModGL .E6 L)} (hEG : E ≤ adjointGroup .E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 3 ^ 5 ≤ Nat.card E) : E6AdToral E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) L := ZMod.algebra L 2
  let k := AlgebraicClosure (ZMod 2)
  let ι : k →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := k) (M := L)).toRingHom
  let : Algebra k L := ι.toAlgebra
  have : Finite E := Nat.finite_of_card_ne_zero (lt_of_lt_of_le (by norm_num) hcard).ne'
  let : Fintype E := Fintype.ofFinite E
  let : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := fun a b => by
        have : IsMulCommutative E := hE.1
        exact mul_comm' a b }
  have hexp : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (hE.2 a a.2)
  obtain ⟨ζ, hζo⟩ := GGFinModel.exists_zeta k Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  let t : (E → Fin Tag.E6.rank → ZMod 3) → E → ModGL Tag.E6 k :=
    fun v a => rootDiagUnit Tag.E6 (zetaVec ζ hζ (v a))
  have hbase : ∀ f : E →* adjointGroup Tag.E6 k, Function.Injective f →
      ∃ v, ∃ g ∈ adjointGroup Tag.E6 k, ∀ a, g * (f a : ModGL Tag.E6 k) * g⁻¹ = t v a := by
    intro f hf
    exact e6RankFive_primeField_toralTarget hexp hcard ζ hζ hζo f hf
  let f : E →* adjointGroup Tag.E6 L := Subgroup.inclusion hEG
  obtain ⟨v, g, hg, hv⟩ := CFSG.LieType.AlgebraicGroups.finite_subgroup_conjugacy_field_extension
    t hbase f (Subgroup.inclusion_injective hEG)
  refine ⟨g, hg, fun e he => ?_⟩
  have hv' := hv ⟨e, he⟩
  change g * e * g⁻¹ = baseChangeGL ι (t v ⟨e, he⟩) at hv'
  rw [hv']
  exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup ι
    (rootDiagUnit_mem_torusGroup (zetaVec ζ hζ (v ⟨e, he⟩)))

theorem card_le_of_not_e6AdToral
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {E : Subgroup (ModGL .E6 L)} [Finite E] (hEG : E ≤ adjointGroup .E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hNT : ¬ E6AdToral E) : Nat.card E ≤ 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := (TableB.isPGroup_of_isElemAbelian hE).exists_card_eq
  have hcard : Nat.card E < 3 ^ 5 :=
    lt_of_not_ge fun h => hNT (e6AdToral_of_card_ge hEG hE h)
  rw [hr] at hcard ⊢
  have hr4 : r ≤ 4 := by
    have hr5 : r < 5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hcard
    omega
  exact Nat.pow_le_pow_right (by norm_num) hr4

theorem eq_of_le_of_card_four_of_not_e6AdToral
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {E F : Subgroup (ModGL .E6 L)} [Finite F] (hFG : F ≤ adjointGroup .E6 L)
    (hF : CFSG.Open.IsElemAbelian 3 F) (hEF : E ≤ F)
    (hcard : Nat.card E = 3 ^ 4) (hNT : ¬ E6AdToral E) : E = F := by
  have hFNT : ¬ E6AdToral F := fun h => hNT (e6AdToral_mono hEF h)
  exact Subgroup.eq_of_le_of_card_ge hEF
    (by rw [hcard]; exact card_le_of_not_e6AdToral hFG hF hFNT)

end CFSG.StandardType.E6RankFive

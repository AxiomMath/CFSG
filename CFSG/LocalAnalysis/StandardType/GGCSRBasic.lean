module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
import CFSG.Adapters.TauCetiExceptional.BridgeTransport
import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley
open TableB TableBExc TableBExcSmallRest

theorem ggCSR_of_lib {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ A : Subgroup (MulAut R),
      (∀ a ∈ A, a ∈ I) → IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 2 := by
  refine h.mono fun R _ I F hR A hAI hA => ?_
  have hlt : Nat.card A < 3 ^ 3 := hR A (fun a ha => hAI a ha) hA
  by_cases hfin : Finite A
  · haveI : Finite A := hfin
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3) (G := A)).mp
      (TableB.isPGroup_of_isElemAbelian hA)
    rw [hk] at hlt ⊢
    have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
  · haveI : Infinite A := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

theorem ggCSR_G2
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun X hXI hX => ?_⟩
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have := finite_recipeGroup .G2 K
  have hI := idImage_subset_inn_of_top .G2 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot .G2 K)
    (fun φ hφ => hI (hXI hφ)) hX
  have h1 := CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2
    K h3 (A.map (recipeEquiv .G2 K).toMonoidHom) (TableB.isElemAbelian_map hA _)
  rw [Subgroup.card_map_of_injective (recipeEquiv .G2 K).injective, hAc] at h1
  exact lt_of_le_of_lt h1 (by norm_num)

theorem ggCSR_triD4
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hI := chevIDImage_subset_inn_triD4 hn K hK
  have hbound : ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian 3 E → Nat.card E < 3 ^ 3 := by
    intro E hE
    have h9 := CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup
      (f := n) (K := K) (σ := σ.toRingHom) hn hK hσ E hE
    exact lt_of_le_of_lt h9 (by norm_num)
  refine card_lt_of_subset_inn (center_eq_bot_of_mulEquiv e hZC)
    (fun A hA => card_lt_of_mulEquiv e hbound hA) (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end CFSG.StandardType

end

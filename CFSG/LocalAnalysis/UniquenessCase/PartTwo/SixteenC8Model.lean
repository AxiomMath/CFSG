module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Sp6Id
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Sp6P
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap spMap_injective spMap_surjective)

theorem c8_nonempty_mulEquiv_of_isSpn {X : Type} [Group X] (hX : IsSpn X 6 1) :
    Nonempty (X ≃* ↥(StatedSp 3 (ZMod 2))) := by
  obtain ⟨-, K, instK, instFin, hK, ⟨e₀⟩⟩ := hX
  letI : Field K := instK
  letI : Finite K := instFin
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using hK
  let eK : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
  let e₁ : ↥(StatedSp 3 K) ≃* ↥(StatedSp 3 (ZMod 2)) :=
    (MulEquiv.ofBijective (spMap (n := 3) eK.toRingHom)
      ⟨spMap_injective _, spMap_surjective eK⟩).symm
  exact ⟨e₀.trans e₁⟩

theorem c8_exists_model {H' : Type} [Group H'] {H P : Subgroup H'} (hPH : P ≤ H)
    (hH : IsSpn ↥H 6 1) (hP : IsE64L3 ↥P) :
    ∃ ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2)),
      P = pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
  classical
  obtain ⟨φ⟩ := c8_nonempty_mulEquiv_of_isSpn hH
  obtain ⟨N, hNn, ⟨e⟩, hL3⟩ := hP
  let N' : Subgroup H' := N.map P.subtype
  have hN'P : N' ≤ P := Subgroup.map_subtype_le N
  have hN'sub : N'.subgroupOf P = N :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective N
  have hN'n : (N'.subgroupOf P).Normal := by rw [hN'sub]; exact hNn
  have hNe : IsElemAbelian 2 N := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact e.injective (by rw [map_mul, map_mul, mul_comm])
    · have h2 : (⟨x, hx⟩ : ↥N) ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        ext i
        simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
        rw [two_nsmul]
        exact CharTwo.add_self_eq_zero _
      simpa using congrArg (fun y : ↥N => (y : ↥P)) h2
  have hN'e : IsElemAbelian 2 N' := IsElemAbelian.map hNe P.subtype
  have hcardN : Nat.card ↥N = 64 := by
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  have hN'64 : Nat.card N' = 64 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcardN]
  have hPcard : Nat.card P = 10752 := by
    haveI := hNn
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [CFSG.Blueprint.LieModel.card_psl_three_two hL3, hcardN] at h
    norm_num at h
    exact h
  obtain ⟨ψ, -, hψ⟩ :=
    c8_exists_model_radical (H := H) (N := N') (P := P) φ hN'P hPH hN'e hN'64 hN'n hPcard
  exact ⟨ψ, hψ⟩

theorem c8_commutator_pullSub_stabilizer {H' : Type} [Group H'] {H : Subgroup H'}
    (ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2))) :
    ⁅pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)),
        pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3))⁆ =
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
  rw [pullSub_eq_map ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)),
    ← Subgroup.map_commutator, c8_commutator_stabilizer_lagrangianZero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

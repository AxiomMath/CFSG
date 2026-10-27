module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNInvol
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
import CFSG.LieType.Chevalley.LatticeWeylGroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Multiplicative

private def cartanRow (p : ℕ) (i : Fin Tag.F4.rank) :
    (Fin Tag.F4.rank → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun x := ∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod p) * x j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem cartanRow_single (p : ℕ) (i : Fin Tag.F4.rank) :
    cartanRow p i (Pi.single i 1) = 2 := by
  have hii : Tag.F4.cartan i i = 2 := by
    revert i
    decide
  simp only [cartanRow, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hii]
  norm_num

theorem exists_involFrame_torusAct_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (e : Multiplicative (Fin Tag.F4.rank → ZMod p) →* R) (a : Fin Tag.F4.rank → R)
    (ha : ∀ i s, a i * e (ofAdd s) * (a i)⁻¹ =
      e (ofAdd (TableBExc.torusAct .F4 p (simple .F4 i) s))) :
    ∃ s₁ ∈ NbrTableBExc.ggTorusInvolSet p e, ∃ s₂ ∈ NbrTableBExc.ggTorusInvolSet p e,
      4 ∣ orderOf (s₁ * s₂) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ i, ExcWeylOuter.torusMulAut .F4 p (simple .F4 i) ∈
      NbrTableBExc.ggTorusInvolSet p e := by
    intro i
    have hrefl : ExcWeylOuter.torusMulAut .F4 p (simple .F4 i) =
        torusReflAut (cartanRow p i) (Pi.single i 1) (cartanRow_single p i) := by
      refine MulEquiv.ext fun x => ?_
      rw [← ofAdd_toAdd x, ExcWeylOuter.torusMulAut_apply, torusReflAut_apply,
        ExcFrames.torusAct_simple]
      rfl
    refine ⟨?_, ?_, a i, fun f => ?_⟩
    · rw [hrefl, pow_two, torusReflAut_mul_self]
    · rw [hrefl]
      exact card_fix_torusReflAut hp hp2 _ _ _
    · rw [← ofAdd_toAdd f, ha, ExcWeylOuter.torusMulAut_apply]
  refine ⟨_, hmem 1, _, hmem 2, ?_⟩
  have h12 : Tag.F4.cartan 1 2 * Tag.F4.cartan 2 1 = 2 := by decide
  rw [← map_mul, orderOf_injective _ (ExcWeylOuter.torusMulAut_injective (τ := .F4) hp2),
    orderOf_simple_mul_simple_eq, h12, TauCeti.coxeterOrder_two]

theorem ggTorusInvolFrameElt_E6Two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusInvolFrameElt 3 4 (TableBExc.RecipeGroup .E6 K) := by
  have : CharP K 2 := charP_two_of_card (show Nat.card K = 2 ^ 1 by rw [hK, pow_one])
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  refine ggTorusInvolFrameElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K) ?_
  obtain ⟨F, hF⟩ :=
    ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_weyl_surjective (K := K) (by rw [hK])
  choose a ha using fun i => hF (simple .F4 i)
  have hfr := exists_involFrame_torusAct_F4 Nat.prime_three (by decide) F.frame
    (fun i => (a i : adjointGroup .E6 K)) fun i s => by rw [F.conj_frame, ha]
  have hcard : Nat.card F.frame.range = 3 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective F.frame_injective).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨g₀, hg₀⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK
    (ExcFrames.isElemAbelian_range_frame F.frame) hcard.ge
  refine ggTorusInvolFrameElt_of_conj F.frame F.frame_injective hfr fun E hE hr _ _ => ?_
  obtain ⟨g, hg⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hr
  refine ⟨g⁻¹ * g₀, ?_⟩
  have key : ∀ (H : Subgroup (adjointGroup .E6 K)) (x y : adjointGroup .E6 K),
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        H.map (MulAut.conj (x * y)).toMonoidHom := fun H x y => by
    rw [Subgroup.map_map, map_mul]
    rfl
  rw [← key, hg₀, ← hg, key, inv_mul_cancel, map_one]
  exact (Subgroup.map_id E).symm

end CFSG.StandardType

end

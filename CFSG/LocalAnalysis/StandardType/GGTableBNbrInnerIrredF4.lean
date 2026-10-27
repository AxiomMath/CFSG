module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeF4
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrredF
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

private theorem moveTableF4_connected :
    ∀ S : Finset (Fin 4), S.Nonempty →
      (∀ i, i ∈ S ↔ (ExcPlusLargeF4.moveTableF4 i).1 ∈ S) → S = Finset.univ := by
  decide +kernel

section Main

private theorem exists_conj_rho_F4_move
    {K : Type} [Field K] [CharP K 2] (i : Fin 4) :
    ∃ g : adjointGroup .F4 K, ∀ A : SL2 K,
      g * TableBF4Two.rho K i A * g⁻¹ =
        TableBF4Two.rho K (ExcPlusLargeF4.moveTableF4 i).1 A := by
  obtain ⟨hne, hroot⟩ := ExcPlusLargeF4.moveTableF4_spec i
  refine ⟨⟨wordRep .F4 K (ExcPlusLargeF4.moveTableF4 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .F4) (L := K)
      (TableBF4Two.isRoot_orthRoot i) (ExcPlusLargeF4.moveTableF4 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul, hroot] at h
    simpa [TableBF4Two.coe_rho] using h

theorem ggSCWeylIrred_F4Plus_largePrime
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K + 1) :
    GGSCWeylIrred p 3 (TableBF4.RecipeGroup K) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro hp2eq
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have h2dvd : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hf]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp f.pos)
    rw [hp2eq] at hpq
    have hodd : Odd (Nat.card K + 1) := by
      obtain ⟨m, hm⟩ := h2dvd
      exact ⟨m, by rw [hm]⟩
    exact hodd.not_two_dvd_nat hpq
  have hp3' : 3 < p := by
    have h2 := hp.two_le
    by_contra h
    have hp_le : p ≤ 3 := by omega
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
  have := TableBF4.finite_recipeGroup (K := K)
  have he := ExcFramesHalf.orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  set e := TableBF4.recipeEquiv K with he_def
  have hT : SylowTorus (TableBF4.RecipeGroup K) p 4 :=
    (OrdPInnerExc.sylowTorus_F4_two K hp hp3' he).of_mulEquiv e.symm
  obtain ⟨s, n, hs, hn⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 (K := K) hp hp2 hpq
  have hu : (-1 : ZMod p) ≠ 1 := by
    haveI : Fact (2 < p) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  have hval : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hn' : n * s * n⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hn, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 K)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  refine ggSCWeylIrred_of_sylowTorus_frameF hp (-1) hu s n hs hn' hZ hT
    (fun i => e.symm.toMonoidHom.comp (TableBF4Two.rho K i)) (fun i => ?_)
    (fun i j hij A B => ?_) (fun i => (ExcPlusLargeF4.moveTableF4 i).1) ?_ ?_ ?_ 3
  · exact e.symm.injective.comp (TableBF4Two.rho_injective i)
  · exact (TableBF4Two.commute_rho hij A B).map e.symm.toMonoidHom
  · intro i
    exact (ExcPlusLargeF4.moveTableF4_spec i).1
  · intro i
    obtain ⟨g, hg⟩ := exists_conj_rho_F4_move (K := K) i
    refine ⟨e.symm g, 1, one_ne_zero, ?_⟩
    have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, pow_one]
    rw [← map_mul, ← map_inv, ← map_mul, hg]
  · intro S hS hInv
    exact moveTableF4_connected S hS hInv

end Main

end CFSG.StandardType

end

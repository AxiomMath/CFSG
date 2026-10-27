module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeE7
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrredF
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

private theorem moveTableE7_connected :
    ∀ S : Finset (Fin 7), S.Nonempty →
      (∀ i, i ∈ S ↔ (ExcPlusLargeE7.moveTableE7 i).1 ∈ S) → S = Finset.univ := by
  decide +kernel

section Main

private theorem exists_conj_rho_E7_move
    {K : Type} [Field K] [CharP K 2] (i : Fin 7) :
    ∃ g : adjointGroup .E7 K,
      ∀ A : SL2 K, g * TableBExcTwo.rho K TableBExcTwo.frameE7 i A * g⁻¹ =
        TableBExcTwo.rho K TableBExcTwo.frameE7 (ExcPlusLargeE7.moveTableE7 i).1 A := by
  obtain ⟨-, hroot⟩ := ExcPlusLargeE7.moveTableE7_spec i
  refine ⟨⟨wordRep .E7 K (ExcPlusLargeE7.moveTableE7 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .E7) (L := K)
      (TableBExcTwo.frameE7.isRoot i) (ExcPlusLargeE7.moveTableE7 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul] at h
    have hroot' : (ExcPlusLargeE7.moveTableE7 i).2.foldr (reflect .E7)
        (TableBExcTwo.frameE7.root i) =
        TableBExcTwo.frameE7.root (ExcPlusLargeE7.moveTableE7 i).1 := hroot
    rw [hroot'] at h
    simpa [TableBExcTwo.coe_rho] using h

theorem ggSCWeylIrred_E7Plus_largePrime
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hpq : p ∣ Nat.card K + 1) :
    GGSCWeylIrred p 6 (TableBExc.RecipeGroup .E7 K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2dvd : 2 ∣ Nat.card K + 1 := hpq
    rw [hK] at h2dvd
    have h2pow : 2 ∣ 2 ^ (f : ℕ) := by
      obtain ⟨g, hg⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt f.pos)
      rw [hg, pow_succ]
      exact dvd_mul_left 2 (2 ^ g)
    exact absurd ((Nat.dvd_add_right h2pow).mp h2dvd) (by norm_num)
  have h11 : 11 ≤ p :=
    ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 (hK ▸ hpq) hp3 hp5
  have := TableBExc.finite_recipeGroup .E7 K
  set e := TableBExc.recipeEquiv .E7 K
  have hT : SylowTorus (TableBExc.RecipeGroup .E7 K) p 7 :=
    (ExcFramesHalf.sylowTorus_E7_half K hp h11 hpq).of_mulEquiv e.symm
  obtain ⟨s, n, hs, hn0⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 (K := K) hp hp2 hpq
  have hu : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hval : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hn : n * s * n⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hn0, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 K)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  refine ggSCWeylIrred_of_sylowTorus_frameF (G₀ := SL2 K) (p := p) (N := 7)
    hp (-1) hu s n hs hn hZ hT
    (fun i => e.symm.toMonoidHom.comp (TableBExcTwo.rho K TableBExcTwo.frameE7 i))
    (fun i => ?_) (fun i j hij A B => ?_)
    (fun i => (ExcPlusLargeE7.moveTableE7 i).1)
    (fun i => (ExcPlusLargeE7.moveTableE7_spec i).1)
    (fun i => ?_) moveTableE7_connected 6
  · exact e.symm.injective.comp (TableBExcTwo.rho_injective _ i)
  · exact (TableBExcTwo.commute_rho _ hij A B).map e.symm.toMonoidHom
  · obtain ⟨g₀, hg₀⟩ := exists_conj_rho_E7_move (K := K) i
    refine ⟨e.symm g₀, 1, one_ne_zero, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ZMod.val_one, pow_one]
    rw [← map_mul, ← map_inv, ← map_mul, hg₀]

end Main

end CFSG.StandardType

end

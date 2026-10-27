module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeE8
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrredF
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

section Main

private theorem exists_conj_rho_E8_move
    {K : Type} [Field K] [CharP K 2] (i : Fin 8) :
    ∃ g : adjointGroup .E8 K,
      ∀ A : SL2 K, g * TableBExcTwo.rho K TableBExcTwo.frameE8 i A * g⁻¹ =
        TableBExcTwo.rho K TableBExcTwo.frameE8 (ExcPlusLargeE8.moveTableE8 i).1 A := by
  obtain ⟨hne, hroot⟩ := ExcPlusLargeE8.moveTableE8_spec i
  refine ⟨⟨wordRep .E8 K (ExcPlusLargeE8.moveTableE8 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .E8) (L := K)
      (TableBExcTwo.frameE8.isRoot i) (ExcPlusLargeE8.moveTableE8 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul] at h
    have hroot' : (ExcPlusLargeE8.moveTableE8 i).2.foldr (reflect .E8)
        (TableBExcTwo.frameE8.root i) =
        TableBExcTwo.frameE8.root (ExcPlusLargeE8.moveTableE8 i).1 := hroot
    rw [hroot'] at h
    simpa [TableBExcTwo.coe_rho] using h

theorem ggSCWeylIrred_E8Plus_largePrime
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hpq : p ∣ Nat.card K + 1) :
    GGSCWeylIrred p 7 (TableBExc.RecipeGroup .E8 K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hp2 : p ≠ 2 := by
    intro hp2eq
    subst hp2eq
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hK2 : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    rw [hK2] at hpq
    have hdvd : (2 : ℕ) ∣ 2 ^ (f : ℕ) := dvd_pow_self 2 f.ne_zero
    have h1 : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right hdvd).mp hpq
    have hle : 2 ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have h11 : 11 ≤ p :=
    ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 (hK ▸ hpq) hp3 hp5
  have := TableBExc.finite_recipeGroup .E8 K
  set e := TableBExc.recipeEquiv .E8 K with he_def
  have hT : SylowTorus (TableBExc.RecipeGroup .E8 K) p 8 :=
    (ExcFramesHalf.sylowTorus_E8_half K hp h11 hpq).of_mulEquiv e.symm
  obtain ⟨s, n, hs, hn_inv⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 (K := K) hp hp2 hpq
  have hu : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    have hp2le : 2 ≤ p := hp.two_le
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    omega
  have hval : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hn : n * s * n⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hn_inv, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 K)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  let f8 : Fin 8 → Fin 8 := fun i => (ExcPlusLargeE8.moveTableE8 i).1
  have hf8 : ∀ i, f8 i ≠ i := fun i => (ExcPlusLargeE8.moveTableE8_spec i).1
  have hf8_eq : f8 = ![1, 2, 3, 2, 5, 3, 3, 3] := by
    funext i
    fin_cases i <;> rfl
  have hconn_aux : ∀ S : Finset (Fin 8), S.Nonempty →
      (∀ i, i ∈ S ↔ (![1, 2, 3, 2, 5, 3, 3, 3] : Fin 8 → Fin 8) i ∈ S) →
      S = Finset.univ := by
    decide +kernel
  have hconn : ∀ S : Finset (Fin 8), S.Nonempty → (∀ i, i ∈ S ↔ f8 i ∈ S) →
      S = Finset.univ := by
    intro S hS h
    exact hconn_aux S hS (fun i => by
      rw [← hf8_eq]
      exact h i)
  refine ggSCWeylIrred_of_sylowTorus_frameF hp (-1) hu s n hs hn hZ hT
    (fun i => e.symm.toMonoidHom.comp (TableBExcTwo.rho K TableBExcTwo.frameE8 i))
    (fun i => e.symm.injective.comp (TableBExcTwo.rho_injective _ i))
    (fun i j hij A B => (TableBExcTwo.commute_rho _ hij A B).map e.symm.toMonoidHom)
    f8 hf8 (fun i => ?_) hconn 7
  · obtain ⟨g₀, hg₀⟩ := exists_conj_rho_E8_move (K := K) i
    refine ⟨e.symm g₀, 1, one_ne_zero, ?_⟩
    have hval1 : (1 : ZMod p).val = 1 := ZMod.val_one p
    rw [hval1, pow_one]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_inv, ← map_mul, hg₀]

end Main

end CFSG.StandardType

end

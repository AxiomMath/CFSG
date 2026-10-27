module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrredF

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

private theorem hconn_moveF4 :
    ∀ S : Finset (Fin 4), S.Nonempty →
      (∀ i, i ∈ S ↔ (![1, 0, 1, 2] : Fin 4 → Fin 4) i ∈ S) → S = Finset.univ := by
  decide +kernel

section Main

section MoveHelper

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KLCE
  CFSG.RankThree.PartOne.KD4T

private theorem exists_conj_rho_F4_move
    {K : Type} [Field K] [CharP K 2] (i : Fin 4) :
    ∃ g : adjointGroup .F4 K, ∀ A : SL2 K,
      g * TableBF4Two.rho K i A * g⁻¹ =
        TableBF4Two.rho K ((ExcPlusLargeF4.moveTableF4 i).1) A := by
  obtain ⟨-, hroot⟩ := ExcPlusLargeF4.moveTableF4_spec i
  refine ⟨⟨wordRep .F4 K (ExcPlusLargeF4.moveTableF4 i).2, ?_⟩, fun A => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup k 1
  · apply Subtype.ext
    have h := wordRep_conj_rootSL2 (τ := .F4) (L := K) (TableBF4Two.isRoot_orthRoot i)
      (ExcPlusLargeF4.moveTableF4 i).2 A
    rw [CFSG.LieType.Chevalley.wordProd_smul, hroot] at h
    simpa [TableBF4Two.coe_rho] using h

end MoveHelper

theorem ggSCWeylIrred_twE6Dvd_largePrime
    {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp3 : p ≠ 3) (hpn : p ∣ 2 ^ n - 1) :
    GGSCWeylIrred p 4 (TwE6Delta.RecipeR K n) := by
  have hp2 : p ≠ 2 := by
    have hmers : mersenne n = 2 ^ n - 1 := by
      have := succ_mersenne n
      omega
    have hodd : Odd (2 ^ n - 1) := by
      rw [← hmers]
      exact mersenne_odd.mpr (by omega)
    exact Odd.ne_two_of_dvd_nat hodd hpn
  have hp4 : p ≠ 4 := by
    intro h
    rw [h] at hp
    exact absurd hp (by norm_num)
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, _, _, _, ι, hk, hι⟩ := exists_injective_f4_recipeR hn hK
  have hpk : p ∣ Nat.card k - 1 := by rw [hk]; exact hpn
  have := TwE6Delta.finite_recipeR (K := K) hK
  obtain ⟨s, m, hs, hm⟩ := exists_order_p_inverting_sl2_split hp hp2 hpk
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
  have hn' : m * s * m⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hm, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 k)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  refine ggSCWeylIrred_of_sylowTorus_frameF hp (-1) hu s m hs hn' hZ
    (sylowTorus_recipeR_split hn hK hp hp5 hpn) (fun i => ι.comp (TableBF4Two.rho k i))
    (fun i => hι.comp (TableBF4Two.rho_injective i))
    (fun i j hij A B => (TableBF4Two.commute_rho hij A B).map ι)
    (fun i => (ExcPlusLargeF4.moveTableF4 i).1)
    (fun i => (ExcPlusLargeF4.moveTableF4_spec i).1)
    (fun i => ?_) ?_ 4
  · obtain ⟨g, hg⟩ := exists_conj_rho_F4_move (K := k) i
    refine ⟨ι g, 1, one_ne_zero, ?_⟩
    have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
    simp only [MonoidHom.comp_apply, h1, pow_one]
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  · intro S hS hfix
    have hf_eq : ∀ i : Fin 4, (ExcPlusLargeF4.moveTableF4 i).1 =
        (![1, 0, 1, 2] : Fin 4 → Fin 4) i := by
      intro i
      fin_cases i <;> rfl
    have hfix' : ∀ i, i ∈ S ↔ (![1, 0, 1, 2] : Fin 4 → Fin 4) i ∈ S := by
      intro i
      have := hfix i
      rwa [hf_eq i] at this
    exact hconn_moveF4 S hS hfix'

end Main

end CFSG.StandardType

end

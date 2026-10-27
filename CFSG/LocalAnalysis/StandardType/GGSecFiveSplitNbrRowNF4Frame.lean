module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNInvol
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameGen
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeF4
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
import CFSG.LocalAnalysis.StandardType.GGTableBF4
import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Multiplicative
  CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

private theorem swap_orthRoot : ∀ i : Fin 4,
    [(2 : Fin Tag.F4.rank)].foldr (reflect .F4) (TableBF4Two.orthRoot i) =
      TableBF4Two.orthRoot (Equiv.swap 0 1 i) := by
  decide +kernel

private theorem hom_ext_single {p N : ℕ} {M : Type} [Monoid M]
    {f g : Multiplicative (Fin N → ZMod p) →* M}
    (h : ∀ i a, f (ofAdd (Pi.single i a)) = g (ofAdd (Pi.single i a))) : f = g := by
  classical
  set P := MulEquiv.piMultiplicative fun _ : Fin N => ZMod p
  have key : f.comp P.symm.toMonoidHom = g.comp P.symm.toMonoidHom := by
    refine MonoidHom.pi_ext fun i x => ?_
    have hx : P.symm (Pi.mulSingle i x) = ofAdd (Pi.single i (toAdd x)) := by
      apply P.injective
      funext j
      rw [MulEquiv.apply_symm_apply]
      exact (Pi.mulSingle_multiplicativeOfAdd_eq (M := fun _ : Fin N => ZMod p) i (toAdd x) j)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx, h]
  refine MonoidHom.ext fun v => ?_
  have := DFunLike.congr_fun key (P v)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rwa [MulEquiv.symm_apply_apply] at this

private theorem conj_frame_swap {p N : ℕ} {R : Type} [Group R]
    (e : Multiplicative (Fin N → ZMod p) →* R) (g : R) (i j : Fin N)
    (h : ∀ k a, g * e (ofAdd (Pi.single k a)) * g⁻¹ = e (ofAdd (Pi.single (Equiv.swap i j k) a)))
    (v : Fin N → ZMod p) : g * e (ofAdd v) * g⁻¹ = e (ofAdd (v ∘ Equiv.swap i j)) := by
  classical
  set S : Multiplicative (Fin N → ZMod p) →* Multiplicative (Fin N → ZMod p) :=
    (NbrFrameOne.swapAut (p := p) i j).toMonoidHom
  have key : (MulAut.conj g).toMonoidHom.comp e = e.comp S :=
    hom_ext_single fun k a => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h, S,
        NbrFrameOne.swapAut_apply]
      congr 2
      funext l
      simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]
  have := DFunLike.congr_fun key (ofAdd v)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, S,
    NbrFrameOne.swapAut_apply] using this

private theorem card_range_frame {p N : ℕ} {R : Type} [Group R]
    {e : Multiplicative (Fin N → ZMod p) →* R} (he : Function.Injective e) :
    Nat.card e.range = p ^ N := by
  rw [← Nat.card_congr (MonoidHom.ofInjective he).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem eq_map_conj {R : Type} [Group R] {E F T : Subgroup R} {g g₀ : R}
    (hE : E.map (MulAut.conj g).toMonoidHom = T) (hF : F.map (MulAut.conj g₀).toMonoidHom = T) :
    E = F.map (MulAut.conj (g⁻¹ * g₀)).toMonoidHom := by
  have key : ∀ (H : Subgroup R) (a b : R), (H.map (MulAut.conj b).toMonoidHom).map
      (MulAut.conj a).toMonoidHom = H.map (MulAut.conj (a * b)).toMonoidHom := fun H a b => by
    rw [Subgroup.map_map, map_mul]
    rfl
  rw [← key, hF, ← hE, key, inv_mul_cancel, map_one]
  exact (Subgroup.map_id E).symm

theorem exists_involFrame_F4
    {K : Type} [Field K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s n : SL2 K}
    (hs : orderOf s = p) (hn : n * s * n⁻¹ = s⁻¹) :
    ∃ e : Multiplicative (Fin 4 → ZMod p) →* adjointGroup .F4 K, Function.Injective e ∧
      ∃ s₁ ∈ NbrTableBExc.ggTorusInvolSet p e, ∃ s₂ ∈ NbrTableBExc.ggTorusInvolSet p e,
        4 ∣ orderOf (s₁ * s₂) := by
  have hval : (-1 : ZMod p).val = p - 1 := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hn' : n * s * n⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hn, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 K)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  obtain ⟨e, m, he, he₁, hm⟩ := exists_frameTorus_of_commutingFrames hp (-1) s n hs hn' hZ
    (TableBF4Two.rho K) TableBF4Two.rho_injective fun i j h A B => TableBF4Two.commute_rho h A B
  obtain ⟨g, hg⟩ : ∃ g : adjointGroup .F4 K, ∀ (i : Fin 4) (A : SL2 K),
      g * TableBF4Two.rho K i A * g⁻¹ = TableBF4Two.rho K (Equiv.swap 0 1 i) A := by
    refine ⟨⟨wordRep .F4 K [2], ?_⟩, fun i A => ?_⟩
    · refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact weylElt_mem_adjointGroup k 1
    · apply Subtype.ext
      have h := wordRep_conj_rootSL2 (τ := .F4) (L := K) (TableBF4Two.isRoot_orthRoot i) [2] A
      rw [CFSG.LieType.Chevalley.wordProd_smul, swap_orthRoot i] at h
      simpa [TableBF4Two.coe_rho] using h
  have hge := conj_frame_swap e g 0 1 fun k a => by rw [he₁, he₁, hg]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  refine ⟨e, he, NbrFrameOne.negAut 0, ⟨NbrFrameOne.negAut_sq 0,
    NbrFrameOne.card_fix_negAut hp hp2 0, m 0, fun f => ?_⟩, NbrFrameOne.swapAut 0 1,
    ⟨NbrFrameOne.swapAut_sq 0 1, NbrFrameOne.card_fix_swapAut hp h01, g, fun f => ?_⟩, ?_⟩
  · rw [← ofAdd_toAdd f, hm, NbrFrameOne.negAut_apply, neg_one_mul]
  · rw [← ofAdd_toAdd f, hge, NbrFrameOne.swapAut_apply]
  · rw [NbrFrameOne.orderOf_negAut_mul_swapAut hp hp2 h01]

theorem ggTorusInvolFrameElt_F4Split
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusInvolFrameElt p 4 (TableBF4.RecipeGroup K) := by
  refine ggTorusInvolFrameElt_of_mulEquiv (TableBF4.recipeEquiv K) ?_
  obtain ⟨s, n, hs, hn⟩ := exists_order_p_inverting_sl2_split (K := K) hp hp2 hpq
  obtain ⟨e, he, hfr⟩ := exists_involFrame_F4 hp hp2 hs hn
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  have hcard : Nat.card e.range = p ^ 4 := card_range_frame he
  obtain ⟨g₀, hg₀⟩ := hT e.range (ExcFrames.isElemAbelian_range_frame e) hcard.ge
  refine ggTorusInvolFrameElt_of_conj e he hfr fun E hE hr _ _ => ?_
  obtain ⟨g, hg⟩ := hT E hE hr
  exact ⟨g⁻¹ * g₀, eq_map_conj hg hg₀⟩

theorem ggTorusInvolFrameElt_F4Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (r : ℕ) :
    GGTorusInvolFrameElt p r (TableBF4.RecipeGroup K) := by
  have hp2 : p ≠ 2 := by omega
  refine ggTorusInvolFrameElt_of_mulEquiv (TableBF4.recipeEquiv K) ?_
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨s, n, hs, hn⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 (K := K) hp hp2 hpq
  obtain ⟨e, he, hfr⟩ := exists_involFrame_F4 hp hp2 hs hn
  have hT := OrdPInnerExc.sylowTorus_F4_two K hp (by omega)
    (ExcFramesHalf.orderOf_eq_two_of_dvd_add_one hp hp2 hpq)
  exact ggTorusInvolFrameElt_of_conj e he hfr fun E hE _ _ hsc =>
    exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT (ExcFrames.isElemAbelian_range_frame e)
      (card_range_frame he) hE hsc

end CFSG.StandardType

end

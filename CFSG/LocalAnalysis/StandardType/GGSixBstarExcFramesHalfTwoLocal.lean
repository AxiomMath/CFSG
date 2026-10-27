module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfKG
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LieType.SeitzGeneration.HyperExFourSL2
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExcTwo

namespace ExcFramesHalf

section Frame

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] {p : ℕ}

variable (K) in
@[expose] noncomputable def frameCoordP (F : OrthFrame τ d) {g : SL2 K} (hg : g ^ p = 1)
    (i : Fin d) : Multiplicative (ZMod p) →* adjointGroup τ K :=
  TableBSymp.zmodPowHom (t := rho K F i.castSucc g) (by rw [← map_pow, hg, map_one])

theorem frameCoordP_apply [NeZero p] (F : OrthFrame τ d) {g : SL2 K} (hg : g ^ p = 1)
    (i : Fin d) (a : Multiplicative (ZMod p)) :
    frameCoordP K F hg i a = rho K F i.castSucc (g ^ (Multiplicative.toAdd a).val) := by
  rw [frameCoordP, TableBSymp.zmodPowHom_apply, map_pow]

theorem frameCoordP_commute [NeZero p] (F : OrthFrame τ d) {g : SL2 K} (hg : g ^ p = 1) :
    Pairwise fun i j : Fin d => ∀ a b,
      Commute (frameCoordP K F hg i a) (frameCoordP K F hg j b) := by
  intro i j hij a b
  rw [frameCoordP_apply, frameCoordP_apply]
  exact commute_rho F (castSucc_ne_castSucc' hij) _ _

variable (K) in
@[expose] noncomputable def frameDP [NeZero p] (F : OrthFrame τ d) {g : SL2 K}
    (hg : g ^ p = 1) : (Fin d → Multiplicative (ZMod p)) →* adjointGroup τ K :=
  MonoidHom.noncommPiCoprod (frameCoordP K F hg) (frameCoordP_commute F hg)

theorem frameCoordP_injective [Fact p.Prime] (F : OrthFrame τ d) {g : SL2 K} (hg : g ^ p = 1)
    (hg1 : g ≠ 1) (i : Fin d) : Function.Injective (frameCoordP K F hg i) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [frameCoordP_apply] at ha
  have h1 : g ^ (Multiplicative.toAdd a).val = 1 :=
    rho_injective F _ (ha.trans (map_one _).symm)
  have hd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hg hg1] at hd
  have h0 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h0
  rw [← ofAdd_toAdd a, h0, ofAdd_zero]

theorem frameCoordP_iSupIndep [Fact p.Prime] (hp2 : p ≠ 2) (F : OrthFrame τ d) {g : SL2 K}
    (hg : g ^ p = 1) : iSupIndep fun i => (frameCoordP K F hg i).range := by
  have hp : p.Prime := Fact.out
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j) (_ : j ≠ i), (frameCoordP K F hg j).range) ≤
      Subgroup.centralizer (Set.range (rho K F i.castSucc)) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    rw [frameCoordP_apply]
    exact (commute_rho F (castSucc_ne_castSucc' (Ne.symm hj)) _ _).eq
  have hc := Subgroup.mem_centralizer_iff.mp (hle hx')
  have hcomm : ∀ A, Commute (g ^ (Multiplicative.toAdd a).val) A := fun A => by
    have h1 := hc (rho K F i.castSucc A) ⟨A, rfl⟩
    rw [frameCoordP_apply, ← map_mul, ← map_mul] at h1
    exact (rho_injective F _ h1).symm
  have h1 := CFSG.LieType.SeitzGeneration.eq_one_of_commute_uSL_vSL hp hp2
    (x := g ^ (Multiplicative.toAdd a).val)
    (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) (hcomm _) (hcomm _)
  rw [frameCoordP_apply, h1, map_one]

theorem frameDP_injective [Fact p.Prime] (hp2 : p ≠ 2) (F : OrthFrame τ d) {g : SL2 K}
    (hg : g ^ p = 1) (hg1 : g ≠ 1) : Function.Injective (frameDP K F hg) :=
  MonoidHom.injective_noncommPiCoprod_of_iSupIndep (frameCoordP K F hg)
    (frameCoordP_iSupIndep hp2 F hg) (frameCoordP_injective F hg hg1)

theorem frameDP_commute [NeZero p] (F : OrthFrame τ d) {g : SL2 K} (hg : g ^ p = 1)
    (f : Fin d → Multiplicative (ZMod p)) (A : SL2 K) :
    Commute (frameDP K F hg f) (rho K F (Fin.last d) A) := by
  have hmem : frameDP K F hg f ∈ (frameDP K F hg).range := ⟨_, rfl⟩
  have hle : (frameDP K F hg).range ≤ Subgroup.centralizer {rho K F (Fin.last d) A} := by
    rw [frameDP, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, frameCoordP_apply]
    exact (commute_rho F (Fin.castSucc_lt_last i).ne _ _).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hmem)

theorem exists_twoLocal_of_frame [Finite K] [CharP K 2] (F : OrthFrame τ d) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ E U : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧ Nat.card E = p ^ d ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpq2 : p ∣ Nat.card K ^ 2 - 1 := by
    have hq : 1 ≤ Nat.card K := Finite.card_pos
    rw [show Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact hpq.mul_right _
  obtain ⟨x, hdet, hxp, hx1⟩ := CFSG.LieType.SeitzGeneration.exists_sl2_order hp hpq2
  set g : SL2 K := ⟨x, hdet⟩ with hgdef
  have hgp : g ^ p = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hxp)
  have hg1 : g ≠ 1 := fun h => hx1 (by simpa [g] using congrArg Subtype.val h)
  set φ : Multiplicative (Fin d → ZMod p) →* adjointGroup τ K :=
    (frameDP K F hgp).comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).toMonoidHom
    with hφ
  have hφinj : Function.Injective φ :=
    (frameDP_injective hp2 F hgp hg1).comp (MulEquiv.piMultiplicative _).injective
  set z : adjointGroup τ K := rho K F (Fin.last d) (uSL 1) with hz
  have hz1 : z ≠ 1 := fun h =>
    TableBF4Two.uSL_one_ne_one (K := K) (rho_injective F _ (h.trans (map_one _).symm))
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← map_pow, TableBF4Two.uSL_one_sq CharTwo.two_eq_zero, map_one]
  refine ⟨φ.range, Subgroup.zpowers z, ExcFrames.isElemAbelian_range_frame φ, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr
      Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hz1
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  · rintro _ ⟨v, rfl⟩
    have hc : Commute (φ v) z := frameDP_commute F hgp _ (uSL 1)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ _
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hy' : y = z ^ k := by
        have h1 : φ v * y * (φ v)⁻¹ = φ v * z ^ k * (φ v)⁻¹ := by
          rw [← hk, (hc.zpow_right k).eq, mul_inv_cancel_right]
        exact mul_left_cancel (mul_right_cancel h1)
      rw [hy']
      exact Subgroup.zpow_mem_zpowers _ _

end Frame

section Tags

theorem ggExcHalfTwoLocalInput_E7 : GGExcHalfTwoLocalInput .E7 :=
  fun _ _ _ _ _ hp hp2 hpq _ => exists_twoLocal_of_frame frameE7 hp hp2 hpq

theorem ggExcHalfTwoLocalInput_E8 : GGExcHalfTwoLocalInput .E8 :=
  fun _ _ _ _ _ hp hp2 hpq _ => exists_twoLocal_of_frame frameE8 hp hp2 hpq

end Tags

end ExcFramesHalf

section Bundle

@[expose] def GGSixBstarExcFramesRestHalfMax : Prop :=
  GGExcNonsplitRankInput .F4 ∧ GGExcHalfMaxElemInput .E7 ∧ GGExcNonsplitRankInput .E7 ∧
    GGExcHalfMaxElemInput .E8 ∧ GGSixBstarExcFrameOn .E8 GGExcE8RestLabel ∧
      GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel ∧
        GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel ∧
          GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel ∧
            GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel

theorem ggSixBstarExcFramesRestHalfKG_of_max (h : GGSixBstarExcFramesRestHalfMax) :
    GGSixBstarExcFramesRestHalfKG := by
  obtain ⟨hF4N, hE7M, hE7N, hE8M, hE8N, hE6S, hE6N, hTwS, hTwN⟩ := h
  exact ⟨hF4N, ⟨ExcFramesHalf.ggExcHalfTwoLocalInput_E7, hE7M⟩, hE7N,
    ⟨ExcFramesHalf.ggExcHalfTwoLocalInput_E8, hE8M⟩, hE8N, hE6S, hE6N, hTwS, hTwN⟩

theorem ggSixBstarExcFramesRest_of_max
    (h : GGSixBstarExcFramesRestHalfMax) : GGSixBstarExcFramesRest :=
  ggSixBstarExcFramesRest_of_half
    (ggSixBstarExcFramesRestHalf_of_kg (ggSixBstarExcFramesRestHalfKG_of_max h))

end Bundle

end CFSG.StandardType

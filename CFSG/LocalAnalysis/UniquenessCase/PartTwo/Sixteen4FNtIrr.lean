module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.F918D0
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQSL2RootCommutator
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W]

private abbrev w183ModTwo {V : Type} [CommGroup V] (hsq : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]
    have h := hsq (Additive.toMul a)
    rw [pow_two] at h
    exact congrArg Additive.ofMul h)

private theorem w183_le_stabSub_fixV {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) :
    H ≤ stabSub (fixV H) :=
  fun g hg => centSub_le_stabSub (fixV H) fun _ hu => hu g hg

private noncomputable def w183StabHom {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLU : L ≤ stabSub U) : ↥L →* ↥(stabSub (fixV (autSub L U))) :=
  ((resHom U).comp (Subgroup.inclusion hLU)).codRestrict _
    (fun l => w183_le_stabSub_fixV (autSub L U)
      (mem_autSub.mpr ⟨⟨l.1, hLU l.2⟩, l.2, rfl⟩))

private noncomputable def w183QuotAct {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLU : L ≤ stabSub U) : ↥L →* MulAut (↥U ⧸ fixV (autSub L U)) :=
  (quotHom (fixV (autSub L U))).comp (w183StabHom hLU)

private noncomputable def w183MuQ {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLU : L ≤ stabSub U) :
    ↥L →* AddMonoid.End (Additive (↥U ⧸ fixV (autSub L U))) where
  toFun l := (w183QuotAct hLU l).toAdditive.toAddMonoidHom
  map_one' := by
    rw [map_one]
    ext x
    rfl
  map_mul' a b := by
    rw [map_mul]
    ext x
    rfl

private theorem w183MuQ_apply_mk {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLU : L ≤ stabSub U) (l : ↥L) (u : ↥U) :
    w183MuQ hLU l
        (Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ fixV (autSub L U))) =
      Additive.ofMul (QuotientGroup.mk ((w183StabHom hLU l).1 u)) :=
  rfl

private noncomputable def w183RepOfEnd {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (μ : G →* AddMonoid.End V) : Representation (ZMod 2) G V where
  toFun g := (μ g).toZModLinearMap 2
  map_one' := by
    ext v
    change μ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v
    change μ (g * h) v = μ g (μ h v)
    rw [map_mul]
    rfl

private theorem w183_mQuot_bot {V : Type} [CommGroup V] (U : Subgroup V) :
    E3.mQuot U ⊥ = rk ↥U := by
  simp [E3.mQuot, rk, Subgroup.relIndex, Subgroup.index_bot]

private theorem w183_rk_le_of_card_le [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {Z : Subgroup W} {c : ℕ} (h : Nat.card ↥Z ≤ 2 ^ c) : rk ↥Z ≤ c := by
  have hcard : Nat.card ↥Z = 2 ^ rk ↥Z := card_eq_two_pow hW2 Z
  have hpow : 2 ^ rk ↥Z ≤ 2 ^ c := by rw [← hcard]; exact h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

theorem s16nt_goal_of_irr_h1 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hirr : commSub ⊤ L ∈ irrSet L) {d c : ℕ}
    (hd : E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = d) (hcd : 2 * c ≤ d)
    (hH1 : ∀ (Q : Type) [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
      (ρ : Representation (ZMod 2) ↥L Q), ρ.IsIrreducible → Module.finrank (ZMod 2) Q = d →
        Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) ≤ c) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  classical
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := U ⊓ fixV L
  have hirr' : commSub U L = U ∧ IsIrrOn L U Z := hirr
  obtain ⟨hUc, hIrr⟩ := hirr'
  obtain ⟨hZU_lt, hUinv, _hZinv, hIrrJ⟩ := hIrr
  have hZU : Z ≤ U := hZU_lt.le
  have hd' : E3.mQuot U Z = d := hd
  have hLU : L ≤ stabSub U := by
    intro l hl
    refine mem_stabSub.mpr fun u => ⟨fun hu => ?_, fun hu => hUinv l hl u hu⟩
    have h1 := hUinv l⁻¹ (L.inv_mem hl) (l u) hu
    simpa using h1
  let C : Subgroup ↥U := fixV (autSub L U)
  have hC : C = Z.subgroupOf U := by
    apply Subgroup.map_injective U.subtype_injective
    rw [map_subtype_fixV_autSub hLU, Subgroup.map_subgroupOf_eq_of_le hZU]
  have hCtop : C < ⊤ :=
    (Subgroup.map_lt_map_iff_of_injective U.subtype_injective).mp (by
      rw [map_subtype_fixV_autSub hLU, Subgroup.map_top, Subgroup.range_subtype]
      exact hZU_lt)
  have hq : ∀ q : ↥U ⧸ C, q ^ 2 = 1 := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow]
    have hv : (v : ↥U) ^ 2 = 1 := Subtype.ext (by simpa using hW2 (v : W))
    rw [hv, QuotientGroup.mk_one]
  letI : Module (ZMod 2) (Additive (↥U ⧸ C)) := w183ModTwo hq
  let ρQ : Representation (ZMod 2) ↥L (Additive (↥U ⧸ C)) :=
    w183RepOfEnd (w183MuQ hLU)
  have hρQ : ρQ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
    constructor
    · obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt hCtop
      exact ⟨0, Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ C), fun h => hu
        ((QuotientGroup.eq_one_iff u).mp (ofMul_eq_zero.mp h.symm))⟩
    · intro M hM
      let W' : Subgroup ↥U :=
        { carrier := {u | Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ C) ∈ M}
          one_mem' := by
            simpa [QuotientGroup.mk_one, ofMul_one] using M.zero_mem
          mul_mem' := by
            intro a b ha hb
            simpa [QuotientGroup.mk_mul, ofMul_mul] using M.add_mem ha hb
          inv_mem' := by
            intro a ha
            simpa [QuotientGroup.mk_inv, ofMul_inv] using M.neg_mem ha }
      have hCW' : C ≤ W' := by
        intro c hc
        show Additive.ofMul (QuotientGroup.mk c : ↥U ⧸ C) ∈ M
        rw [(QuotientGroup.eq_one_iff c).mpr hc]
        simpa using M.zero_mem
      have hW'inv : ∀ (l : MulAut W) (hl : l ∈ L) (u : ↥U), u ∈ W' →
          (⟨l (u : W), hUinv l hl (u : W) u.2⟩ : ↥U) ∈ W' := by
        intro l hl u hu
        have h1 : ρQ ⟨l, hl⟩ (Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ C)) ∈ M :=
          hM ⟨l, hl⟩ _ hu
        change (w183MuQ hLU ⟨l, hl⟩)
            (Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ C)) ∈ M at h1
        rw [w183MuQ_apply_mk hLU ⟨l, hl⟩ u] at h1
        show Additive.ofMul (QuotientGroup.mk
            (⟨l (u : W), hUinv l hl (u : W) u.2⟩ : ↥U) : ↥U ⧸ C) ∈ M
        rw [show (⟨l (u : W), hUinv l hl (u : W) u.2⟩ : ↥U) =
            (w183StabHom hLU ⟨l, hl⟩).1 u from Subtype.ext rfl]
        exact h1
      have hJinv : StableUnder L (W'.map U.subtype) := by
        intro l hl w hw
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
        exact Subgroup.mem_map.mpr
          ⟨⟨l (u : W), hUinv l hl (u : W) u.2⟩, hW'inv l hl u hu, rfl⟩
      have hZJ : Z ≤ W'.map U.subtype := by
        have hZC : Z = C.map U.subtype := by rw [map_subtype_fixV_autSub hLU]
        rw [hZC]
        exact Subgroup.map_mono hCW'
      have hJU : W'.map U.subtype ≤ U := Subgroup.map_subtype_le W'
      rcases hIrrJ (W'.map U.subtype) hJinv hZJ hJU with h | h
      · left
        have hW'C : W' = C := by
          apply Subgroup.map_injective U.subtype_injective
          rw [h, map_subtype_fixV_autSub hLU]
        refine (Submodule.eq_bot_iff M).mpr fun q hq => ?_
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
        have hv : v ∈ W' := hq
        rw [hW'C] at hv
        exact (congrArg Additive.ofMul
          ((QuotientGroup.eq_one_iff v).mpr hv)).trans ofMul_one
      · right
        have hW'top : W' = ⊤ := by
          apply Subgroup.map_injective U.subtype_injective
          rw [h, Subgroup.map_top, Subgroup.range_subtype]
        refine Submodule.eq_top_iff'.mpr fun q => ?_
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
        show v ∈ W'
        exact hW'top ▸ Subgroup.mem_top v
  have hfinrank : Module.finrank (ZMod 2) (Additive (↥U ⧸ C)) = d := by
    have hU2 : IsPGroup 2 ↥U := isPGroup_two_of_sq_eq_one fun u =>
      Subtype.ext (by simpa using hW2 (u : W))
    have hcard : Nat.card (Additive (↥U ⧸ C)) = 2 ^ d :=
      calc Nat.card (Additive (↥U ⧸ C)) = C.index := (Subgroup.index_eq_card C).symm
        _ = Z.relIndex U := by rw [hC]; rfl
        _ = 2 ^ E3.mQuot U Z := E3.relIndex_eq_two_pow hU2 Z
        _ = 2 ^ d := by rw [hd']
    have hpow := FiniteField.pow_finrank_eq_natCard 2 (Additive (↥U ⧸ C))
    have h2 : 2 ^ Module.finrank (ZMod 2) (Additive (↥U ⧸ C)) = 2 ^ d := by
      rw [hpow, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  haveI : Finite ↥L := Finite.of_injective (fun l : ↥L => (l.1 : W → W))
    (fun a b h => Subtype.ext (DFunLike.ext _ _ fun w => congrFun h w))
  have hcomm : XMod.commOf ↥L U = U := by rw [commOf_eq_commSub]; exact hUc
  have hZfix : ∀ z ∈ Z, ∀ x ∈ L, x z = z := fun z hz x hx => mem_fixV.mp hz.2 x hx
  let β : ↥U →* Multiplicative (Additive (↥U ⧸ C)) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u : ↥U ⧸ C))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hβs : Function.Surjective β := by
    intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (Additive.toMul (Multiplicative.toAdd m))
    exact ⟨x, by
      show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk x : ↥U ⧸ C)) = m
      rw [hx, ofMul_toMul, ofAdd_toAdd]⟩
  have hβk : ∀ v : ↥U, β v = 1 ↔ (v : W) ∈ Z := by
    intro v
    show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk v : ↥U ⧸ C)) = 1 ↔
      (v : W) ∈ Z
    rw [ofAdd_eq_one, ofMul_eq_zero, QuotientGroup.eq_one_iff, hC,
      Subgroup.mem_subgroupOf]
  have hβe : ∀ (γ : ↥L) (v : ↥U) (hv : (γ : MulAut W) (v : W) ∈ U),
      β ⟨(γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β v))) := by
    intro γ v hv
    change Multiplicative.ofAdd (Additive.ofMul
        (QuotientGroup.mk (⟨(γ : MulAut W) (v : W), hv⟩ : ↥U) : ↥U ⧸ C)) =
      Multiplicative.ofAdd ((w183MuQ hLU γ)
        (Additive.ofMul (QuotientGroup.mk v : ↥U ⧸ C)))
    rw [w183MuQ_apply_mk hLU γ v]
    rw [show (⟨(γ : MulAut W) (v : W), hv⟩ : ↥U) =
        (w183StabHom hLU γ).1 v from Subtype.ext rfl]
  have hcard := card_le_pow_finrank_H1_dual (W := W) (Γ := ↥L) hW2 L U Z hZU hZfix hUinv hcomm
    (MonoidHom.id ↥L) Function.surjective_id ρQ β hβs hβk hβe
  haveI : Module.Finite (ZMod 2) (Additive (↥U ⧸ C)) := Module.Finite.of_finite
  haveI : Finite (Module.Dual (ZMod 2) (Additive (↥U ⧸ C))) :=
    Module.finite_of_finite (ZMod 2)
  have hdual : (Representation.dual ρQ).IsIrreducible :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.isIrreducible_dual ρQ hρQ
  have hdimdual : Module.finrank (ZMod 2)
      (Module.Dual (ZMod 2) (Additive (↥U ⧸ C))) = d := by
    rw [Subspace.dual_finrank_eq, hfinrank]
  have hH1' : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1 (Representation.dual ρQ)) ≤ c :=
    hH1 (Module.Dual (ZMod 2) (Additive (↥U ⧸ C))) (Representation.dual ρQ) hdual hdimdual
  have hZle : Nat.card ↥Z ≤ 2 ^ c :=
    hcard.trans (Nat.pow_le_pow_right (by norm_num) hH1')
  have hrkZ : rk ↥Z ≤ c := w183_rk_le_of_card_le hW2 hZle
  have hrkU : rk ↥U = rk ↥Z + d := by
    have h1 := E3.mQuot_add (V := U) (U := ⊥) (U' := Z) bot_le hZU
    rw [w183_mQuot_bot U, w183_mQuot_bot Z, hd'] at h1
    exact h1
  change 3 * rk ↥Z ≤ rk ↥U
  rw [hrkU]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

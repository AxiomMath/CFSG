module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotKindsY
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeXLeaf

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL)

local instance twistedE6PilotKindsXNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotKindsXNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Model


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem subsystemGroup_setA_le_centralizer_thetaTorus :
    subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
      centralizer (E6GraphLevi.thetaTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) := by
  rw [← (neighbourTorus_X_Y (algebraMap k K)).1]
  exact subsystemGroup_le_centralizer_relLeviTorus _ fun i hi => by
    have h : ∀ i : Fin Tag.E6.rank, i ≠ 1 →
        e6IndexToF4 i ∈ ({1, 2, 3} : Finset (Fin Tag.F4.rank)) := by decide
    exact h i hi

theorem exists_mul_realize_of_mem_relLeviTorus_one (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ relLeviTorus K (Units.map (algebraMap k K).toMonoidHom).range {1}) :
    ∃ B ∈ unitarySL σ, ∃ w ∈ E6GraphLevi.thetaTorus (algebraMap k K),
      x = w * realize (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) B := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hAσ, -⟩ := unitsRange_facts hf2 hk hσ
  obtain ⟨hcen, -, hWD⟩ := centralizer_thetaTorus_inf_eq hf2 hk hK hσ
  have hWT : E6GraphLevi.thetaTorus (algebraMap k K) ≤
      relLeviTorus K (Units.map (algebraMap k K).toMonoidHom).range {1} := by
    rw [← (neighbourTorus_X_Y (algebraMap k K)).1]
    exact neighbourTorus_le_relLeviTorus _ .X (by decide)
  have hxC : x ∈ graphFixedRootGroup TwistTag.E6 K σ := relLeviTorus_le_C0 hAσ {1} hx
  have hxW : x ∈ centralizer (E6GraphLevi.thetaTorus (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (relLeviTorus_le_centralizer_self _ {1} hx) w (hWT hw))
  have hxWD : x ∈ E6GraphLevi.thetaTorus (algebraMap k K) ⊔ su6Levi σ := by
    rw [← hcen]
    exact mem_inf.2 ⟨hxW, hxC⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hWD.trans (centralizer_le_normalizer _))] at hxWD
  obtain ⟨w, hw, δ, hδ, rfl⟩ := hxWD
  have hδ' : δ ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ := hδ
  rw [(E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
    (E6GraphLevi.two_eq_zero_of_card_sq hf hK)).1] at hδ'
  obtain ⟨B, hB, rfl⟩ := hδ'
  exact ⟨B, hB, w, hw, rfl⟩

theorem ker_realize_le_center (h2 : (2 : K) = 0) :
    (realize h2).ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) K) := by
  intro B hB
  obtain ⟨l, -, hl⟩ := (E6GraphLevi.mem_ker_realize h2 B).1 hB
  rw [mem_center_iff]
  intro A
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hl]
  exact congrFun (congrFun (Matrix.scalar_commute l (fun r' => Commute.all l r')
    (A : Matrix (Fin 6) (Fin 6) K)).symm.eq i) j

end Model

section Piece


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem pieceDichotomy_of_fieldCoverParamX (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (h : FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X))) :
    PieceDichotomy (pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1}) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hA3, -, -, -⟩ := unitsRange_facts hf2 hk hσ
  set h2 := E6GraphLevi.two_eq_zero_of_card_sq hf hK with hh2
  set A : Subgroup Kˣ := (Units.map (algebraMap k K).toMonoidHom).range with hAdef
  set T' : Subgroup (ModGL TwistTag.E6.tag K) := relLeviTorus K A {1} with hT'def
  set XG : Subgroup G := modelToG e (neighbourTorus K A .X) with hXG
  have hW₀ : neighbourTorus K A .X = E6GraphLevi.thetaTorus (algebraMap k K) :=
    (neighbourTorus_X_Y (algebraMap k K)).1
  have hWC : E6GraphLevi.thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    thetaTorus_le_C0 hf hk hK hσ
  have hWLA := subsystemGroup_setA_le_centralizer_thetaTorus (K := K) (k := k)
  have hdec : ∀ x ∈ T', ∃ B ∈ unitarySL σ, ∃ w ∈ E6GraphLevi.thetaTorus (algebraMap k K),
      x = w * realize h2 B := fun x hx =>
    exists_mul_realize_of_mem_relLeviTorus_one hf2 hk hK hσ hx
  choose B hB w hw hxw using hdec
  have key : ∀ (b : Matrix.SpecialLinearGroup (Fin 6) K) (ww x : ModGL TwistTag.E6.tag K),
      ww ∈ E6GraphLevi.thetaTorus (algebraMap k K) → x = ww * realize h2 b →
      ∀ y, realize h2 (b * y * b⁻¹) = x * realize h2 y * x⁻¹ := by
    intro b ww x hww hx y
    subst hx
    have hz : realize h2 b * realize h2 y * (realize h2 b)⁻¹ ∈
        subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
      rw [← E6GraphLevi.range_realize h2, ← map_inv, ← map_mul, ← map_mul]
      exact ⟨_, rfl⟩
    have hc := mem_centralizer_iff.1 (hWLA hz) ww hww
    rw [map_mul, map_mul, map_inv]
    calc realize h2 b * realize h2 y * (realize h2 b)⁻¹ =
        ww * (realize h2 b * realize h2 y * (realize h2 b)⁻¹) * ww⁻¹ := by
          rw [hc, mul_inv_cancel_right]
      _ = ww * realize h2 b * realize h2 y * (ww * realize h2 b)⁻¹ := by group
  have keyG : ∀ (b : Matrix.SpecialLinearGroup (Fin 6) K) (ww : ModGL TwistTag.E6.tag K)
      (x : graphFixedRootGroup TwistTag.E6 K σ), ww ∈ E6GraphLevi.thetaTorus (algebraMap k K) →
      (x : ModGL TwistTag.E6.tag K) = ww * realize h2 b → b ∈ unitarySL σ →
      ∀ y, h.Φ (b * y * b⁻¹) = ((e.symm x : L) : G) * h.Φ y * ((e.symm x : L) : G)⁻¹ := by
    intro b ww x hww hx hb y
    have hbC : realize h2 b ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      realize_mem_C0_of_mem_unitarySL hf hK hσ h2 hb
    have hxe : x = ⟨ww, hWC hww⟩ * ⟨realize h2 b, hbC⟩ := Subtype.ext hx
    have hN1 := h.N1 b hb hbC
    set u : G := ((e.symm ⟨ww, hWC hww⟩ : L) : G) with hu
    have huX : u ∈ XG :=
      symm_mem_modelToG e (show ww ∈ neighbourTorus K A .X by rw [hW₀]; exact hww)
    have hz : h.Φ (b * y * b⁻¹) ∈ centralizer (XG : Set G) := by
      have hmem : h.Φ (b * y * b⁻¹) ∈ h.Φ.range := ⟨_, rfl⟩
      rw [h.range_eq] at hmem
      exact F4Pilot.centralizerPerfectCore_le_centralizer XG hmem
    have hc := mem_centralizer_iff.1 hz u huX
    have hex : ((e.symm x : L) : G) = u * h.Φ b := by
      rw [hxe, map_mul, Subgroup.coe_mul, hN1]
    rw [hex]
    calc h.Φ (b * y * b⁻¹) = u * h.Φ (b * y * b⁻¹) * u⁻¹ := by rw [hc, mul_inv_cancel_right]
      _ = u * h.Φ b * h.Φ y * (u * h.Φ b)⁻¹ := by rw [map_mul, map_mul, map_inv]; group
  let α' : T' → MulAut (Matrix.SpecialLinearGroup (Fin 6) K) := fun x => MulAut.conj (B x x.2)
  have hα' : ∀ (x : T') (y : Matrix.SpecialLinearGroup (Fin 6) K),
      realize h2 (α' x y) = (x : ModGL TwistTag.E6.tag K) * realize h2 y *
        (x : ModGL TwistTag.E6.tag K)⁻¹ := fun x y =>
    key (B x x.2) (w x x.2) x (hw x x.2) (hxw x x.2) y
  have hxd : ∀ d : modelToG e T', ∃ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ T' ∧ ((e.symm x : L) : G) = d :=
    fun d => (mem_modelToG e).1 d.2
  choose xd hxdT hxde using hxd
  let g : modelToG e T' → T' := fun d => ⟨(xd d : ModGL TwistTag.E6.tag K), hxdT d⟩
  have hg : Function.Surjective g := by
    intro x'
    have hC : (x' : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      relLeviTorus_le_C0 (unitsRange_facts hf2 hk hσ).2.2.1 {1} x'.2
    refine ⟨⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩, ?_⟩
    have h1 := hxde ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩
    have h2' : xd ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩ = ⟨x', hC⟩ :=
      e.symm.injective (Subtype.ext h1)
    have h3 : ((xd ⟨((e.symm ⟨x', hC⟩ : L) : G), symm_mem_modelToG e x'.2⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) = x' :=
      congrArg Subtype.val h2'
    exact Subtype.ext h3
  let α : modelToG e T' → MulAut (Matrix.SpecialLinearGroup (Fin 6) K) := α' ∘ g
  have hα : ∀ (d : modelToG e T') (y : Matrix.SpecialLinearGroup (Fin 6) K),
      h.Φ (α d y) = (d : G) * h.Φ y * (d : G)⁻¹ := by
    intro d y
    have h1 := keyG (B (xd d) (hxdT d)) (w (xd d) (hxdT d)) (xd d) (hw _ _) (hxw _ _) (hB _ _) y
    rw [hxde d] at h1
    exact h1
  have hYT : XG ≤ modelToG e T' :=
    modelToG_mono e (neighbourTorus_le_relLeviTorus A .X (by decide))
  have hpiece : pieceCore e A {1} = (perfectCore (fixAll α)).map h.Φ := by
    rw [pieceCore_def]
    exact LinearPilot.centralizerPerfectCore_eq_map_of_le h.Φ h.ker_le hYT h.range_eq α hα
  have hker := ker_realize_le_center h2
  have hreal : (perfectCore (fixAll α)).map (realize h2) = relLevi K {1} := by
    rw [show fixAll α = fixAll α' from LinearPilot.fixAll_comp_of_surjective α' hg,
      ← LinearPilot.perfectCore_range_inf_centralizer (realize h2) hker α' hα',
      E6GraphLevi.range_realize h2]
    exact perfectCore_inf_centralizer_relLeviTorus_X hA3 (by decide) (by decide)
  rw [hpiece]
  refine pieceDichotomy_map_of_isSimpleGroup (CFSG.Quasithin.perfectCore_perfect _) h.Φ
    (realize h2) hker ?_
  rw [hreal]
  exact isSimpleGroup_relLevi_one hK4

end Piece

section Seitz

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (SUmNotOddLieInputAt)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem false_of_field_X_of_swap_Y (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKc : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc)
    {Y : Subgroup G} (hY : Y = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htY : t ∈ centralizer (Y : Set G)) {DY : Subgroup G}
    (hDYe : DY = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {KY : Subgroup (centralizer (Y : Set G) ⧸ oddCore (centralizer (Y : Set G)))}
    (hKY : IsComponent KY)
    (hDKY : (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))) ≤
      KY ⊔ KY.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom)
    (hneY : KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom ≠ KY)
    (hcommY : ⁅KY, KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom⁆ = ⊥)
    (hφY : Nonempty (KY ≃* (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))))) :
    False := by
  have hf : 1 ≤ f := by omega
  have : CharP K 2 := charP_two_of_card hf hK
  have := finite_of_card hK
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨-, hAo, -, hσk⟩ := unitsRange_facts hf2 hk hσ
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  set A : Subgroup Kˣ := (Units.map (algebraMap k K).toMonoidHom).range with hAdef
  obtain ⟨hXp⟩ := nonempty_fieldCoverParamX_2E6_of_leafInputs hGLS hXodd hMinn hMcomp hset hf2 hk
    hK hσ e htC ht hX htX hDe hKc hDKc hKt
  have hTX : X = modelToG e (neighbourTorus K A .X) := by
    rw [hX, (neighbourTorus_X_Y (algebraMap k K)).1]; rfl
  obtain ⟨hYc⟩ := nonempty_swapCover_2E6_Y hset hf2 hk hK hσ e htC ht hY htY hDYe hKY hDKY hneY
    hcommY hφY
  have hTY : Y = modelToG e (neighbourTorus K A .Y) := by
    rw [hY, (neighbourTorus_X_Y (algebraMap k K)).2]; rfl
  have hYc' : SwapCover t (modelToG e (neighbourTorus K A .Y)) (modelToG e (omegaMinusLevi σ))
      (neighbourCore e A .Y) :=
    hYc.cast hTY (by rw [hDYe]; rfl) (by rw [neighbourCore_def, ← hTY])
  subst hTX
  have hdich := pieceDichotomy_of_fieldCoverParamX hf2 hk hK hσ e hXp
  exact false_of_swapCover_of_pieceDichotomy e A hAo (algebraMap k K) hσk hq htC htt
    (N := .Y) (by decide) (modelToG_mono e (relRankOne_le_omegaMinusLevi σ (by decide))) hYc'
    hdich

end Seitz

end CFSG.SeitzReduction.TwistedE6Pilot

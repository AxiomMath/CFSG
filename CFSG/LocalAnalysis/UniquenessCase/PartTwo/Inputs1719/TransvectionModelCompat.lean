module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduce
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeSetting
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeThree barM blockPL blockV)
open CFSG.ComponentClassification.OutcomeLocal (commutatorSpace zmod2_eq_zero_or_one)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator (le_normalizer_of_isWeakSBlock)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective
  ker_barMHomSub subgroupOf_barM_eq_map)
open CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.HardMathSupport.Curtis.Coordinator.PLType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open Subgroup
open scoped commutatorElement

attribute [local instance] CFSG.LieType.Chevalley.commutator_subgroupOf_normal

private noncomputable def commutatorConj {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (t : ↥H) :
    MulAut ↥⁅H, H⁆ :=
  MulAut.congr (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self H))
    (MulAut.conjNormal (G := ↥H) (H := (⁅H, H⁆).subgroupOf H) t)

private theorem commutatorConj_apply {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (t : ↥H) (y : ↥⁅H, H⁆) :
    ((commutatorConj H t) y : LinearMap.GeneralLinearGroup (ZMod 2) W) =
      (t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
        (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
        (t : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ := by
  rw [commutatorConj, MulAut.congr_apply]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [MulAut.conjNormal_apply]
  change ((t : ↥H) : LinearMap.GeneralLinearGroup (ZMod 2) W) *
      ((((Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self H)).symm y) : ↥H) :
        LinearMap.GeneralLinearGroup (ZMod 2) W) *
      ((t : ↥H) : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ =
    (t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
      (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
      (t : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹
  rw [Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]

private theorem not_inner_of_irreducible {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) W} (hmodel : TransvectionModel H t)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ h ∈ H, ∀ w ∈ P, (h : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤) :
    commutatorConj H ⟨t, hmodel.1⟩ ∉
      (MulAut.conj : ↥⁅H, H⁆ →* MulAut ↥⁅H, H⁆).range := by
  intro hinner
  obtain ⟨x, hx⟩ := hinner
  have ht2 : t * t = 1 := isF2Transvection_mul_self hmodel.2.1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hval : ∀ y : ↥⁅H, H⁆, (commutatorConj H ⟨t, hmodel.1⟩ y :
      LinearMap.GeneralLinearGroup (ZMod 2) W) =
      t * (y : LinearMap.GeneralLinearGroup (ZMod 2) W) * t⁻¹ :=
    fun y => commutatorConj_apply H ⟨t, hmodel.1⟩ y
  have hconjval : ∀ y : ↥⁅H, H⁆,
      (MulAut.conj x y : LinearMap.GeneralLinearGroup (ZMod 2) W) =
        t * (y : LinearMap.GeneralLinearGroup (ZMod 2) W) * t⁻¹ := by
    intro y
    rw [hx]
    exact hval y
  have hxeq : (x : LinearMap.GeneralLinearGroup (ZMod 2) W) = t *
      (x : LinearMap.GeneralLinearGroup (ZMod 2) W) * t⁻¹ := by
    have h := hconjval x
    rw [MulAut.conj_apply] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel, mul_one] using h
  have hxt : (x : LinearMap.GeneralLinearGroup (ZMod 2) W) * t =
      t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by
    calc (x : LinearMap.GeneralLinearGroup (ZMod 2) W) * t =
        (t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W) * t⁻¹) * t := by
          nth_rewrite 1 [hxeq]
          rfl
      _ = t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by group
  set c : LinearMap.GeneralLinearGroup (ZMod 2) W :=
    (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t with hc
  have hcA : ∀ y ∈ ⁅H, H⁆, c * y * c⁻¹ = y := by
    intro y hy
    have h := hconjval ⟨y, hy⟩
    rw [MulAut.conj_apply] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc c * y * c⁻¹ = (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t * y * t⁻¹ *
          (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by
          rw [hc]
          have hinv : ((x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t)⁻¹ =
              t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by
            rw [mul_inv_rev, inv_inv, htinv]
          rw [hinv, htinv]
          group
      _ = (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ *
          ((x : LinearMap.GeneralLinearGroup (ZMod 2) W) * y *
            (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹) *
          (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by
          rw [h]
          group
      _ = y := by group
  have hcomm_of_conj : ∀ y : LinearMap.GeneralLinearGroup (ZMod 2) W,
      c * y * c⁻¹ = y → c * y = y * c := by
    intro y hy
    have := congrArg (fun z : LinearMap.GeneralLinearGroup (ZMod 2) W => z * c) hy
    simpa [mul_assoc] using this
  have hct : c * t = t * c := by
    have hxinv : (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t =
        t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ := by
      have this := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) W => g⁻¹) hxt
      rw [mul_inv_rev, mul_inv_rev] at this
      rw [htinv] at this
      exact this.symm
    calc c * t = (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t * t := by rw [hc]
      _ = (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ := by
          rw [mul_assoc, ht2, mul_one]
      _ = t * (t * (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹) := by
          rw [← mul_assoc, ht2, one_mul]
      _ = t * ((x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t) := by rw [hxinv]
      _ = t * c := by rw [hc]
  obtain ⟨a, haH, haA, hpa⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hmodel.2.2.2.1)
  have ha_t : a * t ∈ ⁅H, H⁆ := by
    rcases hpa t hmodel.1 with h | h
    · exact h
    · exact absurd h hmodel.2.2.1
  have hca : c * a = a * c := by
    have h1 : c * (a * t) = (a * t) * c := hcomm_of_conj (a * t) (hcA (a * t) ha_t)
    have h2 : a * t * t = a := by rw [mul_assoc, ht2, mul_one]
    calc c * a = c * (a * t * t) := by rw [h2]
      _ = (c * (a * t)) * t := by group
      _ = ((a * t) * c) * t := by rw [h1]
      _ = (a * t) * (c * t) := by group
      _ = (a * t) * (t * c) := by rw [hct]
      _ = a * (t * (t * c)) := by group
      _ = a * ((t * t) * c) := by rw [mul_assoc]
      _ = a * c := by rw [ht2, one_mul]
  have hca_inv : c * (a : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ =
      a⁻¹ * c := by
    have hcomm : Commute c a := hca
    exact hcomm.inv_right.eq
  have hcentral : ∀ h ∈ H, c * (h : LinearMap.GeneralLinearGroup (ZMod 2) W) =
      (h : LinearMap.GeneralLinearGroup (ZMod 2) W) * c := by
    intro h hh
    rcases hpa h hh with hab | hbA
    · have h1 : c * (a * h) = (a * h) * c := hcomm_of_conj (a * h) (hcA (a * h) hab)
      have hb_eq : (h : LinearMap.GeneralLinearGroup (ZMod 2) W) =
          a⁻¹ * (a * h) := by group
      rw [hb_eq]
      calc c * (a⁻¹ * (a * h)) = (c * a⁻¹) * (a * h) := by group
        _ = (a⁻¹ * c) * (a * h) := by rw [hca_inv]
        _ = a⁻¹ * (c * (a * h)) := by group
        _ = a⁻¹ * ((a * h) * c) := by rw [h1]
        _ = (a⁻¹ * (a * h)) * c := by group
    · exact hcomm_of_conj h (hcA h hbA)
  have hlin : ∀ h ∈ H, ∀ v : W,
      (c : W →ₗ[ZMod 2] W) ((h : W →ₗ[ZMod 2] W) v) =
        (h : W →ₗ[ZMod 2] W) ((c : W →ₗ[ZMod 2] W) v) := by
    intro h hh v
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) W =>
      (g : W →ₗ[ZMod 2] W) v) (hcentral h hh)
    simpa only [← Units.val_mul, ← Module.End.mul_apply] using this
  have hne : commutatorSpace t ≠ ⊥ := by
    have hrank := hmodel.2.1.2
    intro hbot
    rw [hbot, finrank_bot] at hrank
    exact zero_ne_one hrank
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : commutatorSpace t = Submodule.span (ZMod 2) {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hmodel.2.1.2 hw hw0
  have hcw_mem : (c : W →ₗ[ZMod 2] W) w ∈ commutatorSpace t := by
    obtain ⟨u, rfl⟩ := hw
    change ∃ z, ((LinearMap.id : W →ₗ[ZMod 2] W) + (t : W →ₗ[ZMod 2] W)) z =
      (c : W →ₗ[ZMod 2] W) (((LinearMap.id : W →ₗ[ZMod 2] W) +
        (t : W →ₗ[ZMod 2] W)) u)
    refine ⟨(c : W →ₗ[ZMod 2] W) u, ?_⟩
    rw [show ((LinearMap.id : W →ₗ[ZMod 2] W) + (t : W →ₗ[ZMod 2] W)) u =
      u + (t : W →ₗ[ZMod 2] W) u from rfl, map_add, hlin t hmodel.1 u]
    rfl
  have hcw0 : (c : W →ₗ[ZMod 2] W) w ≠ 0 := by
    intro h0
    have hcc : ((c⁻¹ * c : LinearMap.GeneralLinearGroup (ZMod 2) W) :
        W →ₗ[ZMod 2] W) w = w := by
      rw [inv_mul_cancel]
      rfl
    rw [Units.val_mul, Module.End.mul_apply, h0, map_zero] at hcc
    exact hw0 hcc.symm
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcw_mem)
  have hk1 : k = 1 := by
    rcases zmod2_eq_zero_or_one k with h0 | h1
    · exfalso
      apply hcw0
      rw [← hk, h0, zero_smul]
    · exact h1
  have hcw : (c : W →ₗ[ZMod 2] W) w = w := by rw [← hk, hk1, one_smul]
  set T : W →ₗ[ZMod 2] W := (c : W →ₗ[ZMod 2] W) - LinearMap.id with hT
  have hTfix : T w = 0 := by
    rw [hT, LinearMap.sub_apply, LinearMap.id_apply, hcw, sub_self]
  have hker_ne : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hwker : w ∈ LinearMap.ker T := LinearMap.mem_ker.mpr hTfix
    rw [hbot] at hwker
    exact hw0 (by simpa using hwker)
  have hinv : ∀ h ∈ H, ∀ v ∈ LinearMap.ker T,
      (h : W →ₗ[ZMod 2] W) v ∈ LinearMap.ker T := by
    intro h hh v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcomp : (c : W →ₗ[ZMod 2] W) ((h : W →ₗ[ZMod 2] W) v) =
        (h : W →ₗ[ZMod 2] W) ((c : W →ₗ[ZMod 2] W) v) := hlin h hh v
    rw [hT, LinearMap.sub_apply, LinearMap.id_apply] at hv ⊢
    rw [hcomp, ← map_sub, hv, map_zero]
  rcases hirr (LinearMap.ker T) hinv with hbot | htop
  · exact hker_ne hbot
  · have hT0 : T = 0 := LinearMap.ker_eq_top.mp htop
    have hcsub : (c : W →ₗ[ZMod 2] W) - LinearMap.id = 0 := by simpa [hT] using hT0
    have hc_eq : (c : W →ₗ[ZMod 2] W) = LinearMap.id := sub_eq_zero.mp hcsub
    have hc1 : c = 1 := by
      apply Units.ext
      change (c : W →ₗ[ZMod 2] W) = LinearMap.id
      exact hc_eq
    have hxinv_t : (x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t = 1 := by
      rw [← hc, hc1]
    have htx : t = (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := by
      calc t = (x : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            ((x : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ * t) := by group
        _ = (x : LinearMap.GeneralLinearGroup (ZMod 2) W) * 1 := by rw [hxinv_t]
        _ = (x : LinearMap.GeneralLinearGroup (ZMod 2) W) := mul_one _
    exact hmodel.2.2.1 (htx ▸ x.2)

theorem exists_transvectionModel_compat
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (h3 : NineThreeThree M S L)
    (hZ : Subgroup.center ↥(barM M L) = ⊥) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (_ : FiniteDimensional (ZMod 2) W)
      (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
      (t : LinearMap.GeneralLinearGroup (ZMod 2) W)
      (e : ↥(barM M L) ≃* ↥⁅H, H⁆),
      TransvectionModel H t ∧
      (∀ P : Submodule (ZMod 2) W,
        (∀ h ∈ H, ∀ w ∈ P, (h : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤) ∧
      ((blockPL M S L).subgroupOf (barM M L)).map e.toMonoidHom =
        (Subgroup.centralizer ({t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))).subgroupOf
          ⁅H, H⁆ := by
  obtain ⟨s, hsS, hgen, hsn, hZ2⟩ := h3.2.2.2
  have hset := TransvIrr.setting_of hK hA hL hsS hgen hsn hZ2
  have hSL := le_normalizer_of_isWeakSBlock hK hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨W, _, _, _, _, ρ, hirr, htr, hgenρ, hM, hperf, hL1, hs, hC⟩ :=
    TransvIrr.exists_rep_of_setting hset hV2 hsn
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hK hA hL hTM hMT hCT hx hxn)
  have : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr hset.normL
  obtain ⟨hLeq, hmodel⟩ := transvectionModel_of_rep ρ (L.subgroupOf (L ⊔ S))
    ⟨s, hset.mem⟩ hirr htr hgenρ hM hperf hL1 hs
  have rep : PLRep M S L s ρ := ⟨hA, hL, hSL, hZ, hC, hL1, hsS, hgen, htr⟩
  let t : LinearMap.GeneralLinearGroup (ZMod 2) W := ρ ⟨s, hset.mem⟩
  let P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
    (L.subgroupOf (L ⊔ S)).map ρ
  let A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W) := ⁅ρ.range, ρ.range⁆
  have hPA : P = A := hLeq
  let K : Subgroup G := normalizer (S : Set G) ⊓ L
  have hKle : K ≤ L := inf_le_right
  have hker : (barMHomSub rep.hL.le).ker = (restrictRho ρ L le_sup_left).ker :=
    ker_barMHomSub_eq_ker_restrictRho rep le_rfl
  let ebar : ↥(barM M L) ≃* ↥P :=
    (QuotientGroup.quotientKerEquivOfSurjective (barMHomSub rep.hL.le)
      (barMHomSub_surjective _)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective (restrictRho ρ L le_sup_left)
          (restrictRho_surjective ρ L le_sup_left)))
  have hebar_apply : ∀ l : ↥L, ebar (barMHomSub rep.hL.le l) =
      restrictRho ρ L le_sup_left l := by
    intro l
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (barMHomSub rep.hL.le)
        (barMHomSub_surjective _)).symm (barMHomSub rep.hL.le l) =
        (QuotientGroup.mk l : ↥L ⧸ (barMHomSub rep.hL.le).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    dsimp only [ebar]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hcomp : ebar.toMonoidHom.comp (barMHomSub rep.hL.le) =
      restrictRho ρ L le_sup_left := MonoidHom.ext hebar_apply
  have hblock : (blockPL M S L).subgroupOf (barM M L) =
      (K.subgroupOf L).map (barMHomSub rep.hL.le) :=
    subgroupOf_barM_eq_map (X := M) (L := L) (K := K) rep.hL.le hKle
  have hblockE : ((blockPL M S L).subgroupOf (barM M L)).map ebar.toMonoidHom =
      ((K.subgroupOf (L ⊔ S)).map ρ).subgroupOf P := by
    rw [hblock, Subgroup.map_map, hcomp]
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      have hkK : (k : G) ∈ K := by
        change k ∈ K.subgroupOf L at hk
        simpa only [Subgroup.mem_subgroupOf] using hk
      refine ⟨⟨(k : G), Subgroup.mem_sup_left k.2⟩, ?_, ?_⟩
      · change (k : G) ∈ K
        exact hkK
      · rfl
    · intro hx
      change x ∈ ((K.subgroupOf (L ⊔ S)).map ρ).subgroupOf P at hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨m, hm, hmx⟩ := hx
      change m ∈ K.subgroupOf (L ⊔ S) at hm
      have hmK : (m : G) ∈ K := by
        simpa only [Subgroup.mem_subgroupOf] using hm
      refine ⟨⟨(m : G), hKle hmK⟩, ?_, ?_⟩
      · change (m : G) ∈ K
        exact hmK
      · apply Subtype.ext
        have hres : ((restrictRho ρ L le_sup_left) ⟨(m : G), hKle hmK⟩ :
            LinearMap.GeneralLinearGroup (ZMod 2) W) = ρ m := by
          change (ρ ⟨(m : G), Subgroup.mem_sup_left (hKle hmK)⟩ :
            LinearMap.GeneralLinearGroup (ZMod 2) W) = ρ m
          congr 1
        rw [hres]
        exact hmx
  have hpt : (⟨s, mem_sup_right rep.hsS⟩ : ↥(L ⊔ S)) = ⟨s, hset.mem⟩ :=
    Subtype.ext rfl
  have hPmap : ((K.subgroupOf (L ⊔ S)).map ρ) =
      P ⊓ Subgroup.centralizer
        ({t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) := by
    have h := map_normalizer_inf_eq rep
    rw [hpt] at h
    simpa [t, P] using h
  have hblockCongr : ((blockPL M S L).subgroupOf (barM M L)).map
      (ebar.trans (MulEquiv.subgroupCongr hPA)).toMonoidHom =
      (Subgroup.centralizer ({t} :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) W))).subgroupOf A := by
    have hmap_trans : ((blockPL M S L).subgroupOf (barM M L)).map
        (ebar.trans (MulEquiv.subgroupCongr hPA)).toMonoidHom =
        (((blockPL M S L).subgroupOf (barM M L)).map ebar.toMonoidHom).map
          (MulEquiv.subgroupCongr hPA).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hmap_trans, hblockE, hPmap]
    have hgen : ∀ {Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)} (hQ : Q ≤ P),
        (Q.subgroupOf P).map (MulEquiv.subgroupCongr hPA).toMonoidHom = Q.subgroupOf A := by
      intro Q hQ
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        change q ∈ Q.subgroupOf P at hq
        have hq' : (q : LinearMap.GeneralLinearGroup (ZMod 2) W) ∈ Q := by
          simpa only [Subgroup.mem_subgroupOf] using hq
        change ((MulEquiv.subgroupCongr hPA) q :
          LinearMap.GeneralLinearGroup (ZMod 2) W) ∈ Q
        simpa only [MulEquiv.subgroupCongr_apply] using hq'
      · intro hx
        change x ∈ Q.subgroupOf A at hx
        have hx' : (x : LinearMap.GeneralLinearGroup (ZMod 2) W) ∈ Q := by
          simpa only [Subgroup.mem_subgroupOf] using hx
        refine ⟨⟨(x : LinearMap.GeneralLinearGroup (ZMod 2) W), hQ hx'⟩, ?_, ?_⟩
        · change (x : LinearMap.GeneralLinearGroup (ZMod 2) W) ∈ Q
          exact hx'
        · apply Subtype.ext
          exact MulEquiv.subgroupCongr_apply hPA
            ⟨(x : LinearMap.GeneralLinearGroup (ZMod 2) W), hQ hx'⟩
    rw [hgen (Q := P ⊓ Subgroup.centralizer
      ({t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) inf_le_left]
    rw [hPA]
    exact Subgroup.inf_subgroupOf_left
      (H := Subgroup.centralizer ({t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)))
      (K := A)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ.range, t,
    ebar.trans (MulEquiv.subgroupCongr hPA), hmodel, ?_, ?_⟩
  · intro Q hQ
    exact hirr Q (fun m w hw => hQ (ρ m) ⟨m, rfl⟩ w hw)
  · exact hblockCongr

theorem isCentralizerOfTransvectionIn_of_model {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) W} (hmodel : TransvectionModel H t)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ h ∈ H, ∀ w ∈ P, (h : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤)
    {X : Type} [Group X] {m : ℕ} (e : X ≃* ↥⁅H, H⁆) (Y : Subgroup X)
    (hY : Y.map e.toMonoidHom =
      (Subgroup.centralizer ({t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))).subgroupOf
        ⁅H, H⁆)
    (hcard : Nat.card Y = if m = 3 then 720 else 1451520) :
    IsCentralizerOfTransvectionIn X m Y := by
  have hτ2 : commutatorConj H ⟨t, hmodel.1⟩ * commutatorConj H ⟨t, hmodel.1⟩ = 1 := by
    have ht2H : (⟨t, hmodel.1⟩ : ↥H) * ⟨t, hmodel.1⟩ = 1 :=
      Subtype.ext (isF2Transvection_mul_self hmodel.2.1)
    have h : MulAut.conjNormal (G := ↥H) (H := (⁅H, H⁆).subgroupOf H)
          (⟨t, hmodel.1⟩ : ↥H) *
        MulAut.conjNormal (G := ↥H) (H := (⁅H, H⁆).subgroupOf H)
          (⟨t, hmodel.1⟩ : ↥H) = 1 := by
      rw [← map_mul, ht2H, map_one]
    rw [commutatorConj, ← map_mul, h, map_one]
  have hτout : commutatorConj H ⟨t, hmodel.1⟩ ∉
      (MulAut.conj : ↥⁅H, H⁆ →* MulAut ↥⁅H, H⁆).range :=
    not_inner_of_irreducible hmodel hirr
  have hfix : ∀ y : ↥⁅H, H⁆,
      y ∈ (Subgroup.centralizer ({t} : Set
        (LinearMap.GeneralLinearGroup (ZMod 2) W))).subgroupOf ⁅H, H⁆ ↔
        commutatorConj H ⟨t, hmodel.1⟩ y = y := by
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      apply Subtype.ext
      rw [commutatorConj_apply]
      calc (t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ =
          (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹ := by rw [hy]
        _ = (y : LinearMap.GeneralLinearGroup (ZMod 2) W) := by group
    · intro hy
      have hval := congrArg (fun z : ↥⁅H, H⁆ =>
        (z : LinearMap.GeneralLinearGroup (ZMod 2) W)) hy
      simp only [commutatorConj_apply] at hval
      calc (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W) =
          ((t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (y : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W)⁻¹) *
            (t : LinearMap.GeneralLinearGroup (ZMod 2) W) := by rw [hval]
        _ = (t : LinearMap.GeneralLinearGroup (ZMod 2) W) *
            (y : LinearMap.GeneralLinearGroup (ZMod 2) W) := by group
  refine ⟨MulAut.congr e.symm (commutatorConj H ⟨t, hmodel.1⟩), ?_, fun hin => hτout
    ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e.symm _).mp hin), fun y => ?_, hcard⟩
  · rw [← map_mul, hτ2, map_one]
  · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.symm_apply_eq, ← hfix, ← hY, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end

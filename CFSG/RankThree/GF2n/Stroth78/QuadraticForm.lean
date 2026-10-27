module

public import CFSG.RankThree.GF2n.Stroth78.Basic
public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.LargeExtraspecial.S3Fourteen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.CGT.T75H CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
  CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem isExtraspecialPGroup_F (S : Setting z E F) : CFSG.IsExtraspecialPGroup 2 ↥F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nat.card (Subgroup.center ↥F) = 2 := by
    calc
      Nat.card (Subgroup.center ↥F) =
          Nat.card ((Subgroup.center ↥F).map F.subtype) :=
        (Subgroup.card_map_of_injective F.subtype_injective).symm
      _ = Nat.card (centerIn F) := by rw [centerIn_eq_map_center F]
      _ = Nat.card (Subgroup.zpowers z) := by rw [F_centerIn_eq S]
      _ = 2 := by rw [Nat.card_zpowers, S.hyp.orderOf_z]
  have hcomm : ∀ x y : ↥F, ⁅x, y⁆ ∈ Subgroup.center ↥F := by
    intro x y
    have hmem : (⁅(x : G), (y : G)⁆ : G) ∈ (Subgroup.center F).map F.subtype := by
      rw [← S.hyp.extraspecial.2.1]
      exact Subgroup.commutator_mem_commutator x.2 y.2
    obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hmem
    have hx : ⁅x, y⁆ = c := Subtype.ext (by
      simpa [commutatorElement_def] using hc_eq.symm)
    rw [hx]
    exact hc
  have hcenter_two : ∀ c : ↥F, c ∈ Subgroup.center ↥F → c ^ 2 = 1 := by
    intro c hc
    have h := pow_card_eq_one' (G := Subgroup.center ↥F) (x := ⟨c, hc⟩)
    rw [hZ] at h
    simpa using congrArg Subtype.val h
  have hcomm_le : _root_.commutator ↥F ≤ Subgroup.center ↥F := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  have hpow : ∀ x : ↥F, x ^ 2 ∈ Subgroup.center ↥F :=
    CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed.sq_mem_center hcomm_le hcenter_two
  have hnc : ∃ x y : ↥F, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hcommut : _root_.commutator ↥F = ⊥ :=
      (commutator_eq_bot_iff (G := ↥F)).mpr (isMulCommutative_iff.mpr h)
    have hmap : (_root_.commutator ↥F).map F.subtype = ⁅F, F⁆ :=
      Subgroup.map_subtype_commutator F
    rw [hcommut, Subgroup.map_bot] at hmap
    have hcard : Nat.card (⁅F, F⁆ : Subgroup G) = 1 := by
      rw [← hmap]
      simp
    rw [S.hyp.extraspecial.2.2] at hcard
    norm_num at hcard
  exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_card_center
    S.hyp.extraspecial.1 hZ hcomm hpow hnc

@[instance_reducible] noncomputable def modAbF (S : Setting z E F) :
    Module (ZMod 2) (Additive (Abelianization F)) :=
  CFSG.GroupTheory.extraspecialQuotientModule (isExtraspecialPGroup_F S)

noncomputable def fq (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    QuadraticForm (ZMod 2) (Additive (Abelianization F)) :=
  extraspecialQuadForm (isExtraspecialPGroup_F S)

private theorem fq_eq_zero_iff (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (x : ↥F) :
    fq S (Additive.ofMul (Abelianization.of x)) = 0 ↔ x ^ 2 = 1 := by
  rw [fq, extraspecialQuadForm_apply]
  by_cases h : x ^ 2 = 1
  · simp [h]
  · simp [h]

private theorem fq_polar_eq_zero_iff (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (x y : ↥F) :
    QuadraticMap.polar (fq S) (Additive.ofMul (Abelianization.of x))
        (Additive.ofMul (Abelianization.of y)) = 0 ↔ x * y = y * x :=
  polar_extraspecialQuadForm_eq_zero_iff (isExtraspecialPGroup_F S) x y

private theorem fq_nondegenerate (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    (fq S).polarBilin.Nondegenerate :=
  extraspecialQuadForm_nondegenerate (isExtraspecialPGroup_F S)

private noncomputable def toQbar (S : Setting z E F) : ↥F →* QbarOf S :=
  (QuotientGroup.mk' ((ZQ z).subgroupOf (Q z))).comp (Subgroup.inclusion (F_le_Q S))

private theorem ZQ_inf_F_eq (S : Setting z E F) : ZQ z ⊓ F = Subgroup.zpowers z := by
  have hzF : z ∈ F := Subgroup.commutator_le_self F S.hyp.mem_derived
  have hcommEZ : ∀ a ∈ E, ∀ w ∈ Subgroup.zpowers z, a * w = w * a := by
    intro a ha w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hk]
    exact ((S.hyp.commute a ha z hzF).zpow_right k).eq
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxZ, hxF⟩ := hx
    rw [ZQ_eq S] at hxZ
    obtain ⟨e, he, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_comm hcommEZ hxZ
    have hwF : w ∈ F := Subgroup.zpowers_le.mpr hzF hw
    have heF : e ∈ F := by
      have h : e = (e * w) * w⁻¹ := by group
      rw [h]
      exact mul_mem hxF (inv_mem hwF)
    have he1 : e = 1 := by
      have h : e ∈ E ⊓ F := ⟨he, heF⟩
      rwa [S.hyp.inf_eq_bot, Subgroup.mem_bot] at h
    simpa [he1] using hw
  · intro x hx
    exact ⟨by rw [ZQ_eq S]; exact Subgroup.mem_sup_right hx,
      Subgroup.zpowers_le.mpr hzF hx⟩

private theorem mem_ZQ_iff_mem_zpowers_of_mem_F (S : Setting z E F) {x : G} (hx : x ∈ F) :
    x ∈ ZQ z ↔ x ∈ Subgroup.zpowers z := by
  constructor
  · intro hxZ
    have h : x ∈ ZQ z ⊓ F := ⟨hxZ, hx⟩
    rwa [ZQ_inf_F_eq S] at h
  · intro hx
    exact ((ZQ_inf_F_eq S).ge hx).1

private theorem toQbar_eq_one_iff (S : Setting z E F) (f : ↥F) :
    toQbar S f = 1 ↔ f ∈ _root_.commutator ↥F := by
  change QuotientGroup.mk (Subgroup.inclusion (F_le_Q S) f) = 1 ↔
    f ∈ _root_.commutator ↥F
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion, mem_ZQ_iff_mem_zpowers_of_mem_F S f.2, ← F_deriv_eq_zpowers S,
    ← Subgroup.map_subtype_commutator F]
  exact Subgroup.mem_map_iff_mem F.subtype_injective

private noncomputable def abToQbar (S : Setting z E F) :
    Abelianization F →* QbarOf S :=
  QuotientGroup.lift (_root_.commutator ↥F) (toQbar S) (by
    intro f hf
    rw [MonoidHom.mem_ker, toQbar_eq_one_iff]
    exact hf)

private theorem abToQbar_injective (S : Setting z E F) :
    Function.Injective (abToQbar S) := by
  change Function.Injective
    (QuotientGroup.lift (_root_.commutator ↥F) (toQbar S) _)
  rw [QuotientGroup.injective_lift_iff]
  ext f
  rw [MonoidHom.mem_ker, toQbar_eq_one_iff]

private theorem mk_mul_eq_mk_of_mem_E_of_mem_F (S : Setting z E F) {e f : G}
    (he : e ∈ E) (hf : f ∈ F) :
    (QuotientGroup.mk (⟨e * f, by
        rw [Q_eq_sup S]
        exact Subgroup.mul_mem_sup he hf⟩ : ↥(Q z)) : QbarOf S) =
      QuotientGroup.mk (⟨f, F_le_Q S hf⟩ : ↥(Q z)) := by
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  have hdiv : ((⟨e * f, by
        rw [Q_eq_sup S]
        exact Subgroup.mul_mem_sup he hf⟩ : ↥(Q z)) /
      (⟨f, F_le_Q S hf⟩ : ↥(Q z)) : ↥(Q z)) = ⟨e, E_le_Q S he⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_div, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      div_eq_mul_inv]
    group
  rw [hdiv]
  exact E_le_ZQ S he

private theorem abToQbar_surjective (S : Setting z E F) :
    Function.Surjective (abToQbar S) := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) x
  have hq : (q : G) ∈ E ⊔ F := by
    rw [← Q_eq_sup S]
    exact q.2
  obtain ⟨e, he, f, hf, hqef⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hq
  refine ⟨Abelianization.of ⟨f, hf⟩, ?_⟩
  have hq' : q = ⟨e * f, by
      rw [Q_eq_sup S]
      exact Subgroup.mul_mem_sup he hf⟩ := Subtype.ext hqef
  rw [hq']
  change QuotientGroup.mk (⟨f, F_le_Q S hf⟩ : ↥(Q z)) =
    QuotientGroup.mk (⟨e * f, by
      rw [Q_eq_sup S]
      exact Subgroup.mul_mem_sup he hf⟩ : ↥(Q z))
  exact (mk_mul_eq_mk_of_mem_E_of_mem_F S he hf).symm

noncomputable def QbarEquivF (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    Additive (Abelianization F) ≃ₗ[ZMod 2] Additive (QbarOf S) :=
  LinearEquiv.ofBijective
    ((MonoidHom.toAdditive (abToQbar S)).toZModLinearMap 2)
    (show Function.Bijective
        ((MonoidHom.toAdditive (abToQbar S)).toZModLinearMap 2) from
      ⟨fun x y h => by
        apply Additive.toMul.injective
        apply abToQbar_injective S
        have h' := congrArg Additive.toMul h
        change abToQbar S x.toMul = abToQbar S y.toMul at h'
        exact h',
        fun y => by
          obtain ⟨a, ha⟩ := abToQbar_surjective S y.toMul
          refine ⟨Additive.ofMul a, ?_⟩
          change Additive.ofMul (abToQbar S a) = y
          rw [ha]
          rfl⟩)

private theorem QbarEquivF_apply (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))]
    (v : Additive (Abelianization F)) :
    QbarEquivF S v = Additive.ofMul (abToQbar S v.toMul) := by
  change (LinearEquiv.ofBijective
    ((MonoidHom.toAdditive (abToQbar S)).toZModLinearMap 2) _) v =
    Additive.ofMul (abToQbar S v.toMul)
  rw [LinearEquiv.ofBijective_apply]
  rfl

private theorem QbarEquivF_of (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (f : ↥F) :
    QbarEquivF S (Additive.ofMul (Abelianization.of f)) =
      (QuotientGroup.mk (⟨(f : G), F_le_Q S f.2⟩ : ↥(Q z)) : QbarOf S) := by
  rw [QbarEquivF_apply]
  change Additive.ofMul (QuotientGroup.mk (⟨(f : G), F_le_Q S f.2⟩ : ↥(Q z))) =
    (QuotientGroup.mk (⟨(f : G), F_le_Q S f.2⟩ : ↥(Q z)) : QbarOf S)
  rfl

private theorem mk_eq_QbarEquivF_of_mul (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] {e f : G}
    (he : e ∈ E) (hf : f ∈ F) (x : ↥(Q z)) (hx : (x : G) = e * f) :
    (QuotientGroup.mk x : QbarOf S) =
      QbarEquivF S (Additive.ofMul (Abelianization.of (⟨f, hf⟩ : ↥F))) := by
  have hx' : x = ⟨e * f, by
      rw [Q_eq_sup S]
      exact Subgroup.mul_mem_sup he hf⟩ := Subtype.ext hx
  rw [hx', QbarEquivF_of]
  exact mk_mul_eq_mk_of_mem_E_of_mem_F S he hf

noncomputable def q (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    QuadraticForm (ZMod 2) (Additive (QbarOf S)) :=
  (fq S).comp (QbarEquivF S).symm.toLinearMap

theorem q_apply_of_mem_F (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] {f : F} :
    q S (QbarEquivF S (Additive.ofMul (Abelianization.of f))) =
      fq S (Additive.ofMul (Abelianization.of f)) := by
  rw [q, QuadraticMap.comp_apply]
  simp

theorem q_eq_zero_iff (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (x : ↥(Q z)) :
    q S (QuotientGroup.mk x) = 0 ↔ (x : G) ^ 2 = 1 := by
  have hq : (x : G) ∈ E ⊔ F := by
    rw [← Q_eq_sup S]
    exact x.2
  obtain ⟨e, he, f, hf, hxef⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hq
  have hmk : (QuotientGroup.mk x : QbarOf S) =
      QbarEquivF S (Additive.ofMul (Abelianization.of (⟨f, hf⟩ : ↥F))) :=
    mk_eq_QbarEquivF_of_mul S he hf x hxef
  have hqval : q S (QuotientGroup.mk x) =
      fq S (Additive.ofMul (Abelianization.of (⟨f, hf⟩ : ↥F))) := by
    calc
      q S (QuotientGroup.mk x) =
          q S (QbarEquivF S (Additive.ofMul (Abelianization.of (⟨f, hf⟩ : ↥F)))) := by
        rw [hmk]
      _ = fq S (Additive.ofMul (Abelianization.of (⟨f, hf⟩ : ↥F))) :=
        q_apply_of_mem_F S
  rw [hqval, fq_eq_zero_iff]
  have hxG : (x : G) = e * f := hxef
  have he2 : e ^ 2 = 1 := S.hyp.elemAbelian.2 e he
  have hef : e * f = f * e := (S.hyp.commute e he f hf).eq
  have hsq : (x : G) ^ 2 = f ^ 2 := by
    rw [hxG]
    calc
      (e * f) ^ 2 = f ^ 2 := by
        rw [pow_two, pow_two]
        calc
          (e * f) * (e * f) = e * (f * e) * f := by group
          _ = e * (e * f) * f := by rw [hef]
          _ = (e * e) * (f * f) := by group
          _ = f * f := by
            rw [show e * e = 1 by simpa [pow_two] using he2, one_mul]
      _ = f ^ 2 := rfl
  have hpow_iff : ((⟨f, hf⟩ : ↥F) ^ 2 = 1) ↔ f ^ 2 = 1 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hsq, hpow_iff]

private theorem polar_q_apply (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (v w : Additive (QbarOf S)) :
    QuadraticMap.polar (q S) v w =
      QuadraticMap.polar (fq S) ((QbarEquivF S).symm v) ((QbarEquivF S).symm w) := by
  simp only [q, QuadraticMap.comp_apply, QuadraticMap.polar, LinearEquiv.coe_toLinearMap]
  rw [map_add]

theorem polar_q_eq_zero_iff (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (x y : ↥(Q z)) :
    QuadraticMap.polar (q S) (QuotientGroup.mk x) (QuotientGroup.mk y) = 0 ↔
      (x : G) * (y : G) = (y : G) * (x : G) := by
  have hqx : (x : G) ∈ E ⊔ F := by
    rw [← Q_eq_sup S]
    exact x.2
  obtain ⟨e1, he1, f1, hf1, hxef⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hqx
  have hqy : (y : G) ∈ E ⊔ F := by
    rw [← Q_eq_sup S]
    exact y.2
  obtain ⟨e2, he2, f2, hf2, hyef⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hqy
  have hmkx := mk_eq_QbarEquivF_of_mul S he1 hf1 x hxef
  have hmky := mk_eq_QbarEquivF_of_mul S he2 hf2 y hyef
  rw [hmkx, hmky, polar_q_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [fq_polar_eq_zero_iff]
  have hfiff : ((⟨f1, hf1⟩ : ↥F) * ⟨f2, hf2⟩ = ⟨f2, hf2⟩ * ⟨f1, hf1⟩) ↔
      f1 * f2 = f2 * f1 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hfiff]
  have hxG : (x : G) = e1 * f1 := hxef
  have hyG : (y : G) = e2 * f2 := hyef
  have hEab : e1 * e2 = e2 * e1 :=
    congrArg Subtype.val (S.hyp.elemAbelian.1.is_comm.comm ⟨e1, he1⟩ ⟨e2, he2⟩)
  have hxy_eq : (x : G) * (y : G) = (e1 * e2) * (f1 * f2) := by
    rw [hxG, hyG]
    calc
      (e1 * f1) * (e2 * f2) = e1 * (f1 * e2) * f2 := by group
      _ = e1 * (e2 * f1) * f2 := by
        rw [show f1 * e2 = e2 * f1 from (S.hyp.commute e2 he2 f1 hf1).eq.symm]
      _ = (e1 * e2) * (f1 * f2) := by group
  have hyx_eq : (y : G) * (x : G) = (e1 * e2) * (f2 * f1) := by
    rw [hyG, hxG]
    calc
      (e2 * f2) * (e1 * f1) = e2 * (f2 * e1) * f1 := by group
      _ = e2 * (e1 * f2) * f1 := by
        rw [show f2 * e1 = e1 * f2 from (S.hyp.commute e1 he1 f2 hf2).eq.symm]
      _ = (e2 * e1) * (f2 * f1) := by group
      _ = (e1 * e2) * (f2 * f1) := by rw [← hEab]
  constructor
  · intro h
    rw [hxy_eq, hyx_eq, h]
  · intro h
    rw [hxy_eq, hyx_eq] at h
    exact mul_left_cancel h

private theorem polarBilin_q (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    (q S).polarBilin = LinearMap.BilinForm.congr (QbarEquivF S) (fq S).polarBilin := by
  change ((fq S).comp (QbarEquivF S).symm.toLinearMap).polarBilin =
    LinearMap.BilinForm.congr (QbarEquivF S) (fq S).polarBilin
  rw [QuadraticMap.polarBilin_comp]
  ext x y
  simp

theorem q_nondegenerate (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] :
    (q S).polarBilin.Nondegenerate := by
  rw [polarBilin_q]
  exact LinearMap.BilinForm.Nondegenerate.congr (QbarEquivF S) (fq_nondegenerate S)


end CFSG.RankThree.GF2n.Stroth78

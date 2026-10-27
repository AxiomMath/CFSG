module

public import CFSG.RankThree.GF2n.Parrott.J1Sub
public import CFSG.RankThree.GF2n.Parrott.CentralizerCentralizerJ

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)
variable (h : Tim79a.ParrottHyp z)

@[expose] def ParrottEqualityBranch (h : Tim79a.ParrottHyp z) : Prop :=
  ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
    qH (z := z) (D := D) σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂

theorem Fsub_map_conjV_eq (hJ0 : (J0sub (z := z) (D := D)).Normal) (g : ↥(H z)) :
    (Fsub (z := z) (sigma1Nine (z := z) D)).map (conjV h g).toMonoidHom =
      Fsub (z := z) (sigma1Nine (z := z) D) := by
  rw [Fsub, Subgroup.map_map]
  have hcomp : (conjV h g).toMonoidHom.comp (QuotientV.pi z) =
      (QuotientV.pi z).comp (conjJ' z g).toMonoidHom := by
    ext x
    exact conjV_mk h g x
  rw [hcomp, ← Subgroup.map_map, map_centralizerJ_conj,
    centralizerJ_conj_eq_of_J0sub_normal (z := z) (D := D) hJ0 g]

section ActionOnFsub

variable (hJ0 : (J0sub (z := z) (D := D)).Normal)

noncomputable def actFsub :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) →*
      Equiv.Perm ↥(Fsub (z := z) (sigma1Nine (z := z) D)) where
  toFun a :=
    let hmap : (Fsub (z := z) (sigma1Nine (z := z) D)).map
        (actionA h a).toMonoidHom = Fsub (z := z) (sigma1Nine (z := z) D) := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
        ((J z).subgroupOf (H z)) a
      rw [actionA_mk]
      exact Fsub_map_conjV_eq (z := z) (D := D) h hJ0 g
    let hcomp : (actionA h a).symm.toMonoidHom.comp (actionA h a).toMonoidHom =
        MonoidHom.id (QuotientV.V z) := by
      ext v
      simp
    let hmap_symm : (Fsub (z := z) (sigma1Nine (z := z) D)).map
        (actionA h a).symm.toMonoidHom = Fsub (z := z) (sigma1Nine (z := z) D) := by
      calc (Fsub (z := z) (sigma1Nine (z := z) D)).map (actionA h a).symm.toMonoidHom
          = ((Fsub (z := z) (sigma1Nine (z := z) D)).map
              (actionA h a).toMonoidHom).map (actionA h a).symm.toMonoidHom := by
              rw [hmap]
        _ = (Fsub (z := z) (sigma1Nine (z := z) D)).map
              ((actionA h a).symm.toMonoidHom.comp (actionA h a).toMonoidHom) :=
              Subgroup.map_map _ _ _
        _ = (Fsub (z := z) (sigma1Nine (z := z) D)).map
              (MonoidHom.id (QuotientV.V z)) := by rw [hcomp]
        _ = Fsub (z := z) (sigma1Nine (z := z) D) := by simp
    { toFun := fun v =>
        ⟨actionA h a v.1, by
          have hv : actionA h a v.1 ∈ (Fsub (z := z) (sigma1Nine (z := z) D)).map
              (actionA h a).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨v.1, v.2, rfl⟩
          rwa [hmap] at hv⟩
      invFun := fun v =>
        ⟨(actionA h a).symm v.1, by
          have hv : (actionA h a).symm v.1 ∈ (Fsub (z := z) (sigma1Nine (z := z) D)).map
              (actionA h a).symm.toMonoidHom :=
            Subgroup.mem_map.mpr ⟨v.1, v.2, rfl⟩
          rwa [hmap_symm] at hv⟩
      left_inv := by
        intro v
        ext
        simp
      right_inv := by
        intro v
        ext
        simp }
  map_one' := by
    ext v
    simp
  map_mul' := by
    intro a b
    ext v
    simp [MulAut.mul_apply]

noncomputable def actQFsub (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    QP45.originalSubgroup →* Equiv.Perm ↥(Fsub (z := z) (sigma1Nine (z := z) D)) :=
  (actFsub (z := z) (D := D) h hJ0).comp
    ((D.toQA45 (z := z) (hN := hN)).symm.toMonoidHom.comp
      (Subgroup.inclusion QP45_le_QA45))

theorem actQFsub_eq_one (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    actQFsub (z := z) (D := D) h hJ0 = 1 := by
  haveI : IsSimpleGroup QP45.originalSubgroup := isSimpleGroup_QP45_of_model
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (actQFsub (z := z) (D := D) h hJ0).ker with hbot | htop
  · exfalso
    have hinj : Function.Injective (actQFsub (z := z) (D := D) h hJ0) :=
      (MonoidHom.ker_eq_bot_iff (actQFsub (z := z) (D := D) h hJ0)).mp hbot
    have hle : Nat.card QP45.originalSubgroup ≤
        Nat.card (Equiv.Perm ↥(Fsub (z := z) (sigma1Nine (z := z) D))) :=
      Nat.card_le_card_of_injective _ hinj
    rw [card_QP45, Nat.card_perm, card_Fsub_sigma1Nine (z := z) (D := D) h] at hle
    norm_num at hle
  · apply MonoidHom.ext
    intro a
    have ha : a ∈ (actQFsub (z := z) (D := D) h hJ0).ker := by
      rw [htop]
      exact Subgroup.mem_top a
    simpa using (MonoidHom.mem_ker.mp ha)

end ActionOnFsub

theorem centralizerCentralizerJ_image_eq
    : Cimage h (centralizerJ (sigma1Nine (z := z) D)) =
      commutatorVSubmodule h (sigma1Nine (z := z) D) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hK : Kimage h (centralizerJ (sigma1Nine (z := z) D)) =
      fixSubmodule h (sigma1Nine (z := z) D) := by
    change (AddSubgroup.toZModSubmodule 2)
        (Subgroup.toAddSubgroup (Fsub (z := z) (sigma1Nine (z := z) D))) =
      (AddSubgroup.toZModSubmodule 2)
        (Subgroup.toAddSubgroup (autFixedSubgroup ((conjV h) (sigma1Nine (z := z) D))))
    rw [Fsub_sigma1Nine_eq_autFixedSubgroup (z := z) (D := D) (h := h)]
  have hCV := commutatorV_eq_orthogonal_fixSubmodule (z := z) h
    (sigma1Nine (z := z) D) (sigma1Nine_order (z := z) D)
  rw [map_centralizer_eq_orthogonal (z := z) h
    (centralizerJ (sigma1Nine (z := z) D)), hK]
  exact hCV.symm

theorem centralizer_centralizerJ_eq_J1sub
    : (Subgroup.centralizer
        (centralizerJ (sigma1Nine (z := z) D) : Set (J z))).map (J z).subtype =
      J1sub (z := z) (D := D) h := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let σ1 : ↥(H z) := sigma1Nine (z := z) D
  let JC : Subgroup (J z) := centralizerJ σ1
  let CJcJ : Subgroup (J z) := Subgroup.centralizer (JC : Set (J z))
  let P : Subgroup G := ⁅(Subgroup.zpowers σ1).map (H z).subtype, J z⁆
  let Z : Subgroup G := centerIn (J z)
  have hCim : Cimage h JC = commutatorVSubmodule h σ1 :=
    centralizerCentralizerJ_image_eq (z := z) (D := D) (h := h)
  have hCimGrp : CJcJ.map (QuotientV.pi z) = commutatorV h σ1 := by
    apply Subgroup.toAddSubgroup.injective
    have h := congrArg Submodule.toAddSubgroup hCim
    simpa [Cimage, commutatorVSubmodule, CJcJ, JC, Subgroup.toAddSubgroup,
      AddSubgroup.toZModSubmodule] using h
  have hPJ : (P.subgroupOf (J z)).map (QuotientV.pi z) = commutatorV h σ1 := rfl
  have himg : CJcJ.map (QuotientV.pi z) = (P.subgroupOf (J z)).map (QuotientV.pi z) := by
    rw [hCimGrp, hPJ]
  have hZmem : ∀ x : J z, (x : G) ∈ Z → x ∈ CJcJ := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (c : G) c.2)
  have hPle : P ≤ CJcJ.map (J z).subtype := by
    intro x hx
    have hxJ : x ∈ J z := commutator_le_J_sigma1Nine (z := z) (D := D) hx
    have hxImg : QuotientV.pi z ⟨x, hxJ⟩ ∈ CJcJ.map (QuotientV.pi z) := by
      rw [himg, hPJ]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hxImg
    have hker : (⟨x, hxJ⟩ : J z) * c⁻¹ ∈ (QuotientV.pi z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc_eq]
      simp
    have hmemZ : (((⟨x, hxJ⟩ : J z) * c⁻¹ : J z) : G) ∈ Z := by
      have h := hker
      rwa [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at h
    have hx_cJ : (⟨x, hxJ⟩ : J z) = ((⟨x, hxJ⟩ : J z) * c⁻¹) * c := by group
    have hx_CJcJ : (⟨x, hxJ⟩ : J z) ∈ CJcJ := by
      rw [hx_cJ]
      exact CJcJ.mul_mem (hZmem _ hmemZ) hc
    exact Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, hx_CJcJ, rfl⟩
  have hZle : Z ≤ CJcJ.map (J z).subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hZmem ⟨x, hx.1⟩ hx, rfl⟩
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨xJ, hxJ_CJcJ, rfl⟩ := hx
    have hxImg : QuotientV.pi z xJ ∈ (P.subgroupOf (J z)).map (QuotientV.pi z) := by
      rw [← himg]
      exact Subgroup.mem_map_of_mem _ hxJ_CJcJ
    obtain ⟨p, hpPJ, hp_eq⟩ := Subgroup.mem_map.mp hxImg
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hpPJ
    have hker : p⁻¹ * xJ ∈ (QuotientV.pi z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp_eq]
      simp
    have hmemZ : ((p⁻¹ * xJ : J z) : G) ∈ Z := by
      have h := hker
      rwa [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at h
    rw [J1sub]
    change (xJ : G) ∈ P ⊔ centerIn (J z)
    have hx_eq : (xJ : G) = (p : G) * ((p⁻¹ * xJ : J z) : G) := by
      simp
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hpP hmemZ
  · rw [J1sub]
    exact sup_le hPle hZle

theorem derived_le_P_H :
    ⁅H z, H z⁆ ≤ (P_H (z := z) (D := D)).map (H z).subtype := by
  haveI : (P_H (z := z) (D := D)).Normal := P_H_normal (z := z) (D := D)
  have hcard : Nat.card (↥(H z) ⧸ P_H (z := z) (D := D)) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact index_P_H (z := z) (D := D)
  haveI : IsCyclic (↥(H z) ⧸ P_H (z := z) (D := D)) :=
    isCyclic_of_prime_card (p := 2) hcard
  have hcomm : _root_.commutator (↥(H z)) ≤ P_H (z := z) (D := D) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp inferInstance
  simpa [Subgroup.map_subtype_commutator] using
    Subgroup.map_mono (f := (H z).subtype) hcomm

theorem derived_conjV_fixes_Fsub
    (hJ0 : (J0sub (z := z) (D := D)).Normal) {h' : G}
    (hh' : h' ∈ ⁅H z, H z⁆) {v : QuotientV.V z}
    (hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D)) :
    conjV h ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ v = v := by
  obtain ⟨hH, hhH, hH_eq⟩ := Subgroup.mem_map.mp
    (derived_le_P_H (z := z) (D := D) hh')
  have hq : qH (z := z) (D := D) hH ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    (mem_P_H_iff (z := z) (D := D) hH).mp hhH
  let a : QP45.originalSubgroup :=
    ⟨qH (z := z) (D := D) hH, Subgroup.mem_subgroupOf.mp hq⟩
  have hact : actFsub (z := z) (D := D) h hJ0
      (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) = 1 := by
    have h1 : actQFsub (z := z) (D := D) h hJ0 a = 1 := by
      rw [actQFsub_eq_one (z := z) (D := D) h hJ0]
      rfl
    have h2 : (D.toQA45 (z := z) (hN := hN)).symm
        (Subgroup.inclusion QP45_le_QA45 a) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) hH := by
      have h3 : Subgroup.inclusion QP45_le_QA45 a = qH (z := z) (D := D) hH := rfl
      rw [h3, toQA45_symm_qH]
    simpa [actQFsub, h2] using h1
  have happ : actionA h (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) v = v := by
    have hfix : actFsub (z := z) (D := D) h hJ0
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [hact]
      rfl
    exact congrArg Subtype.val hfix
  have hconj : conjV h hH v = v := by
    rw [← actionA_mk (z := z) h hH]
    exact happ
  have hsub : hH = ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ := Subtype.ext hH_eq
  rw [← hsub]
  exact hconj

theorem derived_commutator_CJ_le_center (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    ⁅⁅H z, H z⁆, CJ z (sigma1Nine (z := z) D : G)⁆ ≤ centerIn (J z) := by
  rw [Subgroup.commutator_le]
  intro h' hh' x hx
  have hxJ : x ∈ J z := hx.2
  let xJ : J z := ⟨x, hxJ⟩
  have hxc : (xJ : G) * (sigma1Nine (z := z) D : G) =
      (sigma1Nine (z := z) D : G) * (xJ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hxJc : xJ ∈ centralizerJ (sigma1Nine (z := z) D) := by
    rw [mem_centralizerJ_iff]
    exact hxc
  have hv : QuotientV.pi z xJ ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
    Subgroup.mem_map.mpr ⟨xJ, hxJc, rfl⟩
  have hfix := derived_conjV_fixes_Fsub (z := z) (D := D) h hJ0 hh' hv
  rw [conjV_mk] at hfix
  have hker : conjJ' z ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ xJ * xJ⁻¹ ∈
      (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfix]
    simp
  have hmemZ : ((conjJ' z ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ xJ * xJ⁻¹ :
      J z) : G) ∈ centerIn (J z) := by
    have h := hker
    rwa [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at h
  have hcomm_eq : ⁅h', x⁆ =
      ((conjJ' z ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ xJ * xJ⁻¹ : J z) : G) := by
    have h1 : ((conjJ' z ⟨h', Subgroup.commutator_le_self (H z) hh'⟩ xJ : J z) : G) =
        h' * x * h'⁻¹ := by
      rw [conjJ'_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1]
    simp [xJ, commutatorElement_def]
  rw [hcomm_eq]
  exact hmemZ

theorem centerIn_le_centralizer_J :
    centerIn (J z) ≤ Subgroup.centralizer (J z : Set G) :=
  inf_le_right

end CFSG.RankThree.GF2n.Parrott

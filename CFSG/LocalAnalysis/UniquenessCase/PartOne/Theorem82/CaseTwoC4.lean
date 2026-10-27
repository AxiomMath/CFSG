module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs49
public import CFSG.CGT.PushingUpLit.SolKNA.Residue
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTI
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPairs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private def K49X : Subgroup G := Subgroup.zpowers t.y

private def K49L : Subgroup G := t.d.Lf 0

private noncomputable def K49Q : Subgroup G := t.d.N

private noncomputable def K49H : Subgroup G := t.K49X ⊔ t.K49L ⊔ t.K49Q

private noncomputable def K49LQ : Subgroup G := c.L ⊔ t.K49Q

private noncomputable def K49R : Subgroup G := CFSG.Open.pCoreOf 2 t.K49H

private theorem K49Q_le_M : t.K49Q ≤ c.S.M := by
  rw [K49Q, show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
  exact Subgroup.map_subtype_le _

private theorem K49X_le_M : t.K49X ≤ c.S.M :=
  (Subgroup.zpowers_le.mpr t.hyP).trans t.hP.le

private theorem K49L_le_M : t.K49L ≤ c.S.M :=
  (t.d.hLM 0).trans (t.hdM ▸ le_rfl)

private theorem K49H_le_M : t.K49H ≤ c.S.M :=
  sup_le (sup_le t.K49X_le_M t.K49L_le_M) t.K49Q_le_M

private theorem y_mem_normalizer_L : t.y ∈ Subgroup.normalizer (c.L : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hL : c.L = t.d.Lf 0 ⊔ t.d.Lf 1 ⊔ t.d.Lf 2 := by
    rw [← t.hdL, t.d.hL]
  rw [hL, Subgroup.map_sup, Subgroup.map_sup]
  change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t.y)) (t.d.Lf 0) ⊔
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t.y)) (t.d.Lf 1) ⊔
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t.y)) (t.d.Lf 2) =
    t.d.Lf 0 ⊔ t.d.Lf 1 ⊔ t.d.Lf 2
  rw [t.hyL 0, t.hyL 1, t.hyL 2]
  rw [show (0 + 1 : Fin 3) = 1 from rfl,
    show (1 + 1 : Fin 3) = 2 from rfl,
    show (2 + 1 : Fin 3) = 0 from rfl]
  ac_rfl

private theorem K49X_le_normalizer_L : t.K49X ≤ Subgroup.normalizer (c.L : Set G) :=
  Subgroup.zpowers_le.mpr t.y_mem_normalizer_L

private theorem K49Q_le_normalizer_L : t.K49Q ≤ Subgroup.normalizer (c.L : Set G) :=
  t.K49Q_le_M.trans c.le_normalizer_L

private theorem K49L_le_L : t.K49L ≤ c.L := by
  show t.d.Lf 0 ≤ c.L
  rw [← t.hdL]
  exact t.d.Lf_le_L 0

private theorem K49H_le_normalizer_L : t.K49H ≤ Subgroup.normalizer (c.L : Set G) :=
  sup_le (sup_le t.K49X_le_normalizer_L
    (t.K49L_le_L.trans Subgroup.le_normalizer)) t.K49Q_le_normalizer_L

private theorem K49X_card : Nat.card t.K49X = 3 := by
  rw [K49X, Nat.card_zpowers, t.orderOf_y]

private theorem K49X_le_H : t.K49X ≤ t.K49H := le_sup_left.trans le_sup_left

private theorem K49Q_le_H : t.K49Q ≤ t.K49H := le_sup_right

private theorem K49L_le_H : t.K49L ≤ t.K49H := le_sup_right.trans le_sup_left

private theorem y_mem_H : t.y ∈ t.K49H :=
  t.K49X_le_H (Subgroup.mem_zpowers t.y)

private theorem K49H_map_conj_y : t.K49H.map (MulAut.conj t.y).toMonoidHom = t.K49H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer t.y_mem_H)

private theorem Lf1_le_H : t.d.Lf 1 ≤ t.K49H := by
  calc t.d.Lf 1 = (t.d.Lf 0).map (MulAut.conj t.y).toMonoidHom := (t.hyL 0).symm
    _ ≤ t.K49H.map (MulAut.conj t.y).toMonoidHom := Subgroup.map_mono t.K49L_le_H
    _ = t.K49H := t.K49H_map_conj_y

private theorem Lf2_le_H : t.d.Lf 2 ≤ t.K49H := by
  calc t.d.Lf 2 = (t.d.Lf 1).map (MulAut.conj t.y).toMonoidHom := (t.hyL 1).symm
    _ ≤ t.K49H.map (MulAut.conj t.y).toMonoidHom := Subgroup.map_mono t.Lf1_le_H
    _ = t.K49H := t.K49H_map_conj_y

private theorem L_le_H : c.L ≤ t.K49H := by
  rw [← t.hdL, t.d.hL]
  exact sup_le (sup_le t.K49L_le_H t.Lf1_le_H) t.Lf2_le_H

private theorem K49L_subnormal_H : CFSG.Open.IsSubnormal t.K49L t.K49H := by
  have hLnorm : c.L ≤ Subgroup.normalizer (t.K49L : Set G) := by
    rw [K49L, ← t.hdL]
    exact SylowThreeData.L_le_normalizer_Lf t.d 0
  have hL0L : CFSG.Open.IsSubnormal t.K49L c.L :=
    CFSG.Open.IsSubnormal.step t.K49L_le_L
      ((Subgroup.normal_subgroupOf_iff_le_normalizer t.K49L_le_L).mpr hLnorm)
      (CFSG.Open.IsSubnormal.refl _)
  have hLH : CFSG.Open.IsSubnormal c.L t.K49H :=
    CFSG.Open.IsSubnormal.step t.L_le_H
      ((Subgroup.normal_subgroupOf_iff_le_normalizer t.L_le_H).mpr
        t.K49H_le_normalizer_L) (CFSG.Open.IsSubnormal.refl _)
  exact hL0L.trans hLH

private theorem K49L_mem_oTwoComponentsIn
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    t.K49L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn t.K49H := by
  obtain ⟨hN, hq⟩ := (t.hcomp 0).2.2.2
  letI := hN
  have hqOpen : CFSG.Open.IsQuasisimple
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) := hq
  have hq' : CFSG.IsQuasisimple
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hqOpen
  set e : (t.K49L.subgroupOf t.K49H) ≃* t.K49L :=
    Subgroup.subgroupOfEquivOfLe t.K49L_le_H
  refine CFSG.RankThree.PartTwo.mem_oTwoComponentsIn_iff.mpr
    ⟨t.K49L_le_H, ?_, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥t.K49L := Subgroup.isPerfect_iff.mpr (t.d.hperf 0)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact (CFSG.Open.IsSubnormal.iff_subgroupOf t.K49L_le_H).mp t.K49L_subnormal_H
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (CFSG.pCore_map_iso 2 e.symm)) hq'

private theorem y_sq_mul_y : t.y ^ 2 * t.y = 1 := by
  have h : t.y ^ 2 * t.y = t.y ^ 3 := by simpa using (pow_succ t.y 2).symm
  rw [h, t.hy3]

private theorem hy_sq_inv : (t.y ^ 2)⁻¹ = t.y :=
  inv_eq_of_mul_eq_one_right (y_sq_mul_y t)

private theorem hy_inv : t.y⁻¹ = t.y ^ 2 :=
  inv_eq_of_mul_eq_one_left (y_sq_mul_y t)

private theorem conj_y_sq :
    (MulAut.conj (t.y ^ 2)).toMonoidHom =
      (MulAut.conj t.y).toMonoidHom.comp (MulAut.conj t.y).toMonoidHom := by
  rw [pow_two, map_mul]
  rfl

private theorem Lf0_map_conj_sq :
    (t.d.Lf 0).map (MulAut.conj (t.y ^ 2)).toMonoidHom = t.d.Lf 2 := by
  calc (t.d.Lf 0).map (MulAut.conj (t.y ^ 2)).toMonoidHom
      = (t.d.Lf 0).map ((MulAut.conj t.y).toMonoidHom.comp
          (MulAut.conj t.y).toMonoidHom) := by rw [conj_y_sq]
    _ = ((t.d.Lf 0).map (MulAut.conj t.y).toMonoidHom).map
          (MulAut.conj t.y).toMonoidHom := by rw [Subgroup.map_map]
    _ = t.d.Lf 2 := by
        rw [t.hyL 0]
        rw [show (0 + 1 : Fin 3) = 1 from rfl, t.hyL 1]
        rw [show (1 + 1 : Fin 3) = 2 from rfl]

private theorem K49I_eq : c.L = ⨆ x ∈ t.K49X, CFSG.conjugate t.K49L x := by
  refine le_antisymm ?_ ?_
  · rw [← t.hdL, t.d.hL]
    have h1 : CFSG.conjugate t.K49L (t.y ^ 2) = t.d.Lf 1 := by
      rw [CFSG.conjugate, hy_sq_inv]
      exact t.hyL 0
    have h2 : CFSG.conjugate t.K49L t.y = t.d.Lf 2 := by
      rw [CFSG.conjugate, hy_inv]
      exact Lf0_map_conj_sq (t := t)
    refine sup_le (sup_le ?_ ?_) ?_
    · have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext z
        simp [MulAut.conj_apply]
      have h0 : CFSG.conjugate t.K49L (1 : G) = t.d.Lf 0 := by
        rw [CFSG.conjugate, inv_one]
        change Subgroup.map (MulAut.conj (1 : G)).toMonoidHom t.K49L = t.d.Lf 0
        rw [hone, Subgroup.map_id]
        rfl
      exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem t.K49X) (le_of_eq h0.symm)
    · exact le_iSup₂_of_le (t.y ^ 2)
        (Subgroup.pow_mem t.K49X (Subgroup.mem_zpowers t.y) 2) (le_of_eq h1.symm)
    · exact le_iSup₂_of_le t.y (Subgroup.mem_zpowers t.y) (le_of_eq h2.symm)
  · refine iSup₂_le fun x hx => ?_
    have hxN : x⁻¹ ∈ Subgroup.normalizer (c.L : Set G) :=
      (Subgroup.normalizer (c.L : Set G)).inv_mem (t.K49X_le_normalizer_L hx)
    have hmap : CFSG.conjugate c.L x = c.L := by
      rw [CFSG.conjugate]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    calc CFSG.conjugate t.K49L x ≤ CFSG.conjugate c.L x :=
          Subgroup.map_mono t.K49L_le_L
      _ = c.L := hmap

private theorem K49X_not_le_normalizer_L : ¬ t.K49X ≤ Subgroup.normalizer (t.K49L : Set G) := by
  intro hX
  have hy : t.y ∈ Subgroup.normalizer (t.K49L : Set G) :=
    hX (Subgroup.mem_zpowers t.y)
  have hmap : (t.d.Lf 0).map (MulAut.conj t.y).toMonoidHom = t.d.Lf 0 := by
    simpa [K49L] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  have h01 : t.d.Lf 0 = t.d.Lf 1 := by
    calc t.d.Lf 0 = (t.d.Lf 0).map (MulAut.conj t.y).toMonoidHom := hmap.symm
      _ = t.d.Lf (0 + 1) := t.hyL 0
      _ = t.d.Lf 1 := by rfl
  exact (by decide : (0 : Fin 3) ≠ 1) (t.hinj h01)


private theorem phiKy_ker :
    (t.phiKy).ker = (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
  ext k
  rw [MonoidHom.mem_ker]
  constructor
  · intro hk
    have hK : Subgroup.inclusion t.Ky_le_M k ∈ t.Kq :=
      (QuotientGroup.eq_one_iff _).mp hk
    exact Subgroup.mem_subgroupOf.mpr ⟨k.2, (Subgroup.mem_subgroupOf.mp hK).2⟩
  · intro hk
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    exact Subgroup.mem_subgroupOf.mpr ⟨(t.Ky_le k.2).1,
      (Subgroup.mem_subgroupOf.mp hk).2⟩

private instance K49Nsub_normal (t : CaseTwoTransitive c) :
    ((t.Ky ⊓ t.d.N).subgroupOf t.Ky).Normal := by
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hKyN : t.Ky ≤ Subgroup.normalizer ((t.Ky ⊓ t.d.N : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.d.N)
      ⟨Subgroup.le_normalizer hk, hMN (t.Ky_le_M hk)⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKyN

private noncomputable def eKyBar
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    (↥t.Ky ⧸ (t.Ky ⊓ t.d.N).subgroupOf t.Ky) ≃*
      CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L :=
  ((QuotientGroup.quotientMulEquivOfEq (phiKy_ker t).symm).trans
    (QuotientGroup.quotientKerEquivRange (t.phiKy))).trans
  ((t.eDeltaKy (t.muL_injective hK32 hGA hSp)
      (t.phiKy_range_eq_delta_range hK32 hGA hSp).symm).symm.trans
    ((t.eLhatLb 0).trans (t.eLb 0).symm))

private theorem isAlt_bar2_K49L
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hExt : CFSG.Quasithin.IsExt ↥t.Ky
      (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
      (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) 5 := by
  classical
  obtain ⟨V, hVnormal, -, hVA5⟩ := hExt
  letI := hVnormal
  obtain ⟨eA⟩ := hVA5
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcardQ : Nat.card (↥t.Ky ⧸ V) = 60 := by
    rw [Nat.card_congr eA.toEquiv, hcardA5]
  have hVne : V ≠ ⊤ := by
    intro htop
    rw [htop] at hcardQ
    have h1 : Nat.card (↥t.Ky ⧸ (⊤ : Subgroup ↥t.Ky)) = 1 := Subgroup.index_top
    omega
  have hVg_normal : t.Ky ≤ Subgroup.normalizer
      ((V.map t.Ky.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (f := t.Ky.subtype) (H := V)
    rw [Subgroup.normalizer_eq_top V, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hVg_le_N : V.map t.Ky.subtype ≤ t.d.N := by
    rcases t.le_N_or_eq_Ky hK32 hGA hSp (Subgroup.map_subtype_le V) hVg_normal with
      h | h
    · exact h
    · exfalso
      have hVtop : V = ⊤ := by
        apply Subgroup.map_injective (f := t.Ky.subtype) t.Ky.subtype_injective
        rw [h, Subgroup.map_top, Subgroup.range_subtype]
      exact hVne hVtop
  let Nsub : Subgroup ↥t.Ky := (t.Ky ⊓ t.d.N).subgroupOf t.Ky
  haveI : Nsub.Normal := K49Nsub_normal t
  have hVN : V ≤ Nsub := by
    intro v hv
    exact Subgroup.mem_subgroupOf.mpr
      ⟨v.2, hVg_le_N (Subgroup.mem_map_of_mem t.Ky.subtype hv)⟩
  have hVN' : V ≤ (QuotientGroup.mk' Nsub).ker := by
    rwa [QuotientGroup.ker_mk']
  let qV : (↥t.Ky ⧸ V) →* (↥t.Ky ⧸ Nsub) :=
    QuotientGroup.lift V (QuotientGroup.mk' Nsub) hVN'
  have hqV_surj : Function.Surjective qV := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Nsub y
    refine ⟨QuotientGroup.mk' V x, ?_⟩
    show (QuotientGroup.lift V (QuotientGroup.mk' Nsub) hVN') (QuotientGroup.mk' V x) =
      QuotientGroup.mk' Nsub x
    simp [QuotientGroup.lift_mk]
  have heBar_surj : Function.Surjective
      (eKyBar t hK32 hGA hSp).toMonoidHom :=
    (eKyBar t hK32 hGA hSp).surjective
  have hf_surj : Function.Surjective
      ((eKyBar t hK32 hGA hSp).toMonoidHom.comp qV) :=
    heBar_surj.comp hqV_surj
  let g : alternatingGroup (Fin 5) →* CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L :=
    ((eKyBar t hK32 hGA hSp).toMonoidHom.comp qV).comp eA.symm.toMonoidHom
  have hg_surj : Function.Surjective g := hf_surj.comp eA.symm.surjective
  have hqs : CFSG.IsQuasisimple
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) := by
    obtain ⟨hN, hq⟩ := (t.hcomp 0).2.2.2
    letI := hN
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
  have hc : Subgroup.center
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    change Nat.card (Subgroup.center
      (↥(t.d.Lf 0) ⧸ CFSG.pCore 2 ↥(t.d.Lf 0))) = 1
    rw [Nat.card_congr (Subgroup.centerCongr (t.eLb 0)).toEquiv,
      t.center_Lb_eq_bot hK32 hGA hSp 0]
    simp
  have hSimple : IsSimpleGroup
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 t.K49L) :=
    CFSG.CGT.PushingUpLit.CGT6.isSimpleGroup_of_quasisimple_of_center_eq_bot
      hqs.2.1 hc
  have hSimpleA5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup_five
  have hInj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff g]
    by_contra hker
    have htop : g.ker = ⊤ := by
      rcases hSimpleA5.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
      · exact absurd hbot hker
      · exact htop
    have hg1 : g = 1 := MonoidHom.ker_eq_top_iff.mp htop
    have hrange : g.range = ⊥ := by rw [hg1, MonoidHom.range_one]
    have htoprange : g.range = ⊤ := MonoidHom.range_eq_top.mpr hg_surj
    exact bot_ne_top (hrange.symm.trans htoprange)
  exact ⟨(MulEquiv.ofBijective g ⟨hInj, hg_surj⟩).symm⟩
private theorem K49Q_le_pCoreOf_H
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    t.K49Q ≤ CFSG.Open.pCoreOf 2 t.K49H := by
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hQ2 : IsPGroup 2 ↥t.K49Q := by
    rw [K49Q, show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    t.K49Q_le_H (t.K49H_le_M.trans hMN) hQ2

private theorem pCoreOf_H_le_K49Q
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    CFSG.Open.pCoreOf 2 t.K49H ≤ t.K49Q := by
  classical
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hQ2 : IsPGroup 2 ↥t.K49Q := by
    rw [K49Q, show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
  have hR2 : IsPGroup 2 ↥t.K49R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.K49H
  have hRH : t.K49R ≤ t.K49H := Subgroup.map_subtype_le _
  have hQleR : t.K49Q ≤ t.K49R := t.K49Q_le_pCoreOf_H hK32 hGA hSp
  have hRL_le_N : t.K49R ⊓ c.L ≤ c.L ⊓ t.d.N := by
    refine t.le_inf_N_of_le_L hK32 hGA hSp inf_le_right ?_ ?_
    · have hRHnorm : t.K49H ≤ Subgroup.normalizer (t.K49R : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 t.K49H
      have hHnorm : t.K49H ≤
          Subgroup.normalizer ((t.K49R ⊓ c.L : Subgroup G) : Set G) := by
        intro h hh
        exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.K49R) (K := c.L)
          ⟨hRHnorm hh, t.K49H_le_normalizer_L hh⟩
      exact (t.Ky_le.trans (inf_le_left.trans t.L_le_H)).trans hHnorm
    · intro h3
      have hRL2 : IsPGroup 2 ↥(t.K49R ⊓ c.L) := hR2.to_le inf_le_left
      obtain ⟨n, hn⟩ := hRL2.exists_card_eq
      rw [hn] at h3
      have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
      norm_num at h32
  have hLQH : t.K49LQ ≤ t.K49H := sup_le t.L_le_H t.K49Q_le_H
  have hHnormLQ : t.K49H ≤ Subgroup.normalizer (t.K49LQ : Set G) := by
    intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_sup c.L t.K49Q
      ⟨t.K49H_le_normalizer_L hh, (t.K49H_le_M.trans hMN) hh⟩
  have hLQnorm : (t.K49LQ.subgroupOf t.K49H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLQH).mpr hHnormLQ
  letI := hLQnorm
  let KqH : Subgroup ↥t.K49H := t.K49LQ.subgroupOf t.K49H
  let piH : ↥t.K49H →* (↥t.K49H ⧸ KqH) := QuotientGroup.mk' KqH
  let f : t.K49X →* (↥t.K49H ⧸ KqH) :=
    piH.comp (Subgroup.inclusion t.K49X_le_H)
  have hXleNLQ : t.K49X ≤ Subgroup.normalizer (t.K49LQ : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup c.L t.K49Q
      ⟨t.K49X_le_normalizer_L hx, (t.K49X_le_M.trans hMN) hx⟩
  have hH_le : t.K49H ≤ t.K49X ⊔ t.K49LQ := by
    rw [K49H]
    exact sup_le (sup_le le_sup_left
      (t.K49L_le_L.trans (le_sup_left.trans le_sup_right)))
      (le_sup_right.trans le_sup_right)
  have hH_mul : ∀ h ∈ t.K49H, ∃ x ∈ t.K49X, ∃ lq ∈ t.K49LQ, x * lq = h := by
    intro h hh
    have hx : h ∈ t.K49X ⊔ t.K49LQ := hH_le hh
    change h ∈ ((t.K49X ⊔ t.K49LQ : Subgroup G) : Set G) at hx
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right t.K49X t.K49LQ hXleNLQ
    rw [hset] at hx
    exact Set.mem_mul.mp hx
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective KqH y
    have hh : (h : G) ∈ t.K49H := h.2
    obtain ⟨x, hxX, lq, hlqLQ, hxlq⟩ := hH_mul h hh
    refine ⟨⟨x, hxX⟩, ?_⟩
    show piH ⟨x, t.K49X_le_H hxX⟩ = piH h
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨lq, hLQH hlqLQ⟩, Subgroup.mem_subgroupOf.mpr hlqLQ, ?_⟩
    apply Subtype.ext
    change x * lq = (h : G)
    exact hxlq
  have hcardq_dvd : Nat.card (↥t.K49H ⧸ KqH) ∣ 3 := by
    have h := Subgroup.card_dvd_of_surjective hf_surj
    rwa [t.K49X_card] at h
  let Rbar : Subgroup (↥t.K49H ⧸ KqH) := (t.K49R.subgroupOf t.K49H).map piH
  have hRbar2 : IsPGroup 2 ↥Rbar := by
    have hRsub : IsPGroup 2 ↥(t.K49R.subgroupOf t.K49H) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
    exact hRsub.map piH
  have hRbar_bot : Rbar = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have hcard_dvd : Nat.card ↥Rbar ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (show Rbar ≤ ⊤ from le_top)
      rw [Subgroup.card_top] at h
      exact h.trans hcardq_dvd
    obtain ⟨n, hn⟩ := hRbar2.exists_card_eq
    rw [hn] at hcard_dvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard_dvd with h | h
    · exact hn.trans h
    · exfalso
      have hn0 : n = 0 := by
        by_contra hn0
        have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, hn0⟩
        rw [h] at heven
        norm_num at heven
      subst hn0
      norm_num at h
  have hR_le_LQ : t.K49R ≤ (c.L ⊔ t.K49Q : Subgroup G) := by
    intro r hr
    have hrH : r ∈ t.K49H := hRH hr
    have hmem : (⟨r, hrH⟩ : ↥t.K49H) ∈ KqH := by
      have himg : piH ⟨r, hrH⟩ ∈ Rbar :=
        Subgroup.mem_map.mpr ⟨⟨r, hrH⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
      rw [hRbar_bot, Subgroup.mem_bot] at himg
      exact (QuotientGroup.eq_one_iff _).mp himg
    exact Subgroup.mem_subgroupOf.mp hmem
  have hLQ_mul := Subgroup.coe_mul_of_left_le_normalizer_right c.L t.K49Q
      (c.hyp81.1.trans hMN)
  intro r hr
  have hrLQ : r ∈ (c.L ⊔ t.K49Q : Subgroup G) := hR_le_LQ hr
  change r ∈ ((c.L ⊔ t.K49Q : Subgroup G) : Set G) at hrLQ
  rw [hLQ_mul] at hrLQ
  obtain ⟨l, hlL, q, hqQ, hlrq⟩ := Set.mem_mul.mp hrLQ
  have hqR : q ∈ t.K49R := hQleR hqQ
  have hlR : l ∈ t.K49R := by
    have hl : l = r * q⁻¹ := by rw [← hlrq]; group
    rw [hl]
    exact t.K49R.mul_mem hr (t.K49R.inv_mem hqR)
  have hlQ : l ∈ t.K49Q :=
    (Subgroup.mem_inf.mp (hRL_le_N (Subgroup.mem_inf.mpr ⟨hlR, hlL⟩))).2
  rw [← hlrq]
  exact t.K49Q.mul_mem hlQ hqQ

private theorem K49Q_eq_pCoreOf_H
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    t.K49Q = CFSG.Open.pCoreOf 2 t.K49H :=
  le_antisymm (t.K49Q_le_pCoreOf_H hK32 hGA hSp)
    (t.pCoreOf_H_le_K49Q hK32 hGA hSp)


private theorem CQL_isPGroup : IsPGroup 2 ↥t.CQL := by
  apply (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M).to_le
  intro x hx
  have hxN : x ∈ t.d.N := (Subgroup.mem_inf.mp hx).1
  rwa [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]] at hxN

private theorem tightlyEmbedded_CQL
    {p : ℕ} (hN : t.PairNormalizerLe p)
    (hne : t.CQL ≠ ⊥) :
    CFSG.ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded t.CQL := by
  refine ⟨?_, fun g hg => ?_⟩
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp t.CQL_isPGroup
    rw [hn]
    rcases n with _ | n
    · have hcard : Nat.card t.CQL = 1 := by simpa using hn
      exact absurd (Subgroup.eq_bot_of_card_eq t.CQL hcard) hne
    · exact Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩
  · have hg' : g⁻¹ ∉ Subgroup.normalizer (t.CQL : Set G) :=
      fun h => hg (by simpa using (Subgroup.normalizer (t.CQL : Set G)).inv_mem h)
    rcases t.isTI_CQL hN g⁻¹ with hbot | heq
    · change Odd (Nat.card ↥(t.CQL ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ t.CQL))
      rw [hbot, Subgroup.card_bot]
      exact odd_one
    · exfalso
      apply hg
      have hle : t.CQL ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ t.CQL :=
        heq.symm.le.trans inf_le_right
      have heq2 : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ t.CQL = t.CQL :=
        (Subgroup.eq_of_le_of_card_ge hle (by
          rw [CFSG.CGT.Timmesfeld75.conjSubgroup,
            Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])).symm
      have hmem : g⁻¹ ∈ Subgroup.normalizer (t.CQL : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        exact heq2
      simpa using (Subgroup.normalizer (t.CQL : Set G)).inv_mem hmem

private theorem catalog_of_case3
    (h : CFSG.Open.StatedClassicalModel G .PSL 3 3 1 ∨
      CFSG.Open.StatedClassicalModel G .PSU 3 3 1 ∨
      CFSG.Blueprint.LieModel G .G2 0 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M12) :
    CFSG.Blueprint.Catalog G := by
  rcases h with h | h | h | h | h
  · exact CFSG.Blueprint.lieModel_catalog G .PSL 3 3 1 (Or.inl ⟨by decide, h⟩)
  · exact CFSG.Blueprint.lieModel_catalog G .PSU 3 3 1 (Or.inl ⟨by decide, h⟩)
  · exact CFSG.Blueprint.lieModel_catalog G .G2 0 3 1 h
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))

private theorem CQL_comm_or_pRank_one
    (X : C4Data G c.S.M)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2)
    {p : ℕ} (hN : t.PairNormalizerLe p)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    IsMulCommutative ↥t.CQL ∨ CFSG.Open.pRank 2 t.CQL = 1 := by
  by_cases hcomm : IsMulCommutative ↥t.CQL
  · exact Or.inl hcomm
  by_cases hrank : CFSG.Open.pRank 2 t.CQL ≤ 1
  · refine Or.inr (le_antisymm hrank ?_)
    exact CFSG.AGLEmbedding.one_le_pRank_of_isPGroup_of_ne_bot Nat.prime_two t.CQL_isPGroup
      (fun hbot => hcomm (hbot ▸ (inferInstance : IsMulCommutative ↥(⊥ : Subgroup G))))
  have hrankGe : 2 ≤ CFSG.Open.pRank 2 t.CQL := by omega
  refine Or.inr ?_
  exfalso
  by_cases hbot : t.CQL = ⊥
  · exact hcomm (hbot ▸ (inferInstance : IsMulCommutative ↥(⊥ : Subgroup G)))
  have hKProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G :=
    CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp c.standing.kProper
  have hMax : CFSG.IsMaximalTwoLocal (Subgroup.normalizer (t.CQL : Set G)) := by
    rw [t.normalizer_CQL hN hbot]
    refine ⟨c.S.maxLocal.1, ?_⟩
    intro K hMK hPL
    exact hMK.ne ((c.S.maxLocal.2 K hPL hMK.le).symm)
  have hChar : Subgroup.normalizer (t.CQL : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (t.CQL : Set G)) : Set G) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (t.CQL : Set G)) := by
    rw [t.normalizer_CQL hN hbot]
    exact c.standing.charTwo c.S.M c.S.maxLocal.1
  have hTight := t.tightlyEmbedded_CQL hN hbot
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥t.CQL))
  have hRtop : (R : Subgroup ↥t.CQL) = ⊤ :=
    (R.is_maximal' (t.CQL_isPGroup.of_equiv
      (Subgroup.topEquiv : (⊤ : Subgroup ↥t.CQL) ≃* ↥t.CQL).symm) le_top).symm
  have hRnc : ¬ ∀ a ∈ (R : Subgroup ↥t.CQL).map t.CQL.subtype,
      ∀ b ∈ (R : Subgroup ↥t.CQL).map t.CQL.subtype, a * b = b * a := by
    intro h
    have hmem : ∀ x : ↥t.CQL, (x : G) ∈ (R : Subgroup ↥t.CQL).map t.CQL.subtype := fun x =>
      Subgroup.mem_map_of_mem _ (by rw [hRtop]; exact Subgroup.mem_top x)
    exact hcomm ⟨⟨fun a b => Subtype.ext (h a (hmem a) b (hmem b))⟩⟩
  have hRankR : 2 ≤ CFSG.Open.pRank 2 ((R : Subgroup ↥t.CQL).map t.CQL.subtype) := by
    rw [hRtop, Subgroup.map_top, t.CQL.range_subtype]
    exact hrankGe
  rcases hST G hKProper c.standing.simple c.standing.nonab t.CQL hTight hMax hChar R hRnc hRankR with
    ⟨hcyc, -⟩ | ⟨h2eq, h2abel⟩ | ⟨-, hcat⟩ | ⟨-, hcyc, -⟩ | ⟨-, hcat⟩ | ⟨-, hcat⟩
  · exact hcomm hcyc.isMulCommutative
  · have hcore : CFSG.Open.pCoreOf 2 t.CQL = t.CQL := by
      apply le_antisymm (Subgroup.map_subtype_le (CFSG.pCore 2 ↥t.CQL))
      have htop : (⊤ : Subgroup ↥t.CQL) ≤ CFSG.pCore 2 ↥t.CQL :=
        CFSG.LieType.BorelTits.le_pCore 2 inferInstance
          (t.CQL_isPGroup.of_equiv
            (Subgroup.topEquiv : (⊤ : Subgroup ↥t.CQL) ≃* ↥t.CQL).symm)
      have hmap : (⊤ : Subgroup ↥t.CQL).map t.CQL.subtype ≤
          CFSG.Open.pCoreOf 2 t.CQL := by
        show (⊤ : Subgroup ↥t.CQL).map t.CQL.subtype ≤
          (CFSG.pCore 2 ↥t.CQL).map t.CQL.subtype
        exact Subgroup.map_mono htop
      rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
    have habel : CFSG.Open.IsElemAbelian 2 t.CQL := by
      rw [← hcore, ← h2eq]
      exact h2abel
    exact hcomm habel.1
  · exact X.notCatalog (catalog_of_case3 hcat)
  · exact hcomm hcyc.isMulCommutative
  · exact X.notCatalog
      (CFSG.Blueprint.lieModel_catalog G .PSL _ _ _ (Or.inl ⟨by decide, hcat⟩))
  · rcases hcat with hs | hs
    · obtain ⟨s, -, -, hs⟩ := hs
      exact X.notCatalog (CFSG.Blueprint.lieModel_catalog G .twistedB2 0 2 s hs)
    · obtain ⟨s, -, hs⟩ := hs
      exact X.notCatalog
        (CFSG.Blueprint.lieModel_catalog G .PSU _ _ _ (Or.inl ⟨by decide, hs⟩))


theorem not_isExt_Ky (X : C4Data G c.S.M)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    {p : ℕ} (hN : t.PairNormalizerLe p) :
    ¬ CFSG.Quasithin.IsExt ↥t.Ky
        (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) := by
  intro hExt
  have hCent : Subgroup.centralizer (t.K49X : Set G) =
      Subgroup.centralizer ({t.y} : Set G) := by
    rw [K49X, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPC : CFSG.Quasithin.perfectCore
      (Subgroup.centralizer (t.K49X : Set G) ⊓ c.L) = t.Ky := by
    rw [hCent, inf_comm]
    rfl
  have hExt' := hExt
  rw [← hPC] at hExt'
  have hres := hK49 G t.K49H t.K49X t.K49L t.K49Q c.L t.K49X_le_H t.K49X_card
    (t.K49L_mem_oTwoComponentsIn hK32 hGA hSp)
    (t.isAlt_bar2_K49L hK32 hGA hSp hExt) t.K49X_not_le_normalizer_L
    (t.K49Q_eq_pCoreOf_H hK32 hGA hSp) rfl t.K49I_eq hExt'
  have hV_le_N : X.V ≤ t.d.N := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 X.le
      X.le_normalizer X.elemAbelian.isPGroup
  have hV_le_H : X.V ≤ t.K49H := hV_le_N.trans t.K49Q_le_H
  have hH_le_NV : t.K49H ≤ Subgroup.normalizer (X.V : Set G) :=
    t.K49H_le_M.trans X.le_normalizer
  have hVleOmega : X.V ≤
      CFSG.RankThree.PartOne.omegaOne 2 t.CQL :=
    (hres.2.2 (t.CQL_comm_or_pRank_one X hST hN hK32 hGA hSp)).2.2 2
      Nat.prime_two X.V hV_le_H hH_le_NV X.elemAbelian
  have homega_le : CFSG.RankThree.PartOne.omegaOne 2 t.CQL ≤ t.CQL :=
    (Subgroup.closure_le t.CQL).mpr fun _ hx => hx.1
  exact X.not_isTI (t.isTI_of_le_CQL hN (hVleOmega.trans homega_le)
    X.le_normalizer)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

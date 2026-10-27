module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3Hyp
public import CFSG.LocalAnalysis.WeakClosure81.W16QDCfg
public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certified


namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem w16q_iSub_UAOf_eq (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) :
    iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V)) (⊤ : Subgroup (VG (D.img H)))
        (vHat (D.img H)) =
      wHat (D.img H) (D.sp (conjClosure V₀ H)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G' : Subgroup (LGL 2 D.W) := D.img H
  let Γ : Set (Subgroup (LGL 2 D.W)) := D.conjImgFam V
  let VA : Subgroup (LGL 2 D.W) → Submodule (ZMod 2) D.W := D.conjImgSpace V₀ V
  let A0 : Subgroup (LGL 2 D.W) := D.img V
  let V' : Subgroup (VG G') := UAOf G' VA A0
  let E' : Subgroup (VG G') := vHat G'
  have hAssump : Assumption131 G' Γ VA (mRank A0) :=
    Cex16.assumption131_iSub16 d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min.fam16
      d.cfg.not_le D
  have hrank : ∀ B ∈ Γ, mRank B ≤ mRank A0 :=
    Cex16.mRank_le_iSub16 d.cfg.cex d.cfg.min.fam16 D
  have hA0 : A0 ∈ Γ := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hV_le_H : V ≤ H := d.cfg.cex.V_le_S.trans d.cfg.min.fam16.1
  have hconj_le : ∀ x ∈ H, conjSubgroup V x ≤ H := by
    intro x hx y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x * y * x⁻¹ ∈ H := hV_le_H hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hx) h1) hx
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h2
  have htrans : ∀ B ∈ Γ, ∀ B' ∈ Γ, ∃ g ∈ G', B' = cj g B := by
    rintro B ⟨x, hxH, rfl⟩ B' ⟨y, hyH, rfl⟩
    refine ⟨D.ρ ⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩,
      D.mem_img.2 ⟨_, H.mul_mem (H.inv_mem hyH) hxH, rfl⟩, ?_⟩
    have hcoej : ((⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩ : ↥H) : G) = y⁻¹ * x := rfl
    rw [D.img_conj (hconj_le x hxH) ⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩,
      conjSubgroup_conjSubgroup, hcoej]
    congr 1
    congr 1
    group
  have hIsub : iSub V' ⊤ E' = ⨆ B ∈ Γ, wHat G' (VA B) :=
    (thirteen_two_three hAssump hrank htrans hA0).2
  have hInorm : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hV0_le_I : V₀ ≤ iSub16 V H := le_sup_right.trans d.cfg.le_iSub16
  have hI0_le_I : conjClosure V₀ H ≤ iSub16 V H :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hInorm hh) z).1 (hV0_le_I hz)
  have key : ∀ x ∈ conjClosure V₀ H,
      SemidirectProduct.inl (Multiplicative.ofAdd (D.ι x)) ∈
        ⨆ B ∈ Γ, wHat G' (VA B) := by
    intro x hx
    rw [conjClosure] at hx
    refine Subgroup.closure_induction
      (p := fun z _ => SemidirectProduct.inl (Multiplicative.ofAdd (D.ι z)) ∈
        ⨆ B ∈ Γ, wHat G' (VA B)) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨h, hh, z0, hz0, rfl⟩
      have hzI : h * z0 * h⁻¹ ∈ iSub16 V H :=
        (Subgroup.mem_normalizer_iff.mp (hInorm hh) z0).1 (hV0_le_I hz0)
      have hmem : h * z0 * h⁻¹ ∈ conjSubgroup V₀ h⁻¹ :=
        mem_conjSubgroup_iff.mpr (by
          have hh0 : h⁻¹ * (h * z0 * h⁻¹) * h⁻¹⁻¹ = z0 := by group
          rwa [hh0])
      have hB : D.img (conjSubgroup V h⁻¹) ∈ Γ := ⟨h⁻¹, H.inv_mem hh, rfl⟩
      have hle : wHat G' (VA (D.img (conjSubgroup V h⁻¹))) ≤
          ⨆ B ∈ Γ, wHat G' (VA B) := le_iSup₂_of_le _ hB le_rfl
      refine hle (mem_wHat.mpr ⟨D.ι (h * z0 * h⁻¹), ?_, rfl⟩)
      show D.ι (h * z0 * h⁻¹) ∈ D.conjImgSpace V₀ V (D.img (conjSubgroup V h⁻¹))
      rw [ModDataE.conjImgSpace]
      exact (le_iSup (fun x :
          {x : G // x ∈ H ∧ D.img (conjSubgroup V x) = D.img (conjSubgroup V h⁻¹)} =>
        D.sp (conjSubgroup V₀ x.1)) ⟨h⁻¹, H.inv_mem hh, rfl⟩)
        (D.mem_sp.mpr ⟨h * z0 * h⁻¹, ⟨hmem, hzI⟩, rfl⟩)
    · rw [D.ι_one, ofAdd_zero, map_one]
      exact one_mem _
    · intro y z hy hz ihy ihz
      rw [D.ι_mul y (hI0_le_I hy) z (hI0_le_I hz), ofAdd_add, map_mul]
      exact mul_mem ihy ihz
    · intro y hy ihy
      rw [D.ι_inv (hI0_le_I hy), ofAdd_neg, map_inv]
      exact inv_mem ihy
  rw [hIsub]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun B hB => wHat_mono ?_
    refine iSup_le fun x => D.sp_mono ?_
    exact conjSubgroup_le_conjClosure V₀ H x.2.1
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_wHat.mp hx
    obtain ⟨e, he, rfl⟩ := hw
    exact key e he.1

theorem w16q_card_wHat (D : ModDataE H (iSub16 V H)) (W : Submodule (ZMod 2) D.W) :
    Nat.card ↥(wHat (D.img H) W) = Nat.card ↥W := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun w : ↥W =>
      (⟨SemidirectProduct.inl (Multiplicative.ofAdd (w : D.W)),
        mem_wHat.mpr ⟨(w : D.W), w.2, rfl⟩⟩ : ↥(wHat (D.img H) W))) ?_)).symm
  constructor
  · intro a b hab
    have h1 : (Multiplicative.ofAdd (a : D.W) : Multiplicative D.W)
        = Multiplicative.ofAdd (b : D.W) :=
      SemidirectProduct.inl_injective (Subtype.ext_iff.mp hab)
    exact Subtype.ext (Multiplicative.ofAdd.injective h1)
  · intro x
    obtain ⟨w, hw, hwx⟩ := mem_wHat.mp x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx.symm⟩

theorem w16q_card_sp (D : ModDataE H (iSub16 V H)) (S : Subgroup G) :
    Nat.card ↥(D.sp S) = Nat.card ↥(S ⊓ iSub16 V H) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : ↥(S ⊓ iSub16 V H) =>
      (⟨D.ι (e : G), D.mem_sp.mpr ⟨(e : G), e.2, rfl⟩⟩ : ↥(D.sp S))) ?_).symm
  constructor
  · intro a b hab
    exact Subtype.ext (D.ι_injOn a.2.2 b.2.2 (Subtype.ext_iff.mp hab))
  · intro w
    obtain ⟨e, he, hwe⟩ := D.mem_sp.mp w.2
    exact ⟨⟨e, he⟩, Subtype.ext hwe⟩

theorem w16q_card_iSub_UAOf (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) :
    Nat.card ↥(iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
        (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) =
      Nat.card ↥(conjClosure V₀ H) := by
  have hI0_le_I : conjClosure V₀ H ≤ iSub16 V H :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hh) z).1
        ((le_sup_right.trans d.cfg.le_iSub16) hz)
  rw [w16q_iSub_UAOf_eq d D, w16q_card_wHat D, w16q_card_sp D, inf_eq_left.mpr hI0_le_I]

theorem w16q_inf_iSub_UAOf (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) :
    UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V) ⊓
        iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) =
      wHat (D.img H) (D.sp V₀) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G' : Subgroup (LGL 2 D.W) := D.img H
  let Γ : Set (Subgroup (LGL 2 D.W)) := D.conjImgFam V
  let VA : Subgroup (LGL 2 D.W) → Submodule (ZMod 2) D.W := D.conjImgSpace V₀ V
  let A0 : Subgroup (LGL 2 D.W) := D.img V
  let V' : Subgroup (VG G') := UAOf G' VA A0
  let E' : Subgroup (VG G') := vHat G'
  have hHyp : SevenK.Hyp716 V' ⊤ E' :=
    IsMinFam16.hyp716_UAOf_img d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min d.cfg.not_le D
  have hAssump : Assumption131 G' Γ VA (mRank A0) :=
    Cex16.assumption131_iSub16 d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min.fam16
      d.cfg.not_le D
  have hΓV : A0 ∈ Γ := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hinf : V' ⊓ pCoreOf 2 (⊤ : Subgroup (VG G')) = wHat G' (VA A0) :=
    inf_pCoreOf_UAOf hAssump hΓV
  have hVA_eq : VA A0 = D.sp V₀ :=
    Cex16.conjImgSpace_img_eq d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min.fam16
      d.cfg.not_le D
  have hwHat_le_iSub : wHat G' (VA A0) ≤ iSub V' ⊤ E' := by
    rw [← hinf]
    exact le_iSup₂_of_le V' hHyp.mem le_rfl
  have hiSub_le_pcore : iSub V' ⊤ E' ≤ pCoreOf 2 (⊤ : Subgroup (VG G')) := by
    unfold iSub
    exact iSup_le fun U => iSup_le fun _ => inf_le_right
  have h1 : V' ⊓ iSub V' ⊤ E' = V' ⊓ pCoreOf 2 (⊤ : Subgroup (VG G')) :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans hiSub_le_pcore))
      (le_inf inf_le_left (hinf.le.trans hwHat_le_iSub))
  rw [h1, hinf, hVA_eq]

theorem w16q_card_inf_iSub_UAOf (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) :
    Nat.card ↥(UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V) ⊓
        iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) =
      Nat.card ↥V₀ := by
  have hV0_le_I : V₀ ≤ iSub16 V H := le_sup_right.trans d.cfg.le_iSub16
  rw [w16q_inf_iSub_UAOf d D, w16q_card_wHat D, w16q_card_sp D, inf_eq_left.mpr hV0_le_I]

theorem w16q_exists_theta (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H))
    (hfaith : conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H) :
    ∃ θ : X ≃* ↥(D.img (conjClosure V H)),
      ∀ k : ↥(conjClosure V H), θ (φ k) =
        (⟨D.ρ (Subgroup.inclusion d.cfg.conjClosure_le_H k),
          D.mem_img.mpr ⟨Subgroup.inclusion d.cfg.conjClosure_le_H k, by
            simpa using k.2, rfl⟩⟩ : ↥(D.img (conjClosure V H))) := by
  classical
  let K := conjClosure V H
  let I := iSub16 V H
  have hKH : K ≤ H := d.cfg.conjClosure_le_H
  have hIK : I ≤ K := d.cfg.iSub16_le_conjClosure
  have hIea : IsElemAbelian 2 I :=
    Cex16.isElemAbelian_iSub16 d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hKinfC : K ⊓ centralizer (I : Set G) = I := by
    refine le_antisymm hfaith ?_
    refine le_inf hIK ?_
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact B2F.isElemAbelian_comm hIea hj hi
  let ρK : ↥K →* ↥(D.img K) :=
    (D.ρ.comp (Subgroup.inclusion hKH)).codRestrict (D.img K) fun k =>
      D.mem_img.mpr ⟨Subgroup.inclusion hKH k, by simpa using k.2, rfl⟩
  have hker_ρK : ρK.ker = I.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have hρ : D.ρ (Subgroup.inclusion hKH k) = 1 := congrArg Subtype.val hk
      have hmem : (Subgroup.inclusion hKH k : G) ∈ centralizer (I : Set G) :=
        (D.ρ_eq_one_iff (Subgroup.inclusion hKH k)).mp hρ
      have hinf : (Subgroup.inclusion hKH k : G) ∈ K ⊓ centralizer (I : Set G) :=
        ⟨by simpa using k.2, hmem⟩
      rwa [hKinfC] at hinf
    · intro hk
      apply Subtype.ext
      exact (D.ρ_eq_one_iff (Subgroup.inclusion hKH k)).mpr (by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact B2F.isElemAbelian_comm hIea hj hk)
  have hker_φ : φ.ker = I.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact d.bar.ker_iff k
  let θ : X →* ↥(D.img K) :=
    (MonoidHom.liftOfSurjective φ d.bar.surjective) ⟨ρK, by rw [hker_φ, hker_ρK]⟩
  have hcomp : θ.comp φ = ρK := by
    simpa [θ, MonoidHom.liftOfSurjective] using
      MonoidHom.liftOfRightInverse_comp (f := φ)
        (f_inv := Function.surjInv d.bar.surjective)
        (Function.rightInverse_surjInv d.bar.surjective) ⟨ρK, by rw [hker_φ, hker_ρK]⟩
  have hθφ : ∀ k, θ (φ k) = ρK k := fun k => DFunLike.congr_fun hcomp k
  have hθ_surj : Function.Surjective θ := by
    intro y
    obtain ⟨j, hjK, hjρ⟩ := D.mem_img.mp y.2
    refine ⟨φ ⟨(j : G), hjK⟩, ?_⟩
    rw [hθφ]
    apply Subtype.ext
    show D.ρ (Subgroup.inclusion hKH ⟨(j : G), hjK⟩) = (y : LGL 2 D.W)
    have hincl : Subgroup.inclusion hKH ⟨(j : G), hjK⟩ = j := Subtype.ext rfl
    rw [hincl]
    exact hjρ
  have hker_θ : θ.ker = ⊥ := by
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := d.bar.surjective x
      rw [hθφ] at hx
      have hk : k ∈ I.subgroupOf K := by rw [← hker_ρK]; exact hx
      rw [← hker_φ] at hk
      exact hk
    · intro hx; rw [hx]; exact map_one θ
  have hθ_inj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hker_θ
  refine ⟨MulEquiv.ofBijective θ ⟨hθ_inj, hθ_surj⟩, ?_⟩
  intro k
  exact hθφ k

theorem w16q_isExtraspecial_of_mulEquiv {p : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) [h : CFSG.IsExtraspecial p A] : CFSG.IsExtraspecial p B where
  center_order_p := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.IsExtraspecial.center_order_p p A
  quotient_elementary_abelian := by
    haveI := CFSG.IsExtraspecial.quotient_elementary_abelian p A
    exact CFSG.IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
        (Subgroup.map_center_eq e)) inferInstance
  quotient_nontrivial := by
    haveI := CFSG.IsExtraspecial.quotient_nontrivial p A
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm.surjective.nontrivial

end DichCfg

theorem w16q_oddCoreCenter_le_center {X : Type} [Group X] [Finite X] {Y : Subgroup X} {p : ℕ}
    (h : Heis2p X Y p) : oddCoreCenter X ≤ Subgroup.center X := by
  intro z hz
  obtain ⟨w, hwcenter, hwz⟩ := Subgroup.mem_map.mp hz
  have hz_eq : z = (w : X) := hwz.symm
  have hcent : ∀ m ∈ fusionOddCore X, z * m = m * z := by
    intro m hm
    rw [hz_eq]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwcenter ⟨m, hm⟩).symm
  have hY : Y ≤ Subgroup.centralizer ({z} : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hv1 : v = 1
    · rw [hv1]; simp
    · exact (h.inv_center hv hv1).2 z hz
  have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    rw [← h.sup_eq]
    exact sup_le hY fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcent m hm).symm
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top x))

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

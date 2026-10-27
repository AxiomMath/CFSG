module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
import CFSG.LocalAnalysis.StandardType.FF81.CentAFrameAut
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelLevi
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

private theorem caInv_liftSub_conj_mem {m : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}
    {K L : Subgroup (GL (BlkIdx 1 m) (ZMod 2))}
    (hn : ∀ g ∈ L, ∀ u ∈ K, g * u * g⁻¹ ∈ K) :
    ∀ y ∈ liftSub φ L, ∀ u ∈ liftSub φ K, y * u * y⁻¹ ∈ liftSub φ K := by
  intro y hy u hu
  obtain ⟨hyY, hyK⟩ := mem_liftSub.mp hy
  obtain ⟨huY, huK⟩ := mem_liftSub.mp hu
  have hY : y * u * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hyY huY) (Y.inv_mem hyY)
  refine mem_liftSub.mpr ⟨hY, ?_⟩
  have hmap : φ ⟨y * u * y⁻¹, hY⟩ =
      φ ⟨y, hyY⟩ * φ ⟨u, huY⟩ * (φ ⟨y, hyY⟩)⁻¹ := by
    change φ (⟨y, hyY⟩ * ⟨u, huY⟩ * ⟨y, hyY⟩⁻¹) =
      φ ⟨y, hyY⟩ * φ ⟨u, huY⟩ * (φ ⟨y, hyY⟩)⁻¹
    simp only [map_mul, map_inv]
  rw [hmap]
  exact hn (φ ⟨y, hyY⟩) hyK (φ ⟨u, huY⟩) huK

theorem le_liftSub_uSub_of_invariant (hS : CentASetting m Y L R b t φ) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXH : X ≤ Subgroup.centralizer ({t} : Set G))
    (hXn : ∀ y ∈ liftSub φ (Cent 1 m), ∀ x ∈ X, y * x * y⁻¹ ∈ X) :
    X ≤ liftSub φ (uSub 1 m) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := by
    rcases hS.m_cases with hm | hm
    · exact ⟨4, by omega⟩
    · exact ⟨5, by omega⟩
  have hk4 : 4 ≤ k := by
    rcases hS.m_cases with hm | hm <;> omega
  let CY : Subgroup G := liftSub φ (Cent 1 (k + 2))
  let U : Subgroup G := liftSub φ (uSub 1 (k + 2))
  let Xt : Subgroup G := X ⊔ U
  let T : Subgroup G := Xt ⊓ Subgroup.normalizer (U : Set G)
  have hcardU : Nat.card U = Nat.card (uSub 1 (k + 2)) := by
    change Nat.card (Subgroup.map Y.subtype
      (Subgroup.map φ.symm.toMonoidHom (uSub 1 (k + 2)))) = Nat.card (uSub 1 (k + 2))
    rw [Subgroup.card_map_of_injective
      (K := Subgroup.map φ.symm.toMonoidHom (uSub 1 (k + 2))) Y.subtype_injective]
    rw [Subgroup.card_map_of_injective (K := uSub 1 (k + 2)) φ.symm.injective]
  have hU2 : IsPGroup 2 U :=
    IsPGroup.of_card (hcardU.trans (card_uSub 1 (k + 2)))
  have hU_le_CY : U ≤ CY := liftSub_mono (uSub_le_cent 1 (k + 2))
  have hCY_le_NX : CY ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff.mpr hXn
  have hU_le_NX : U ≤ Subgroup.normalizer (X : Set G) := hU_le_CY.trans hCY_le_NX
  have hCY_N_U : CY ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff.mpr
      (caInv_liftSub_conj_mem (normal_uSub 1 (k + 2)))
  have hCY_le_H : CY ≤ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_liftSub_cent hS).mp hy).2
  have hU_le_H : U ≤ Subgroup.centralizer ({t} : Set G) := hU_le_CY.trans hCY_le_H
  have hXt2 : IsPGroup 2 Xt := hX2.to_sup_of_normal_left' hU2 hU_le_NX
  have hXt_le_H : Xt ≤ Subgroup.centralizer ({t} : Set G) := sup_le hXH hU_le_H
  have hCY_N_Xt : CY ≤ Subgroup.normalizer (Xt : Set G) :=
    (le_inf hCY_le_NX hCY_N_U).trans (Subgroup.inf_normalizer_le_normalizer_sup X U)
  have hCY_N_NU : CY ≤
      Subgroup.normalizer ((Subgroup.normalizer (U : Set G)) : Set G) :=
    fun y hy => Subgroup.le_normalizer (hCY_N_U hy)
  have hCY_N_T : CY ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hCY_N_Xt hCY_N_NU).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Xt)
        (K := Subgroup.normalizer (U : Set G)))
  have hClaimA : T ⊓ Subgroup.centralizer ({bStarG φ} : Set G) ≤ Y := by
    intro x hx
    have hxT : x ∈ T := hx.1
    have hxCb : x ∈ Subgroup.centralizer ({bStarG φ} : Set G) := hx.2
    have hxXt : x ∈ Xt := hxT.1
    have hxNU : x ∈ Subgroup.normalizer (U : Set G) := hxT.2
    have hxCt : x ∈ Subgroup.centralizer ({t} : Set G) := hXt_le_H hxXt
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxCt
    have hxNl : x ∈ Subgroup.normalizer (lStar φ : Set G) :=
      centralizer_bStarG_le_normalizer hS hxCb
    let Lt : Subgroup G := lStar φ ⊓ Subgroup.centralizer ({t} : Set G)
    let D : Subgroup G := T ⊓ Lt
    have hD_le_T : D ≤ T := inf_le_left
    have hD_le_Lt : D ≤ Lt := inf_le_right
    have hD2 : IsPGroup 2 D := hXt2.to_le (hD_le_T.trans inf_le_left)
    have hnD : ∀ g ∈ Lt, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
      intro g hg d hd
      have hgL : g ∈ lStar φ := hg.1
      have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      have hgCY : g ∈ CY := (mem_liftSub_cent hS).mpr ⟨liftSub_le _ hgL, hgt⟩
      refine ⟨?_, ?_, ?_⟩
      · exact Subgroup.le_normalizer_iff.mp hCY_N_T g hgCY d hd.1
      · exact Subgroup.le_normalizer_iff.mp (Subgroup.le_normalizer (H := lStar φ))
          g hgL d hd.2.1
      · exact Subgroup.le_normalizer_iff.mp
          (Subgroup.le_normalizer (H := Subgroup.centralizer ({t} : Set G)))
          g hg.2 d hd.2.2
    have hD_le_uStar : D ≤ uStar φ :=
      le_uStar_of_isPGroup_of_normal hS D hD_le_Lt hD2 hnD
    have hc : ∀ g ∈ lStar φ, g * t = t * g → x * g * x⁻¹ * g⁻¹ ∈ uStar φ := by
      intro g hgL hgt
      have hgCY : g ∈ CY := (mem_liftSub_cent hS).mpr ⟨liftSub_le _ hgL, hgt⟩
      have hgCt : g ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hgt
      have hgxgT : g * x⁻¹ * g⁻¹ ∈ T :=
        Subgroup.le_normalizer_iff.mp hCY_N_T g hgCY x⁻¹ (T.inv_mem hxT)
      have hmemT : x * g * x⁻¹ * g⁻¹ ∈ T := by
        simpa only [mul_assoc] using T.mul_mem hxT hgxgT
      have hxgxL : x * g * x⁻¹ ∈ lStar φ :=
        (Subgroup.mem_normalizer_iff.mp hxNl g).mp hgL
      have hmemL : x * g * x⁻¹ * g⁻¹ ∈ lStar φ :=
        (lStar φ).mul_mem hxgxL ((lStar φ).inv_mem hgL)
      have hmemC : x * g * x⁻¹ * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
        (Subgroup.centralizer ({t} : Set G)).mul_mem
          ((Subgroup.centralizer ({t} : Set G)).mul_mem
            ((Subgroup.centralizer ({t} : Set G)).mul_mem hxCt hgCt)
            ((Subgroup.centralizer ({t} : Set G)).inv_mem hxCt))
          ((Subgroup.centralizer ({t} : Set G)).inv_mem hgCt)
      exact hD_le_uStar ⟨hmemT, hmemL, hmemC⟩
    obtain ⟨a, haL, hconj⟩ := exists_mem_lStar_eq_conj hS hxNl hxt hc
    have haY : a ∈ Y := liftSub_le _ haL
    let z : G := a⁻¹ * x
    have hzCb : z ∈ Subgroup.centralizer ({bStarG φ} : Set G) :=
      (Subgroup.centralizer ({bStarG φ} : Set G)).mul_mem
        ((Subgroup.centralizer ({bStarG φ} : Set G)).inv_mem
          (lStar_le_centralizer hS haL)) hxCb
    have hzCl : z ∈ Subgroup.centralizer (lStar φ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hzconj : z * h * z⁻¹ = h := by
        calc z * h * z⁻¹ = a⁻¹ * (x * h * x⁻¹) * a := by
              simp only [z]
              group
          _ = a⁻¹ * (a * h * a⁻¹) * a := by rw [hconj h hh]
          _ = h := by group
      calc h * z = (z * h * z⁻¹) * z := by rw [hzconj]
        _ = z * h := by group
    have hz_sup : z ∈ R ⊔ Subgroup.zpowers (bStarG φ) :=
      centralizer_bStarG_inf_le hS ⟨hzCb, hzCl⟩
    have hbY : bStarG φ ∈ Y := liftSub_le _ (bStarG_mem hS).2
    have hconjR : ∀ r ∈ R, MulAut.conj (bStarG φ) r = r := by
      intro r hr
      have hcomm : bStarG φ * r = r * bStarG φ :=
        Subgroup.mem_centralizer_iff.mp (hS.rad_le hr) (bStarG φ) hbY
      show bStarG φ * r * (bStarG φ)⁻¹ = r
      rw [hcomm]
      group
    have hbN_R : bStarG φ ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      ext r
      constructor
      · rintro ⟨s, hs, rfl⟩
        change (MulAut.conj (bStarG φ)) s ∈ R
        rw [hconjR s hs]
        exact hs
      · intro hr
        exact ⟨r, hr, hconjR r hr⟩
    have hzpow_le_NR : Subgroup.zpowers (bStarG φ) ≤
        Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hbN_R
    have hz_mul : z ∈ (R : Set G) * (Subgroup.zpowers (bStarG φ) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R
        (Subgroup.zpowers (bStarG φ)) hzpow_le_NR]
      exact hz_sup
    obtain ⟨r, hr, s, hs, hzs⟩ := hz_mul
    have hsY : s ∈ Y := (Subgroup.zpowers_le.mpr hbY) hs
    have hcomm_ra : Commute r a :=
      (Subgroup.mem_centralizer_iff.mp (hS.rad_le hr) a haY).symm
    have hcomm_rs : Commute r s :=
      (Subgroup.mem_centralizer_iff.mp (hS.rad_le hr) s hsY).symm
    have hcomm_ry0 : Commute r (a * s) := hcomm_ra.mul_right hcomm_rs
    have hx_eq : x = r * (a * s) := by
      calc x = a * z := by simp only [z]; group
        _ = a * (r * s) := by rw [← hzs]
        _ = r * (a * s) := by rw [← mul_assoc, ← hcomm_ra.eq, mul_assoc]
    obtain ⟨n, hnpow⟩ := hXt2.exists_pow_pow_eq_one ⟨x, hxXt⟩
    have hxpow : x ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hnpow
    have hpow_mul : r ^ 2 ^ n * (a * s) ^ 2 ^ n = 1 := by
      have h := hxpow
      rw [hx_eq, hcomm_ry0.mul_pow (2 ^ n)] at h
      exact h
    have hrpow_eq : r ^ 2 ^ n = ((a * s) ^ 2 ^ n)⁻¹ :=
      eq_inv_of_mul_eq_one_left hpow_mul
    have hy0Y : a * s ∈ Y := Y.mul_mem haY hsY
    have hrmemY : r ^ 2 ^ n ∈ Y := by
      rw [hrpow_eq]
      exact Y.inv_mem (Y.pow_mem hy0Y _)
    have hrmemR : r ^ 2 ^ n ∈ R := R.pow_mem hr _
    have hone : r ^ 2 ^ n = 1 := by
      refine eq_one_of_forall_commute_of_mem φ hrmemY ?_
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hS.rad_le hrmemR) g hg).symm
    have hodd_r : Odd (orderOf r) :=
      hS.rad_odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hr)
    have hdvd : orderOf r ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hone
    have hcop : Nat.Coprime (orderOf r) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd_r)
    have hr1 : r = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    rw [hx_eq, hr1, one_mul]
    exact hy0Y
  have hClaimB : T ⊓ Subgroup.centralizer ({bStarG φ} : Set G) ≤ U := by
    let K : Subgroup G := T ⊓ Subgroup.centralizer ({bStarG φ} : Set G)
    have hKY : K ≤ Y := hClaimA
    let D : Subgroup (GL (BlkIdx 1 (k + 2)) (ZMod 2)) :=
      (K.subgroupOf Y).map φ.toMonoidHom
    have hbY : bStarG φ ∈ Y := liftSub_le _ (bStarG_mem hS).2
    have hbmap : φ ⟨bStarG φ, hbY⟩ = bStar (k + 2) := by
      simpa only [bStarG] using φ.apply_symm_apply (bStar (k + 2))
    have hD_le : D ≤ Cent 1 (k + 2) ⊓
        Subgroup.centralizer ({bStar (k + 2)} : Set (GL (BlkIdx 1 (k + 2)) (ZMod 2))) := by
      intro d hd
      obtain ⟨y, hyKsub, rfl⟩ := Subgroup.mem_map.mp hd
      have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hyKsub
      have hyXt : (y : G) ∈ Xt := hyK.1.1
      have hyt : (y : G) * t = t * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hXt_le_H hyXt)
      have hyCY : (y : G) ∈ CY := (mem_liftSub_cent hS).mpr ⟨y.2, hyt⟩
      have hyCent : φ y ∈ Cent 1 (k + 2) := (mem_liftSub.mp hyCY).2
      have hyb : (y : G) * bStarG φ = bStarG φ * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyK.2
      have hcomm : φ y * φ ⟨bStarG φ, hbY⟩ = φ ⟨bStarG φ, hbY⟩ * φ y := by
        have h1 : φ (y * ⟨bStarG φ, hbY⟩) = φ (⟨bStarG φ, hbY⟩ * y) := by
          congr 1
          exact Subtype.ext hyb
        simpa only [map_mul] using h1
      have hcommC : φ y ∈
          Subgroup.centralizer ({bStar (k + 2)} : Set _) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa only [hbmap] using hcomm
      exact ⟨hyCent, hcommC⟩
    have hK_le_Xt : K ≤ Xt := fun x hx => hx.1.1
    have hK2 : IsPGroup 2 K := hXt2.to_le hK_le_Xt
    have hcardD : Nat.card D = Nat.card (K.subgroupOf Y) :=
      Subgroup.card_map_of_injective φ.injective
    have hcardD' : Nat.card D = Nat.card K := by
      rw [hcardD, natCard_subgroupOf_eq K Y hKY]
    obtain ⟨nD, hnD⟩ := hK2.exists_card_eq
    have hD2 : IsPGroup 2 D := IsPGroup.of_card (hcardD'.trans hnD)
    have hnDnorm : ∀ g ∈ Cent 1 (k + 2) ⊓
        Subgroup.centralizer ({bStar (k + 2)} : Set (GL (BlkIdx 1 (k + 2)) (ZMod 2))),
        ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
      intro g hg d hd
      obtain ⟨z, hzsub, rfl⟩ := Subgroup.mem_map.mp hd
      have hzK : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hzsub
      let y : ↥Y := φ.symm g
      have hgy : φ y = g := φ.apply_symm_apply g
      have hyt : (y : G) * t = t * (y : G) := by
        have hcomm : g * jGL 1 (k + 2) = jGL 1 (k + 2) * g :=
          Subgroup.mem_centralizer_singleton_iff.mp hg.1
        have hcomm' : φ y * φ ⟨t, hS.t_mem⟩ = φ ⟨t, hS.t_mem⟩ * φ y := by
          simpa only [← hgy, ← hS.φ_t] using hcomm
        have hsub : y * ⟨t, hS.t_mem⟩ = ⟨t, hS.t_mem⟩ * y :=
          φ.injective (by simpa only [map_mul] using hcomm')
        simpa using congrArg Subtype.val hsub
      have hyb : (y : G) * bStarG φ = bStarG φ * (y : G) := by
        have hcomm : φ y * φ ⟨bStarG φ, hbY⟩ = φ ⟨bStarG φ, hbY⟩ * φ y := by
          simpa only [hgy, hbmap] using
            (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
        have hsub : y * ⟨bStarG φ, hbY⟩ = ⟨bStarG φ, hbY⟩ * y :=
          φ.injective (by simpa only [map_mul] using hcomm)
        simpa using congrArg Subtype.val hsub
      have hyCY : (y : G) ∈ CY := (mem_liftSub_cent hS).mpr ⟨y.2, hyt⟩
      have hwT : (y : G) * (z : G) * (y : G)⁻¹ ∈ T :=
        Subgroup.le_normalizer_iff.mp hCY_N_T (y : G) hyCY (z : G) hzK.1
      have hybC : (y : G) ∈ Subgroup.centralizer ({bStarG φ} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hyb
      have hwCb : (y : G) * (z : G) * (y : G)⁻¹ ∈
          Subgroup.centralizer ({bStarG φ} : Set G) :=
        (Subgroup.centralizer ({bStarG φ} : Set G)).mul_mem
          ((Subgroup.centralizer ({bStarG φ} : Set G)).mul_mem hybC hzK.2)
          ((Subgroup.centralizer ({bStarG φ} : Set G)).inv_mem hybC)
      have hwK : (y : G) * (z : G) * (y : G)⁻¹ ∈ K := ⟨hwT, hwCb⟩
      refine Subgroup.mem_map.mpr ⟨⟨_, hKY hwK⟩, Subgroup.mem_subgroupOf.mpr hwK, ?_⟩
      rw [← hgy]
      conv_lhs => rw [show (⟨_, hKY hwK⟩ : ↥Y) = y * z * y⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom]
    have hD_le_uSub : D ≤ uSub 1 (k + 2) :=
      le_uSub_of_normal_centBStar (by omega) D hD_le hD2 hnDnorm
    intro x hx
    have hxK : x ∈ K := hx
    refine mem_liftSub.mpr ⟨hKY hxK, hD_le_uSub ?_⟩
    exact Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.mem_subgroupOf.mpr hxK)
  have hUT : U ≤ T := le_inf le_sup_right (Subgroup.le_normalizer)
  have hT_le_NU : T ≤ Subgroup.normalizer (U : Set G) := inf_le_right
  have hL_le_CY : L ≤ CY := by
    rw [← liftSub_leviB hS]
    exact liftSub_mono (leviB_le_cent (k + 2))
  obtain ⟨P, hPL, hbP, hPiso⟩ := exists_sl3_bStarG hS
  have hP_le_NT : P ≤ Subgroup.normalizer (T : Set G) :=
    hPL.trans (hL_le_CY.trans hCY_N_T)
  have hP_le_NU : P ≤ Subgroup.normalizer (U : Set G) :=
    hPL.trans (hL_le_CY.trans hCY_N_U)
  have hT2 : IsPGroup 2 T := hXt2.to_le inf_le_left
  have hsol : IsSolvable ↥T := by
    haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hfix : ∀ x ∈ T, bStarG φ * x * (bStarG φ)⁻¹ * x⁻¹ ∈ U → x ∈ U := by
    intro x hxT hcommU
    have hxN_U : x ∈ Subgroup.normalizer (U : Set G) := hT_le_NU hxT
    have hbN_U : ∀ n ∈ U, bStarG φ * n * (bStarG φ)⁻¹ ∈ U := by
      intro n hn
      exact Subgroup.le_normalizer_iff.mp hCY_N_U (bStarG φ) (bStarG_mem hS).2 n hn
    have hg : x⁻¹ * (bStarG φ * x * (bStarG φ)⁻¹) ∈ U := by
      have hxinvN : x⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        Subgroup.inv_mem _ hxN_U
      have h := (Subgroup.mem_normalizer_iff.mp hxinvN
        (bStarG φ * x * (bStarG φ)⁻¹ * x⁻¹)).mp hcommU
      have heq : x⁻¹ * (bStarG φ * x * (bStarG φ)⁻¹ * x⁻¹) * x =
          x⁻¹ * (bStarG φ * x * (bStarG φ)⁻¹) := by group
      have h' : x⁻¹ * (bStarG φ * x * (bStarG φ)⁻¹ * x⁻¹) * x ∈ U := by
        simpa using h
      rwa [heq] at h'
    have hcop : Nat.Coprime (orderOf (bStarG φ)) (Nat.card U) := by
      rw [orderOf_bStarG hS, hcardU, card_uSub 1 (k + 2)]
      exact Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
    obtain ⟨n, hnU, hfixn⟩ :=
      CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime U hbN_U hg hcop
    have hxnT : x * n ∈ T := T.mul_mem hxT (hUT hnU)
    have hxnCb : x * n ∈ Subgroup.centralizer ({bStarG φ} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x * n) * bStarG φ = (bStarG φ * (x * n) * (bStarG φ)⁻¹) * bStarG φ := by
            rw [hfixn]
        _ = bStarG φ * (x * n) := by group
    have hxnU : x * n ∈ U := hClaimB ⟨hxnT, hxnCb⟩
    have hx_eq : x = (x * n) * n⁻¹ := by group
    rw [hx_eq]
    exact U.mul_mem hxnU (U.inv_mem hnU)
  have hT_le_U : T ≤ U :=
    CFSG.StandardType.FrameRoute.FS81.le_of_l3TwoFixedPointFree hUT hT_le_NU hP_le_NT
      hP_le_NU hPiso hbP (orderOf_bStarG hS) hsol hfix
  have hT_eq_U : T = U := le_antisymm hT_le_U hUT
  have hXt_le_U : Xt ≤ U := by
    by_contra hnot
    have hU_le_Xt : U ≤ Xt := le_sup_right
    have hnorm : Subgroup.normalizer ((U.subgroupOf Xt) : Set ↥Xt) = U.subgroupOf Xt := by
      rw [← Subgroup.subgroupOf_normalizer_eq hU_le_Xt]
      rw [← Subgroup.inf_subgroupOf_left (Subgroup.normalizer (U : Set G)) Xt]
      rw [show Xt ⊓ Subgroup.normalizer (U : Set G) = T from rfl, hT_eq_U]
    have hlt : U.subgroupOf Xt < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hnot (Subgroup.subgroupOf_eq_top.mp htop)
    haveI : Group.IsNilpotent ↥Xt := hXt2.isNilpotent
    have hnc : NormalizerCondition ↥Xt :=
      Group.normalizerCondition_of_isNilpotent (G := ↥Xt)
    have hgrowth := hnc (U.subgroupOf Xt) hlt
    rw [hnorm] at hgrowth
    exact absurd hgrowth (lt_irrefl _)
  intro x hx
  exact hXt_le_U (Subgroup.mem_sup_left hx)

end CFSG.StandardType.FF81.CentA

end

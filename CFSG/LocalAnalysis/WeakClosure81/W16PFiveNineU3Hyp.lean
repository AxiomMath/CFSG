module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineHyp711
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem mul_conj_commutator_eq {Q : Type*} [Group Q] {i d v : Q} (hd : i * d = d * i) :
    i * (d * v) * i⁻¹ * (d * v)⁻¹ = d * (i * v * i⁻¹ * v⁻¹) * d⁻¹ := by
  have h1 : i * (d * v) = d * (i * v) := by
    rw [← mul_assoc, hd, mul_assoc]
  rw [h1]
  group

theorem Cex16.conjImgSpace_img_eq (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    D.conjImgSpace V₀ V (D.img V) = D.sp V₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Subgroup G := iSub16 V H
  have hV_le_H : V ≤ H := h.V_le_S.trans hF.1
  have hV0_le_V : V₀ ≤ V := h.hyp.h6.le
  have hV0_le_O : V₀ ≤ pCoreOf 2 H := Cex16.V₀_le_pCoreOf h5 hS h hF hV
  have hV0_le_I : V₀ ≤ I := (le_inf hV0_le_V hV0_le_O).trans (CFSG.Quasithin.le_conjClosure _ _)
  have hI_le_S : I ≤ S := (Cex16.iSub16_le_pCoreOf h hF).trans (h.pCoreOf_le_S h1 hS hF)
  have hU_le : U ≤ pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le.trans hV_le_H) ?_
      (B2F.isPGroup_of_isElemAbelian (h.hyp.h6.elemAbelian.mono h.le))
    exact hF.2.1.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hI_norm : ∀ x ∈ H, x ∈ Subgroup.normalizer (I : Set G) :=
    fun x hx => CFSG.Quasithin.le_normalizer_conjClosure _ _ hx
  have hcommI_V : ⁅I, V⁆ ≤ V₀ :=
    Subgroup.commutator_le.mpr fun s hs v hv => h.comm_mem_V₀ (hI_le_S hs) hv
  have hcomm_conj : ∀ x ∈ H, ⁅I, conjSubgroup V x⁆ = conjSubgroup ⁅I, V⁆ x := by
    intro x hx
    have hI_map : I.map (MulAut.conj x⁻¹).toMonoidHom = I :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hI_norm x hx)
    calc ⁅I, conjSubgroup V x⁆
        = ⁅I.map (MulAut.conj x⁻¹).toMonoidHom,
            V.map (MulAut.conj x⁻¹).toMonoidHom⁆ := by
            rw [hI_map]; rfl
      _ = (⁅I, V⁆).map (MulAut.conj x⁻¹).toMonoidHom :=
            (Subgroup.map_commutator (H₁ := I) (H₂ := V)
              (MulAut.conj x⁻¹).toMonoidHom).symm
      _ = conjSubgroup ⁅I, V⁆ x := rfl
  have hVnt : D.img V ≠ ⊥ := by
    intro hbot
    have hVcent : V ≤ Subgroup.centralizer (I : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have hρv : D.ρ (⟨v, hV_le_H hv⟩ : ↥H) = 1 := by
        have hmem : D.ρ (⟨v, hV_le_H hv⟩ : ↥H) ∈ D.img V :=
          D.mem_img.2 ⟨⟨v, hV_le_H hv⟩, hv, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      exact Subgroup.mem_centralizer_iff.1 ((D.ρ_eq_one_iff _).1 hρv) i hi
    have hVeq : V = U ⊔ V₀ := by
      rw [← Cex16.inf_centralizer_iSub16_eq h1 h5 hS h hF hV]
      exact le_antisymm (le_inf le_rfl hVcent) inf_le_left
    have hVleO : V ≤ pCoreOf 2 H := by
      rw [hVeq]
      exact sup_le hU_le hV0_le_O
    exact hV hVleO
  have hsingle : ∀ {x : G}, x ∈ H → D.img (conjSubgroup V x) = D.img V →
      conjSubgroup V₀ x = V₀ := by
    intro x hxH himg
    have hVcent : ¬ V ≤ Subgroup.centralizer (I : Set G) := by
      intro hc
      apply hVnt
      rw [eq_bot_iff]
      intro r hr
      obtain ⟨j, hj, rfl⟩ := D.mem_img.1 hr
      rw [Subgroup.mem_bot]
      exact (D.ρ_eq_one_iff j).2 (hc hj)
    have hex : ∃ v ∈ V, ∃ i ∈ I, i * v ≠ v * i := by
      by_contra hcon
      apply hVcent
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      by_contra hne
      exact hcon ⟨v, hv, i, hi, hne⟩
    obtain ⟨v, hv, i, hi, hvi⟩ := hex
    have hcomm_ne : i * v * i⁻¹ * v⁻¹ ≠ 1 := by
      intro h1
      apply hvi
      have h2 : i * v * i⁻¹ = v := mul_inv_eq_one.mp h1
      calc i * v = i * v * i⁻¹ * i := by group
        _ = v * i := by rw [h2]
    have hvρ_mem : D.ρ (⟨v, hV_le_H hv⟩ : ↥H) ∈ D.img (conjSubgroup V x) := by
      rw [himg]
      exact D.mem_img.2 ⟨⟨v, hV_le_H hv⟩, hv, rfl⟩
    obtain ⟨j, hjVx, hjρ⟩ := D.mem_img.1 hvρ_mem
    have hdjH : (j : G) * v⁻¹ ∈ H := H.mul_mem j.2 (H.inv_mem (hV_le_H hv))
    have hρjv : D.ρ (⟨(j : G) * v⁻¹, hdjH⟩ : ↥H) = 1 := by
      have he : (⟨(j : G) * v⁻¹, hdjH⟩ : ↥H) = j * (⟨v, hV_le_H hv⟩ : ↥H)⁻¹ := by
        ext; simp
      rw [he, map_mul, map_inv, hjρ, mul_inv_cancel]
    have hdC : (j : G) * v⁻¹ ∈ Subgroup.centralizer (I : Set G) :=
      (D.ρ_eq_one_iff _).1 hρjv
    have hdcomm : i * ((j : G) * v⁻¹) = ((j : G) * v⁻¹) * i :=
      Subgroup.mem_centralizer_iff.1 hdC i hi
    have hcommI : i * v * i⁻¹ * v⁻¹ ∈ V₀ := h.comm_mem_V₀ (hI_le_S hi) hv
    have hdcomm2 : (i * v * i⁻¹ * v⁻¹) * ((j : G) * v⁻¹) =
        ((j : G) * v⁻¹) * (i * v * i⁻¹ * v⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hdC _ (hV0_le_I hcommI)
    have hcomm_eq : i * (j : G) * i⁻¹ * (j : G)⁻¹ = i * v * i⁻¹ * v⁻¹ := by
      have h1 := mul_conj_commutator_eq (i := i) (d := (j : G) * v⁻¹) (v := v) hdcomm
      have hdv : ((j : G) * v⁻¹) * v = (j : G) := by group
      rw [hdv] at h1
      rw [h1, ← hdcomm2]
      group
    have hcommV0 : i * (j : G) * i⁻¹ * (j : G)⁻¹ ∈ V₀ := by
      rw [hcomm_eq]; exact hcommI
    have hcommV0x : i * (j : G) * i⁻¹ * (j : G)⁻¹ ∈ conjSubgroup V₀ x := by
      have hmem : i * (j : G) * i⁻¹ * (j : G)⁻¹ ∈ ⁅I, conjSubgroup V x⁆ :=
        Subgroup.commutator_mem_commutator hi hjVx
      rw [hcomm_conj x hxH] at hmem
      exact Subgroup.map_mono hcommI_V hmem
    refine conjSubgroup_eq_of_isTI h.hyp.isTI ?_
    intro hbot
    have h1 : i * (j : G) * i⁻¹ * (j : G)⁻¹ = 1 :=
      Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨hcommV0, hcommV0x⟩)
    exact hcomm_ne (hcomm_eq ▸ h1)
  rw [ModDataE.conjImgSpace]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨x, hxH, hxEq⟩
    rw [hsingle hxH hxEq]
  · have hle := le_iSup (fun x : {x : G // x ∈ H ∧ D.img (conjSubgroup V x) = D.img V} =>
      D.sp (conjSubgroup V₀ x.1)) ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
    simpa [conjSubgroup_one] using hle

theorem IsMinFam16.hyp716_UAOf_img (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    SevenK.Hyp716 (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
      (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G' : Subgroup (LGL 2 D.W) := D.img H
  let Γ : Set (Subgroup (LGL 2 D.W)) := D.conjImgFam V
  let VA : Subgroup (LGL 2 D.W) → Submodule (ZMod 2) D.W := D.conjImgSpace V₀ V
  let A : Subgroup (LGL 2 D.W) := D.img V
  let U' : Subgroup (VG G') := UAOf G' VA A
  let E' : Subgroup (VG G') := vHat G'
  have h131 : Assumption131 G' Γ VA (mRank A) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank : ∀ B ∈ Γ, mRank B ≤ mRank A := Cex16.mRank_le_iSub16 h hH.1 D
  have hVAle : ∀ B ∈ Γ, VA B ≤ fixSub B :=
    Cex16.conjImgSpace_le_fixSub_iSub16 h1 h5 hS h hH.1 hV D
  have hV_le_H : V ≤ H := h.V_le_S.trans hH.1.1
  have hconj_le : ∀ x ∈ H, conjSubgroup V x ≤ H := by
    intro x hx y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x * y * x⁻¹ ∈ H := hV_le_H hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hx) h1) hx
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h2
  have hA : A ∈ Γ := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
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
  have hΩ : omegaSet U' (⊤ : Subgroup (VG G')) E' = UAOf G' VA '' Γ :=
    (thirteen_two_three h131 hrank htrans hA).1
  have hE_norm : (E'.subgroupOf (⊤ : Subgroup (VG G'))).Normal :=
    (normal_vHat (G := G')).subgroupOf _
  have hOm : ∀ W ∈ omegaSet U' (⊤ : Subgroup (VG G')) E', W ≤ (⊤ : Subgroup (VG G')) :=
    fun _ _ => le_top
  haveI hK_normal : (kSub U' (⊤ : Subgroup (VG G')) E').Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
      (kSub_subgroupOf_normal (V := U') le_top hE_norm hOm)
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  change SevenK.Hyp716 U' (⊤ : Subgroup (VG G')) E'
  refine { toHyp73 := ?_, oddCore := ?_, transitive := ?_ }
  · exact
      { elemAbelian := (hyp7_UAOf h131 hrank hA (hVAle A hA)).1
        ti := (hyp7_UAOf h131 hrank hA (hVAle A hA)).2.2
        noncyclic := (hyp7_UAOf h131 hrank hA (hVAle A hA)).2.1
        abelian := (isElemAbelian_wHat (G := G') ⊤).1
        le := le_top
        normal := hE_norm
        mem := by rw [hΩ]; exact ⟨A, hA, rfl⟩
        omega_le := hOm
        iSub_le := le_rfl
        pcore_le := (iSub_le_pCoreOf_kSub le_top).trans
          (pCoreOf_kSub_le_pCoreOf (V := U') le_top hE_norm hOm)
        jnormal := iSub_subgroupOf_normal (V := U') le_top hE_norm }
  · exact fusionOddCoreOf_eq_bot_of_charTwo (charTwo_top_VG (V := D.W) (G := G')) _
  · intro W hW
    rw [hΩ] at hW
    obtain ⟨B, hB, rfl⟩ := hW
    obtain ⟨x, hxH, rfl⟩ := hB
    have hsup : S ⊔ conjClosure V H = H := IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
    have hK0_le_H : conjClosure V H ≤ H :=
      CFSG.Quasithin.conjClosure_le fun g hg z hz =>
        H.mul_mem (H.mul_mem hg (hV_le_H hz)) (H.inv_mem hg)
    have hS_le_NV : S ≤ Subgroup.normalizer (V : Set G) :=
      h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
    have hS_le_NK0 : S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
      hH.1.1.trans (CFSG.Quasithin.le_normalizer_conjClosure V H)
    have hx' : x ∈ (↑(S ⊔ conjClosure V H) : Set G) := by
      rw [hsup]; exact hxH
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S (conjClosure V H) hS_le_NK0] at hx'
    obtain ⟨s, hsS, k0, hk0K0, hsk⟩ := hx'
    have hk0H : k0 ∈ H := hK0_le_H hk0K0
    have hVs : conjSubgroup V s = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hS_le_NV hsS)
    have hconj_x : conjSubgroup V x = conjSubgroup V k0 := by
      rw [← hsk, ← conjSubgroup_conjSubgroup, hVs]
    let ρH : ↥H →* G' := D.ρ.codRestrict G' (fun j => D.mem_img.2 ⟨j, j.2, rfl⟩)
    let f : ↥H →* VG G' := (SemidirectProduct.inr : G' →* VG G').comp ρH
    let W0 : Subgroup G := ((kSub U' (⊤ : Subgroup (VG G')) E').comap f).map H.subtype
    have hK0_le_W0 : conjClosure V H ≤ W0 := by
      refine CFSG.Quasithin.conjClosure_le ?_
      intro g hg z hz
      have hHmem : g * z * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg (hV_le_H hz)) (H.inv_mem hg)
      refine Subgroup.mem_map.2 ⟨⟨g * z * g⁻¹, hHmem⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hgz : g * z * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have e : (g⁻¹) * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
        rw [e]; exact hz
      have hB : D.img (conjSubgroup V g⁻¹) ∈ Γ := ⟨g⁻¹, H.inv_mem hg, rfl⟩
      have hUB : UAOf G' VA (D.img (conjSubgroup V g⁻¹)) ∈
          omegaSet U' (⊤ : Subgroup (VG G')) E' := by
        rw [hΩ]; exact ⟨_, hB, rfl⟩
      have hle : aHat G' (D.img (conjSubgroup V g⁻¹)) ≤
          kSub U' (⊤ : Subgroup (VG G')) E' := le_sup_right.trans (le_kSub hUB)
      refine hle (mem_aHat.mpr ⟨⟨D.ρ ⟨g * z * g⁻¹, hHmem⟩,
        D.mem_img.2 ⟨⟨g * z * g⁻¹, hHmem⟩, hHmem, rfl⟩⟩, ?_, rfl⟩)
      exact D.mem_img.2 ⟨⟨g * z * g⁻¹, hHmem⟩, hgz, rfl⟩
    obtain ⟨j, hj, hjval⟩ := Subgroup.mem_map.1 (hK0_le_W0 hk0K0)
    have hfj : f j ∈ kSub U' (⊤ : Subgroup (VG G')) E' := hj
    refine ⟨f j, hfj, ?_⟩
    have hgval : (((ρH j)⁻¹ : G') : LGL 2 D.W) = D.ρ (⟨(j : G)⁻¹, H.inv_mem j.2⟩ : ↥H) := by
      show (D.ρ j)⁻¹ = D.ρ (⟨(j : G)⁻¹, H.inv_mem j.2⟩ : ↥H)
      rw [show (⟨(j : G)⁻¹, H.inv_mem j.2⟩ : ↥H) = j⁻¹ from Subtype.ext rfl, map_inv]
    rw [show f j = (SemidirectProduct.inr (ρH j) : VG G') from rfl]
    conv_rhs => rw [← inv_inv (ρH j)]
    rw [conjSubgroup_UAOf_inr_inv h131 hA ((ρH j)⁻¹)]
    congr 1
    rw [hconj_x, ← hjval, hgval]
    rw [show H.subtype j = ((j : G)⁻¹)⁻¹ from (inv_inv (j : G)).symm]
    exact (D.img_conj hV_le_H (⟨(j : G)⁻¹, H.inv_mem j.2⟩ : ↥H)).symm

theorem IsMinFam16.exists_isBarMap_kSub_UAOf_img (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∃ ψ : ↥(kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
        (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) →* ↥(D.img (conjClosure V H)),
      SevenK.IsBarMap (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))
        (iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) ψ ∧
      ∀ k, ((ψ k : ↥(D.img (conjClosure V H))) : LGL 2 D.W) = projG (D.img H) k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G' : Subgroup (LGL 2 D.W) := D.img H
  let Γ : Set (Subgroup (LGL 2 D.W)) := D.conjImgFam V
  let VA : Subgroup (LGL 2 D.W) → Submodule (ZMod 2) D.W := D.conjImgSpace V₀ V
  let A : Subgroup (LGL 2 D.W) := D.img V
  let U' : Subgroup (VG G') := UAOf G' VA A
  let E' : Subgroup (VG G') := vHat G'
  let Ksub : Subgroup (VG G') := kSub U' ⊤ E'
  let Isub : Subgroup (VG G') := iSub U' ⊤ E'
  let M1 : Subgroup (LGL 2 D.W) := ⨆ B ∈ Γ, B
  let T : Subgroup (LGL 2 D.W) := D.img (conjClosure V H)
  have hHyp : SevenK.Hyp716 U' (⊤ : Subgroup (VG G')) E' :=
    IsMinFam16.hyp716_UAOf_img h1 h5 hS h hH hV D
  have h131 : Assumption131 G' Γ VA (mRank A) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank : ∀ B ∈ Γ, mRank B ≤ mRank A := Cex16.mRank_le_iSub16 h hH.1 D
  have hV_le_H : V ≤ H := h.V_le_S.trans hH.1.1
  have hconj_le : ∀ x ∈ H, conjSubgroup V x ≤ H := by
    intro x hx y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x * y * x⁻¹ ∈ H := hV_le_H hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hx) h1) hx
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h2
  have hA : A ∈ Γ := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
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
  have hΩ : omegaSet U' (⊤ : Subgroup (VG G')) E' = UAOf G' VA '' Γ :=
    (thirteen_two_three h131 hrank htrans hA).1
  have hIsub_eq : Isub = ⨆ B ∈ Γ, wHat G' (VA B) :=
    (thirteen_two_three h131 hrank htrans hA).2
  have hΓinv : ∀ B ∈ Γ, ∀ g ∈ G', cj g B ∈ Γ := by
    rintro B ⟨x, hxH, rfl⟩ g ⟨k, hkH, rfl⟩
    refine ⟨x * k⁻¹, H.mul_mem hxH (H.inv_mem hkH), ?_⟩
    rw [D.img_conj (hconj_le x hxH) k, conjSubgroup_conjSubgroup]
    simp
  have hcj_eq : ∀ g : LGL 2 D.W, cj g M1 = ⨆ B ∈ Γ, cj g B := by
    intro g
    show (M1.map (MulAut.conj g).toMonoidHom) = _
    rw [show M1 = ⨆ B ∈ Γ, B from rfl, Subgroup.map_iSup]
    refine iSup_congr fun B => ?_
    rw [Subgroup.map_iSup]
    rfl
  have hM1_inv : ∀ g ∈ G', cj g M1 = M1 := by
    intro g hg
    apply le_antisymm
    · rw [hcj_eq g]
      refine iSup₂_le fun B hB => le_iSup₂_of_le (cj g B) (hΓinv B hB g hg) le_rfl
    · have h1 : cj g⁻¹ M1 ≤ M1 := by
        rw [hcj_eq g⁻¹]
        refine iSup₂_le fun B hB =>
          le_iSup₂_of_le (cj g⁻¹ B) (hΓinv B hB g⁻¹ (G'.inv_mem hg)) le_rfl
      calc M1 = cj g (cj g⁻¹ M1) := (cj_cj_inv g M1).symm
        _ ≤ cj g M1 := cj_mono g h1
  have hM1_le_T : M1 ≤ T := by
    refine iSup₂_le fun B hB => ?_
    obtain ⟨x, hxH, rfl⟩ := hB
    exact D.img_mono (conjSubgroup_le_conjClosure V H hxH)
  have hker_projG : (projG G').ker = E' := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr x
      have hg : (g : LGL 2 D.W) = 1 := by simpa using hx
      have hg1 : g = 1 := Subtype.ext hg
      rw [hg1, map_one, mul_one]
      exact mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩
    · intro hx
      obtain ⟨v, -, rfl⟩ := mem_wHat.mp hx
      simp
  have hT_le_M1 : T ≤ M1 := by
    change ((conjClosure V H).subgroupOf H).map D.ρ ≤ M1
    rw [Subgroup.map_le_iff_le_comap]
    have hle : conjClosure V H ≤ (M1.comap D.ρ).map H.subtype := by
      refine CFSG.Quasithin.conjClosure_le ?_
      intro g hg z hz
      have hHmem : g * z * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg (hV_le_H hz)) (H.inv_mem hg)
      refine Subgroup.mem_map.2 ⟨⟨g * z * g⁻¹, hHmem⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hAM1 : A ≤ M1 := le_iSup₂_of_le A hA (le_refl A)
      have hzA : D.ρ (⟨z, hV_le_H hz⟩ : ↥H) ∈ M1 :=
        hAM1 (D.mem_img.2 ⟨⟨z, hV_le_H hz⟩, hz, rfl⟩)
      have hgG : D.ρ (⟨g, hg⟩ : ↥H) ∈ G' := D.mem_img.2 ⟨⟨g, hg⟩, hg, rfl⟩
      have hconj : D.ρ (⟨g * z * g⁻¹, hHmem⟩ : ↥H) =
          (MulAut.conj (D.ρ (⟨g, hg⟩ : ↥H))) (D.ρ (⟨z, hV_le_H hz⟩ : ↥H)) := by
        rw [show (⟨g * z * g⁻¹, hHmem⟩ : ↥H) =
            (⟨g, hg⟩ : ↥H) * (⟨z, hV_le_H hz⟩ : ↥H) * (⟨g, hg⟩ : ↥H)⁻¹ from
          Subtype.ext (by simp)]
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [hconj]
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj (D.ρ (⟨g, hg⟩ : ↥H))).toMonoidHom hzA
      rw [show (M1.map (MulAut.conj (D.ρ (⟨g, hg⟩ : ↥H))).toMonoidHom) =
          cj (D.ρ (⟨g, hg⟩ : ↥H)) M1 from rfl, hM1_inv _ hgG] at hmem
      exact hmem
    intro j hj
    rw [Subgroup.mem_comap]
    have hj' : (j : G) ∈ (M1.comap D.ρ).map H.subtype := hle (Subgroup.mem_subgroupOf.mp hj)
    obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.1 hj'
    rw [Subgroup.mem_comap] at hk
    have hkj : k = j := Subtype.ext hkval
    rw [hkj] at hk
    exact hk
  have hT : T = M1 := le_antisymm hT_le_M1 hM1_le_T
  have hKsub : Ksub = ⨆ B ∈ Γ, UAOf G' VA B := by
    show (⨆ W, ⨆ (_ : W ∈ omegaSet U' (⊤ : Subgroup (VG G')) E'), W) =
      (⨆ B, ⨆ (_ : B ∈ Γ), UAOf G' VA B)
    rw [hΩ, iSup_image]
  let φ : ↥Ksub →* LGL 2 D.W := (projG G').comp Ksub.subtype
  have hφ_range : φ.range = T := by
    have h1 : φ.range = Ksub.map (projG G') := by
      rw [show φ = (projG G').comp Ksub.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
    rw [h1]
    have h2 : Ksub.map (projG G') = M1 := by
      rw [hKsub, Subgroup.map_iSup]
      refine iSup_congr fun B => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hB => ?_
      exact map_projG_wHat_sup_aHat (h131.le_G B hB)
    rw [h2, hT]
  have hIsub_le_E : Isub ≤ E' := by
    rw [hIsub_eq]
    exact iSup₂_le fun B _ => wHat_le_vHat (VA B)
  have hIsub_normal : Isub.Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hHyp.toHyp73.jnormal
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  let Ah : Subgroup (VG G') := aHat G' M1
  have hAh_inf_E : Ah ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨g, hgM1, rfl⟩ := mem_aHat.mp hxA
    rw [Subgroup.mem_bot]
    have hg1 : g = 1 := by
      have hmem : (SemidirectProduct.inr g : VG G') ∈ (projG G').ker := by
        rw [hker_projG]; exact hxE
      rw [MonoidHom.mem_ker] at hmem
      exact Subtype.ext (by simpa [projG_inr] using hmem)
    rw [hg1, map_one]
  have hAh_le_N : Ah ≤ Subgroup.normalizer (Isub : Set (VG G')) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hIsub_normal]
    exact le_top
  have hKsub_le : Ksub ≤ Isub ⊔ Ah := by
    rw [hKsub]
    refine iSup₂_le fun B hB => ?_
    refine sup_le ?_ ?_
    · have hb : wHat G' (VA B) ≤ Isub := by
        rw [hIsub_eq]
        exact le_iSup₂_of_le B hB (le_refl _)
      exact hb.trans le_sup_left
    · have hle : B ≤ M1 := le_iSup₂_of_le B hB (le_refl _)
      exact (Subgroup.map_mono (Subgroup.comap_mono (f := G'.subtype) hle)).trans le_sup_right
  have hmul : (↑(Isub ⊔ Ah) : Set (VG G')) = ↑Isub * ↑Ah :=
    Subgroup.coe_mul_of_right_le_normalizer_left Isub Ah hAh_le_N
  have hker_iff : ∀ k : ↥Ksub, φ k = 1 ↔ (k : VG G') ∈ Isub := by
    intro k
    constructor
    · intro hk
      have hkE : (k : VG G') ∈ E' := by
        rw [← hker_projG, MonoidHom.mem_ker]
        exact hk
      have hk' : (k : VG G') ∈ (↑Isub * ↑Ah : Set (VG G')) := hmul ▸ hKsub_le k.2
      obtain ⟨i, hi, a, ha, hia⟩ := Set.mem_mul.mp hk'
      have hi1 : projG G' i = 1 := by
        rw [← MonoidHom.mem_ker, hker_projG]
        exact hIsub_le_E hi
      have hak : projG G' a = projG G' (k : VG G') := by
        rw [← hia, map_mul, hi1, one_mul]
      have hkproj : projG G' (k : VG G') = 1 := MonoidHom.mem_ker.mp (hker_projG.symm ▸ hkE)
      have haE : a ∈ E' := by
        rw [← hker_projG, MonoidHom.mem_ker, hak, hkproj]
      have ha1 : a = 1 := by
        have hmem : a ∈ Ah ⊓ E' := ⟨ha, haE⟩
        rwa [hAh_inf_E, Subgroup.mem_bot] at hmem
      rw [← hia, ha1, mul_one]
      exact hi
    · intro hk
      have hkE : (k : VG G') ∈ E' := hIsub_le_E hk
      have hk1 : projG G' (k : VG G') = 1 := MonoidHom.mem_ker.mp (hker_projG.symm ▸ hkE)
      exact hk1
  let ψ : ↥Ksub →* ↥T := φ.codRestrict T (fun k => hφ_range ▸ MonoidHom.mem_range.mpr ⟨k, rfl⟩)
  refine ⟨ψ, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro y
      have hy : (y : LGL 2 D.W) ∈ φ.range := hφ_range.symm ▸ y.2
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hy
      exact ⟨k, Subtype.ext hk⟩
    · intro k
      rw [Subtype.ext_iff]
      exact hker_iff k
  · intro k
    rfl

end CFSG.LocalAnalysis.WeakClosure81

end

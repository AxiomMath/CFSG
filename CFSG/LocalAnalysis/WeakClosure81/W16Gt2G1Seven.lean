module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W3Lem71Holds
public import CFSG.Goldschmidt.Steps.G74Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section NoCert

theorem hat_comm_oddCore (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ y : ↥(Mo.img H), y ∈ CFSG.oddCore ↥(Mo.img H) →
      ∀ a : ↥(Mo.img H), (a : LGL 2 Mo.W) ∈ Mo.img V → a * y = y * a := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVA_self : hatVA Mo V₀ V (Mo.img V) = Mo.sp V₀ := by
    have h := hatVA_img_conj h1 h5 h15 hS c Mo (Subgroup.one_mem H)
    rw [conjSubgroup_one, conjSubgroup_one] at h
    exact h
  have h131 := assumption131_hat h1 h5 h15 hS c Mo
  have h73 := (hyp711_hat h1 h5 h15 hS c Mo).toHyp73
  have hJnorm : ((vHat (Mo.img H)).subgroupOf (⊤ : Subgroup (VG (Mo.img H)))).Normal :=
    Subgroup.Normal.subgroupOf (normal_vHat (G := Mo.img H)) ⊤
  have hker_eq : vHat (Mo.img H) = (projG (Mo.img H)).ker := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker]
      rw [vHat, mem_wHat] at hx
      obtain ⟨v, -, rfl⟩ := hx
      simp [projG]
    · exact ker_projG_le_vHat
  have htrans : ∀ A ∈ hatGamma Mo V, ∀ B ∈ hatGamma Mo V, ∃ g ∈ Mo.img H, B = cj g A :=
    hatGamma_transitive Mo V hVH
  have hrank : ∀ A ∈ hatGamma Mo V, mRank A ≤ E3.mQuot V (U ⊔ V₀) :=
    mRank_le_hat h1 h5 h15 hS c Mo
  have hA₀ : Mo.img V ∈ hatGamma Mo V := img_mem_hatGamma c Mo
  have hΩ := (thirteen_two_three h131 hrank htrans hA₀).1
  have hIJ : iSub (hatV1 Mo V₀ V) ⊤ (vHat (Mo.img H)) ≤ vHat (Mo.img H) := by
    rw [iSub]
    refine iSup₂_le fun U hU => ?_
    change U ∈ omegaSet (UAOf (Mo.img H) (hatVA Mo V₀ V) (Mo.img V)) ⊤
      (vHat (Mo.img H)) at hU
    rw [hΩ] at hU
    obtain ⟨A, hA, rfl⟩ := hU
    rw [inf_pCoreOf_UAOf h131 hA]
    exact wHat_le_vHat _
  have hVbig : 2 < (vHat (Mo.img H)).relIndex (hatV1 Mo V₀ V) := by
    rw [hker_eq, Subgroup.relIndex_ker]
    rw [hatV1, UAOf, map_projG_wHat_sup_aHat (Mo.img_mono hVH)]
    rw [show Mo.img V = Mo.img (conjSubgroup V 1) from by rw [conjSubgroup_one]]
    rw [card_img_conjSubgroup h1 h5 h15 hS c Mo (Subgroup.one_mem H)]
    have h1lt : (1 : ℕ) < E3.mQuot V (U ⊔ V₀) := by omega
    simpa using Nat.pow_lt_pow_right (by norm_num : 1 < 2) h1lt
  let O : Subgroup (LGL 2 Mo.W) := (CFSG.oddCore ↥(Mo.img H)).map (Mo.img H).subtype
  have hOle : O ≤ Mo.img H := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf (Mo.img H)).Normal := by
    have h : O.subgroupOf (Mo.img H) = CFSG.oddCore ↥(Mo.img H) := by
      change ((CFSG.oddCore ↥(Mo.img H)).map (Mo.img H).subtype).comap
        (Mo.img H).subtype = CFSG.oddCore ↥(Mo.img H)
      exact Subgroup.comap_map_eq_self_of_injective (Mo.img H).subtype_injective _
    rw [h]
    exact CFSG.oddCore_normal ↥(Mo.img H)
  have hOodd : Odd (Nat.card O) := by
    have hcard : Nat.card O = Nat.card (CFSG.oddCore ↥(Mo.img H)) :=
      Subgroup.card_map_of_injective (Mo.img H).subtype_injective
    rw [hcard]
    have heq : CFSG.oddCore ↥(Mo.img H) = CFSG.pPrimeCore 2 ↥(Mo.img H) := by
      apply le_antisymm
      · refine sSup_le fun N hN => le_sSup ?_
        exact ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
      · refine sSup_le fun N hN => le_sSup ?_
        exact ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩
    rw [heq]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(Mo.img H)))
  let Rsub : Subgroup (VG (Mo.img H)) := vHat (Mo.img H) ⊔ aHat (Mo.img H) O
  have hnormO : Mo.img H ≤ Subgroup.normalizer (O : Set (LGL 2 Mo.W)) := by
    haveI : (O.subgroupOf (Mo.img H)).Normal := hOn
    exact le_normalizer_of_normal_subgroupOf hOle
  have hVN : hatV1 Mo V₀ V ≤ Subgroup.normalizer (Rsub : Set (VG (Mo.img H))) := by
    rw [hatV1, UAOf, hVA_self]
    refine sup_le ?_ ?_
    · refine (wHat_le_vHat (Mo.sp V₀)).trans ?_
      have h := vHat_le_normalizer_wHat_sup_aHat (V := Mo.W) (G := Mo.img H)
        (W := ⊤) (A := O) le_top
      rw [show wHat (Mo.img H) ⊤ = vHat (Mo.img H) from rfl] at h
      simpa [Rsub] using h
    · rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := mem_aHat.mp hx
      have hy' := (mem_wHat_sup_aHat (G := Mo.img H) (W := ⊤) (A := O)
        (fun o _ => by
          rw [CFSG.Quasithin.G11.conjSub, Submodule.map_top]
          exact LinearMap.range_eq_top.mpr (o : LGL 2 Mo.W).surjective)).mp hy
      obtain ⟨v, -, o, ho, rfl⟩ := hy'
      have hco : ((a * o * a⁻¹ : ↥(Mo.img H)) : LGL 2 Mo.W) ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hnormO a.2) (o : LGL 2 Mo.W)).1 ho
      have e2 : (SemidirectProduct.inr a : VG (Mo.img H)) * SemidirectProduct.inr o *
          (SemidirectProduct.inr a)⁻¹ = SemidirectProduct.inr (a * o * a⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      have e : (SemidirectProduct.inr a : VG (Mo.img H)) *
          (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr o) *
          (SemidirectProduct.inr a)⁻¹ =
          SemidirectProduct.inl (Multiplicative.ofAdd ((a : LGL 2 Mo.W) v)) *
          SemidirectProduct.inr (a * o * a⁻¹) := by
        calc (SemidirectProduct.inr a : VG (Mo.img H)) *
              (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr o) *
              (SemidirectProduct.inr a)⁻¹
            = (SemidirectProduct.inr a * SemidirectProduct.inl (Multiplicative.ofAdd v) *
                (SemidirectProduct.inr a)⁻¹) *
              (SemidirectProduct.inr a * SemidirectProduct.inr o *
                (SemidirectProduct.inr a)⁻¹) := by group
          _ = SemidirectProduct.inl (Multiplicative.ofAdd ((a : LGL 2 Mo.W) v)) *
              SemidirectProduct.inr (a * o * a⁻¹) := by
                rw [inr_mul_inl_mul_inr_inv, e2]
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (mem_wHat.mpr ⟨_, Submodule.mem_top, rfl⟩))
        (Subgroup.mem_sup_right (mem_aHat.mpr ⟨a * o * a⁻¹, hco, rfl⟩))
  have hRodd : Odd ((vHat (Mo.img H)).relIndex Rsub) := by
    rw [hker_eq, Subgroup.relIndex_ker]
    rw [show Rsub = vHat (Mo.img H) ⊔ aHat (Mo.img H) O from rfl, vHat,
      Subgroup.map_sup, map_projG_wHat, map_projG_aHat hOle, bot_sup_eq]
    exact hOodd
  have hcommVR : ⁅hatV1 Mo V₀ V, Rsub⁆ ≤ vHat (Mo.img H) :=
    seven_three_five (V := hatV1 Mo V₀ V) (H := ⊤) (E := vHat (Mo.img H))
      (J := vHat (Mo.img H)) (R := Rsub)
      h73.elemAbelian h73.ti (isElemAbelian_wHat (G := Mo.img H) ⊤).1 le_top hJnorm
      h73.mem (fun _ _ => le_top) (wHat_le_pCoreOf (G := Mo.img H) ⊤) hJnorm hIJ
      hVbig le_sup_left le_top hVN hRodd
  intro y hy a ha
  have hmem_y : (SemidirectProduct.inr y : VG (Mo.img H)) ∈ Rsub := by
    refine Subgroup.mem_sup_right ?_
    exact mem_aHat.mpr ⟨y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
  have hmem_a : (SemidirectProduct.inr a : VG (Mo.img H)) ∈ hatV1 Mo V₀ V := by
    rw [hatV1, UAOf]
    exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨a, ha, rfl⟩)
  have hcomm_elem : ⁅(SemidirectProduct.inr a : VG (Mo.img H)),
      SemidirectProduct.inr y⁆ ∈ vHat (Mo.img H) :=
    hcommVR (Subgroup.commutator_mem_commutator hmem_a hmem_y)
  have hproj : projG (Mo.img H) ⁅(SemidirectProduct.inr a : VG (Mo.img H)),
      SemidirectProduct.inr y⁆ = 1 := by
    rw [hker_eq] at hcomm_elem
    exact MonoidHom.mem_ker.mp hcomm_elem
  rw [map_commutatorElement, projG_inr, projG_inr] at hproj
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hproj)

end NoCert

section Certified


theorem hat_commute_of_isPGroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H)
    (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) :
    (∀ x ∈ V, ∀ w ∈ conjSubgroup V₀ h, x * w = w * x) ∧
      (∀ w ∈ conjSubgroup V h, ∀ x ∈ V₀, w * x = x * w) ∧
      ∀ a ∈ Mo.img V, ∀ b ∈ Mo.img (conjSubgroup V h), a * b = b * a := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVA_self : hatVA Mo V₀ V (Mo.img V) = Mo.sp V₀ := by
    have h := hatVA_img_conj h1 h5 h15 hS c Mo (Subgroup.one_mem H)
    rw [conjSubgroup_one, conjSubgroup_one] at h
    exact h
  have h131 := assumption131_hat h1 h5 h15 hS c Mo
  let jinv : ↥H := (⟨h, hh⟩ : ↥H)⁻¹
  let gimg : ↥(Mo.img H) := ⟨Mo.ρ jinv, Mo.mem_img.mpr ⟨jinv, jinv.2, rfl⟩⟩
  let ĥ : ↥(Mo.img H) := ⟨Mo.ρ ⟨h, hh⟩, Mo.mem_img.mpr ⟨⟨h, hh⟩, hh, rfl⟩⟩
  have hgimg : gimg = ĥ⁻¹ := by
    apply Subtype.ext
    simp only [gimg, ĥ, jinv, map_inv, Subgroup.coe_inv]
  have hcj : cj (gimg : LGL 2 Mo.W) (Mo.img V) = Mo.img (conjSubgroup V h) := by
    have h1' := ModDataE.img_conj (M := Mo) (A := V) hVH jinv
    simpa [gimg, jinv] using h1'
  have hconj : conjSubgroup (hatV1 Mo V₀ V) (SemidirectProduct.inr ĥ : VG (Mo.img H)) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ h)) ⊔
        aHat (Mo.img H) (Mo.img (conjSubgroup V h)) := by
    have hUA := conjSubgroup_UAOf_inr_inv (V := Mo.W) (G := Mo.img H)
      (Γ := hatGamma Mo V) (VA := hatVA Mo V₀ V) (i := E3.mQuot V (U ⊔ V₀))
      h131 (img_mem_hatGamma c Mo) gimg
    rw [hcj] at hUA
    rw [hgimg, inv_inv] at hUA
    have hshape : UAOf (Mo.img H) (hatVA Mo V₀ V) (Mo.img (conjSubgroup V h)) =
        wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ h)) ⊔
          aHat (Mo.img H) (Mo.img (conjSubgroup V h)) := by
      rw [UAOf, hatVA_img_conj h1 h5 h15 hS c Mo hh]
    change conjSubgroup (UAOf (Mo.img H) (hatVA Mo V₀ V) (Mo.img V))
        (SemidirectProduct.inr ĥ : VG (Mo.img H)) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ h)) ⊔
        aHat (Mo.img H) (Mo.img (conjSubgroup V h))
    rw [hUA]
    exact hshape
  have hconjVH : conjSubgroup V h ≤ H := by
    calc conjSubgroup V h ≤ conjSubgroup H h := E3.conjSubgroup_mono_left h hVH
      _ = H := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hh)
  have hmap_le : (hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr ĥ : VG (Mo.img H)) ⊔ vHat (Mo.img H)).map
      (projG (Mo.img H)) ≤ Mo.img (V ⊔ conjSubgroup V h) := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hatV1, UAOf, Subgroup.map_sup, map_projG_wHat,
        map_projG_aHat (Mo.img_mono hVH), bot_sup_eq]
      exact Mo.img_mono le_sup_left
    · rw [hconj, Subgroup.map_sup, map_projG_wHat, map_projG_aHat (Mo.img_mono hconjVH),
        bot_sup_eq]
      exact Mo.img_mono le_sup_right
    · rw [vHat, map_projG_wHat]
      exact bot_le
  have hP2 : IsPGroup 2 ((hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr ĥ : VG (Mo.img H)) ⊔ vHat (Mo.img H)).map
      (projG (Mo.img H))) := hP.to_le hmap_le
  have hker2 : IsPGroup 2 (projG (Mo.img H)).ker :=
    (isElemAbelian_wHat (G := Mo.img H) ⊤).isPGroup.to_le (ker_projG_le_vHat (V := Mo.W))
  have hcomap : IsPGroup 2 (((hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr ĥ : VG (Mo.img H)) ⊔ vHat (Mo.img H)).map
      (projG (Mo.img H))).comap (projG (Mo.img H))) :=
    hP2.comap_of_ker_isPGroup (projG (Mo.img H)) hker2
  have hP' : IsPGroup 2 ↥(hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr ĥ : VG (Mo.img H)) ⊔ vHat (Mo.img H)) :=
    hcomap.to_le (Subgroup.le_comap_map (projG (Mo.img H)) _)
  have h73 := (hyp711_hat h1 h5 h15 hS c Mo).toHyp73
  have hJnorm : ((vHat (Mo.img H)).subgroupOf (⊤ : Subgroup (VG (Mo.img H)))).Normal :=
    Subgroup.Normal.subgroupOf (normal_vHat (G := Mo.img H)) ⊤
  have hcomm := seven_three_one (V := hatV1 Mo V₀ V) (H := ⊤)
    (E := vHat (Mo.img H)) (J := vHat (Mo.img H))
    h73.elemAbelian h73.ti (isElemAbelian_wHat (G := Mo.img H) ⊤).1 le_top
    hJnorm h73.mem
    (fun _ _ => le_top) (wHat_le_pCoreOf (G := Mo.img H) ⊤)
    hJnorm (Subgroup.mem_top _) hP'
  refine ⟨?_, ?_, ?_⟩
  · intro x hx w hw
    have hxH : x ∈ H := hVH hx
    have hwI : w ∈ conjClosure (U ⊔ V₀) H :=
      conjSubgroup_le_conjClosure_of_mem (Z := U ⊔ V₀) hh le_sup_right hw
    let a : ↥(Mo.img H) := ⟨Mo.ρ ⟨x, hxH⟩, Mo.mem_img.mpr ⟨⟨x, hxH⟩, hxH, rfl⟩⟩
    have haV : (a : LGL 2 Mo.W) ∈ Mo.img V := Mo.mem_img.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
    have hmem_u : (SemidirectProduct.inr a : VG (Mo.img H)) ∈ hatV1 Mo V₀ V := by
      rw [hatV1, UAOf]
      exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨a, haV, rfl⟩)
    have hwsp : Mo.ι w ∈ Mo.sp (conjSubgroup V₀ h) :=
      Mo.mem_sp.mpr ⟨w, ⟨hw, hwI⟩, rfl⟩
    have hmem_v : (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι w)) :
        VG (Mo.img H)) ∈ conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr ĥ : VG (Mo.img H)) := by
      rw [hconj]
      exact Subgroup.mem_sup_left (mem_wHat.mpr ⟨Mo.ι w, hwsp, rfl⟩)
    have hc := hcomm (SemidirectProduct.inr a) hmem_u
      (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι w))) hmem_v
    have he : (SemidirectProduct.inr a : VG (Mo.img H)) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι w)) *
        (SemidirectProduct.inr a)⁻¹ =
        SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι w)) := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have h1' : (SemidirectProduct.inl
        (Multiplicative.ofAdd ((a : LGL 2 Mo.W) (Mo.ι w))) : VG (Mo.img H)) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι w)) : VG (Mo.img H)) := by
      rw [← inr_mul_inl_mul_inr_inv a (Mo.ι w), he]
    have hval : (a : LGL 2 Mo.W) (Mo.ι w) = Mo.ι w :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective h1')
    have hxwI : x * w * x⁻¹ ∈ conjClosure (U ⊔ V₀) H := by
      have hxI : conjClosure (U ⊔ V₀) H =
          conjSubgroup (conjClosure (U ⊔ V₀) H) x⁻¹ :=
        (conjSubgroup_eq_iff_mem_normalizer.mpr
          (le_normalizer_conjClosure (U ⊔ V₀) H (H.inv_mem hxH))).symm
      rw [hxI]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : x⁻¹ * (x * w * x⁻¹) * (x⁻¹)⁻¹ = w := by group
      rw [e]
      exact hwI
    have hxwx : x * w * x⁻¹ = w := by
      refine Mo.ι_injOn hxwI hwI ?_
      rw [← Mo.ρ_ι ⟨x, hxH⟩ w hwI]
      exact hval
    calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [hxwx]
  · intro w hw x hx
    have hwH : w ∈ H := hconjVH hw
    let jwinv : ↥H := (⟨w, hwH⟩ : ↥H)⁻¹
    let a : ↥(Mo.img H) := ⟨Mo.ρ ⟨w, hwH⟩, Mo.mem_img.mpr ⟨⟨w, hwH⟩, hwH, rfl⟩⟩
    have haV : (a : LGL 2 Mo.W) ∈ Mo.img (conjSubgroup V h) :=
      Mo.mem_img.mpr ⟨⟨w, hwH⟩, hw, rfl⟩
    have hmem_v : (SemidirectProduct.inr a : VG (Mo.img H)) ∈
        conjSubgroup (hatV1 Mo V₀ V) (SemidirectProduct.inr ĥ : VG (Mo.img H)) := by
      rw [hconj]
      exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨a, haV, rfl⟩)
    have hxI : x ∈ conjClosure (U ⊔ V₀) H :=
      le_sup_right.trans (le_conjClosure (U ⊔ V₀) H) hx
    have hmem_u : (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) :
        VG (Mo.img H)) ∈ hatV1 Mo V₀ V := by
      rw [hatV1, UAOf, hVA_self]
      exact Subgroup.mem_sup_left
        (mem_wHat.mpr ⟨Mo.ι x, Mo.mem_sp.mpr ⟨x, ⟨hx, hxI⟩, rfl⟩, rfl⟩)
    have hc := hcomm (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x))) hmem_u
      (SemidirectProduct.inr a) hmem_v
    have he : (SemidirectProduct.inr a⁻¹ : VG (Mo.img H)) *
        SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) *
        (SemidirectProduct.inr a⁻¹ : VG (Mo.img H))⁻¹ =
        (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) : VG (Mo.img H)) := by
      have h2 : (SemidirectProduct.inr a⁻¹ : VG (Mo.img H)) = (SemidirectProduct.inr a)⁻¹ :=
        map_inv SemidirectProduct.inr a
      rw [h2, inv_inv]
      calc (SemidirectProduct.inr a)⁻¹ *
            SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) *
            SemidirectProduct.inr a
          = (SemidirectProduct.inr a)⁻¹ * (SemidirectProduct.inl
              (Multiplicative.ofAdd (Mo.ι x)) * SemidirectProduct.inr a) := by group
        _ = (SemidirectProduct.inr a)⁻¹ * (SemidirectProduct.inr a *
              SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x))) := by rw [hc]
        _ = SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) := by group
    have h1' : (SemidirectProduct.inl
        (Multiplicative.ofAdd (((a⁻¹ : ↥(Mo.img H)) : LGL 2 Mo.W) (Mo.ι x))) :
        VG (Mo.img H)) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (Mo.ι x)) : VG (Mo.img H)) := by
      rw [← inr_mul_inl_mul_inr_inv a⁻¹ (Mo.ι x), he]
    have hval : ((a⁻¹ : ↥(Mo.img H)) : LGL 2 Mo.W) (Mo.ι x) = Mo.ι x :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective h1')
    have hwxI : w⁻¹ * x * w ∈ conjClosure (U ⊔ V₀) H := by
      have hwI : conjClosure (U ⊔ V₀) H =
          conjSubgroup (conjClosure (U ⊔ V₀) H) w :=
        (conjSubgroup_eq_iff_mem_normalizer.mpr
          (le_normalizer_conjClosure (U ⊔ V₀) H hwH)).symm
      rw [hwI]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
      rw [e]
      exact hxI
    have hxa : w⁻¹ * x * w = x := by
      have h2 : Mo.ι (w⁻¹ * x * w) = Mo.ι x := by
        have hh2 := Mo.ρ_ι jwinv x hxI
        have h4 : Mo.ρ jwinv = ((a⁻¹ : ↥(Mo.img H)) : LGL 2 Mo.W) := by
          simp [a, jwinv, map_inv]
        rw [h4] at hh2
        rw [hval] at hh2
        rw [show (jwinv : G) * x * (jwinv : G)⁻¹ = w⁻¹ * x * w by
          simp [jwinv, Subgroup.coe_inv]] at hh2
        exact hh2.symm
      exact Mo.ι_injOn hwxI hxI h2
    calc w * x = w * (w⁻¹ * x * w) := by rw [hxa]
      _ = x * w := by group
  · intro a ha b hb
    have haH : a ∈ Mo.img H := Mo.img_mono hVH ha
    have hbH : b ∈ Mo.img H := Mo.img_mono hconjVH hb
    let a' : ↥(Mo.img H) := ⟨a, haH⟩
    let b' : ↥(Mo.img H) := ⟨b, hbH⟩
    have hmem_u : (SemidirectProduct.inr a' : VG (Mo.img H)) ∈ hatV1 Mo V₀ V := by
      rw [hatV1, UAOf]
      exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨a', ha, rfl⟩)
    have hmem_v : (SemidirectProduct.inr b' : VG (Mo.img H)) ∈
        conjSubgroup (hatV1 Mo V₀ V) (SemidirectProduct.inr ĥ : VG (Mo.img H)) := by
      rw [hconj]
      exact Subgroup.mem_sup_right (mem_aHat.mpr ⟨b', hb, rfl⟩)
    have hc := hcomm (SemidirectProduct.inr a') hmem_u (SemidirectProduct.inr b') hmem_v
    have h2 : a' * b' = b' * a' :=
      SemidirectProduct.inr_injective (by simpa only [map_mul] using hc)
    exact congrArg Subtype.val h2

private def hatL_gh (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (g' : G) (hg' : g' ∈ H) :
    ↥(Mo.img H) :=
  ⟨Mo.ρ ⟨g', hg'⟩, Mo.mem_img.mpr ⟨⟨g', hg'⟩, hg', rfl⟩⟩

private theorem hatL_Vt_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    hatV1 Mo V₀ V = wHat (Mo.img H) (Mo.sp V₀) ⊔ aHat (Mo.img H) (Mo.img V) := by
  rw [hatV1, UAOf]
  have h := hatVA_img_conj h1 h5 h15 hS c Mo (Subgroup.one_mem H)
  rw [conjSubgroup_one, conjSubgroup_one] at h
  rw [h]

private theorem hatL_W_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {g' : G}
    (hg' : g' ∈ H) :
    conjSubgroup (hatV1 Mo V₀ V) (SemidirectProduct.inr (hatL_gh Mo g' hg') : VG (Mo.img H)) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) ⊔
        aHat (Mo.img H) (Mo.img (conjSubgroup V g')) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have h131 := assumption131_hat h1 h5 h15 hS c Mo
  have hUA := conjSubgroup_UAOf_inr_inv (V := Mo.W) (G := Mo.img H)
      (Γ := hatGamma Mo V) (VA := hatVA Mo V₀ V) (i := E3.mQuot V (U ⊔ V₀))
      h131 (img_mem_hatGamma c Mo) ((hatL_gh Mo g' hg')⁻¹)
  rw [inv_inv] at hUA
  have hcj : cj (((hatL_gh Mo g' hg')⁻¹ : ↥(Mo.img H)) : LGL 2 Mo.W) (Mo.img V) =
      Mo.img (conjSubgroup V g') := by
    have h := ModDataE.img_conj (M := Mo) (A := V) hVH (⟨g', hg'⟩ : ↥H)⁻¹
    simpa [hatL_gh, Subgroup.coe_inv, map_inv] using h
  rw [hcj] at hUA
  have hshape : UAOf (Mo.img H) (hatVA Mo V₀ V) (Mo.img (conjSubgroup V g')) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) ⊔
        aHat (Mo.img H) (Mo.img (conjSubgroup V g')) := by
    rw [UAOf, hatVA_img_conj h1 h5 h15 hS c Mo hg']
  rw [hshape] at hUA
  simpa only [hatV1] using hUA

private theorem hatL_Vt_map (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    (hatV1 Mo V₀ V).map (projG (Mo.img H)) = Mo.img V := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rw [hatL_Vt_eq h1 h5 h15 hS c Mo, Subgroup.map_sup, map_projG_wHat,
    map_projG_aHat (Mo.img_mono hVH), bot_sup_eq]

private theorem hatL_W_map (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {g' : G}
    (hg' : g' ∈ H) :
    (conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg') : VG (Mo.img H))).map
        (projG (Mo.img H)) = Mo.img (conjSubgroup V g') := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hconjVH : conjSubgroup V g' ≤ H := by
    calc conjSubgroup V g' ≤ conjSubgroup H g' := E3.conjSubgroup_mono_left g' hVH
      _ = H := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg')
  rw [hatL_W_eq h1 h5 h15 hS c Mo hg', Subgroup.map_sup, map_projG_wHat,
    map_projG_aHat (Mo.img_mono hconjVH), bot_sup_eq]

private theorem hatL_X_map (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {g' : G}
    (hg' : g' ∈ H) :
    ((hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg') : VG (Mo.img H)))).map (projG (Mo.img H)) =
      Mo.img (V ⊔ conjSubgroup V g') := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hconjVH : conjSubgroup V g' ≤ H := by
    calc conjSubgroup V g' ≤ conjSubgroup H g' := E3.conjSubgroup_mono_left g' hVH
      _ = H := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg')
  rw [Subgroup.map_sup, hatL_Vt_map h1 h5 h15 hS c Mo, hatL_W_map h1 h5 h15 hS c Mo hg',
    ← ModDataE.img_sup (M := Mo) (S := V) (S' := conjSubgroup V g') hVH hconjVH]

private theorem hatL_gh_not_mem_normalizer (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) ∉
      Subgroup.normalizer (hatV1 Mo V₀ V : Set (VG (Mo.img H))) := by
  intro hmem
  have hW : conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) = hatV1 Mo V₀ V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hmem
  have hmap := congrArg (Subgroup.map (projG (Mo.img H))) hW
  rw [hatL_W_map h1 h5 h15 hS c Mo hg'.1, hatL_Vt_map h1 h5 h15 hS c Mo] at hmap
  have hM : g' ∈ M := by
    have h := (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo hg'.1 (Subgroup.one_mem H)).mp
      (by rw [conjSubgroup_one]; exact hmap)
    simpa using h
  exact hg'M hM

private theorem hatL_wHat_le_normalizer_W (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H) :
    wHat (Mo.img H) (Mo.sp V₀) ≤ Subgroup.normalizer
      (wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) ⊔
        aHat (Mo.img H) (Mo.img (conjSubgroup V g')) : Subgroup (VG (Mo.img H))) := by
  have h131 := assumption131_hat h1 h5 h15 hS c Mo
  have hrank := mRank_le_hat h1 h5 h15 hS c Mo
  have hA : Mo.img (conjSubgroup V g') ∈ hatGamma Mo V := ⟨g', hg', rfl⟩
  have hcomm : commSub (Mo.img (conjSubgroup V g')) ≤ Mo.sp (conjSubgroup V₀ g') := by
    rw [← hatVA_img_conj h1 h5 h15 hS c Mo hg']
    exact commSub_le_VA_of_mRank_le h131 hA (hrank _ hA)
  exact (wHat_le_vHat _).trans (vHat_le_normalizer_wHat_sup_aHat hcomm)

private theorem hatL_inl_mul_inr_mul_inl_inv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {G : Subgroup (LGL 2 V)} (u : V) (a : G) :
    (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) * SemidirectProduct.inr a *
        (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd (u - (a : LGL 2 V) u)) *
        SemidirectProduct.inr a := by
  have h := inr_mul_inl_mul_inr_inv a (-u)
  have h2 : (SemidirectProduct.inr a : VG G) *
      SemidirectProduct.inl (Multiplicative.ofAdd (-u)) =
      SemidirectProduct.inl (Multiplicative.ofAdd ((a : LGL 2 V) (-u))) *
        SemidirectProduct.inr a := by
    rw [← h]; group
  rw [← map_inv SemidirectProduct.inl, mul_assoc, ← ofAdd_neg, h2, ← mul_assoc,
    ← map_mul SemidirectProduct.inl, ← ofAdd_add, map_neg, ← sub_eq_add_neg]

private theorem hatL_inf_normalizer_ge (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H) :
    wHat (Mo.img H) (Mo.sp V₀) ≤ hatV1 Mo V₀ V ⊓
      Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg') : VG (Mo.img H))) := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [hatL_Vt_eq h1 h5 h15 hS c Mo]
    exact Subgroup.mem_sup_left hx
  · rw [hatL_W_eq h1 h5 h15 hS c Mo hg']
    exact hatL_wHat_le_normalizer_W h1 h5 h15 hS c Mo hg' hx

private theorem hatL_inf_normalizer_le (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    hatV1 Mo V₀ V ⊓ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))) ≤
      wHat (Mo.img H) (Mo.sp V₀) := by
  intro x hx
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVM : V ≤ M := Subgroup.le_normalizer.trans (le_of_eq c.cex.hyp.h6.normalizer_eq)
  have hVN₀ : V ≤ Subgroup.normalizer (V₀ : Set G) := hVM.trans c.cex.hyp.h6.le_normalizer₀
  have hstabV : ∀ a ∈ Mo.img V, CFSG.Quasithin.G11.conjSub a (Mo.sp V₀) = Mo.sp V₀ := by
    intro a ha
    obtain ⟨j, hjV, rfl⟩ := Mo.mem_img.mp ha
    rw [ModDataE.conjSub_sp]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ (hVN₀ hjV))
  have hxV : x ∈ wHat (Mo.img H) (Mo.sp V₀) ⊔ aHat (Mo.img H) (Mo.img V) := by
    have h := hx.1
    rw [hatL_Vt_eq h1 h5 h15 hS c Mo] at h
    exact h
  obtain ⟨u, hu, a, haV, rfl⟩ := (mem_wHat_sup_aHat (G := Mo.img H) (W := Mo.sp V₀)
      (A := Mo.img V) hstabV).mp hxV
  obtain ⟨j, hjV, hja⟩ := Mo.mem_img.mp haV
  have hconjVH : conjSubgroup V g' ≤ H := by
    calc conjSubgroup V g' ≤ conjSubgroup H g' := E3.conjSubgroup_mono_left g' hVH
      _ = H := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg'.1)
  have hleN : conjSubgroup V g' ≤ Subgroup.normalizer (conjSubgroup V₀ g' : Set G) := by
    calc conjSubgroup V g' ≤ conjSubgroup (Subgroup.normalizer (V₀ : Set G)) g' :=
          E3.conjSubgroup_mono_left g' hVN₀
      _ = Subgroup.normalizer (conjSubgroup V₀ g' : Set G) := E3.conjSubgroup_normalizer V₀ g'
  have hstabW : ∀ a ∈ Mo.img (conjSubgroup V g'), CFSG.Quasithin.G11.conjSub a
      (Mo.sp (conjSubgroup V₀ g')) = Mo.sp (conjSubgroup V₀ g') := by
    intro a ha
    obtain ⟨j, hjV, rfl⟩ := Mo.mem_img.mp ha
    rw [ModDataE.conjSub_sp]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ (hleN hjV))
  have hjn : ∀ y ∈ conjSubgroup V g', (j : G) * y * (j : G)⁻¹ ∈
      conjSubgroup V g' ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
    intro y hy
    have hyH : y ∈ H := hconjVH hy
    let by' : ↥(Mo.img H) := ⟨Mo.ρ ⟨y, hyH⟩, Mo.mem_img.mpr ⟨⟨y, hyH⟩, hyH, rfl⟩⟩
    have hbyW : (SemidirectProduct.inr by' : VG (Mo.img H)) ∈
        conjSubgroup (hatV1 Mo V₀ V)
          (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) := by
      rw [hatL_W_eq h1 h5 h15 hS c Mo hg'.1]
      exact Subgroup.mem_sup_right (mem_aHat.mpr
        ⟨by', Mo.mem_img.mpr ⟨⟨y, hyH⟩, hy, rfl⟩, rfl⟩)
    have hmemN := (Subgroup.mem_normalizer_iff.mp hx.2 (SemidirectProduct.inr by')).1 hbyW
    set cc : ↥(Mo.img H) := a * by' * a⁻¹ with hcc
    have he : (SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr a) *
        SemidirectProduct.inr by' *
        (SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr a)⁻¹ =
        (SemidirectProduct.inl (Multiplicative.ofAdd (u - (cc : LGL 2 Mo.W) u)) *
          SemidirectProduct.inr cc : VG (Mo.img H)) := by
      have h1' : (SemidirectProduct.inr a : VG (Mo.img H)) * SemidirectProduct.inr by' *
          (SemidirectProduct.inr a)⁻¹ = SemidirectProduct.inr cc := by
        rw [hcc, map_mul, map_mul, map_inv]
      calc (SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr a) *
            SemidirectProduct.inr by' *
            (SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr a)⁻¹
          = SemidirectProduct.inl (Multiplicative.ofAdd u) *
            ((SemidirectProduct.inr a : VG (Mo.img H)) * SemidirectProduct.inr by' *
              (SemidirectProduct.inr a)⁻¹) *
            (SemidirectProduct.inl (Multiplicative.ofAdd u))⁻¹ := by group
        _ = SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr cc *
            (SemidirectProduct.inl (Multiplicative.ofAdd u))⁻¹ := by rw [h1']
        _ = SemidirectProduct.inl (Multiplicative.ofAdd (u - (cc : LGL 2 Mo.W) u)) *
            SemidirectProduct.inr cc := hatL_inl_mul_inr_mul_inl_inv u cc
    have hmemN' : (SemidirectProduct.inl (Multiplicative.ofAdd (u - (cc : LGL 2 Mo.W) u)) *
        SemidirectProduct.inr cc : VG (Mo.img H)) ∈ conjSubgroup (hatV1 Mo V₀ V)
          (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) := by
      rwa [he] at hmemN
    obtain ⟨w, hw, b, hb, heq⟩ := (mem_wHat_sup_aHat (G := Mo.img H)
        (W := Mo.sp (conjSubgroup V₀ g')) (A := Mo.img (conjSubgroup V g')) hstabW).mp
        (by rwa [hatL_W_eq h1 h5 h15 hS c Mo hg'.1] at hmemN')
    have hbc : cc = b := by
      apply Subtype.ext
      have h := congrArg (projG (Mo.img H)) heq
      simp only [map_mul, projG_inl, projG_inr, one_mul] at h
      exact h
    have hcimg : (cc : LGL 2 Mo.W) ∈ Mo.img (conjSubgroup V g') := by
      rw [hbc]; exact hb
    have hjc : (cc : LGL 2 Mo.W) = Mo.ρ (j * (⟨y, hyH⟩ : ↥H) * j⁻¹) := by
      simp [hcc, by', hja, map_mul, map_inv]
    obtain ⟨t, ht, htc⟩ := Mo.mem_img.mp hcimg
    have hC : ((t⁻¹ * (j * (⟨y, hyH⟩ : ↥H) * j⁻¹) : ↥H) : G) ∈
        H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      have hρ : Mo.ρ (t⁻¹ * (j * (⟨y, hyH⟩ : ↥H) * j⁻¹)) = 1 := by
        rw [map_mul, map_inv, htc, ← hjc]
        simp
      exact ⟨(t⁻¹ * (j * (⟨y, hyH⟩ : ↥H) * j⁻¹) : ↥H).2,
        (Mo.ρ_eq_one_iff (t⁻¹ * (j * (⟨y, hyH⟩ : ↥H) * j⁻¹))).1 hρ⟩
    have hmem : ((j * (⟨y, hyH⟩ : ↥H) * j⁻¹ : ↥H) : G) ∈
        conjSubgroup V g' ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
      have hmul := Subgroup.mul_mem (conjSubgroup V g' ⊔
          (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)))
        (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hC)
      rwa [show (t : G) * ((t⁻¹ * (j * (⟨y, hyH⟩ : ↥H) * j⁻¹) : ↥H) : G) =
          ((j * (⟨y, hyH⟩ : ↥H) * j⁻¹ : ↥H) : G) by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group] at hmul
    simpa using hmem
  have hjU : (j : G) ∈ U ⊔ V₀ := mem_sup_of_normalizes_conj h1 h5 h15 hS c hg' hg'M hjV hjn
  have hCker : Mo.img (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) = ⊥ := by
    rw [ModDataE.img, Subgroup.map_eq_bot_iff]
    intro j' hj'
    rw [MonoidHom.mem_ker]
    exact (Mo.ρ_eq_one_iff j').2 (Subgroup.mem_subgroupOf.mp hj').2
  have hUV₀C : U ⊔ V₀ ≤ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    calc U ⊔ V₀ = V ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :=
          (inf_centralizer_eq_sup h1 h5 h15 hS c).symm
      _ ≤ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := inf_le_right
  have ha1 : (a : LGL 2 Mo.W) = 1 := by
    have hpa : (a : LGL 2 Mo.W) ∈ Mo.img (U ⊔ V₀) := by
      rw [← hja]
      exact Mo.mem_img.mpr ⟨j, hjU, rfl⟩
    have := Mo.img_mono hUV₀C hpa
    rwa [hCker] at this
  have ha : a = 1 := Subtype.ext ha1
  rw [ha, map_one, mul_one]
  exact mem_wHat.mpr ⟨u, hu, rfl⟩

private theorem hatL_inf_normalizer (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    hatV1 Mo V₀ V ⊓ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))) =
      wHat (Mo.img H) (Mo.sp V₀) :=
  le_antisymm (hatL_inf_normalizer_le h1 h5 h15 hS c Mo hg' hg'M)
    (hatL_inf_normalizer_ge h1 h5 h15 hS c Mo hg'.1)

private theorem hatL_vHat_eq_ker (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    vHat (Mo.img H) = (projG (Mo.img H)).ker := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker]
    rw [vHat, mem_wHat] at hx
    obtain ⟨v, -, rfl⟩ := hx
    simp [projG]
  · exact ker_projG_le_vHat

private theorem hatL_mQuot_U1 (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    E3.mQuot (hatV1 Mo V₀ V) (wHat (Mo.img H) (Mo.sp V₀)) = E3.mQuot V (U ⊔ V₀) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVM : V ≤ M := Subgroup.le_normalizer.trans (le_of_eq c.cex.hyp.h6.normalizer_eq)
  have hVN₀ : V ≤ Subgroup.normalizer (V₀ : Set G) := hVM.trans c.cex.hyp.h6.le_normalizer₀
  have hWU : wHat (Mo.img H) (Mo.sp V₀) = hatV1 Mo V₀ V ⊓ vHat (Mo.img H) := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, wHat_le_vHat _ hx⟩
      rw [hatL_Vt_eq h1 h5 h15 hS c Mo]
      exact Subgroup.mem_sup_left hx
    · rintro x ⟨hxV, hxv⟩
      change x ∈ wHat (Mo.img H) ⊤ at hxv
      obtain ⟨v, -, rfl⟩ := mem_wHat.mp hxv
      have hstabV : ∀ a ∈ Mo.img V, CFSG.Quasithin.G11.conjSub a (Mo.sp V₀) = Mo.sp V₀ := by
        intro a ha
        obtain ⟨j, hjV, rfl⟩ := Mo.mem_img.mp ha
        rw [ModDataE.conjSub_sp]
        congr 1
        exact conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ (hVN₀ hjV))
      have hxV' : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG (Mo.img H)) ∈
          wHat (Mo.img H) (Mo.sp V₀) ⊔ aHat (Mo.img H) (Mo.img V) := by
        rw [← hatL_Vt_eq h1 h5 h15 hS c Mo]
        exact hxV
      obtain ⟨w, hw, a, ha, heq⟩ := (mem_wHat_sup_aHat (G := Mo.img H) (W := Mo.sp V₀)
          (A := Mo.img V) hstabV).mp hxV'
      have ha1 : a = 1 := by
        have h := congrArg (projG (Mo.img H)) heq
        simp only [map_mul, projG_inl, projG_inr, one_mul] at h
        exact Subtype.ext h.symm
      rw [ha1, map_one, mul_one] at heq
      rw [heq]
      exact mem_wHat.mpr ⟨w, hw, rfl⟩
  have hrel : (hatV1 Mo V₀ V ⊓ vHat (Mo.img H)).relIndex (hatV1 Mo V₀ V) =
      2 ^ E3.mQuot V (U ⊔ V₀) := by
    rw [inf_comm, Subgroup.inf_relIndex_right, hatL_vHat_eq_ker Mo, Subgroup.relIndex_ker,
      hatL_Vt_map h1 h5 h15 hS c Mo,
      show Mo.img V = Mo.img (conjSubgroup V 1) from by rw [conjSubgroup_one],
      card_img_conjSubgroup h1 h5 h15 hS c Mo (Subgroup.one_mem H)]
  unfold E3.mQuot
  rw [hWU, hrel, padicValNat.prime_pow]
  rfl

private theorem hatL_U1_ne_bot (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (c : Cfg1620 M V₀ V U S R H g B) :
    wHat (Mo.img H) (Mo.sp V₀) ≠ ⊥ := by
  intro h
  have hsp : Mo.sp V₀ = ⊥ := (wHat_eq_bot_iff (G := Mo.img H)).mp h
  have hV₀bot : V₀ ⊓ conjClosure (U ⊔ V₀) H = ⊥ :=
    (ModDataE.sp_eq_bot_iff (M := Mo)).mp hsp
  rw [show V₀ ⊓ conjClosure (U ⊔ V₀) H = V₀ from
      inf_eq_left.mpr (le_sup_right.trans (le_conjClosure (U ⊔ V₀) H))] at hV₀bot
  exact c.cex.hyp.ne_bot hV₀bot

private theorem hatL_U1_ne_Vt (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    wHat (Mo.img H) (Mo.sp V₀) ≠ hatV1 Mo V₀ V := by
  intro h
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hImgBot : Mo.img V = ⊥ ↔
      V ≤ Subgroup.centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rw [ModDataE.img, Subgroup.map_eq_bot_iff]
    constructor
    · intro hh x hxV
      exact (Mo.ρ_eq_one_iff ⟨x, hVH hxV⟩).1
        (MonoidHom.mem_ker.mp (hh (Subgroup.mem_subgroupOf.mpr hxV)))
    · intro hh j hj
      exact MonoidHom.mem_ker.mpr
        ((Mo.ρ_eq_one_iff j).2 (hh (Subgroup.mem_subgroupOf.mp hj)))
  have hle1 : aHat (Mo.img H) (Mo.img V) ≤ wHat (Mo.img H) ⊤ := by
    have h2 : aHat (Mo.img H) (Mo.img V) ≤ wHat (Mo.img H) (Mo.sp V₀) := by
      rw [h, hatL_Vt_eq h1 h5 h15 hS c Mo]
      exact le_sup_right
    exact h2.trans (wHat_mono le_top)
  have hdisj : aHat (Mo.img H) (Mo.img V) ⊓ wHat (Mo.img H) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxw⟩
    obtain ⟨a, ha, rfl⟩ := mem_aHat.mp hxa
    obtain ⟨v, -, hv⟩ := mem_wHat.mp hxw
    have hh : (a : LGL 2 Mo.W) = 1 := by
      have h' := congrArg (projG (Mo.img H)) hv
      simpa only [map_mul, projG_inl, projG_inr, one_mul] using h'
    rw [show a = 1 from Subtype.ext hh, map_one]
    exact Subgroup.mem_bot.mpr rfl
  have haBot : aHat (Mo.img H) (Mo.img V) = ⊥ := by
    calc aHat (Mo.img H) (Mo.img V)
        = aHat (Mo.img H) (Mo.img V) ⊓ wHat (Mo.img H) ⊤ := (inf_eq_left.mpr hle1).symm
      _ = ⊥ := hdisj
  exact not_le_centralizer_conjClosure h1 h5 h15 hS c ((hImgBot).mp ((aHat_eq_bot_iff
    (Mo.img_mono hVH)).mp haBot))

private theorem hatL_comm_ne_bot (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {g' : G} (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    ⁅hatV1 Mo V₀ V, conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))⁆ ≠ ⊥ := by
  intro h
  have hle : hatV1 Mo V₀ V ≤ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h.trans (Subgroup.centralizer_le_normalizer _)
  have hU : hatV1 Mo V₀ V ⊓ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))) = hatV1 Mo V₀ V :=
    inf_eq_left.mpr hle
  rw [hatL_inf_normalizer h1 h5 h15 hS c Mo hg' hg'M] at hU
  exact hatL_U1_ne_Vt h1 h5 h15 hS c Mo hU

private theorem hatL_hyp7 (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Hyp7 (hatV1 Mo V₀ V) :=
  hyp7_UAOf (assumption131_hat h1 h5 h15 hS c Mo) (mRank_le_hat h1 h5 h15 hS c Mo)
    (A := Mo.img V) (img_mem_hatGamma c Mo)
    (hatVA_le_fixSub h1 h5 h15 hS c Mo (Mo.img V) (img_mem_hatGamma c Mo))

private theorem hatL_B_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {g' : G}
    (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    conjSubgroup (hatV1 Mo V₀ V) (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) ⊓
      Subgroup.normalizer (hatV1 Mo V₀ V) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) := by
  have hg'inv : g'⁻¹ ∈ H ⊓ centralizer (U : Set G) :=
    ⟨H.inv_mem hg'.1, (Subgroup.centralizer (U : Set G)).inv_mem hg'.2⟩
  have hg'invM : g'⁻¹ ∉ M := fun h => hg'M (by simpa using M.inv_mem h)
  have hghinv : hatL_gh Mo g'⁻¹ (H.inv_mem hg'.1) = (hatL_gh Mo g' hg'.1)⁻¹ := by
    apply Subtype.ext
    simp only [hatL_gh, Subgroup.coe_inv]
    rw [show (⟨g'⁻¹, H.inv_mem hg'.1⟩ : ↥H) = (⟨g', hg'.1⟩ : ↥H)⁻¹ from Subtype.ext rfl,
      map_inv]
  have h := hatL_inf_normalizer h1 h5 h15 hS c Mo hg'inv hg'invM
  have hconj := congrArg (fun S : Subgroup (VG (Mo.img H)) => conjSubgroup S
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))) h
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_normalizer] at hconj
  rw [hghinv, map_inv, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hconj
  have hR : conjSubgroup (wHat (Mo.img H) (Mo.sp V₀))
      (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) =
      wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) := by
    have h1' := conjSubgroup_wHat_sup_aHat_inr_inv (V := Mo.W) (G := Mo.img H)
      (Mo.sp V₀) (⊥ : Subgroup (LGL 2 Mo.W)) ((hatL_gh Mo g' hg'.1)⁻¹)
    have haBot : (wHat (Mo.img H) (Mo.sp V₀) ⊔
        aHat (Mo.img H) (⊥ : Subgroup (LGL 2 Mo.W))) = wHat (Mo.img H) (Mo.sp V₀) := by
      rw [(aHat_eq_bot_iff (G := Mo.img H) bot_le).mpr rfl, sup_bot_eq]
    have h2 : conjSub ((hatL_gh Mo g' hg'.1)⁻¹ : LGL 2 Mo.W) (Mo.sp V₀) =
        Mo.sp (conjSubgroup V₀ g') := by
      have hcoe : ((hatL_gh Mo g' hg'.1)⁻¹ : LGL 2 Mo.W) =
          Mo.ρ ((⟨g', hg'.1⟩ : ↥H)⁻¹) := by
        simp only [hatL_gh, map_inv, Subgroup.coe_inv, inv_inv]
      rw [hcoe, ModDataE.conjSub_sp]
      congr 1
      simp only [Subgroup.coe_inv, inv_inv]
    have h2' : aHat (Mo.img H) (cj ((hatL_gh Mo g' hg'.1)⁻¹ : LGL 2 Mo.W)
        (⊥ : Subgroup (LGL 2 Mo.W))) = ⊥ := by
      rw [show cj ((hatL_gh Mo g' hg'.1)⁻¹ : LGL 2 Mo.W)
          (⊥ : Subgroup (LGL 2 Mo.W)) = ⊥ from Subgroup.map_bot _,
        (aHat_eq_bot_iff (G := Mo.img H) bot_le).mpr rfl]
    rw [inv_inv, haBot] at h1'
    simp only [Subgroup.coe_inv] at h1'
    rw [h2, h2', sup_bot_eq] at h1'
    exact h1'
  rw [hR] at hconj
  exact hconj

private theorem hatL_isNaturalSum_rank_le {Q : Type} [Group Q] [Finite Q] {ι F : Type}
    [Fintype ι] [DecidableEq ι] [Field F] [Finite F] (act : Q → Matrix ι ι F) {K : Subgroup Q}
    (h : IsNaturalSum act K) (hK : K ≠ ⊥) {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Fintype.card ι * n ≤ padicValNat 2 (Nat.card K) := by
  classical
  obtain ⟨s, hsup, hsupK, hmod⟩ := h
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hse
    exact hK (by rw [← hsupK, hse, Finset.sup_empty])
  obtain ⟨W, hW⟩ := hsne
  obtain ⟨-, -, -, θ, hadd, hinj, hrange, hconj⟩ := hmod W hW
  have hWK : W ≤ K := by rw [← hsupK]; exact Finset.le_sup (f := id) hW
  have hcardW : Nat.card ↥W = 2 ^ (n * Fintype.card ι) := by
    have e : (ι → F) ≃ ↥W :=
      (Equiv.ofInjective θ hinj).trans (Equiv.subtypeEquivRight (fun x => by rw [hrange]; rfl))
    rw [← Nat.card_congr e, Nat.card_fun, hF, Nat.card_eq_fintype_card, ← pow_mul]
  have hdvd : Nat.card ↥W ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hWK
  have hle := padicValNat_two_le_of_dvd (Nat.card_pos (α := ↥K)).ne' hdvd
  rw [hcardW, padicValNat.prime_pow] at hle
  simpa [Nat.mul_comm] using hle

private theorem hatL_card_wHat {J E : Subgroup G} (Mo : ModDataE J E)
    (W : Submodule (ZMod 2) Mo.W) :
    Nat.card ↥(wHat (Mo.img J) W) = Nat.card ↥W := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun w : ↥W =>
      (⟨SemidirectProduct.inl (Multiplicative.ofAdd (w : Mo.W)),
        mem_wHat.mpr ⟨(w : Mo.W), w.2, rfl⟩⟩ : ↥(wHat (Mo.img J) W))) ?_)).symm
  constructor
  · intro a b hab
    have h1 : (Multiplicative.ofAdd (a : Mo.W) : Multiplicative Mo.W)
        = Multiplicative.ofAdd (b : Mo.W) :=
      SemidirectProduct.inl_injective (Subtype.ext_iff.mp hab)
    exact Subtype.ext (Multiplicative.ofAdd.injective h1)
  · intro x
    obtain ⟨w, hw, hwx⟩ := mem_wHat.mp x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx.symm⟩

private theorem hatL_card_sp {J E : Subgroup G} (Mo : ModDataE J E) (S : Subgroup G) :
    Nat.card ↥(Mo.sp S) = Nat.card ↥(S ⊓ E) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : ↥(S ⊓ E) =>
      (⟨Mo.ι (e : G), Mo.mem_sp.mpr ⟨(e : G), e.2, rfl⟩⟩ : ↥(Mo.sp S))) ?_).symm
  constructor
  · intro a b hab
    exact Subtype.ext (Mo.ι_injOn a.2.2 b.2.2 (Subtype.ext_iff.mp hab))
  · intro w
    obtain ⟨e, he, hwe⟩ := Mo.mem_sp.mp w.2
    exact ⟨⟨e, he⟩, Subtype.ext hwe⟩

private theorem hatL_padic_card_sup {J E : Subgroup G} (Mo : ModDataE J E)
    {A B : Subgroup (VG (Mo.img J))} (hA : A ≤ wHat (Mo.img J) ⊤)
    (hB : B ≤ wHat (Mo.img J) ⊤) (hAB : A ⊓ B = ⊥)
    (hcardA : Nat.card ↥A = Nat.card ↥V₀) (hcardB : Nat.card ↥B = Nat.card ↥V₀) :
    padicValNat 2 (Nat.card ↥(A ⊔ B)) = 2 * mSub V₀ := by
  haveI : Nonempty ↥A := ⟨⟨1, A.one_mem⟩⟩
  haveI : Nonempty ↥B := ⟨⟨1, B.one_mem⟩⟩
  rw [CFSG.Goldschmidt.G74.card_sup_of_inf_eq_bot
      (isElemAbelian_wHat (G := Mo.img J) ⊤).1 hA hB hAB,
    padicValNat.mul (Nat.card_pos (α := ↥A)).ne' (Nat.card_pos (α := ↥B)).ne',
    hcardA, hcardB, mSub, rk]
  ring

theorem hatL_shape (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {g' : G}
    (hg' : g' ∈ H ⊓ centralizer (U : Set G)) (hg'M : g' ∉ M) :
    (CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥(Mo.img (V ⊔ conjSubgroup V g'))
        (E3.mQuot V (U ⊔ V₀)) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz ↥(Mo.img (V ⊔ conjSubgroup V g'))
        (E3.mQuot V (U ⊔ V₀)) ∨
      (E3.mQuot V (U ⊔ V₀) = 1 ∧ ∃ m : ℕ, Odd m ∧
        Nonempty (↥(Mo.img (V ⊔ conjSubgroup V g')) ≃* DihedralGroup m))) ∧
      E3.mQuot V (U ⊔ V₀) ≤ mSub V₀ := by
  classical
  let Vt : Subgroup (VG (Mo.img H)) := hatV1 Mo V₀ V
  let g1 : VG (Mo.img H) := (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H))
  let U1 : Subgroup (VG (Mo.img H)) := Vt ⊓ Subgroup.normalizer (conjSubgroup Vt g1)
  let B1 : Subgroup (VG (Mo.img H)) := conjSubgroup Vt g1 ⊓ Subgroup.normalizer Vt
  let X : Subgroup (VG (Mo.img H)) := Vt ⊔ conjSubgroup Vt g1
  have hVt : Vt = hatV1 Mo V₀ V := rfl
  have hg1 : g1 = (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) := rfl
  have hW3 := w3Lem71_holds (G := VG (Mo.img H)) Vt g1
      (hatL_hyp7 h1 h5 h15 hS c Mo)
      (hatL_gh_not_mem_normalizer h1 h5 h15 hS c Mo hg' hg'M)
      (by
        change (hatV1 Mo V₀ V ⊓ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
          (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)))) ≠ ⊥
        rw [hatL_inf_normalizer h1 h5 h15 hS c Mo hg' hg'M]
        exact hatL_U1_ne_bot Mo c)
      (by
        change (hatV1 Mo V₀ V ⊓ Subgroup.normalizer (conjSubgroup (hatV1 Mo V₀ V)
          (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)))) ≠ hatV1 Mo V₀ V
        rw [hatL_inf_normalizer h1 h5 h15 hS c Mo hg' hg'M]
        exact hatL_U1_ne_Vt h1 h5 h15 hS c Mo)
      (hatL_comm_ne_bot h1 h5 h15 hS c Mo hg' hg'M)
  obtain ⟨hO2, hUB, -, hshape, -, hnat⟩ := hW3
  have hO2' : pCoreOf 2 X = U1 ⊔ B1 := hO2
  have hUB' : U1 ⊓ B1 = ⊥ := hUB
  have hUeq : U1 = wHat (Mo.img H) (Mo.sp V₀) :=
    hatL_inf_normalizer h1 h5 h15 hS c Mo hg' hg'M
  have hBeq : B1 = wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) :=
    hatL_B_eq h1 h5 h15 hS c Mo hg' hg'M
  have hXvHat : X ⊓ vHat (Mo.img H) = pCoreOf 2 X := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
        (by rw [Subgroup.inf_subgroupOf_left]; exact normal_vHat.subgroupOf X)
        (((isElemAbelian_wHat (G := Mo.img H) ⊤).isPGroup).to_le inf_le_right)
    · rw [hO2']
      refine sup_le ?_ ?_
      · intro x hx
        have hx' : x ∈ wHat (Mo.img H) (Mo.sp V₀) := by rwa [hUeq] at hx
        have hxVt : x ∈ Vt := by
          rw [hVt, hatL_Vt_eq h1 h5 h15 hS c Mo]
          exact Subgroup.mem_sup_left hx'
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hxVt, wHat_le_vHat _ hx'⟩
      · intro x hx
        have hx' : x ∈ wHat (Mo.img H) (Mo.sp (conjSubgroup V₀ g')) := by rwa [hBeq] at hx
        have hxW : x ∈ conjSubgroup Vt g1 := by
          rw [hVt, hg1, hatL_W_eq h1 h5 h15 hS c Mo hg'.1]
          exact Subgroup.mem_sup_left hx'
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hxW, wHat_le_vHat _ hx'⟩
  have hψker : ((projG (Mo.img H)).comp X.subtype).ker =
      (X ⊓ vHat (Mo.img H)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [hatL_vHat_eq_ker Mo]
      exact MonoidHom.mem_ker.mpr hx
    · rintro ⟨-, hx⟩
      have hx' : (x : VG (Mo.img H)) ∈ (projG (Mo.img H)).ker := by
        rw [hatL_vHat_eq_ker Mo] at hx
        exact hx
      exact MonoidHom.mem_ker.mp hx'
  have hψker' : ((projG (Mo.img H)).comp X.subtype).ker =
      (pCoreOf 2 X).subgroupOf X := by
    rw [hψker, hXvHat]
  have hψrange : ((projG (Mo.img H)).comp X.subtype).range =
      Mo.img (V ⊔ conjSubgroup V g') := by
    have h : X.map (projG (Mo.img H)) = Mo.img (V ⊔ conjSubgroup V g') := by
      rw [show X = hatV1 Mo V₀ V ⊔ conjSubgroup (hatV1 Mo V₀ V)
        (SemidirectProduct.inr (hatL_gh Mo g' hg'.1) : VG (Mo.img H)) from by
          rw [show X = Vt ⊔ conjSubgroup Vt g1 from rfl, hVt, hg1]]
      exact hatL_X_map h1 h5 h15 hS c Mo hg'.1
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact h
  obtain ⟨Z, hZgrp, φ, hφsurj, hφker, hPZ⟩ := hshape
  letI : Group Z := hZgrp
  have hφker' : φ.ker = (pCoreOf 2 X).subgroupOf X := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker k
  let eφ : ↥X ⧸ φ.ker ≃* Z := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  have hψrk : ((projG (Mo.img H)).comp X.subtype).rangeRestrict.ker =
      ((projG (Mo.img H)).comp X.subtype).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => Subtype.ext_iff.mp h, fun h => Subtype.ext h⟩
  let eψ : ↥X ⧸ ((projG (Mo.img H)).comp X.subtype).ker ≃*
      ↥(Mo.img (V ⊔ conjSubgroup V g')) :=
    (QuotientGroup.quotientMulEquivOfEq hψrk.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective
        ((projG (Mo.img H)).comp X.subtype).rangeRestrict
        ((projG (Mo.img H)).comp X.subtype).rangeRestrict_surjective).trans
          (MulEquiv.subgroupCongr hψrange))
  have hkerEq : φ.ker = ((projG (Mo.img H)).comp X.subtype).ker := by
    rw [hφker', hψker']
  let eZ : Z ≃* ↥(Mo.img (V ⊔ conjSubgroup V g')) :=
    eφ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans eψ)
  have hmq : E3.mQuot V (U ⊔ V₀) = E3.mQuot Vt U1 := by
    rw [← hatL_mQuot_U1 h1 h5 h15 hS c Mo, ← hUeq]
  refine ⟨?_, ?_⟩
  · rcases hPZ with ⟨n, hL2, hn⟩ | ⟨n, hSz, hn⟩ | ⟨m, hm, hD, hn1⟩
    · left
      rw [hmq, hn]
      exact CFSG.Blueprint.LieModel.of_mulEquiv eZ hL2
    · right; left
      rw [hmq, hn]
      exact CFSG.Blueprint.LieModel.of_mulEquiv eZ hSz
    · right; right
      refine ⟨?_, m, hm, ?_⟩
      · rw [hmq]; exact hn1
      · exact ⟨eZ.symm.trans hD.some⟩
  · have hVE : V₀ ⊓ conjClosure (U ⊔ V₀) H = V₀ :=
      inf_eq_left.mpr (le_sup_right.trans (le_conjClosure (U ⊔ V₀) H))
    have hWE : conjSubgroup V₀ g' ⊓ conjClosure (U ⊔ V₀) H = conjSubgroup V₀ g' :=
      inf_eq_left.mpr
        ((E3.conjSubgroup_mono_left g' (le_sup_right : V₀ ≤ U ⊔ V₀)).trans
          (conjSubgroup_le_conjClosure (U ⊔ V₀) H hg'.1))
    have hcardU : Nat.card ↥U1 = Nat.card ↥V₀ := by
      rw [hUeq, hatL_card_wHat Mo, hatL_card_sp Mo, hVE]
    have hcardB : Nat.card ↥B1 = Nat.card ↥V₀ := by
      rw [hBeq, hatL_card_wHat Mo, hatL_card_sp Mo, hWE, E3.card_conjSubgroup]
    have hcore : padicValNat 2 (Nat.card ↥(pCoreOf 2 X)) = 2 * mSub V₀ := by
      rw [hO2']
      refine hatL_padic_card_sup Mo ?_ ?_ hUB' hcardU hcardB
      · rw [hUeq]; exact wHat_le_vHat _
      · rw [hBeq]; exact wHat_le_vHat _
    have hKne : (pCoreOf 2 X).subgroupOf X ≠ ⊥ := by
      intro h
      have hbot : pCoreOf 2 X = ⊥ := by
        rw [← inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X)]
        exact disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp h)
      have hU1bot : U1 = ⊥ := by
        have hle : U1 ≤ pCoreOf 2 X := by rw [hO2']; exact le_sup_left
        exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
      exact hatL_U1_ne_bot Mo c (hUeq ▸ hU1bot)
    have hcardK : Nat.card ↥((pCoreOf 2 X).subgroupOf X) =
        Nat.card ↥(pCoreOf 2 X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).toEquiv
    rcases hnat with ⟨n, F, hFf, hFfin, hFc, hFcard, hn, act, -, hnatS⟩ |
        ⟨a, F, hFf, hFfin, hFc, hFcard, hn, act, -, hnatS⟩ |
        ⟨m, hm, hn1, -, -⟩
    · letI : Field F := hFf
      letI : Finite F := hFfin
      haveI : CharP F 2 := hFc
      have hbound := hatL_isNaturalSum_rank_le (Q := ↥X) (ι := Fin 2) (F := F)
        (fun x : ↥X => act x) hnatS hKne hFcard
      simp only [Fintype.card_fin] at hbound
      rw [hcardK, hcore] at hbound
      rw [hmq, hn]
      omega
    · letI : Field F := hFf
      letI : Finite F := hFfin
      haveI : CharP F 2 := hFc
      have hbound := hatL_isNaturalSum_rank_le (Q := ↥X) (ι := Fin 4) (F := F)
        (fun x : ↥X => act x) hnatS hKne hFcard
      simp only [Fintype.card_fin] at hbound
      rw [hcardK, hcore] at hbound
      rw [hmq, hn]
      omega
    · rw [hmq]; rw [hn1]
      exact one_le_mSub_of_ne_bot c.cex.hyp.elemAbelian₀ c.cex.hyp.ne_bot

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

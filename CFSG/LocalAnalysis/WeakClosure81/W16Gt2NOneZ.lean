module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneLin
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneImg
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

private theorem le_normalizer_inf_centralizer_I :
    H ≤ Subgroup.normalizer
      ((H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) : Subgroup G) : Set G) := fun h hh =>
  mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hh)
    (le_normalizer_conjClosure (U ⊔ V₀) H hh)

private theorem commutator_conj_mem_of_mem {y : G} (hyH : y ∈ H)
    (hy : ∀ k ∈ conjClosure V H,
      ⁅y, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))
    {h : G} (hh : h ∈ H) :
    ∀ k ∈ conjClosure V H,
      ⁅h * y * h⁻¹, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  intro k hk
  have hk' : h⁻¹ * k * h ∈ conjClosure V H := by
    have hnorm : h⁻¹ ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
      le_normalizer_conjClosure V H (H.inv_mem hh)
    simpa using (Subgroup.mem_normalizer_iff.1 hnorm k).1 hk
  have h1 := hy (h⁻¹ * k * h) hk'
  have hkey : h * ⁅y, h⁻¹ * k * h⁆ * h⁻¹ = ⁅h * y * h⁻¹, k⁆ := by
    rw [conjugate_commutatorElement]
    rw [show h * (h⁻¹ * k * h) * h⁻¹ = k by group]
  have hmem : h * ⁅y, h⁻¹ * k * h⁆ * h⁻¹ ∈
      H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_inf_centralizer_I hh)
      (⁅y, h⁻¹ * k * h⁆)).1 h1
  rwa [hkey] at hmem

private theorem commutator_inv_mem_of_mem {y : G} (hyH : y ∈ H)
    (hy : ∀ k ∈ conjClosure V H,
      ⁅y, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    ∀ k ∈ conjClosure V H,
      ⁅y⁻¹, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  intro k hk
  have hkey : y * ⁅y⁻¹, k⁆ * y⁻¹ = ⁅y, k⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  have hmem : y * ⁅y⁻¹, k⁆ * y⁻¹ ∈
      H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rw [hkey]
    exact Subgroup.inv_mem _ (hy k hk)
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_inf_centralizer_I hyH) (⁅y⁻¹, k⁆)).2 hmem

private theorem conj_mem_inf_centralizer_conjSubgroup_L
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {b : G}
    (hb : b ∈ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)))
    {y : G} (hyH : y ∈ H) (hyM : y ∈ M)
    (hy : ∀ k ∈ conjClosure V H,
      ⁅y, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    ∀ w ∈ (U ⊔ V₀) ⊓ centralizer (conjSubgroup (V ⊔ conjSubgroup V g) b : Set G),
      y * w * y⁻¹ ∈ (U ⊔ V₀) ⊓ centralizer (conjSubgroup (V ⊔ conjSubgroup V g) b : Set G) := by
  have hbH : b ∈ H := c.mem.1 hb.1
  have hLbK : conjSubgroup (V ⊔ conjSubgroup V g) b ≤ conjClosure V H :=
    conjSubgroup_L_le_conjClosure c hbH
  have hyN : y ∈ Subgroup.normalizer ((U ⊔ V₀ : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_inf h1 h5 h15 hS c ⟨hyH, hyM⟩
  intro w hw
  have hwUV : w ∈ U ⊔ V₀ := (Subgroup.mem_inf.1 hw).1
  have hwC : w ∈ centralizer (conjSubgroup (V ⊔ conjSubgroup V g) b : Set G) :=
    (Subgroup.mem_inf.1 hw).2
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN w).1 hwUV, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxK : x ∈ conjClosure V H := hLbK hx
  have hcxC : ⁅y, x⁆ ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) := (hy x hxK).2
  have hyx : y * x * y⁻¹ = ⁅y, x⁆ * x := by
    rw [commutatorElement_def]
    group
  have hxy : x * y = ⁅y, x⁆⁻¹ * y * x := by
    calc x * y = ⁅y, x⁆⁻¹ * (⁅y, x⁆ * x) * y := by group
      _ = ⁅y, x⁆⁻¹ * (y * x * y⁻¹) * y := by rw [← hyx]
      _ = ⁅y, x⁆⁻¹ * y * x := by group
  have hxwx : x * w * x⁻¹ = w := by
    have h := Subgroup.mem_centralizer_iff.1 hwC x hx
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [h]
      _ = w := by group
  have hzI : y * w * y⁻¹ ∈ conjClosure (U ⊔ V₀) H :=
    le_conjClosure (U ⊔ V₀) H ((Subgroup.mem_normalizer_iff.1 hyN w).1 hwUV)
  have hfix : ⁅y, x⁆⁻¹ * (y * w * y⁻¹) * ⁅y, x⁆ = y * w * y⁻¹ := by
    have hcomm : (y * w * y⁻¹) * ⁅y, x⁆ = ⁅y, x⁆ * (y * w * y⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hcxC (y * w * y⁻¹) hzI
    calc ⁅y, x⁆⁻¹ * (y * w * y⁻¹) * ⁅y, x⁆
        = ⁅y, x⁆⁻¹ * ((y * w * y⁻¹) * ⁅y, x⁆) := by group
      _ = ⁅y, x⁆⁻¹ * (⁅y, x⁆ * (y * w * y⁻¹)) := by rw [hcomm]
      _ = y * w * y⁻¹ := by group
  have hmain : x * (y * w * y⁻¹) * x⁻¹ = y * w * y⁻¹ := by
    calc x * (y * w * y⁻¹) * x⁻¹
        = (x * y) * w * (x * y)⁻¹ := by group
      _ = (⁅y, x⁆⁻¹ * y * x) * w * (⁅y, x⁆⁻¹ * y * x)⁻¹ := by rw [hxy]
      _ = ⁅y, x⁆⁻¹ * (y * (x * w * x⁻¹) * y⁻¹) * ⁅y, x⁆ := by group
      _ = ⁅y, x⁆⁻¹ * (y * w * y⁻¹) * ⁅y, x⁆ := by rw [hxwx]
      _ = y * w * y⁻¹ := hfix
  calc x * (y * w * y⁻¹) = (x * (y * w * y⁻¹) * x⁻¹) * x := by group
    _ = (y * w * y⁻¹) * x := by rw [hmain]

private theorem mem_normalizer_inf_centralizer_conjSubgroup_L
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {b : G}
    (hb : b ∈ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)))
    {y : G} (hyH : y ∈ H) (hyM : y ∈ M)
    (hy : ∀ k ∈ conjClosure V H,
      ⁅y, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    y ∈ Subgroup.normalizer
      (((U ⊔ V₀) ⊓ centralizer (conjSubgroup (V ⊔ conjSubgroup V g) b : Set G) :
        Subgroup G) : Set G) := by
  have hfw := conj_mem_inf_centralizer_conjSubgroup_L h1 h5 h15 hS c hb hyH hyM hy
  have hbw := conj_mem_inf_centralizer_conjSubgroup_L h1 h5 h15 hS c hb
    (H.inv_mem hyH) (M.inv_mem hyM) (commutator_inv_mem_of_mem hyH hy)
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h2 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [← h2]
    simpa using hbw (y * x * y⁻¹) hx
  · intro w hw
    rw [mem_conjSubgroup_iff]
    exact hfw w hw

theorem mem_centralizer_sup_of_comm_mem (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {z : G}
    (hzK : z ∈ conjClosure V H)
    (hz : ∀ k ∈ conjClosure V H,
      ⁅z, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    z ∈ centralizer ((U ⊔ V₀ : Subgroup G) : Set G) := by
  have hzH : z ∈ H := conjClosure_le_H c hzK
  have hzM : z ∈ M := by
    have hle : conjSubgroup V z⁻¹ ≤
        V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hwV : z⁻¹ * x * z ∈ V := by simpa using hx
      have hcomm : ⁅z, z⁻¹ * x * z⁆ ∈
          H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
        hz (z⁻¹ * x * z) (le_conjClosure V H hwV)
      have hx_eq : x = ⁅z, z⁻¹ * x * z⁆ * (z⁻¹ * x * z) := by
        rw [commutatorElement_def]
        group
      rw [hx_eq]
      exact (V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))).mul_mem
        (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hwV)
    have hzinvM : z⁻¹ ∈ M :=
      (conjSubgroup_le_sup_iff h1 h5 h15 hS c (y := z⁻¹) (H.inv_mem hzH)).1 hle
    simpa using M.inv_mem hzinvM
  have hzN : z ∈ Subgroup.normalizer ((U ⊔ V₀ : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_inf h1 h5 h15 hS c ⟨hzH, hzM⟩
  have hzNV₀ : z ∈ Subgroup.normalizer (V₀ : Set G) := by
    rw [c.cex.hyp.normalizer₀]
    exact hzM
  refine NOne.mem_centralizer_of_conj_eq_complements (A₁ := U) (A₂ := V₀)
    (B2F.isElemAbelian_mono (sup_le c.cex.le c.cex.hyp.h6.le) c.cex.hyp.h6.elemAbelian)
    c.cex.ne_bot c.cex.hyp.ne_bot c.cex.inf_eq_bot hzN hzNV₀ ?_
  intro D hDle hDinf hDsup
  obtain ⟨b, hb, hbD⟩ := exists_mem_inf_conj_eq h1 hS c hn hDle hDinf hDsup
  have hbA : b ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 hb).2
  have hnorm := mem_normalizer_inf_centralizer_conjSubgroup_L h1 h5 h15 hS c hb hzH hzM hz
  rw [inf_centralizer_conjSubgroup_L c hbA, hbD] at hnorm
  exact hnorm

theorem mem_inf_centralizer_of_comm_mem (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {z : G}
    (hzK : z ∈ conjClosure V H)
    (hz : ∀ k ∈ conjClosure V H,
      ⁅z, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    z ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  have hzH : z ∈ H := conjClosure_le_H c hzK
  have hIle : conjClosure (U ⊔ V₀) H ≤ Subgroup.centralizer ({z} : Set G) := by
    refine conjClosure_le ?_
    intro h hh w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hz'K : h⁻¹ * z * h ∈ conjClosure V H := by
      have hnorm : h⁻¹ ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
        le_normalizer_conjClosure V H (H.inv_mem hh)
      simpa using (Subgroup.mem_normalizer_iff.1 hnorm z).1 hzK
    have hz' : ∀ k ∈ conjClosure V H,
        ⁅h⁻¹ * z * h, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      intro k hk
      simpa using commutator_conj_mem_of_mem hzH hz (H.inv_mem hh) k hk
    have hcent := mem_centralizer_sup_of_comm_mem h1 h5 h15 hS c hn hz'K hz'
    have hw' := Subgroup.mem_centralizer_iff.1 hcent w hw
    have hmain : h * w * h⁻¹ * z = z * (h * w * h⁻¹) := by
      calc h * w * h⁻¹ * z = h * (w * (h⁻¹ * z * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * z * h) * w) * h⁻¹ := by rw [hw']
        _ = z * (h * w * h⁻¹) := by group
    exact hmain.symm
  have hcent : z ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact (Subgroup.mem_centralizer_iff.1 (hIle hi) z (Set.mem_singleton z)).symm
  exact ⟨hzH, hcent⟩

theorem eq_one_of_comm_img (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {z : LGL 2 Mo.W} (hz : z ∈ Mo.img (conjClosure V H))
    (hzc : ∀ k ∈ Mo.img (conjClosure V H), z * k = k * z) : z = 1 := by
  obtain ⟨j, hjK, hjρ⟩ := Mo.mem_img.1 hz
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have hzj : ∀ k ∈ conjClosure V H,
      ⁅(j : G), k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    intro k hk
    have hkH : k ∈ H := hKH hk
    have hkimg : Mo.ρ ⟨k, hkH⟩ ∈ Mo.img (conjClosure V H) :=
      Mo.mem_img.2 ⟨⟨k, hkH⟩, hk, rfl⟩
    have hcomm : z * Mo.ρ ⟨k, hkH⟩ = Mo.ρ ⟨k, hkH⟩ * z := hzc _ hkimg
    have hcommK : ⁅(j : G), k⁆ ∈ conjClosure V H := by
      rw [commutatorElement_def]
      exact (conjClosure V H).mul_mem
        ((conjClosure V H).mul_mem ((conjClosure V H).mul_mem hjK hk)
          ((conjClosure V H).inv_mem hjK)) ((conjClosure V H).inv_mem hk)
    have hcommH : ⁅(j : G), k⁆ ∈ H := hKH hcommK
    have hsub : (⟨⁅(j : G), k⁆, hcommH⟩ : ↥H) = ⁅j, ⟨k, hkH⟩⁆ := rfl
    have hρ1 : Mo.ρ ⟨⁅(j : G), k⁆, hcommH⟩ = 1 := by
      rw [hsub, map_commutatorElement, hjρ]
      rw [commutatorElement_def, hcomm]
      group
    exact ⟨hcommH, (Mo.ρ_eq_one_iff ⟨⁅(j : G), k⁆, hcommH⟩).1 hρ1⟩
  have hzjCH : (j : G) ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
    mem_inf_centralizer_of_comm_mem h1 h5 h15 hS c hn hjK hzj
  rw [← hjρ]
  exact (Mo.ρ_eq_one_iff j).2 hzjCH.2

theorem eq_zero_of_apply_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {t y : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) (hy : y ∈ Mo.img H) (hy1 : y ≠ 1)
    (hyo : Odd (orderOf y)) (hty : t * y * t⁻¹ = y⁻¹) {w : Mo.W} (hw : w ∈ Mo.sp V₀)
    (hyw : y w = w) : w = 0 := by
  by_contra hw0
  obtain ⟨e, he, hew⟩ := Mo.mem_sp.1 hw
  have heV₀ : e ∈ V₀ := he.1
  have heI : e ∈ conjClosure (U ⊔ V₀) H := he.2
  have he1 : e ≠ 1 := by
    intro h
    exact hw0 (by rw [← hew, h, Mo.ι_one])
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have ht2 : t * t = 1 := by
    have hcard := card_img_eq_two h1 h5 h15 hS c Mo hn
    have hz := img_eq_zpowers h1 h5 h15 hS c Mo hn ht ht1
    have h1' : orderOf t = 2 := by
      have h2 : Nat.card (Subgroup.zpowers t) = orderOf t := Nat.card_zpowers t
      rw [← hz, hcard] at h2
      exact h2.symm
    have h3 := pow_orderOf_eq_one t
    rwa [h1', pow_two] at h3
  obtain ⟨x, hxzp, hxconj⟩ := NOne.exists_mem_zpowers_conj_eq ht2 hty hyo
  have hxH : x ∈ Mo.img H := (Subgroup.zpowers_le.2 hy) hxzp
  obtain ⟨j, hjH, hjρ⟩ := Mo.mem_img.1 hxH
  let t' : LGL 2 Mo.W := y * t
  have ht'_eq : t' = x⁻¹ * t * x := hxconj.symm
  have ht'2 : t' * t' = 1 := by
    rw [ht'_eq]
    calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
      _ = 1 := by rw [ht2]; group
  have ht'ne : t' ≠ 1 := by
    intro h
    apply ht1
    have h2 : x * t' * x⁻¹ = 1 := by rw [h]; group
    rwa [ht'_eq, show x * (x⁻¹ * t * x) * x⁻¹ = t by group] at h2
  have hρinv : Mo.ρ (j⁻¹) = x⁻¹ := by rw [map_inv, hjρ]
  have hconj := Mo.img_conj (A := V) hVH (j⁻¹)
  rw [show (((j⁻¹ : ↥H) : G))⁻¹ = (j : G) by simp] at hconj
  have ht'_mem : t' ∈ Mo.img (conjSubgroup V (j : G)) := by
    rw [← hconj, mem_cj, hρinv, inv_inv, ht'_eq,
      show x * (x⁻¹ * t * x) * x⁻¹ = t by group]
    exact ht
  have hcardVh : Nat.card (Mo.img (conjSubgroup V (j : G))) = 2 := by
    have h := card_img_conjSubgroup h1 h5 h15 hS c Mo (x := (j : G)) hjH
    rw [hn] at h
    simpa using h
  have htw : t w = w := by
    obtain ⟨v₁, hv₁, hρv₁⟩ := Mo.mem_img.1 ht
    have hcomm : (v₁ : G) * e = e * (v₁ : G) :=
      B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hv₁ (c.cex.hyp.h6.le heV₀)
    rw [← hew, ← hρv₁, Mo.ρ_ι v₁ e heI]
    rw [show (v₁ : G) * e * (v₁ : G)⁻¹ = e by rw [hcomm]; group]
  have ht'w : t' w = w := by
    show (y * t) w = w
    rw [LinearEquiv.mul_apply, htw, hyw]
  have hVjH : conjSubgroup V (j : G) ≤ H :=
    (conjSubgroup_le_conjClosure_of_mem hjH (le_rfl : V ≤ V)).trans hKH
  have hfix_pair : ∀ v : ↥H, (v : G) ∈ conjSubgroup V (j : G) → Mo.ρ v w = w := by
    intro v hv
    have hmem : Mo.ρ v ∈ Mo.img (conjSubgroup V (j : G)) := Mo.mem_img.2 ⟨v, hv, rfl⟩
    by_cases hv1 : Mo.ρ v = 1
    · rw [hv1]
      rfl
    · rw [CFSG.ShultStronglyClosedTI.eq_of_ne_one_of_card_two
        (Mo.img (conjSubgroup V (j : G))) hcardVh ht'_mem ht'ne hmem hv1]
      exact ht'w
  have hVh_cent : conjSubgroup V (j : G) ≤ Subgroup.centralizer ({e} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hvH : v ∈ H := hVjH hv
    have hvI : v * e * v⁻¹ ∈ conjClosure (U ⊔ V₀) H :=
      (Subgroup.mem_normalizer_iff.1
        (le_normalizer_conjClosure (U ⊔ V₀) H hvH) e).1 heI
    have hιeq : Mo.ι (v * e * v⁻¹) = Mo.ι e := by
      rw [← Mo.ρ_ι ⟨v, hvH⟩ e heI, hew]
      exact hfix_pair ⟨v, hvH⟩ hv
    have hve : v * e * v⁻¹ = e := Mo.ι_injOn hvI heI hιeq
    have h2 : v * e = e * v := by
      calc v * e = (v * e * v⁻¹) * v := by group
        _ = e * v := by rw [hve]
    exact h2.symm
  have hVhM : conjSubgroup V (j : G) ≤ M :=
    hVh_cent.trans (c.cex.hyp.centralizer_le heV₀ he1)
  have ht'_HM : t' ∈ Mo.img (H ⊓ M) :=
    Mo.img_mono (le_inf hVjH hVhM) ht'_mem
  have ht't : t' * t = t * t' := img_commute_of_mem_inf h1 h5 h15 hS c Mo hn ht'_HM ht
  have hy_eq : y = t' * t := by
    have h : (y * t) * t = y := by rw [mul_assoc, ht2, mul_one]
    rw [show t' = y * t from rfl]
    exact h.symm
  have hyy : y * y = 1 := by
    rw [hy_eq]
    calc (t' * t) * (t' * t) = t' * (t * t') * t := by group
      _ = t' * (t' * t) * t := by rw [← ht't]
      _ = (t' * t') * (t * t) := by group
      _ = 1 := by rw [ht'2, ht2, mul_one]
  have hdvd : orderOf y ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hyy
  have horder1 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      rw [h] at hyo
      obtain ⟨k, hk⟩ := hyo
      omega
  exact hy1 (orderOf_eq_one_iff.1 horder1)

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoB

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

private theorem conjSubgroup_le_H (c : Cfg1620 M V₀ V U S R H g B) :
    conjSubgroup V g ≤ H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hx']
  exact H.mul_mem (H.mul_mem (H.inv_mem c.g_mem.1) ((c.V_le_R.trans c.mem.1) hx)) c.g_mem.1

private theorem hatBarSub_conjSubgroup_eq (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (kk : ↥H)
    (hkK : (kk : G) ∈ conjClosure V H) :
    hatBarSub Mo V (conjSubgroup V (kk : G)) =
      conjSubgroup (hatBarSub Mo V V)
        (hatBar Mo V ⟨Mo.ρ kk, Mo.mem_img.2 ⟨kk, hkK, rfl⟩⟩) := by
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hrK : Mo.ρ kk ∈ hatK Mo V := Mo.mem_img.2 ⟨kk, hkK, rfl⟩
  have himg : Mo.img (conjSubgroup V (kk : G)) = cj (Mo.ρ kk⁻¹) (Mo.img V) := by
    have h := Mo.img_conj (A := V) hVH kk⁻¹
    simpa using h.symm
  change hatBarSub Mo V (conjSubgroup V (kk : G)) =
    conjSubgroup (hatBarSub Mo V V) (hatBar Mo V ⟨Mo.ρ kk, hrK⟩)
  ext y
  constructor
  · intro hy
    rw [mem_hatBarSub_iff] at hy
    obtain ⟨x, hxmem, hxy⟩ := hy
    rw [himg, mem_cj, map_inv, inv_inv] at hxmem
    let x' : ↥(hatK Mo V) :=
      ⟨Mo.ρ kk * (x : LGL 2 Mo.W) * (Mo.ρ kk)⁻¹,
        (hatK Mo V).mul_mem ((hatK Mo V).mul_mem hrK x.2) ((hatK Mo V).inv_mem hrK)⟩
    have hx'mem : (x' : LGL 2 Mo.W) ∈ Mo.img V := by
      change Mo.ρ kk * (x : LGL 2 Mo.W) * (Mo.ρ kk)⁻¹ ∈ Mo.img V
      exact hxmem
    have hx'eq : x' =
        (⟨Mo.ρ kk, hrK⟩ : ↥(hatK Mo V)) * x * (⟨Mo.ρ kk, hrK⟩ : ↥(hatK Mo V))⁻¹ :=
      Subtype.ext rfl
    have hπ : hatBar Mo V x' =
        hatBar Mo V ⟨Mo.ρ kk, hrK⟩ * y * (hatBar Mo V ⟨Mo.ρ kk, hrK⟩)⁻¹ := by
      rw [hx'eq, map_mul, map_mul, map_inv, hxy]
    rw [mem_conjSubgroup_iff, mem_hatBarSub_iff]
    exact ⟨x', hx'mem, hπ⟩
  · intro hy
    rw [mem_conjSubgroup_iff] at hy
    rw [mem_hatBarSub_iff] at hy
    obtain ⟨x', hx'mem, hx'y⟩ := hy
    let x : ↥(hatK Mo V) :=
      ⟨(Mo.ρ kk)⁻¹ * (x' : LGL 2 Mo.W) * Mo.ρ kk,
        (hatK Mo V).mul_mem ((hatK Mo V).mul_mem ((hatK Mo V).inv_mem hrK) x'.2) hrK⟩
    have hxmem : (x : LGL 2 Mo.W) ∈ Mo.img (conjSubgroup V (kk : G)) := by
      rw [himg, mem_cj, map_inv, inv_inv]
      change Mo.ρ kk * ((Mo.ρ kk)⁻¹ * (x' : LGL 2 Mo.W) * Mo.ρ kk) * (Mo.ρ kk)⁻¹ ∈ Mo.img V
      have hval : Mo.ρ kk * ((Mo.ρ kk)⁻¹ * (x' : LGL 2 Mo.W) * Mo.ρ kk) * (Mo.ρ kk)⁻¹ =
          (x' : LGL 2 Mo.W) := by group
      rw [hval]
      exact hx'mem
    have hxeq : x = (⟨Mo.ρ kk, hrK⟩ : ↥(hatK Mo V))⁻¹ * x' * ⟨Mo.ρ kk, hrK⟩ :=
      Subtype.ext rfl
    have hπ : hatBar Mo V x = y := by
      rw [hxeq, map_mul, map_mul, map_inv, hx'y]
      group
    rw [mem_hatBarSub_iff]
    exact ⟨x, hxmem, hπ⟩

theorem hatBarSub_sup (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    hatBarSub Mo V (V ⊔ conjSubgroup V g) =
      hatBarSub Mo V V ⊔ hatBarSub Mo V (conjSubgroup V g) := by
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hVgH : conjSubgroup V g ≤ H := conjSubgroup_le_H c
  have hmonoV : Mo.img V ≤ hatK Mo V := Mo.img_mono (le_conjClosure V H)
  have hmonoVg : Mo.img (conjSubgroup V g) ≤ hatK Mo V :=
    Mo.img_mono (conjSubgroup_le_conjClosure_of_mem c.g_mem.1 le_rfl)
  simp only [hatBarSub, Mo.img_sup hVH hVgH, Subgroup.subgroupOf_sup hmonoV hmonoVg,
    Subgroup.map_sup]

theorem isElemAbelian_hatBarSub (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    IsElemAbelian 2 (hatBarSub Mo V V) := by
  have hE : IsElemAbelian 2 (V.subgroupOf H) :=
    IsElemAbelian.subgroupOf c.cex.hyp.h6.elemAbelian H
  have h1 : IsElemAbelian 2 (Mo.img V) := IsElemAbelian.map hE Mo.ρ
  have h2 : IsElemAbelian 2 ((Mo.img V).subgroupOf (hatK Mo V)) :=
    IsElemAbelian.subgroupOf h1 (hatK Mo V)
  simpa only [hatBarSub] using IsElemAbelian.map h2 (hatBar Mo V)

theorem exists_conj_hatBarSub_of_mem (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G}
    (hh : h ∈ H) :
    ∃ γ : hatX Mo V ⧸ Subgroup.center (hatX Mo V),
      hatBarSub Mo V (conjSubgroup V h) = conjSubgroup (hatBarSub Mo V V) γ := by
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  obtain ⟨k, hkK, hk_eq, -⟩ := c.exists_mem_conjClosure_conjSubgroup_eq h15 hS hh
  let kk : ↥H := ⟨k, hKH hkK⟩
  have hkK' : (kk : G) ∈ conjClosure V H := hkK
  refine ⟨hatBar Mo V ⟨Mo.ρ kk, Mo.mem_img.2 ⟨kk, hkK', rfl⟩⟩, ?_⟩
  rw [hk_eq]
  exact hatBarSub_conjSubgroup_eq c Mo kk hkK'

theorem exists_mem_conj_hatBarSub (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (γ : hatX Mo V ⧸ Subgroup.center (hatX Mo V)) :
    ∃ h ∈ H, hatBarSub Mo V (conjSubgroup V h) = conjSubgroup (hatBarSub Mo V V) γ := by
  obtain ⟨x₀, hx₀⟩ := hatBar_surjective Mo V γ
  obtain ⟨kk, hkk, hρ⟩ := Mo.mem_img.1 x₀.2
  have hγ : hatBar Mo V ⟨Mo.ρ kk, Mo.mem_img.2 ⟨kk, hkk, rfl⟩⟩ = γ := by
    have hx₀eq : (⟨Mo.ρ kk, Mo.mem_img.2 ⟨kk, hkk, rfl⟩⟩ : ↥(hatK Mo V)) = x₀ :=
      Subtype.ext hρ
    rw [hx₀eq, hx₀]
  refine ⟨(kk : G), kk.2, ?_⟩
  rw [← hγ]
  exact hatBarSub_conjSubgroup_eq c Mo kk hkk

end NoCert

section Certified


theorem img_normalizes_of_bar_normalizes (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {J : Subgroup G} (hJ : J ≤ V ⊔ conjSubgroup V g)
    {x : ↥(hatK Mo V)} (hxL : (x : LGL 2 Mo.W) ∈ Mo.img (V ⊔ conjSubgroup V g))
    (hx : hatBar Mo V x ∈ Subgroup.normalizer (↑(hatBarSub Mo V J) :
      Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V)))) :
    ∀ a ∈ Mo.img J, (x : LGL 2 Mo.W) * a * (x : LGL 2 Mo.W)⁻¹ ∈ Mo.img J := by
  intro a haJ
  have haL : a ∈ Mo.img (V ⊔ conjSubgroup V g) := Mo.img_mono hJ haJ
  have haK : a ∈ hatK Mo V := (Mo.img_mono c.L_le_conjClosure) haL
  let aK : ↥(hatK Mo V) := ⟨a, haK⟩
  let y : ↥(hatK Mo V) := x * aK * x⁻¹
  have hyL : (y : LGL 2 Mo.W) ∈ Mo.img (V ⊔ conjSubgroup V g) := by
    change (x : LGL 2 Mo.W) * a * (x : LGL 2 Mo.W)⁻¹ ∈ Mo.img (V ⊔ conjSubgroup V g)
    exact (Mo.img (V ⊔ conjSubgroup V g)).mul_mem
      ((Mo.img (V ⊔ conjSubgroup V g)).mul_mem hxL haL)
      ((Mo.img (V ⊔ conjSubgroup V g)).inv_mem hxL)
  have hπy : hatBar Mo V y ∈ hatBarSub Mo V J := by
    have hπaK : hatBar Mo V aK ∈ hatBarSub Mo V J := by
      rw [mem_hatBarSub_iff]
      exact ⟨aK, by change a ∈ Mo.img J; exact haJ, rfl⟩
    have hyeq : hatBar Mo V y = hatBar Mo V x * hatBar Mo V aK * (hatBar Mo V x)⁻¹ := by
      change hatBar Mo V (x * aK * x⁻¹) = _
      rw [map_mul, map_mul, map_inv]
    rw [hyeq]
    exact (Subgroup.mem_normalizer_iff.1 hx (hatBar Mo V aK)).1 hπaK
  rw [mem_hatBarSub_iff] at hπy
  obtain ⟨a'', ha''J, hπa''⟩ := hπy
  have hker : a''⁻¹ * y ∈ (hatBar Mo V).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπa'', inv_mul_cancel]
  have hcent : a''⁻¹ * y ∈ Subgroup.center ↥(hatK Mo V) := by
    rw [← ker_hatBar hn h1 h5 h15 hS c Mo]
    exact hker
  have hzL : ((a''⁻¹ * y : ↥(hatK Mo V)) : LGL 2 Mo.W) ∈
      Mo.img (V ⊔ conjSubgroup V g) :=
    (Mo.img (V ⊔ conjSubgroup V g)).mul_mem
      ((Mo.img (V ⊔ conjSubgroup V g)).inv_mem (Mo.img_mono hJ ha''J)) hyL
  have hone : a''⁻¹ * y = 1 := inf_center_hatL hn h1 h5 h15 hS c Mo (a''⁻¹ * y) hzL hcent
  have hy_eq : y = a'' := by
    calc y = 1 * y := (one_mul y).symm
      _ = (a'' * a''⁻¹) * y := by rw [mul_inv_cancel]
      _ = a'' * (a''⁻¹ * y) := by rw [mul_assoc]
      _ = a'' * 1 := by rw [hone]
      _ = a'' := mul_one a''
  change (y : LGL 2 Mo.W) ∈ Mo.img J
  rw [hy_eq]
  exact ha''J

theorem inf_normalizer_hatBarSub (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ x ∈ hatBarSub Mo V V,
      x ∈ Subgroup.normalizer (↑(hatBarSub Mo V (conjSubgroup V g)) :
        Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))) → x = 1 := by
  intro x hxV hxN
  rw [mem_hatBarSub_iff] at hxV
  obtain ⟨vhat, hvV, hvx⟩ := hxV
  have hVgH : conjSubgroup V g ≤ H := conjSubgroup_le_H c
  have hvL : (vhat : LGL 2 Mo.W) ∈ Mo.img (V ⊔ conjSubgroup V g) :=
    Mo.img_mono le_sup_left hvV
  have hxN' : hatBar Mo V vhat ∈ Subgroup.normalizer
      (↑(hatBarSub Mo V (conjSubgroup V g)) :
        Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))) := by
    rw [hvx]
    exact hxN
  have hnorm := img_normalizes_of_bar_normalizes hn h1 h5 h15 hS c Mo
    (J := conjSubgroup V g) le_sup_right hvL hxN'
  obtain ⟨j, hjV, hjv⟩ := Mo.mem_img.1 hvV
  have hconj : ∀ w ∈ conjSubgroup V g,
      (j : G) * w * (j : G)⁻¹ ∈
        conjSubgroup V g ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
    intro w hw
    have hwH : w ∈ H := hVgH hw
    have hxH : (j : G) * w * (j : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem j.2 hwH) (H.inv_mem j.2)
    have hmem : Mo.ρ (⟨(j : G) * w * (j : G)⁻¹, hxH⟩ : ↥H) ∈
        Mo.img (conjSubgroup V g) := by
      have h := hnorm (Mo.ρ ⟨w, hwH⟩) (Mo.mem_img.2 ⟨⟨w, hwH⟩, hw, rfl⟩)
      rw [← hjv] at h
      have he : Mo.ρ (⟨(j : G) * w * (j : G)⁻¹, hxH⟩ : ↥H) =
          Mo.ρ j * Mo.ρ ⟨w, hwH⟩ * (Mo.ρ j)⁻¹ := by
        rw [show (⟨(j : G) * w * (j : G)⁻¹, hxH⟩ : ↥H) =
            (⟨j, j.2⟩ : ↥H) * ⟨w, hwH⟩ * (⟨j, j.2⟩ : ↥H)⁻¹ from Subtype.ext rfl,
          map_mul, map_mul, map_inv]
      rw [he]
      exact h
    exact (Mo.ρ_mem_img_iff hVgH hxH).1 hmem
  have hjU : (j : G) ∈ U ⊔ V₀ :=
    mem_sup_of_normalizes_conj h1 h5 h15 hS c c.g_mem c.g_not hjV hconj
  have hjcent : (j : G) ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi
      (le_conjClosure (U ⊔ V₀) H hjU)
  have hρ1 : Mo.ρ j = 1 := (Mo.ρ_eq_one_iff j).2 hjcent
  have hv1 : vhat = 1 := by
    apply Subtype.ext
    rw [← hjv, hρ1]
    rfl
  rw [← hvx, hv1, map_one]

theorem not_comm_hatBarSub (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ¬ ∀ a ∈ hatBarSub Mo V V, ∀ b ∈ hatBarSub Mo V (conjSubgroup V g), a * b = b * a := by
  intro hcomm
  have hN : ∀ a ∈ hatBarSub Mo V V,
      a ∈ Subgroup.normalizer (↑(hatBarSub Mo V (conjSubgroup V g)) :
        Set (hatX Mo V ⧸ Subgroup.center (hatX Mo V))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h : a * b * a⁻¹ = b := by
        rw [hcomm a ha b hb]
        group
      rwa [h]
    · intro hb
      have hw : a * b * a⁻¹ ∈ hatBarSub Mo V (conjSubgroup V g) := hb
      have hcomm' : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ :=
        hcomm a⁻¹ ((hatBarSub Mo V V).inv_mem ha) (a * b * a⁻¹) hw
      have hb_eq : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = ((a * b * a⁻¹) * a⁻¹) * a := by rw [hcomm']
          _ = a * b * a⁻¹ := by group
      rwa [hb_eq]
  have hbot : hatBarSub Mo V V = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    exact inf_normalizer_hatBarSub hn h1 h5 h15 hS c Mo a ha (hN a ha)
  have hcard : Nat.card ↥(hatBarSub Mo V V) = 1 := by rw [hbot, Subgroup.card_bot]
  have hcardV := card_hatBarSub_V hn h1 h5 h15 hS c Mo
  have hn0 : E3.mQuot V (U ⊔ V₀) ≠ 0 := by omega
  have hgt : 1 < 2 ^ E3.mQuot V (U ⊔ V₀) := Nat.one_lt_pow hn0 (by norm_num)
  rw [← hcardV] at hgt
  rw [hcard] at hgt
  exact absurd hgt (lt_irrefl 1)

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

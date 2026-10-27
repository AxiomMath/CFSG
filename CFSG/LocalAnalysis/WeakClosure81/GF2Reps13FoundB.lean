module

public import CFSG.Quasithin.Background.A1cModuleSub
public import CFSG.Quasithin.Background.C1PackSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s13_schur_perfect (hW : ∀ w : W, w * w = 1) (M R : Subgroup (MulAut W))
    (hMR : ⁅M, R⁆ = ⊥) (hR : ⁅R, R⁆ = R) (Y : Subgroup W) (hYM : StableUnder M Y)
    (hYR : StableUnder R Y) (hirr : IsIrrOn M Y (Y ⊓ fixV M)) :
    commSub Y R ≤ Y ⊓ fixV M := by
  classical
  letI : MulDistribMulAction ↥M W := MulDistribMulAction.compHom W M.subtype
  have hYM' : XMod.IsInv ↥M Y := fun a y hy => hYM a a.2 y hy
  letI : MulDistribMulAction ↥M ↥Y := XMod.subAction hYM'
  have hfixed : XMod.fixed ↥M Y = Y ⊓ fixV M := by
    ext w
    exact ⟨fun h => ⟨h.1, fun x hx => h.2 ⟨x, hx⟩⟩,
      fun h => ⟨h.1, fun a => h.2 a a.2⟩⟩
  have hirrSec : XMod.IsIrrSec ↥M (Y ⊓ fixV M) Y :=
    ⟨hirr.1, fun J hJ hC hJY => hirr.2.2.2 J (fun x hx u hu => hJ ⟨x, hx⟩ u hu) hC hJY⟩
  have hirrSec' : XMod.IsIrrSec ↥M (XMod.fixed ↥M Y) Y := by
    rw [hfixed]; exact hirrSec
  have hsub := XMod.isIrrSec_subAction hYM' hirrSec'
  have hRY : R ≤ stabSub Y := by
    intro r hr
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 := hYR r⁻¹ (R.inv_mem hr) (r u) hu
      rwa [MulAut.inv_apply_self] at h1
    · exact hYR r hr u
  let σR : ↥R →* MulAut ↥Y := (resHom Y).comp (Subgroup.inclusion hRY)
  have hσR : ∀ (t : ↥R) (u : ↥Y), ((σR t) u : W) = (t : MulAut W) (u : W) := by
    intro t u
    change (((resHom Y) (Subgroup.inclusion hRY t)) u : W) = (t : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  have hcommMR : ∀ (a : ↥M) (t : ↥R),
      (a : MulAut W) * (t : MulAut W) = (t : MulAut W) * (a : MulAut W) := by
    intro a t
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMR
    have hm : (a : MulAut W) ∈ Subgroup.centralizer (R : Set (MulAut W)) := hle a.2
    rw [Subgroup.mem_centralizer_iff] at hm
    exact (hm (t : MulAut W) t.2).symm
  have heqv : ∀ t : ↥R, σR t ∈ XMod.eqvAut ↥M ↥Y := by
    intro t
    rw [XMod.mem_eqvAut_iff]
    intro a y
    apply Subtype.ext
    rw [hσR t (a • y)]
    change (t : MulAut W) ((a : MulAut W) (y : W)) =
      (a : MulAut W) (((σR t) y : ↥Y) : W)
    rw [hσR t y]
    exact (congrArg (fun φ : MulAut W => φ (y : W)) (hcommMR a t)).symm
  have hperf : _root_.commutator ↥R = ⊤ := (Subgroup.isPerfect_iff.2 hR).commutator_eq_top
  let Zq : Subgroup ↥Y := XMod.fixed ↥M (⊤ : Subgroup ↥Y)
  let σM : ↥M →* MulAut ↥Y := MulDistribMulAction.toMulAut ↥M ↥Y
  have hne : Zq ≠ ⊤ := ne_of_lt hsub.1
  have hirr' : ∀ J : Subgroup ↥Y, Zq ≤ J →
      (∀ s : ↥M, ∀ x ∈ J, σM s x ∈ J) → J = Zq ∨ J = ⊤ := by
    intro J hZJ hJ
    refine hsub.2 J ?_ hZJ le_top
    intro s x hx
    have h := hJ s x hx
    rw [MulDistribMulAction.toMulAut_apply] at h
    rw [MulDistribMulAction.toMulEquiv_apply] at h
    exact h
  have hσfix : ∀ (s : ↥M) x, x ∈ Zq ↔ σM s x ∈ Zq := by
    intro s x
    rw [MulDistribMulAction.toMulAut_apply]
    constructor
    · intro hx
      exact (XMod.isInv_fixed (A := ↥M) (L := (⊤ : Subgroup ↥Y))) s x hx
    · intro hx
      have h2 : s⁻¹ • (s • x) ∈ Zq :=
        (XMod.isInv_fixed (A := ↥M) (L := (⊤ : Subgroup ↥Y))) s⁻¹ (s • x) hx
      rwa [inv_smul_smul] at h2
  have hτfix : ∀ (t : ↥R) x, x ∈ Zq ↔ σR t x ∈ Zq := by
    intro t x
    have hmap : Zq.map (σR t : ↥Y →* ↥Y) = Zq := by
      simpa only [Zq] using XMod.map_fixed_eq (A := ↥M) (P := ↥Y) (heqv t)
    constructor
    · intro hx
      rw [← hmap, Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
    · intro hx
      have hmap' : Zq.map (σR t⁻¹ : ↥Y →* ↥Y) = Zq := by
        simpa only [Zq] using XMod.map_fixed_eq (A := ↥M) (P := ↥Y) (heqv t⁻¹)
      have h2 : (σR t⁻¹) ((σR t) x) ∈ Zq := by
        rw [← hmap', Subgroup.mem_map]
        exact ⟨(σR t) x, hx, rfl⟩
      have h3 : (σR t⁻¹) ((σR t) x) = x := by
        rw [map_inv, MulAut.inv_apply_self]
      rwa [h3] at h2
  have hcommST : ∀ (s : ↥M) (t : ↥R) x, σM s (σR t x) * (σR t (σM s x))⁻¹ ∈ Zq := by
    intro s t x
    have heq : σM s (σR t x) = σR t (σM s x) := by
      rw [MulDistribMulAction.toMulAut_apply]
      rw [MulDistribMulAction.toMulEquiv_apply]
      exact (heqv t s x).symm
    rw [heq, mul_inv_cancel]
    exact Zq.one_mem
  have key := CFSG.Quasithin.C1Pack.schur_perfect_trivial Zq σM σR hσfix hτfix hne hirr'
    hcommST hperf
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨r, hr, y, hy, rfl⟩
  have hkey : σR ⟨r, hr⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹ ∈ Zq := key ⟨r, hr⟩ ⟨y, hy⟩
  have hmemW : (((σR ⟨r, hr⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y) : W)) ∈ Y ⊓ fixV M := by
    refine ⟨(Subtype.mem _), ?_⟩
    intro m hm
    have h2 : (⟨m, hm⟩ : ↥M) •
        (σR ⟨r, hr⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹) =
        (σR ⟨r, hr⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹) := hkey.2 ⟨m, hm⟩
    exact congrArg Subtype.val h2
  have hval : (((σR ⟨r, hr⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y) : W)) =
      (r : MulAut W) y * y⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσR]
  rwa [hval] at hmemW

end CFSG.LocalAnalysis.WeakClosure81

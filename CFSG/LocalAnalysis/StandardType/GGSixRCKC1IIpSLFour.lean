module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Cent
import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
import CFSG.LinearAlgebra.SLBlockFourRankOne
import CFSG.LinearAlgebra.SLBlockFourRankTwo
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rckIIpSLFourBridge : RCKIIpSLFourBridge := by
  intro X _ _ Ksub J V r hJodd _hKodd hFour hCore hCent hEmbed
  obtain ⟨hrV, hVJ, hVab, _hVcard, hrne, hconjV⟩ := hFour
  obtain ⟨m, φ, W, E, H, hφrange, hφker, hBlock, hHmap, hWdim⟩ := hEmbed
  obtain ⟨hWE, hHmem⟩ := hBlock
  have hF2 : ∀ a : GaloisField 2 1, a = 0 ∨ a = 1 := rck1416_gf2_eq_zero_or_one
  have hcenter :
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    rw [Subgroup.mem_bot]
    obtain ⟨a, ha, hAeq⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hA
    apply Subtype.ext
    rw [← hAeq, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij]
      have hpow : a ^ (m + 1) = 1 := by simpa using ha
      have hpos : 0 < m + 1 := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      rcases hF2 a with ha0 | ha1
      · subst ha0
        rw [zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at hpow
        exact absurd hpow zero_ne_one
      · exact ha1
    · rw [if_neg hij, if_neg hij]
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hφker.trans (le_of_eq hcenter))
  let Mat := Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)
  obtain ⟨r₀, hr₀H, hr₀r⟩ :
      ∃ r₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1),
        r₀ ∈ H ∧ φ r₀ = r := by
    have hrJ : r ∈ H.map φ := by rw [hHmap]; exact hVJ hrV
    obtain ⟨r₀, hr₀H, hr₀r⟩ := Subgroup.mem_map.mp hrJ
    exact ⟨r₀, hr₀H, hr₀r⟩
  have hr₀W : ∀ w ∈ W, (r₀ : Mat).mulVec w ∈ W :=
    fun w hw => ((hHmem r₀).mp hr₀H).1 w hw
  have hr₀E : ∀ e ∈ E,
      (r₀ : Mat).mulVec e = e :=
    fun e he => ((hHmem r₀).mp hr₀H).2 e he
  have hr2 : r * r = 1 := by simpa [pow_two] using hVab.2 r hrV
  have hr₀sq : r₀ * r₀ = 1 := by
    apply hφinj
    rw [map_mul, map_one, hr₀r, hr2]
  have hr₀ne : r₀ ≠ 1 := by
    intro h
    apply hrne
    rw [← hr₀r, h, map_one]
  let N : (Fin (m + 1) → GaloisField 2 1) →ₗ[GaloisField 2 1]
      (Fin (m + 1) → GaloisField 2 1) :=
    Matrix.toLin' ((r₀ : Mat) - 1)
  let U : Submodule (GaloisField 2 1) (Fin (m + 1) → GaloisField 2 1) := LinearMap.range N
  let UE : Submodule (GaloisField 2 1) (Fin (m + 1) → GaloisField 2 1) := U ⊔ E
  have hNE : ∀ e ∈ E, N e = 0 := by
    intro e he
    simp only [N, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, hr₀E e he, Matrix.one_mulVec, sub_self]
  have hNW : ∀ w ∈ W, N w ∈ W := by
    intro w hw
    simp only [N, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact W.sub_mem (hr₀W w hw) hw
  have hr₀sqM :
      (r₀ : Mat) * r₀ = 1 := by
    simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1) =>
      (z : Mat)) hr₀sq
  have hxx : ∀ x : Fin (m + 1) → GaloisField 2 1, x + x = 0 := by
    intro x
    rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (GaloisField 2 1) 2,
      CharP.cast_eq_zero (GaloisField 2 1) 2, zero_smul]
  have hN2 : ∀ x, N (N x) = 0 := by
    intro x
    simp only [N, Matrix.toLin'_apply]
    have hinner : ((r₀ : Mat) - 1).mulVec x =
        (r₀ : Mat).mulVec x - x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hinner, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hr₀sqM,
      Matrix.one_mulVec, Matrix.one_mulVec]
    have habel : x - (r₀ : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec x -
        ((r₀ : Mat).mulVec x - x) =
        (x + x) - ((r₀ : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec x +
          (r₀ : Mat).mulVec x) := by
      abel
    rw [habel, hxx x, hxx ((r₀ : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 1)).mulVec x)]
    abel
  have hNrange0 : ∀ u ∈ U, N u = 0 := by
    rintro u ⟨x, rfl⟩
    exact hN2 x
  have hUleW : U ≤ W := by
    rintro u ⟨x, rfl⟩
    obtain ⟨w, hw, e, he, hx⟩ :=
      Submodule.mem_sup.mp (show x ∈ W ⊔ E by rw [hWE.sup_eq_top]; exact Submodule.mem_top)
    rw [← hx, map_add, hNE e he, add_zero]
    exact hNW w hw
  have hUker : U ≤ LinearMap.ker N := by
    intro u hu
    rw [LinearMap.mem_ker]
    exact hNrange0 u hu
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hN0 : N = 0 := LinearMap.range_eq_bot.mp hbot
    have hN0' : Matrix.toLin' ((r₀ : Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField 2 1)) - 1) = 0 := hN0
    have hmat0 : ((r₀ : Mat) - 1) = 0 := by
      apply Matrix.toLin'.injective
      rw [hN0', map_zero]
    have hr₀1 : r₀ = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact sub_eq_zero.mp hmat0
    exact hr₀ne hr₀1
  have hfinM : Module.finrank (GaloisField 2 1)
      (Fin (m + 1) → GaloisField 2 1) =
      Module.finrank (GaloisField 2 1) W + Module.finrank (GaloisField 2 1) E := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (s := W) (t := E)
    rw [hWE.sup_eq_top, finrank_top, disjoint_iff.mp hWE.1, finrank_bot, add_zero] at h
    exact h
  have hfinUE : Module.finrank (GaloisField 2 1) UE =
      Module.finrank (GaloisField 2 1) U + Module.finrank (GaloisField 2 1) E := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (s := U) (t := E)
    rw [disjoint_iff.mp (Disjoint.mono_left hUleW hWE.1), finrank_bot, add_zero] at h
    simpa [UE] using h
  have hUEker : UE ≤ LinearMap.ker N := by
    intro x hx
    change x ∈ U ⊔ E at hx
    obtain ⟨u, hu, e, he, rfl⟩ := Submodule.mem_sup.mp hx
    rw [LinearMap.mem_ker, map_add, hNrange0 u hu, hNE e he, add_zero]
  have hmono : Module.finrank (GaloisField 2 1) UE ≤
      Module.finrank (GaloisField 2 1) (LinearMap.ker N) :=
    Submodule.finrank_mono hUEker
  have hrank_le : Module.finrank (GaloisField 2 1) U ≤ 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    have hUfin : Module.finrank (GaloisField 2 1) U + Module.finrank (GaloisField 2 1) E ≤
        Module.finrank (GaloisField 2 1) (LinearMap.ker N) := by
      rw [← hfinUE]
      exact hmono
    have hkey : 2 * Module.finrank (GaloisField 2 1) U + Module.finrank (GaloisField 2 1) E ≤
        4 + Module.finrank (GaloisField 2 1) E := by
      calc 2 * Module.finrank (GaloisField 2 1) U + Module.finrank (GaloisField 2 1) E
          = Module.finrank (GaloisField 2 1) U +
            (Module.finrank (GaloisField 2 1) U +
              Module.finrank (GaloisField 2 1) E) := by ring
        _ ≤ Module.finrank (GaloisField 2 1) U +
            Module.finrank (GaloisField 2 1) (LinearMap.ker N) := by linarith
        _ = Module.finrank (GaloisField 2 1)
              (Fin (m + 1) → GaloisField 2 1) := by
            simpa [U] using hrn
        _ = Module.finrank (GaloisField 2 1) W + Module.finrank (GaloisField 2 1) E := hfinM
        _ = 4 + Module.finrank (GaloisField 2 1) E := by rw [hWdim]
    omega
  have hUpos : 0 < Module.finrank (GaloisField 2 1) U := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hUne ((Submodule.finrank_eq_zero).mp h0)
  have hrank : Module.finrank (GaloisField 2 1) U = 1 ∨
      Module.finrank (GaloisField 2 1) U = 2 := by omega
  rcases hrank with hrank1 | hrank2
  ·
    obtain ⟨T₀, hT₀block, hT₀r, hT₀card⟩ :=
      CFSG.LinearAlgebra.exists_card_eq_sixtyFour_commute_of_finrank_range_eq_one
        (F := GaloisField 2 1) (ι := Fin (m + 1)) hF2 hWE hWdim hr₀W hr₀E hr₀sq
        (by simpa [U, N] using hrank1)
    have hT₀H : T₀ ≤ H := fun t ht => (hHmem t).mpr (hT₀block t ht)
    have hTJ : T₀.map φ ≤ J := by
      rw [← hHmap]
      exact Subgroup.map_mono hT₀H
    have hTr : ∀ t ∈ T₀.map φ, t * r = r * t := by
      rintro _ ⟨t, ht, rfl⟩
      rw [← hr₀r, ← map_mul, ← map_mul, hT₀r t ht]
    have hTcard : Nat.card (T₀.map φ) = 64 := by
      rw [Subgroup.card_map_of_injective hφinj, hT₀card]
    exact (rck_cent96At_false_of_le hJodd hCent hTJ hTr hTcard).elim
  ·
    have hUleW' : U ≤ W := hUleW
    let P : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1) → Prop := fun y =>
      (∀ x, Matrix.toLin' ((y : Mat) - 1)
          x ∈ U) ∧
      (∀ u ∈ U, Matrix.toLin' ((y : Mat) - 1)
          u = 0) ∧
      (∀ e ∈ E, Matrix.toLin' ((y : Mat) - 1)
          e = 0)
    have hlin : ∀ y y' : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1),
        Matrix.toLin' (((y * y' : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1)) : Mat) - 1) =
          (Matrix.toLin' ((y : Mat) - 1)).comp
            (Matrix.toLin' ((y' : Matrix (Fin (m + 1)) (Fin (m + 1))
              (GaloisField 2 1)) - 1)) +
          Matrix.toLin' ((y : Mat) - 1) +
          Matrix.toLin' ((y' : Mat) - 1) := by
      intro y y'
      have hmat : (((y * y' : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1)) : Mat) - 1) =
          ((y : Mat) - 1) *
            ((y' : Mat) - 1) +
          ((y : Mat) - 1) +
          ((y' : Mat) - 1) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        noncomm_ring
      rw [hmat, map_add, map_add, Matrix.toLin'_mul]
    have hcomp0 : ∀ y y' : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1),
        P y → P y' →
        (Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)) - 1)).comp
          (Matrix.toLin' ((y' : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1)) = 0 := by
      intro y y' hy hy'
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact hy.2.1 _ (hy'.1 x)
    have hPmul : ∀ y y', P y → P y' → P (y * y') := by
      intro y y' hy hy'
      have h0 := hcomp0 y y' hy hy'
      have hlin' := hlin y y'
      rw [h0, zero_add] at hlin'
      refine ⟨?_, ?_, ?_⟩
      · intro x
        rw [hlin', LinearMap.add_apply]
        exact U.add_mem (hy.1 x) (hy'.1 x)
      · intro u hu
        rw [hlin', LinearMap.add_apply, hy.2.1 u hu, hy'.2.1 u hu, add_zero]
      · intro e he
        rw [hlin', LinearMap.add_apply, hy.2.2 e he, hy'.2.2 e he, add_zero]
    have hPsq : ∀ y, P y → y * y = 1 := by
      intro y hy
      have h0 := hcomp0 y y hy hy
      have hlin' := hlin y y
      rw [h0, zero_add] at hlin'
      have h2 : Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) +
          Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) = 0 := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.add_apply, LinearMap.zero_apply]
        rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (GaloisField 2 1) 2,
          CharP.cast_eq_zero (GaloisField 2 1) 2, zero_smul]
      have hto : Matrix.toLin' (((y * y : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) = 0 := by
        rw [hlin', h2]
      have hmat0 : (((y * y : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) = 0 := by
        apply Matrix.toLin'.injective
        rw [hto, map_zero]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact sub_eq_zero.mp hmat0
    let Y₀ : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :=
      { carrier := {y | P y}
        one_mem' := by
          refine ⟨?_, ?_, ?_⟩
          · intro x
            have h1 : ((1 : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) - 1 = 0 := by simp
            rw [h1, Matrix.toLin'_apply, Matrix.zero_mulVec]
            exact U.zero_mem
          · intro u _
            have h1 : ((1 : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) - 1 = 0 := by simp
            rw [h1, Matrix.toLin'_apply, Matrix.zero_mulVec]
          · intro e _
            have h1 : ((1 : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) - 1 = 0 := by simp
            rw [h1, Matrix.toLin'_apply, Matrix.zero_mulVec]
        mul_mem' := fun hy hy' => hPmul _ _ hy hy'
        inv_mem' := fun {y} hy => by
          have hsq := hPsq y hy
          rw [inv_eq_of_mul_eq_one_right hsq]
          exact hy }
    have hYmem : ∀ y, y ∈ Y₀ ↔ P y := fun _ => Iff.rfl
    have hYH : Y₀ ≤ H := by
      intro y hy
      have hy := (hYmem y).mp hy
      refine (hHmem y).mpr ⟨?_, ?_⟩
      · intro w hw
        change (y : Mat).mulVec w ∈ W
        have h2 : ((y : Mat) - 1).mulVec w ∈ W := hUleW' (by
          show ((y : Mat) - 1).mulVec w ∈ U
          simpa only [Matrix.toLin'_apply] using hy.1 w)
        have h3 : (y : Mat).mulVec w = ((y : Mat) - 1).mulVec w + w := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
          abel
        rw [h3]
        exact W.add_mem h2 hw
      · intro e he
        have h1 := hy.2.2 e he
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
        exact h1
    have hYr : ∀ y ∈ Y₀, y * r₀ = r₀ * y := by
      intro y hy
      have hy := (hYmem y).mp hy
      have h1 : (Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1)).comp N = 0 := by
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.zero_apply]
        exact hy.2.1 (N x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
      have h2 : N.comp (Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1)) = 0 := by
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.zero_apply]
        exact hNrange0 _ (hy.1 x)
      have hm1 : ((y : Mat) - 1) *
          ((r₀ : Mat) - 1) = 0 := by
        apply Matrix.toLin'.injective
        rw [Matrix.toLin'_mul, h1, map_zero]
      have hm2 : ((r₀ : Mat) - 1) *
          ((y : Mat) - 1) = 0 := by
        apply Matrix.toLin'.injective
        rw [Matrix.toLin'_mul, h2, map_zero]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      have h : (y : Mat) * r₀ -
          (r₀ : Mat) *
            (y : Mat) = 0 := by
        calc (y : Mat) * r₀ - (r₀ : Mat) * (y : Mat)
            = (((y : Mat) - 1) * ((r₀ : Mat) - 1)) -
              (((r₀ : Mat) - 1) * ((y : Mat) - 1)) := by noncomm_ring
          _ = 0 := by rw [hm1, hm2, sub_zero]
      exact sub_eq_zero.mp h
    have hPconj : ∀ c ∈ H, c * r₀ = r₀ * c → ∀ y, P y → P (c * y * c⁻¹) := by
      intro c hcH hcr y hy
      have hcE : ∀ e ∈ E, (c : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec e = e := ((hHmem c).mp hcH).2
      have hcr_inv : c⁻¹ * r₀ = r₀ * c⁻¹ := by
        calc c⁻¹ * r₀ = c⁻¹ * r₀ * (c * c⁻¹) := by group
          _ = c⁻¹ * (r₀ * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * r₀) * c⁻¹ := by rw [← hcr]
          _ = r₀ * c⁻¹ := by group
      have hcU : ∀ u ∈ U, (c : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec u ∈ U := by
        rintro u ⟨x, rfl⟩
        refine ⟨(c : Mat).mulVec x, ?_⟩
        simp only [N, Matrix.toLin'_apply]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        have hcmat : (c : Mat) * r₀ =
            (r₀ : Mat) * c := by
          simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1) =>
            (z : Mat)) hcr
        calc ((r₀ : Mat) - 1) * (c : Mat)
            = (r₀ : Mat) * (c : Mat) - c := by noncomm_ring
          _ = (c : Mat) * r₀ - c := by rw [← hcmat]
          _ = (c : Mat) * ((r₀ : Mat) - 1) := by noncomm_ring
      have hciU : ∀ u ∈ U, ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec u ∈ U := by
        rintro u ⟨x, rfl⟩
        refine ⟨((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
          Mat).mulVec x, ?_⟩
        simp only [N, Matrix.toLin'_apply]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        have hcmat : ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
            Mat) * r₀ =
            (r₀ : Mat) *
              ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) := by
          simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1) =>
            (z : Mat)) hcr_inv
        calc ((r₀ : Mat) - 1) * ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
              (GaloisField 2 1)) : Mat)
            = (r₀ : Mat) * ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
                (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
                (GaloisField 2 1)) - ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
                (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
                (GaloisField 2 1)) := by noncomm_ring
          _ = ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) * r₀ -
              ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) := by rw [← hcmat]
          _ = ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) *
              ((r₀ : Mat) - 1) := by noncomm_ring
      have hciE : ∀ e ∈ E, ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec e = e := by
        intro e he
        have h1 : (c : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)).mulVec e = e := hcE e he
        calc ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
              Mat).mulVec e
            = ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat).mulVec
                ((c : Matrix (Fin (m + 1)) (Fin (m + 1))
                  (GaloisField 2 1)).mulVec e) := by rw [h1]
          _ = e := by
            rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
              Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      have hcc : (c : Mat) *
          ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
            Mat) = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_adjugate,
          Matrix.SpecialLinearGroup.det_coe, one_smul]
      have hmat : (((c * y * c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 1)) : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) =
          (c : Mat) *
            (((y : Mat) - 1) *
              ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat)) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        calc ((c : Mat) * (y : Mat)) *
              ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                Mat) - 1
            = (c : Mat) * ((y : Mat) - 1) *
                ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                  Mat) := by
              conv_lhs => rw [← hcc]
              noncomm_ring
          _ = (c : Mat) * (((y : Mat) - 1) *
                ((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
                  Mat)) := by noncomm_ring
      refine ⟨?_, ?_, ?_⟩
      · intro x
        rw [Matrix.toLin'_apply, hmat]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hcU _ (hy.1 _)
      · intro u hu
        rw [Matrix.toLin'_apply, hmat]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        have h0 : ((y : Mat) - 1).mulVec
            (((c⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) :
              Mat).mulVec u) = 0 := by
          simpa only [Matrix.toLin'_apply] using hy.2.1 _ (hciU u hu)
        rw [h0, Matrix.mulVec_zero]
      · intro e he
        rw [Matrix.toLin'_apply, hmat]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rw [hciE e he]
        have h0 : ((y : Mat) - 1).mulVec e = 0 := by
          simpa only [Matrix.toLin'_apply] using hy.2.2 e he
        rw [h0, Matrix.mulVec_zero]
    have hYnormal : ∀ c ∈ H, c * r₀ = r₀ * c →
        ∀ y ∈ Y₀, c * y * c⁻¹ ∈ Y₀ := by
      intro c hcH hcr y hy
      exact (hYmem _).mpr (hPconj c hcH hcr y ((hYmem y).mp hy))
    have hQJ : Y₀.map φ ≤ J ⊓ Subgroup.centralizer ({r} : Set X) := by
      intro q hq
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hHmap]
        exact Subgroup.mem_map_of_mem φ (hYH hy)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hr₀r, ← map_mul, ← map_mul, hYr y hy]
    have hQp : IsPGroup 2 (Y₀.map φ) := by
      intro q
      obtain ⟨y, hy, hq⟩ := Subgroup.mem_map.mp q.2
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hsq : φ y * φ y = 1 := by rw [← map_mul, hPsq y hy, map_one]
      simpa [pow_two, hq] using hsq
    have hQnorm : ∀ h ∈ J ⊓ Subgroup.centralizer ({r} : Set X),
        ∀ q ∈ Y₀.map φ, h * q * h⁻¹ ∈ Y₀.map φ := by
      intro h hh q hq
      have hhJ : h ∈ J := (Subgroup.mem_inf.mp hh).1
      have hhr : h * r = r * h :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hh).2
      obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp (by rwa [hHmap])
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
      have hcr : c * r₀ = r₀ * c := by
        apply hφinj
        rw [map_mul, map_mul, hr₀r]
        exact hhr
      refine ⟨c * y * c⁻¹, hYnormal c hcH hcr y hy, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hQpCore : Y₀.map φ ≤
        pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)) :=
      le_pCoreOf_of_normalized 2 hQJ hQp hQnorm
    have hcomm : ∀ v ∈ V.comap φ, v ≠ 1 →
        ∀ y : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1),
          (∀ x, Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) x ∈ U) →
          (∀ u ∈ U, Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) u = 0) →
          (∀ e ∈ E, Matrix.toLin' ((y : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1) e = 0) →
          v * y * v⁻¹ * y⁻¹ = 1 ∨ v * y * v⁻¹ * y⁻¹ = r₀ := by
      intro v hv hvne y hy1 hy2 hy3
      have hy : P y := ⟨hy1, hy2, hy3⟩
      have hq : φ y ∈ Y₀.map φ := ⟨y, hy, rfl⟩
      have hqc := hQpCore hq
      have hvV : φ v ∈ V := hv
      have hc := hCore (φ v) hvV (φ y) hqc
      rw [Subgroup.mem_zpowers_iff] at hc
      obtain ⟨k, hk⟩ := hc
      have hcases : φ v * φ y * (φ v)⁻¹ * (φ y)⁻¹ = 1 ∨
          φ v * φ y * (φ v)⁻¹ * (φ y)⁻¹ = r := by
        rw [← hk]
        have hmod := zpow_eq_zpow_emod' (x := r) k (n := 2) (by rwa [pow_two])
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          rw [hmod]
          rw [show k % (↑(2 : ℕ) : ℤ) = 0 from by simpa using h, zpow_zero]
        · right
          rw [hmod]
          rw [show k % (↑(2 : ℕ) : ℤ) = 1 from by simpa using h, zpow_one]
      have hmapcomm : φ (v * y * v⁻¹ * y⁻¹) =
          φ v * φ y * (φ v)⁻¹ * (φ y)⁻¹ := by
        simp only [map_mul, map_inv]
      rcases hcases with h1 | h1
      · left
        apply hφinj
        rw [hmapcomm, h1, map_one]
      · right
        apply hφinj
        rw [hmapcomm, h1, hr₀r]
    have hrange_ker : ∀ v ∈ V.comap φ, v ≠ 1 →
        LinearMap.range (Matrix.toLin' ((v : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1)) = U ∧
          LinearMap.ker (Matrix.toLin' ((v : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 1)) - 1)) = LinearMap.ker N := by
      intro v hv hvne
      have hvV : φ v ∈ V := hv
      have hvne' : φ v ≠ 1 := fun h => hvne (hφinj (by rw [h, map_one]))
      have hvH : v ∈ H := by
        have hmem : φ v ∈ H.map φ := by rw [hHmap]; exact hVJ hvV
        obtain ⟨h, hh, hφh⟩ := Subgroup.mem_map.mp hmem
        have hveq : v = h := hφinj (by rw [hφh])
        rwa [hveq]
      have hvW : ∀ w ∈ W, (v : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec w ∈ W := ((hHmem v).mp hvH).1
      have hvE : ∀ e ∈ E, (v : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 1)).mulVec e = e := ((hHmem v).mp hvH).2
      have hvr : v * r₀ = r₀ * v := by
        apply hφinj
        have hcommV : (⟨φ v, hvV⟩ : ↥V) * ⟨r, hrV⟩ = ⟨r, hrV⟩ * ⟨φ v, hvV⟩ :=
          isMulCommutative_iff.mp hVab.1 _ _
        have hval : φ v * r = r * φ v := congrArg Subtype.val hcommV
        rw [map_mul, map_mul, hr₀r]
        exact hval
      have hconj : ∃ j : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1),
          v = j * r₀ * j⁻¹ := by
        obtain ⟨jX, hjXJ, hvj⟩ := hconjV (φ v) hvV hvne'
        obtain ⟨j, _hjH, hj⟩ := Subgroup.mem_map.mp (by rw [hHmap]; exact hjXJ)
        refine ⟨j, ?_⟩
        apply hφinj
        rw [map_mul, map_mul, map_inv, hj, hr₀r]
        exact hvj
      have := CFSG.LinearAlgebra.range_ker_eq_of_finrank_range_eq_two
        (F := GaloisField 2 1) (ι := Fin (m + 1)) hF2 hWE hWdim hr₀W hr₀E hr₀sq
        (by simpa [U, N] using hrank2) hvW hvE hvr hconj
        (hcomm v hv hvne)
      simpa [U, N] using this
    have hVrange : V ≤ φ.range := by
      calc V ≤ J := hVJ
        _ = H.map φ := hHmap.symm
        _ ≤ φ.range := Subgroup.map_le_range φ H
    refine Or.inl ⟨m, 1, le_rfl, ?_⟩
    refine ⟨φ, V.comap φ, U, LinearMap.ker N, hφrange, hφker, ?_, ?_, hUker, ?_, ?_⟩
    · exact Subgroup.map_comap_eq_self hVrange
    · intro v hv hv1
      exact hφinj (by rw [hv1, map_one])
    · intro v hv hvne
      have h := hrange_ker v hv hvne
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact h
    · intro b hb
      simp at hb

end CFSG.StandardType.RCKC1

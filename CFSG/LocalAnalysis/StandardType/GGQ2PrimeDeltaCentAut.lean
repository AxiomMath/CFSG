module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeDeltaCentAutBlock
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
public import CFSG.Fischer.Polar.Delta
public import Certificates.Certificate3600
import all CFSG.Fischer.F4
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer CFSG.LargeExtraspecial.SMod20.Aut Matrix
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT autConj autConj_apply centralizer_T46)

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

private theorem tvP_val_ptIdx (r s : Fin 693) :
    (tvP r s).val = ptIdx (uVec s + hermStd (uVec s) (uVec r) • uVec r) := by
  rw [tvP, piSU_apply]
  change ptIdx (tvM (uVec r) *ᵥ uVec s) = _
  rw [tvM_mulVec]

private theorem tvP_fix_iff_orth (r s : Fin 693) :
    tvP r s = s ↔ hermStd (uVec s) (uVec r) = 0 := by
  constructor
  · intro h
    by_contra hne
    have hr := uVec_iso ptsFacts r.2
    have hs := uVec_iso ptsFacts s.2
    have hw0 : uVec s + hermStd (uVec s) (uVec r) • uVec r ≠ 0 := by
      have := mulVec_ne_zero (tvGL (uVec r) hr) (uVec_ne_zero ptsFacts s.2)
      rwa [tvGL_val, tvM_mulVec] at this
    have hwi : hermStd (uVec s + hermStd (uVec s) (uVec r) • uVec r)
        (uVec s + hermStd (uVec s) (uVec r) • uVec r) = 0 := by
      have := isIsom_tvM hr (uVec s) (uVec s)
      rw [herm_eq_std, herm_eq_std, tvM_mulVec] at this
      rw [this]
      exact hs
    have hv := tvP_val_ptIdx r s
    rw [h] at hv
    have e := uVec_ptIdx ptsFacts hw0 hwi
    rw [← hv] at e
    obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw0
    rw [hcw] at e
    have h2 := congrArg (hermStd (uVec s)) e
    rw [hs, hermStd_smul_right, hermStd_add_right, hermStd_smul_right, hs, zero_add] at h2
    have h3 : c ^ 2 * (hermStd (uVec s) (uVec r) ^ 2 * hermStd (uVec s) (uVec r)) = 0 := h2.symm
    have h4 : ∀ a t : F4, a ≠ 0 → t ≠ 0 → a ^ 2 * (t ^ 2 * t) ≠ 0 := by decide
    exact h4 c _ hc hne h3
  · intro h
    apply Fin.ext
    rw [tvP_val_ptIdx, h, zero_smul, add_zero]
    exact ptIdx_uVec ptsFacts s.2

private theorem hermStd_transfer_of_same_fix {P Q : Fin 693}
    (hPQ : ∀ s : Fin 693, hermStd (uVec s) (uVec P) = 0 → hermStd (uVec s) (uVec Q) = 0)
    {u v : W} {a b : F4} (hb : b ≠ 0) (hu : uVec P = a • u) (hv : uVec Q = b • v)
    {x : W} (hx0 : x ≠ 0) (hxi : hermStd x x = 0) (hxu : hermStd x u = 0) :
    hermStd x v = 0 := by
  obtain ⟨d, hd, hdx⟩ := uVec_ptOf x hx0 hxi
  have h1 := hPQ (ptOf x hx0 hxi)
    (by rw [hdx, hu, hermStd_smul_left, hermStd_smul_right, hxu, mul_zero, mul_zero])
  rw [hdx, hv, hermStd_smul_left, hermStd_smul_right] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h hd
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hb
    · exact h

private theorem orth_transfer_of_tvP_fixed (A : GU0)
    (φ : F4 ≃+* F4) (h : ∀ p : Fin 693, uVec p 0 = 0 → tvP (semiPerm A φ p) = tvP p)
    {i j : Fin 6} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) {c : F4} (hc : c ≠ 0) {x : W}
    (hx0 : x ≠ 0) (hxi : hermStd x x = 0)
    (hxu : hermStd x (Pi.single i 1 + c • Pi.single j 1) = 0) :
    hermStd x (semiVec A φ (Pi.single i 1 + c • Pi.single j 1)) = 0 := by
  obtain ⟨hu0, hui⟩ := pairVec_ne_zero_and_isotropic hij hc
  obtain ⟨a, ha, hau⟩ := uVec_ptOf _ hu0 hui
  obtain ⟨b, hb, hbq⟩ := uVec_semiPerm A φ (ptOf _ hu0 hui)
  rw [hau, semiVec_smul, smul_smul] at hbq
  have hp0 : uVec (ptOf _ hu0 hui) 0 = 0 := by
    rw [hau]
    simp [Pi.single_apply, hi.symm, hj.symm]
  have hfix : ∀ s : Fin 693, hermStd (uVec s) (uVec (ptOf _ hu0 hui)) = 0 →
      hermStd (uVec s) (uVec (semiPerm A φ (ptOf _ hu0 hui))) = 0 := fun s hs => by
    rw [← tvP_fix_iff_orth] at hs ⊢
    rw [h _ hp0]
    exact hs
  exact hermStd_transfer_of_same_fix hfix (mul_ne_zero hb ((map_ne_zero φ).2 ha)) hau hbq
    hx0 hxi hxu

private theorem eq_semiPerm_of_mem_autT
    {y : Equiv.Perm (Fin 693)} (hy : y ∈ autT) :
    ∃ (A : GU0) (φ : F4 ≃+* F4), y = semiPerm A φ := by
  obtain ⟨A, φ, h⟩ := exists_semiPerm (autConj ⟨y, hy⟩)
  refine ⟨A, φ, ?_⟩
  generalize semiPerm A φ = π at h ⊢
  have hc : π⁻¹ * y ∈ centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [mem_centralizer_iff]
    intro g hg
    have e := h ⟨g, hg⟩
    rw [autConj_apply] at e
    calc g * (π⁻¹ * y) = π⁻¹ * (π * g * π⁻¹) * y := by group
      _ = π⁻¹ * (y * g * y⁻¹) * y := by rw [← e]
      _ = π⁻¹ * y * g := by group
  rw [centralizer_T46, mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

private theorem semiPerm_refl_eq_piGU (A : GU0) :
    semiPerm A (RingEquiv.refl F4) = piGU A := by
  have hf : ∀ w : W, fvec (RingEquiv.refl F4) w = w := fun w => funext fun i => rfl
  ext p
  rw [semiPerm_val, semiVec, hf]
  change _ = (A • p).val
  rw [smul_val]

private theorem piGU_deltaGU_fix_of_zero {p : Fin 693}
    (hp : uVec p 0 = 0) : piGU deltaGU p = p := by
  apply Fin.ext
  change (deltaGU • p).val = p.val
  have hd : deltaM *ᵥ uVec p = uVec p := by
    funext i
    rw [deltaM, mulVec_diagonal]
    by_cases hi : i = 0
    · subst hi
      simp [hp]
    · simp [hi]
  rw [smul_val, deltaGU_val, hd, ptIdx_uVec ptsFacts p.2]

private theorem tvP_mem_inf_centralizer_delta
    {p : Fin 693} (hp : uVec p 0 = 0) :
    tvP p ∈ T46 ⊓ centralizer ({piGU deltaGU} : Set (Equiv.Perm (Fin 693))) := by
  refine mem_inf.2 ⟨tvP_mem p, ?_⟩
  rw [mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have h := semiPerm_tvP deltaGU (RingEquiv.refl F4) p
  rw [semiPerm_refl_eq_piGU, piGU_deltaGU_fix_of_zero hp] at h
  exact mul_inv_eq_iff_eq_mul.1 h

private theorem piGU_eq_of_matrix_smul (g h : GU0) {c : F4}
    (hc : c ≠ 0) (hgh : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      c • ((h : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) : piGU g = piGU h := by
  ext p
  change (g • p).val = (h • p).val
  rw [smul_val, smul_val, hgh, smul_mulVec, ptIdx_smul hc]

private theorem deltaGU_pow_val (k : ℕ) :
    (((deltaGU ^ k : GU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal fun i => if i = 0 then F4.ω ^ k else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, deltaGU_val, deltaM, diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp [pow_succ]

private theorem piGU_diag_mem_zpowers (A : GU0) {α β : F4}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hA : ∀ k l : Fin 6, ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) k l =
      if k = l then (if l = 0 then α else β) else 0) : piGU A ∈ zpowers (piGU deltaGU) := by
  have h3 : ∀ a b : F4, a ≠ 0 → b ≠ 0 →
      a = b * F4.ω ^ 0 ∨ a = b * F4.ω ^ 1 ∨ a = b * F4.ω ^ 2 := by decide
  obtain ⟨n, hn⟩ : ∃ n : ℕ, α = β * F4.ω ^ n := by
    rcases h3 α β hα hβ with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hpow : piGU A = piGU (deltaGU ^ n) := by
    refine piGU_eq_of_matrix_smul A (deltaGU ^ n) hβ ?_
    ext k l
    rw [hA, deltaGU_pow_val, Matrix.smul_apply, diagonal_apply]
    by_cases hkl : k = l
    · subst hkl
      by_cases hk : k = 0
      · simp [hk, hn]
      · simp [hk]
    · simp [hkl]
  rw [hpow, map_pow]
  exact pow_mem (mem_zpowers _) n

theorem mem_zpowers_of_commute_inf_centralizer
    {y : Equiv.Perm (Fin 693)} (hy : y ∈ autT)
    (hc : ∀ c ∈ T46 ⊓ centralizer ({piGU deltaGU} : Set (Equiv.Perm (Fin 693))), y * c = c * y) :
    y ∈ zpowers (piGU deltaGU) := by
  obtain ⟨A, φ, rfl⟩ := eq_semiPerm_of_mem_autT hy
  have hfix : ∀ p : Fin 693, uVec p 0 = 0 → tvP (semiPerm A φ p) = tvP p := fun p hp => by
    rw [← semiPerm_tvP, hc _ (tvP_mem_inf_centralizer_delta hp), mul_inv_cancel_right]
  obtain ⟨hφ, α, β, hα, hβ, hA⟩ := semiVec_diag_of_orth_pairs A φ
    fun i j hi hj hij c hcc x hx0 hxi hxu => orth_transfer_of_tvP_fixed A φ hfix hi hj hij
      (by rcases hcc with rfl | rfl <;> decide) hx0 hxi hxu
  obtain rfl : φ = RingEquiv.refl F4 := RingEquiv.ext hφ
  rw [semiPerm_refl_eq_piGU]
  exact piGU_diag_mem_zpowers A hα hβ hA

end CFSG.GGQ2Prime

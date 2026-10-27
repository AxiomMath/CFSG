module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphI1
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphTheta

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley

@[expose] noncomputable def ggHalfBlockHom {G : Type} [Group G]
    (φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G) : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* G
  | .L => φ₁
  | .K => φ₂
  | .M => (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂

private theorem ggHalfGraphAgree_slLower2Hom_transvection {u v : Fin 4} (huv : u ≠ v)
    (c : F2) :
    slLower2Hom 3 (SpecialLinearGroup.transvection huv c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne huv)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

private theorem ggHalfGraphAgree_slUpper2Hom_transvection {u v : Fin 4} (huv : u ≠ v)
    (c : F2) :
    slUpper2Hom 3 (SpecialLinearGroup.transvection huv c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne huv)) c := by
  rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_transvection,
    slUpperBlockHom_transvection]

private theorem ggHalfGraphAgree_slPerm_conj_transvection {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    {i j : Fin (n + 1)} (hij : i ≠ j) (c : F2) :
    slPerm gf2_two π * SpecialLinearGroup.transvection hij c * (slPerm gf2_two π)⁻¹ =
      SpecialLinearGroup.transvection (π.injective.ne hij) c := by
  have h := conj_transvection_of_coe_eq_signedPerm (g := slPerm gf2_two π)
    (coe_slPerm gf2_two π) (fun s => by simp) hij c
  simpa using h

private theorem ggHalfGraphAgree_slPerm_conj_slE (π : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    slPerm gf2_two π * slE i j * (slPerm gf2_two π)⁻¹ = slE (π i) (π j) := by
  by_cases hij : i = j
  · subst hij
    simp [slE]
  · rw [slE, dif_neg hij, ggHalfGraphAgree_slPerm_conj_transvection π hij 1, slE,
      dif_neg (π.injective.ne hij)]

private theorem ggHalfGraphAgree_agree4 {G : Type} [Group G]
    {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (hagree : φ₁.comp (slLower2Hom 3) = φ₂.comp (slUpper2Hom 3)) (u v : Fin 4) :
    φ₁ (slE u.succ.succ v.succ.succ) = φ₂ (slE u.castSucc.castSucc v.castSucc.castSucc) := by
  by_cases huv : u = v
  · subst huv
    simp [slE]
  · have h := DFunLike.congr_fun hagree (SpecialLinearGroup.transvection huv (1 : F2))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      ggHalfGraphAgree_slLower2Hom_transvection huv 1,
      ggHalfGraphAgree_slUpper2Hom_transvection huv 1] at h
    rw [slE, dif_neg ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne huv)),
      slE, dif_neg ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne huv))]
    exact h

private theorem ggHalfGraphAgree_LK {G : Type} [Group G]
    {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (hagree : φ₁.comp (slLower2Hom 3) = φ₂.comp (slUpper2Hom 3))
    (c d c' d' : Fin 6) (hc : c.val = 2 + c'.val) (hd : d.val = 2 + d'.val) :
    φ₁ (slE c d) = φ₂ (slE c' d') := by
  have hc' : c'.val < 4 := by have := c.isLt; omega
  have hd' : d'.val < 4 := by have := d.isLt; omega
  let u : Fin 4 := ⟨c'.val, hc'⟩
  let v : Fin 4 := ⟨d'.val, hd'⟩
  have hcu : c = u.succ.succ := by
    apply Fin.ext
    dsimp only [u]
    simp only [Fin.val_succ, Fin.val_mk]
    omega
  have hdv : d = v.succ.succ := by
    apply Fin.ext
    dsimp only [v]
    simp only [Fin.val_succ, Fin.val_mk]
    omega
  have hc'u : c' = u.castSucc.castSucc := by
    apply Fin.ext
    dsimp only [u]
    simp only [Fin.val_castSucc, Fin.val_mk]
  have hd'v : d' = v.castSucc.castSucc := by
    apply Fin.ext
    dsimp only [v]
    simp only [Fin.val_castSucc, Fin.val_mk]
  have h4 := ggHalfGraphAgree_agree4 hagree u v
  rw [← hcu, ← hdv] at h4
  rw [← hc'u, ← hd'v] at h4
  exact h4

private def ggHalfGraphAgree_mup : Fin 6 → Fin 6 := ![0, 1, 4, 5, 0, 0]

private theorem ggHalfGraphAgree_mup_val (c : Fin 6) (hc : c.val < 4) :
    (ggHalfGraphAgree_mup c).val = (ggHalfSigma (GGHalfBlk.lab .M c)).val := by
  revert hc
  fin_cases c <;> decide

private def ggHalfGraphAgree_pidown : Fin 6 → Fin 6 := ![0, 1, 3, 2, 5, 4]

private theorem ggHalfGraphAgree_pidown_val (c : Fin 6) :
    (ggHalfGraphAgree_pidown c).val = (ggHalfPi (GGHalfBlk.lab .M c)).val - 2 := by
  fin_cases c <;> decide

private def ggHalfGraphAgree_sdown : Fin 6 → Fin 6 := ![0, 0, 3, 2, 1, 0]

private theorem ggHalfGraphAgree_sdown_val (d : Fin 6) :
    (ggHalfGraphAgree_sdown d).val = (ggHalfSLoc d).val - 2 := by
  fin_cases d <;> decide

private theorem ggHalfGraphAgree_sigma_succ_succ (u : Fin 4) :
    sigmaPerm 3 (u.succ.succ) = ggHalfGraphAgree_mup u.castSucc.castSucc := by
  fin_cases u <;> decide

private theorem ggHalfGraphAgree_tau_sdown (d : Fin 6) (hd : 2 ≤ d.val) :
    tauPerm 3 (ggHalfGraphAgree_sdown d) = ggHalfGraphAgree_pidown d := by
  revert hd
  fin_cases d <;> decide

private theorem ggHalfGraphAgree_ggHalfSLoc_ge (d : Fin 6) (hd : 2 ≤ d.val) :
    2 ≤ (ggHalfSLoc d).val := by
  revert hd
  fin_cases d <;> decide

private theorem ggHalfGraphAgree_ggHalfSigma_lt (a : Fin 8) (h : a.val < 6) :
    (ggHalfSigma a).val < 6 := by
  revert h
  fin_cases a <;> decide

private theorem ggHalfGraphAgree_ggHalfPi_ge (a : Fin 8) (h : 4 ≤ a.val) :
    2 ≤ (ggHalfPi a).val := by
  revert h
  fin_cases a <;> decide

private theorem ggHalfGraphAgree_ggHalfSigma_injective : Function.Injective ggHalfSigma := by
  decide

private theorem ggHalfGraphAgree_ggHalfPi_injective : Function.Injective ggHalfPi := by
  decide

private theorem ggHalfGraphAgree_ML {G : Type} [Group G]
    {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (hagree : φ₁.comp (slLower2Hom 3) = φ₂.comp (slUpper2Hom 3))
    (c d : Fin 6) (hc : c.val < 4) (hd : d.val < 4) :
    gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹ =
      φ₁ (slE (ggHalfGraphAgree_mup c) (ggHalfGraphAgree_mup d)) := by
  let u : Fin 4 := ⟨c.val, hc⟩
  let v : Fin 4 := ⟨d.val, hd⟩
  have hcu : c = u.castSucc.castSucc := by
    apply Fin.ext
    dsimp only [u]
    simp only [Fin.val_castSucc, Fin.val_mk]
  have hdv : d = v.castSucc.castSucc := by
    apply Fin.ext
    dsimp only [v]
    simp only [Fin.val_castSucc, Fin.val_mk]
  have hΦ : φ₂ (slE c d) = φ₁ (slE u.succ.succ v.succ.succ) := by
    rw [hcu, hdv]
    exact (ggHalfGraphAgree_agree4 hagree u v).symm
  have hmu : ggHalfGraphAgree_mup c = sigmaPerm 3 u.succ.succ := by
    rw [hcu, ggHalfGraphAgree_sigma_succ_succ u]
  have hmv : ggHalfGraphAgree_mup d = sigmaPerm 3 v.succ.succ := by
    rw [hdv, ggHalfGraphAgree_sigma_succ_succ v]
  calc gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹
      = gElt φ₁ * φ₁ (slE u.succ.succ v.succ.succ) * (gElt φ₁)⁻¹ := by rw [hΦ]
    _ = φ₁ (slE (sigmaPerm 3 u.succ.succ) (sigmaPerm 3 v.succ.succ)) := by
        rw [show gElt φ₁ = φ₁ (slPerm gf2_two (sigmaPerm 3)) from rfl]
        rw [← map_mul, ← map_inv, ← map_mul, ggHalfGraphAgree_slPerm_conj_slE]
    _ = φ₁ (slE (ggHalfGraphAgree_mup c) (ggHalfGraphAgree_mup d)) := by
        rw [← hmu, ← hmv]

private theorem ggHalfGraphAgree_MK {G : Type} [Group G]
    {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (hagree : φ₁.comp (slLower2Hom 3) = φ₂.comp (slUpper2Hom 3))
    (hI1 : ∀ c d : Fin 6, c ≠ d →
      gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹ =
        hElt φ₂ * φ₁ (slE (ggHalfSLoc d) (ggHalfSLoc c)) * (hElt φ₂)⁻¹)
    (c d : Fin 6) (hc : 2 ≤ c.val) (hd : 2 ≤ d.val) (hcd : c ≠ d) :
    gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹ =
      φ₂ (slE (ggHalfGraphAgree_pidown d) (ggHalfGraphAgree_pidown c)) := by
  have hSd2 : 2 ≤ (ggHalfSLoc d).val := ggHalfGraphAgree_ggHalfSLoc_ge d hd
  have hSc2 : 2 ≤ (ggHalfSLoc c).val := ggHalfGraphAgree_ggHalfSLoc_ge c hc
  have hL : φ₁ (slE (ggHalfSLoc d) (ggHalfSLoc c)) =
      φ₂ (slE (ggHalfGraphAgree_sdown d) (ggHalfGraphAgree_sdown c)) := by
    refine ggHalfGraphAgree_LK hagree _ _ _ _
      (by show (ggHalfSLoc d).val = 2 + (ggHalfGraphAgree_sdown d).val
          rw [ggHalfGraphAgree_sdown_val d]; omega)
      (by show (ggHalfSLoc c).val = 2 + (ggHalfGraphAgree_sdown c).val
          rw [ggHalfGraphAgree_sdown_val c]; omega)
  calc gElt φ₁ * φ₂ (slE c d) * (gElt φ₁)⁻¹
      = hElt φ₂ * φ₁ (slE (ggHalfSLoc d) (ggHalfSLoc c)) * (hElt φ₂)⁻¹ :=
        hI1 c d hcd
    _ = hElt φ₂ * φ₂ (slE (ggHalfGraphAgree_sdown d) (ggHalfGraphAgree_sdown c)) *
          (hElt φ₂)⁻¹ := by rw [hL]
    _ = φ₂ (slE (tauPerm 3 (ggHalfGraphAgree_sdown d))
          (tauPerm 3 (ggHalfGraphAgree_sdown c))) := by
        rw [show hElt φ₂ = φ₂ (slPerm gf2_two (tauPerm 3)) from rfl]
        rw [← map_mul, ← map_inv, ← map_mul, ggHalfGraphAgree_slPerm_conj_slE]
    _ = φ₂ (slE (ggHalfGraphAgree_pidown d) (ggHalfGraphAgree_pidown c)) := by
        rw [ggHalfGraphAgree_tau_sdown d hd, ggHalfGraphAgree_tau_sdown c hc]

private theorem ggHalfGraphAgree_frame_inj {m : GGHalfE6Model} {b : GGHalfBlk}
    (hb : m.FrameOK b) {i j k l : Fin 8}
    (hi : b.Lab i) (hj : b.Lab j) (hk : b.Lab k) (hl : b.Lab l)
    (hij : i ≠ j) (hkl : k ≠ l)
    (heq : m.frame b i j = m.frame b k l) : i = k ∧ j = l := by
  by_contra hne
  have hne' : ¬ (l = j ∧ k = i) := fun ⟨hlj, hki⟩ => hne ⟨hki.symm, hlj.symm⟩
  have h0 : m.frame b i j + m.frame b l k = 0 := by
    have hB : m.frame b l k = -m.frame b k l := hb.2.1 k l hk hl hkl
    rw [heq, hB]
    exact add_neg_cancel _
  exact hb.2.2.2.1 i j l k hi hj hl hk hij hkl.symm hne' h0

private theorem ggHalfGraphAgree_lab_inj {b : GGHalfBlk} {c c' : Fin 6}
    (h : b.lab c = b.lab c') : c = c' := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  cases b <;> simp only [GGHalfBlk.lab, GGHalfBlk.off] at hv <;> omega

private theorem ggHalfGraphAgree_lab_mem (b : GGHalfBlk) (c : Fin 6) : b.Lab (b.lab c) := by
  cases b <;>
    simp only [GGHalfBlk.lab, GGHalfBlk.off, GGHalfBlk.Lab, Fin.val_mk] <;>
    (have := c.isLt; omega)

private theorem ggHalfGraphAgree_lab_ne {b : GGHalfBlk} {c d : Fin 6} (h : c ≠ d) :
    b.lab c ≠ b.lab d := fun hh => h (ggHalfGraphAgree_lab_inj hh)

private theorem ggHalfGraphAgree_mem_Y {m : GGHalfE6Model} {b : GGHalfBlk} {c d : Fin 6}
    (hcd : c ≠ d) : m.frame b (b.lab c) (b.lab d) ∈ m.Y b :=
  ⟨b.lab c, b.lab d, ggHalfGraphAgree_lab_mem b c, ggHalfGraphAgree_lab_mem b d,
    ggHalfGraphAgree_lab_ne hcd, rfl⟩

private theorem ggHalfGraphAgree_lab_L (c : Fin 6) :
    GGHalfBlk.lab .L c = (⟨c.val, by have := c.isLt; omega⟩ : Fin 8) :=
  Fin.ext (by simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk, Nat.zero_add])

private theorem ggHalfGraphAgree_lab_K (c : Fin 6) :
    GGHalfBlk.lab .K c = (⟨2 + c.val, by have := c.isLt; omega⟩ : Fin 8) :=
  Fin.ext (by simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk])

private theorem ggHalfGraphAgree_lab_M (c : Fin 6) :
    GGHalfBlk.lab .M c = (⟨2 + c.val, by have := c.isLt; omega⟩ : Fin 8) :=
  Fin.ext (by simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk])

private theorem ggHalfGraphAgree_overlap_LK {m : GGHalfE6Model} (hmL : m.FrameOK .L)
    (hmK : m.FrameOK .K) (hO : m.Overlap) {c d c' d' : Fin 6} (hcd : c ≠ d) (hcd' : c' ≠ d')
    (hfr : m.frame .L (GGHalfBlk.lab .L c) (GGHalfBlk.lab .L d) = m.frame .K (GGHalfBlk.lab .K c') (GGHalfBlk.lab .K d')) :
    c.val = 2 + c'.val ∧ d.val = 2 + d'.val := by
  have hrY : m.frame .L (GGHalfBlk.lab .L c) (GGHalfBlk.lab .L d) ∈ m.Y .L ∩ m.Y .K :=
    ⟨ggHalfGraphAgree_mem_Y hcd, by rw [hfr]; exact ggHalfGraphAgree_mem_Y hcd'⟩
  rw [hO.2.2.2.1] at hrY
  obtain ⟨γ, δ, hγ2, hγ6, hδ2, hδ6, hγδ, hγδr⟩ := hrY
  have hLc : (GGHalfBlk.lab .L c) = γ := (ggHalfGraphAgree_frame_inj hmL
    (ggHalfGraphAgree_lab_mem .L c) (ggHalfGraphAgree_lab_mem .L d)
    hγ6 hδ6 (ggHalfGraphAgree_lab_ne hcd) hγδ hγδr.symm).1
  have hLd : (GGHalfBlk.lab .L d) = δ := (ggHalfGraphAgree_frame_inj hmL
    (ggHalfGraphAgree_lab_mem .L c) (ggHalfGraphAgree_lab_mem .L d)
    hγ6 hδ6 (ggHalfGraphAgree_lab_ne hcd) hγδ hγδr.symm).2
  have heqK : m.frame .K (GGHalfBlk.lab .K c') (GGHalfBlk.lab .K d') = m.frame .K γ δ := by
    rw [← hfr, ← hγδr, hO.1 γ δ hγ2 hγ6 hδ2 hδ6 hγδ]
  have hKc' : (GGHalfBlk.lab .K c') = γ := (ggHalfGraphAgree_frame_inj hmK
    (ggHalfGraphAgree_lab_mem .K c') (ggHalfGraphAgree_lab_mem .K d')
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd') hγδ heqK).1
  have hKd' : (GGHalfBlk.lab .K d') = δ := (ggHalfGraphAgree_frame_inj hmK
    (ggHalfGraphAgree_lab_mem .K c') (ggHalfGraphAgree_lab_mem .K d')
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd') hγδ heqK).2
  constructor
  · have h1 := congrArg Fin.val hLc
    have h2 := congrArg Fin.val hKc'
    rw [ggHalfGraphAgree_lab_L] at h1
    rw [ggHalfGraphAgree_lab_K] at h2
    simp only [Fin.val_mk] at h1 h2
    omega
  · have h1 := congrArg Fin.val hLd
    have h2 := congrArg Fin.val hKd'
    rw [ggHalfGraphAgree_lab_L] at h1
    rw [ggHalfGraphAgree_lab_K] at h2
    simp only [Fin.val_mk] at h1 h2
    omega

private theorem ggHalfGraphAgree_overlap_LM {m : GGHalfE6Model} (hmL : m.FrameOK .L)
    (hmM : m.FrameOK .M) (hO : m.Overlap) {c d c' d' : Fin 6} (hcd : c ≠ d) (hcd' : c' ≠ d')
    (hfr : m.frame .L (GGHalfBlk.lab .L c) (GGHalfBlk.lab .L d) = m.frame .M (GGHalfBlk.lab .M c') (GGHalfBlk.lab .M d')) :
    c = ggHalfGraphAgree_mup c' ∧ d = ggHalfGraphAgree_mup d' ∧ c'.val < 4 ∧ d'.val < 4 := by
  have hrY : m.frame .L (GGHalfBlk.lab .L c) (GGHalfBlk.lab .L d) ∈ m.Y .L ∩ m.Y .M :=
    ⟨ggHalfGraphAgree_mem_Y hcd, by rw [hfr]; exact ggHalfGraphAgree_mem_Y hcd'⟩
  rw [hO.2.2.2.2.1] at hrY
  obtain ⟨γ, δ, hγ2, hγ6, hδ2, hδ6, hγδ, hγδr⟩ := hrY
  have hMc' : (GGHalfBlk.lab .M c') = γ := (ggHalfGraphAgree_frame_inj hmM
    (ggHalfGraphAgree_lab_mem .M c') (ggHalfGraphAgree_lab_mem .M d')
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd') hγδ (by rw [← hfr, ← hγδr])).1
  have hMd' : (GGHalfBlk.lab .M d') = δ := (ggHalfGraphAgree_frame_inj hmM
    (ggHalfGraphAgree_lab_mem .M c') (ggHalfGraphAgree_lab_mem .M d')
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd') hγδ (by rw [← hfr, ← hγδr])).2
  have hLc : (GGHalfBlk.lab .L c) = ggHalfSigma γ := (ggHalfGraphAgree_frame_inj hmL
    (ggHalfGraphAgree_lab_mem .L c) (ggHalfGraphAgree_lab_mem .L d)
    (ggHalfGraphAgree_ggHalfSigma_lt γ hγ6) (ggHalfGraphAgree_ggHalfSigma_lt δ hδ6)
    (ggHalfGraphAgree_lab_ne hcd)
    (fun hh => hγδ (ggHalfGraphAgree_ggHalfSigma_injective hh))
    (by rw [← hγδr, hO.2.1 γ δ hγ2 hγ6 hδ2 hδ6 hγδ])).1
  have hLd : (GGHalfBlk.lab .L d) = ggHalfSigma δ := (ggHalfGraphAgree_frame_inj hmL
    (ggHalfGraphAgree_lab_mem .L c) (ggHalfGraphAgree_lab_mem .L d)
    (ggHalfGraphAgree_ggHalfSigma_lt γ hγ6) (ggHalfGraphAgree_ggHalfSigma_lt δ hδ6)
    (ggHalfGraphAgree_lab_ne hcd)
    (fun hh => hγδ (ggHalfGraphAgree_ggHalfSigma_injective hh))
    (by rw [← hγδr, hO.2.1 γ δ hγ2 hγ6 hδ2 hδ6 hγδ])).2
  have hc'4 : c'.val < 4 := by
    have h := congrArg Fin.val hMc'
    rw [ggHalfGraphAgree_lab_M] at h
    simp only [Fin.val_mk] at h
    omega
  have hd'4 : d'.val < 4 := by
    have h := congrArg Fin.val hMd'
    rw [ggHalfGraphAgree_lab_M] at h
    simp only [Fin.val_mk] at h
    omega
  refine ⟨?_, ?_, hc'4, hd'4⟩
  · apply Fin.ext
    rw [ggHalfGraphAgree_mup_val c' hc'4, hMc']
    have h := congrArg Fin.val hLc
    rw [ggHalfGraphAgree_lab_L] at h
    simp only [Fin.val_mk] at h
    exact h
  · apply Fin.ext
    rw [ggHalfGraphAgree_mup_val d' hd'4, hMd']
    have h := congrArg Fin.val hLd
    rw [ggHalfGraphAgree_lab_L] at h
    simp only [Fin.val_mk] at h
    exact h

private theorem ggHalfGraphAgree_overlap_MK {m : GGHalfE6Model} (hmK : m.FrameOK .K)
    (hmM : m.FrameOK .M) (hO : m.Overlap) {c d c' d' : Fin 6} (hcd : c ≠ d) (hcd' : c' ≠ d')
    (hfr : m.frame .M (GGHalfBlk.lab .M c) (GGHalfBlk.lab .M d) = m.frame .K (GGHalfBlk.lab .K c') (GGHalfBlk.lab .K d')) :
    c' = ggHalfGraphAgree_pidown d ∧ d' = ggHalfGraphAgree_pidown c ∧ 2 ≤ c.val ∧ 2 ≤ d.val := by
  have hrY : m.frame .M (GGHalfBlk.lab .M c) (GGHalfBlk.lab .M d) ∈ m.Y .K ∩ m.Y .M :=
    ⟨by rw [hfr]; exact ggHalfGraphAgree_mem_Y hcd', ggHalfGraphAgree_mem_Y hcd⟩
  rw [hO.2.2.2.2.2] at hrY
  obtain ⟨γ, δ, hγ4, hδ4, hγδ, hγδr⟩ := hrY
  have hγ2 : GGHalfBlk.Lab .M γ := by show 2 ≤ γ.val; omega
  have hδ2 : GGHalfBlk.Lab .M δ := by show 2 ≤ δ.val; omega
  have hMc : (GGHalfBlk.lab .M c) = γ := (ggHalfGraphAgree_frame_inj (k := γ) (l := δ) hmM
    (ggHalfGraphAgree_lab_mem .M c) (ggHalfGraphAgree_lab_mem .M d)
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd) hγδ hγδr.symm).1
  have hMd : (GGHalfBlk.lab .M d) = δ := (ggHalfGraphAgree_frame_inj (k := γ) (l := δ) hmM
    (ggHalfGraphAgree_lab_mem .M c) (ggHalfGraphAgree_lab_mem .M d)
    hγ2 hδ2 (ggHalfGraphAgree_lab_ne hcd) hγδ hγδr.symm).2
  have heqK : m.frame .K (GGHalfBlk.lab .K c') (GGHalfBlk.lab .K d') = m.frame .K (ggHalfPi δ) (ggHalfPi γ) := by
    rw [← hfr, ← hγδr, hO.2.2.1 γ δ hγ4 hδ4 hγδ]
  have hKc' : (GGHalfBlk.lab .K c') = ggHalfPi δ := (ggHalfGraphAgree_frame_inj hmK
    (ggHalfGraphAgree_lab_mem .K c') (ggHalfGraphAgree_lab_mem .K d')
    (ggHalfGraphAgree_ggHalfPi_ge δ hδ4) (ggHalfGraphAgree_ggHalfPi_ge γ hγ4)
    (ggHalfGraphAgree_lab_ne hcd')
    (fun hh => hγδ (ggHalfGraphAgree_ggHalfPi_injective hh).symm) heqK).1
  have hKd' : (GGHalfBlk.lab .K d') = ggHalfPi γ := (ggHalfGraphAgree_frame_inj hmK
    (ggHalfGraphAgree_lab_mem .K c') (ggHalfGraphAgree_lab_mem .K d')
    (ggHalfGraphAgree_ggHalfPi_ge δ hδ4) (ggHalfGraphAgree_ggHalfPi_ge γ hγ4)
    (ggHalfGraphAgree_lab_ne hcd')
    (fun hh => hγδ (ggHalfGraphAgree_ggHalfPi_injective hh).symm) heqK).2
  have hc2 : 2 ≤ c.val := by
    have h := congrArg Fin.val hMc
    rw [ggHalfGraphAgree_lab_M] at h
    simp only [Fin.val_mk] at h
    omega
  have hd2 : 2 ≤ d.val := by
    have h := congrArg Fin.val hMd
    rw [ggHalfGraphAgree_lab_M] at h
    simp only [Fin.val_mk] at h
    omega
  refine ⟨?_, ?_, hc2, hd2⟩
  · apply Fin.ext
    rw [ggHalfGraphAgree_pidown_val d, hMd]
    have h := congrArg Fin.val hKc'
    rw [ggHalfGraphAgree_lab_K] at h
    simp only [Fin.val_mk] at h
    omega
  · apply Fin.ext
    rw [ggHalfGraphAgree_pidown_val c, hMc]
    have h := congrArg Fin.val hKd'
    rw [ggHalfGraphAgree_lab_K] at h
    simp only [Fin.val_mk] at h
    omega

namespace GGHalfCtx

theorem frames_agree {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) :
    ∀ (b b' : GGHalfBlk) (c d c' d' : Fin 6), c ≠ d → c' ≠ d' →
      m.frame b (b.lab c) (b.lab d) = m.frame b' (b'.lab c') (b'.lab d') →
      ggHalfBlockHom φ₁ φ₂ b (slE c d) = ggHalfBlockHom φ₁ φ₂ b' (slE c' d') := by
  intro b b' c d c' d' hcd hcd' hfr
  obtain ⟨hmL, hmK, hmM, -, -, -, hO, -, -, -⟩ := hm
  cases b <;> cases b'
  · obtain ⟨h1, h2⟩ := ggHalfGraphAgree_frame_inj hmL
      (ggHalfGraphAgree_lab_mem .L c) (ggHalfGraphAgree_lab_mem .L d)
      (ggHalfGraphAgree_lab_mem .L c') (ggHalfGraphAgree_lab_mem .L d')
      (ggHalfGraphAgree_lab_ne hcd) (ggHalfGraphAgree_lab_ne hcd') hfr
    rw [ggHalfGraphAgree_lab_inj h1, ggHalfGraphAgree_lab_inj h2]
  · obtain ⟨hc, hd⟩ := ggHalfGraphAgree_overlap_LK hmL hmK hO hcd hcd' hfr
    exact ggHalfGraphAgree_LK h.coords.agree c d c' d' hc hd
  · obtain ⟨hc, hd, hc'4, hd'4⟩ := ggHalfGraphAgree_overlap_LM hmL hmM hO hcd hcd' hfr
    rw [hc, hd]
    exact (ggHalfGraphAgree_ML h.coords.agree c' d' hc'4 hd'4).symm
  · obtain ⟨hc, hd⟩ := ggHalfGraphAgree_overlap_LK hmL hmK hO hcd' hcd hfr.symm
    exact (ggHalfGraphAgree_LK h.coords.agree c' d' c d hc hd).symm
  · obtain ⟨h1, h2⟩ := ggHalfGraphAgree_frame_inj hmK
      (ggHalfGraphAgree_lab_mem .K c) (ggHalfGraphAgree_lab_mem .K d)
      (ggHalfGraphAgree_lab_mem .K c') (ggHalfGraphAgree_lab_mem .K d')
      (ggHalfGraphAgree_lab_ne hcd) (ggHalfGraphAgree_lab_ne hcd') hfr
    rw [ggHalfGraphAgree_lab_inj h1, ggHalfGraphAgree_lab_inj h2]
  · obtain ⟨hc, hd, hc2, hd2⟩ := ggHalfGraphAgree_overlap_MK hmK hmM hO hcd' hcd hfr.symm
    rw [hc, hd]
    exact (ggHalfGraphAgree_MK h.coords.agree (graph_I1 h hg) c' d' hc2 hd2 hcd').symm
  · obtain ⟨hc, hd, hc4, hd4⟩ := ggHalfGraphAgree_overlap_LM hmL hmM hO hcd' hcd hfr.symm
    rw [hc, hd]
    exact ggHalfGraphAgree_ML h.coords.agree c d hc4 hd4
  · obtain ⟨hc', hd', hc2, hd2⟩ := ggHalfGraphAgree_overlap_MK hmK hmM hO hcd hcd' hfr
    rw [hc', hd']
    exact ggHalfGraphAgree_MK h.coords.agree (graph_I1 h hg) c d hc2 hd2 hcd
  · obtain ⟨h1, h2⟩ := ggHalfGraphAgree_frame_inj hmM
      (ggHalfGraphAgree_lab_mem .M c) (ggHalfGraphAgree_lab_mem .M d)
      (ggHalfGraphAgree_lab_mem .M c') (ggHalfGraphAgree_lab_mem .M d')
      (ggHalfGraphAgree_lab_ne hcd) (ggHalfGraphAgree_lab_ne hcd') hfr
    rw [ggHalfGraphAgree_lab_inj h1, ggHalfGraphAgree_lab_inj h2]

end GGHalfCtx

end CFSG.StandardType

end

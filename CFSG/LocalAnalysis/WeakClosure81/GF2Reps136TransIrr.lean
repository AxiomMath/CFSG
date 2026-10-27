module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136IrrCorr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TransAbs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136LemmaF

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_forall_mem_of_map_eq {M : Subgroup W} {g : MulAut W}
    (h : M.map g.toMonoidHom = M) : ∀ m ∈ M, g m ∈ M :=
  fun m hm => h ▸ Subgroup.mem_map_of_mem g.toMonoidHom hm

private theorem w1369_im_map_secAut {U C : Subgroup W} {g : MulAut W}
    (hU : ∀ u ∈ U, g u ∈ U) (hC : ∀ z ∈ C, g z ∈ C) (M : Subgroup W) :
    (w1369_im U C M).map (secAut U C g hU hC).toMonoidHom =
      w1369_im U C (M.map g.toMonoidHom) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [w1369_im, Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [QuotientGroup.mk'_apply]
    change secAut U C g hU hC (QuotientGroup.mk u) ∈
      w1369_im U C (M.map g.toMonoidHom)
    rw [secAut_mk, w1369_im, Subgroup.mem_map]
    exact ⟨⟨g (u : W), hU (u : W) u.2⟩,
      Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem g.toMonoidHom (Subgroup.mem_subgroupOf.mp hu)), rfl⟩
  · intro hx
    rw [w1369_im, Subgroup.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmu : (u : W) ∈ M.map g.toMonoidHom := Subgroup.mem_subgroupOf.mp hu
    rw [Subgroup.mem_map] at hmu
    obtain ⟨m, hm, hmg⟩ := hmu
    have hmU : m ∈ U := by
      have h1 : g⁻¹ (u : W) ∈ U := inv_mem_of_forall_mem g hU (u : W) u.2
      rw [← hmg] at h1
      simpa using h1
    rw [Subgroup.mem_map]
    refine ⟨QuotientGroup.mk (⟨m, hmU⟩ : ↥U), ?_, ?_⟩
    · rw [w1369_im, Subgroup.mem_map]
      exact ⟨⟨m, hmU⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    · change secAut U C g hU hC (QuotientGroup.mk ⟨m, hmU⟩) =
        QuotientGroup.mk' (C.subgroupOf U) u
      rw [secAut_mk, QuotientGroup.mk'_apply]
      exact congrArg (fun z : ↥U => (QuotientGroup.mk z : Sect U C)) (Subtype.ext hmg)

theorem transitive_on_irr (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      I₂ = I₁.map g.toMonoidHom := by
  classical
  let U : Subgroup W := Wd L
  let C : Subgroup W := Cd L
  have hCU : C ≤ U := inf_le_left
  have hLstab : StabPair L U C := by
    intro a ha
    have h := irr_stab (L.le_normalizer ha)
    exact ⟨w1369_forall_mem_of_map_eq h.1, w1369_forall_mem_of_map_eq h.2.1⟩
  have hYstab : StabPair (Y ⊓ Subgroup.normalizer (L : Set (MulAut W))) U C := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp ha).2
    have h := irr_stab haN
    exact ⟨w1369_forall_mem_of_map_eq h.1, w1369_forall_mem_of_map_eq h.2.1⟩
  obtain ⟨r, J, hD⟩ := fix_decomp hw2 c hfix
  have hJprop : ∀ i : Fin r, C ≤ J i ∧ J i ≤ U ∧ IsIrrOn L (J i) C ∧
      commSub (J i) L ⊔ C = J i ∧ StableUnder (Subgroup.zpowers t) (J i) ∧
      1 ≤ tcost t L (J i) := hD.2.2.1
  have hind0 : ∀ i : Fin r, J i ⊓ (C ⊔ ⨆ (j : Fin r) (_ : j ≠ i), J j) ≤ C :=
    hD.2.2.2.1
  have hspan0 : C ⊔ ⨆ i, J i = U := hD.2.2.2.2.1
  let I : Fin r → Subgroup (Sect U C) := fun i => w1369_im U C (J i)
  let Λ : Subgroup (MulAut (Sect U C)) := secSub U C L
  let N : Subgroup (MulAut (Sect U C)) :=
    secSub U C (Y ⊓ Subgroup.normalizer (L : Set (MulAut W)))
  have hQ : ∀ x : Sect U C, x ^ 2 = 1 := sect_exp_two hw2 U C
  have hΛN : Λ ≤ N :=
    CFSG.Quasithin.autSec_mono (le_inf c.comp.1 L.le_normalizer) U C
  have hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ := by
    intro n hn l hl
    obtain ⟨g, hg, hgn⟩ := (w1369_mem_secSub_iff hYstab).mp hn
    obtain ⟨a, ha, hal⟩ := (w1369_mem_secSub_iff hLstab).mp hl
    rw [← hgn, ← hal]
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
    have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    have hmap := secSub_map_conj hLstab (hYstab g hg).1 (hYstab g hg).2
    rw [hLmap] at hmap
    change MulAut.conj (secAut U C g (hYstab g hg).1 (hYstab g hg).2)
      (secAut U C a (hLstab a ha).1 (hLstab a ha).2) ∈ secSub U C L
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (w1369_secAut_mem_secSub hLstab ha)
  have hstab : ∀ i, StableUnder Λ (I i) := fun i =>
    w1369_stable_im hLstab (hJprop i).2.2.1.2.1
  have hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J' : Subgroup (Sect U C), StableUnder Λ J' →
      J' ≤ I i → J' = ⊥ ∨ J' = I i := by
    intro i
    have h := w1369_irr_transfer hLstab (hJprop i).1 (hJprop i).2.1 (hJprop i).2.2.1
    exact ⟨bot_lt_iff_ne_bot.mp h.1, fun J' hJ' hJ'sub => h.2.2.2 J' hJ' bot_le hJ'sub⟩
  have hspan : ⨆ i, I i = ⊤ := by
    have h1 := w1369_im_sup (U := U) (C := C) (A := C) (B := ⨆ i, J i) hCU
      (iSup_le fun i => (hJprop i).2.1)
    rw [hspan0, w1369_im_top, w1369_im_C] at h1
    rw [bot_sup_eq, w1369_im_iSup (fun i => (hJprop i).2.1)] at h1
    exact h1.symm
  have hind : ∀ i, I i ⊓ (⨆ (j : Fin r) (_ : j ≠ i), I j) = ⊥ :=
    w1369_hind_im (fun i => (hJprop i).1) (fun i => (hJprop i).2.1) hind0
  have hhend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ →
      ∀ f : Sect U C →* Sect U C,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨
      (∀ x ∈ I i, f x = 1) :=
    w1369_perfect_cent_hend hw2 hCU hLstab (fun i => (hJprop i).1)
      (fun i => (hJprop i).2.1) (fun i => (hJprop i).2.2.1) (fix_hend hw2 c hD)
  have hirrN : ∀ M : Subgroup (Sect U C), StableUnder N M → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hpre := lemmaF hw2 c hT (perfCentTriv_of_fixes hw2 c hfix)
      (w1369_pre U C M) (w1369_C_le_pre hCU M) (Subgroup.map_subtype_le _)
      (w1369_stable_pre hYstab hM)
    have him : w1369_im U C (w1369_pre U C M) = M := w1369_im_pre U C M
    rcases hpre with h | h
    · left
      rw [← him, h, w1369_im_C]
    · right
      rw [← him, h, w1369_im_top]
  intro I₁ hI₁ I₂ hI₂
  obtain ⟨-, hC₁, h₁U, hirr₁, -⟩ := irr_to_sect hw2 L hI₁
  obtain ⟨-, hC₂, h₂U, hirr₂, hcomm₂⟩ := irr_to_sect hw2 L hI₂
  have hS₁ : w1369_im U C (I₁ ⊔ C) ≠ ⊥ ∧ StableUnder Λ (w1369_im U C (I₁ ⊔ C)) ∧
      ∀ J' : Subgroup (Sect U C), StableUnder Λ J' → J' ≤ w1369_im U C (I₁ ⊔ C) →
        J' = ⊥ ∨ J' = w1369_im U C (I₁ ⊔ C) := by
    have h := w1369_irr_transfer hLstab hC₁ h₁U hirr₁
    exact ⟨bot_lt_iff_ne_bot.mp h.1, h.2.1,
      fun J' hJ' hJ'sub => h.2.2.2 J' hJ' bot_le hJ'sub⟩
  have hS₂ : w1369_im U C (I₂ ⊔ C) ≠ ⊥ ∧ StableUnder Λ (w1369_im U C (I₂ ⊔ C)) ∧
      ∀ J' : Subgroup (Sect U C), StableUnder Λ J' → J' ≤ w1369_im U C (I₂ ⊔ C) →
        J' = ⊥ ∨ J' = w1369_im U C (I₂ ⊔ C) := by
    have h := w1369_irr_transfer hLstab hC₂ h₂U hirr₂
    exact ⟨bot_lt_iff_ne_bot.mp h.1, h.2.1,
      fun J' hJ' hJ'sub => h.2.2.2 J' hJ' bot_le hJ'sub⟩
  obtain ⟨n, hn, hnS⟩ := trans_abs hQ hΛN hnorm hD.2.1 hstab hsimple hspan hind hhend hirrN
    (w1369_im U C (I₁ ⊔ C)) (w1369_im U C (I₂ ⊔ C)) hS₁ hS₂
  obtain ⟨g, hg, hgn⟩ := (w1369_mem_secSub_iff hYstab).mp hn
  have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
  have hgstab := irr_stab hgN
  have hUmap : U.map g.toMonoidHom = U := hgstab.1
  have hCmap : C.map g.toMonoidHom = C := hgstab.2.1
  have hSS : w1369_im U C (I₂ ⊔ C) =
      (w1369_im U C (I₁ ⊔ C)).map
        (secAut U C g (hYstab g hg).1 (hYstab g hg).2).toMonoidHom := by
    simpa [hgn] using hnS
  have himage := w1369_im_map_secAut (hYstab g hg).1 (hYstab g hg).2 (I₁ ⊔ C)
  have hu : (I₁ ⊔ C).map g.toMonoidHom ≤ U :=
    (Subgroup.map_mono h₁U).trans (le_of_eq hUmap)
  have hc : C ≤ (I₁ ⊔ C).map g.toMonoidHom :=
    (le_of_eq hCmap.symm).trans (Subgroup.map_mono le_sup_right)
  have hpre : I₂ ⊔ C = (I₁ ⊔ C).map g.toMonoidHom := by
    have h := congrArg (w1369_pre U C) (hSS.trans himage)
    rwa [w1369_pre_im hC₂ h₂U, w1369_pre_im hc hu] at h
  have hsup : I₂ ⊔ C = I₁.map g.toMonoidHom ⊔ C := by
    rw [hpre, Subgroup.map_sup, hCmap]
  have hI₁' : I₁.map g.toMonoidHom ∈ irrSet L := hgstab.2.2 I₁ hI₁
  have hcomm₁' : commSub (I₁.map g.toMonoidHom ⊔ C) L = I₁.map g.toMonoidHom :=
    (irr_to_sect hw2 L hI₁').2.2.2.2
  have hcomm := congrArg (fun M : Subgroup W => commSub M L) hsup
  rw [hcomm₂, hcomm₁'] at hcomm
  exact ⟨g, hg, hcomm⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

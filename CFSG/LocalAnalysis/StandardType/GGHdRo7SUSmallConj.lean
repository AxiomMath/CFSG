module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAPerm

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7SmConjAux_cx7Fun : SMV 7 →ₗ[ZMod 3] SMV 7 :=
  LinearMap.id + (smDual (smOnes 7)).smulRight (smOnes 7)
private noncomputable def hdRo7SmConjAux_cx8Fun : SMV 8 →ₗ[ZMod 3] SMV 8 :=
  LinearMap.id - (smDual (smOnes 8)).smulRight (smOnes 8)
private lemma hdRo7SmConjAux_cx7Fun_apply (v : SMV 7) :
    hdRo7SmConjAux_cx7Fun v = v + (∑ i, v i) • smOnes 7 := by
  ext i
  simp [hdRo7SmConjAux_cx7Fun, hdRo7SmAAux_smDual_apply, smDot, smOnes,
    LinearMap.smulRight_apply]
private lemma hdRo7SmConjAux_cx8Fun_apply (v : SMV 8) :
    hdRo7SmConjAux_cx8Fun v = v - (∑ i, v i) • smOnes 8 := by
  ext i
  simp [hdRo7SmConjAux_cx8Fun, hdRo7SmAAux_smDual_apply, smDot, smOnes,
    LinearMap.smulRight_apply]
private lemma hdRo7SmConjAux_cx7Fun_invol (v : SMV 7) :
    hdRo7SmConjAux_cx7Fun (hdRo7SmConjAux_cx7Fun v) = v := by
  rw [hdRo7SmConjAux_cx7Fun_apply, hdRo7SmConjAux_cx7Fun_apply]
  ext i
  simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.smul_apply, smOnes, Pi.one_apply,
    smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  have h9 : (9 : ZMod 3) = 0 := by decide
  rw [h9, mul_zero, add_zero]
private lemma hdRo7SmConjAux_cx8Fun_invol (v : SMV 8) :
    hdRo7SmConjAux_cx8Fun (hdRo7SmConjAux_cx8Fun v) = v := by
  rw [hdRo7SmConjAux_cx8Fun_apply, hdRo7SmConjAux_cx8Fun_apply]
  ext i
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Pi.smul_apply, smOnes, Pi.one_apply,
    smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  have h6 : (6 : ZMod 3) = 0 := by decide
  rw [h6, mul_zero, add_zero]
private noncomputable def hdRo7SmConjAux_cx7 : SMGL 7 :=
  LinearEquiv.ofLinearMap hdRo7SmConjAux_cx7Fun hdRo7SmConjAux_cx7Fun
    (LinearMap.ext fun v => hdRo7SmConjAux_cx7Fun_invol v)
    (LinearMap.ext fun v => hdRo7SmConjAux_cx7Fun_invol v)
private noncomputable def hdRo7SmConjAux_cx8 : SMGL 8 :=
  LinearEquiv.ofLinearMap hdRo7SmConjAux_cx8Fun hdRo7SmConjAux_cx8Fun
    (LinearMap.ext fun v => hdRo7SmConjAux_cx8Fun_invol v)
    (LinearMap.ext fun v => hdRo7SmConjAux_cx8Fun_invol v)
private lemma hdRo7SmConjAux_cx7_apply (v : SMV 7) :
    hdRo7SmConjAux_cx7 v = v + (∑ i, v i) • smOnes 7 :=
  hdRo7SmConjAux_cx7Fun_apply v
private lemma hdRo7SmConjAux_cx8_apply (v : SMV 8) :
    hdRo7SmConjAux_cx8 v = v - (∑ i, v i) • smOnes 8 :=
  hdRo7SmConjAux_cx8Fun_apply v
private lemma hdRo7SmConjAux_cx7_invol (v : SMV 7) :
    hdRo7SmConjAux_cx7 (hdRo7SmConjAux_cx7 v) = v :=
  hdRo7SmConjAux_cx7Fun_invol v
private lemma hdRo7SmConjAux_cx8_invol (v : SMV 8) :
    hdRo7SmConjAux_cx8 (hdRo7SmConjAux_cx8 v) = v :=
  hdRo7SmConjAux_cx8Fun_invol v
private lemma hdRo7SmConjAux_smDot_add_smul_ones_right {m : ℕ} (w v : SMV m) (c : ZMod 3) :
    smDot w (v + c • smOnes m) = smDot w v + c * (∑ i, w i) := by
  have h : (∑ x, w x * c) = (∑ x, w x) * c := by rw [Finset.sum_mul]
  simp only [smDot, Pi.add_apply, Pi.smul_apply, smOnes, Pi.one_apply, smul_eq_mul, mul_one,
    mul_add, Finset.sum_add_distrib]
  rw [h]
  ring
private lemma hdRo7SmConjAux_smDot_add_smul_ones_left {m : ℕ} (w v : SMV m) (c : ZMod 3) :
    smDot (w + c • smOnes m) v = smDot w v + c * (∑ i, v i) := by
  have h : (∑ x, c * v x) = c * (∑ x, v x) := by rw [Finset.mul_sum]
  simp only [smDot, Pi.add_apply, Pi.smul_apply, smOnes, Pi.one_apply, smul_eq_mul, mul_one,
    add_mul, Finset.sum_add_distrib]
  rw [h]
private lemma hdRo7SmConjAux_smDot_sub_smul_ones_right {m : ℕ} (w v : SMV m) (c : ZMod 3) :
    smDot w (v - c • smOnes m) = smDot w v - c * (∑ i, w i) := by
  rw [sub_eq_add_neg, ← neg_smul, hdRo7SmConjAux_smDot_add_smul_ones_right]
  ring
private lemma hdRo7SmConjAux_smDot_sub_smul_ones_left {m : ℕ} (w v : SMV m) (c : ZMod 3) :
    smDot (w - c • smOnes m) v = smDot w v - c * (∑ i, v i) := by
  rw [sub_eq_add_neg, ← neg_smul, hdRo7SmConjAux_smDot_add_smul_ones_left]
  ring
private lemma hdRo7SmConjAux_cx7_symm (w v : SMV 7) :
    smDot w (hdRo7SmConjAux_cx7 v) = smDot (hdRo7SmConjAux_cx7 w) v := by
  rw [hdRo7SmConjAux_cx7_apply, hdRo7SmConjAux_cx7_apply,
    hdRo7SmConjAux_smDot_add_smul_ones_right, hdRo7SmConjAux_smDot_add_smul_ones_left]
  ring
private lemma hdRo7SmConjAux_cx8_symm (w v : SMV 8) :
    smDot w (hdRo7SmConjAux_cx8 v) = smDot (hdRo7SmConjAux_cx8 w) v := by
  rw [hdRo7SmConjAux_cx8_apply, hdRo7SmConjAux_cx8_apply,
    hdRo7SmConjAux_smDot_sub_smul_ones_right, hdRo7SmConjAux_smDot_sub_smul_ones_left]
  ring
private lemma hdRo7SmConjAux_perm_ones {m : ℕ} {g : SMGL m} (hg : SMIsPerm g) :
    g (smOnes m) = smOnes m := by
  obtain ⟨σ, hσ⟩ := hg
  ext i
  rw [hσ (smOnes m) i]
  rfl
private lemma hdRo7SmConjAux_perm_sum {m : ℕ} {g : SMGL m} (hg : SMIsPerm g) (v : SMV m) :
    (∑ i, (g v) i) = ∑ i, v i := by
  obtain ⟨σ, hσ⟩ := hg
  rw [show (∑ i, (g v) i) = ∑ i, v (σ.symm i) from
    Finset.sum_congr rfl (fun i _ => hσ v i)]
  exact Equiv.sum_comp σ.symm (fun j => v j)
private lemma hdRo7SmConjAux_cx7_perm (g : SMGL 7) (hg : SMIsPerm g) :
    ggLinConj hdRo7SmConjAux_cx7 g = g := by
  have hτ : ∀ v, hdRo7SmConjAux_cx7.symm v = hdRo7SmConjAux_cx7 v := fun v =>
    hdRo7SmConjAux_cx7.injective (by rw [LinearEquiv.apply_symm_apply, hdRo7SmConjAux_cx7_invol])
  ext v i
  rw [ggLinConj_apply, hτ]
  have hgcx : g (hdRo7SmConjAux_cx7 v) = g v + (∑ j, v j) • smOnes 7 := by
    rw [hdRo7SmConjAux_cx7_apply, map_add, map_smul, hdRo7SmConjAux_perm_ones hg]
  rw [hgcx, hdRo7SmConjAux_cx7_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smOnes, Pi.one_apply, mul_one, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hdRo7SmConjAux_perm_sum hg v]
  ring_nf
  have h9 : (9 : ZMod 3) = 0 := by decide
  rw [h9, mul_zero, add_zero]
private lemma hdRo7SmConjAux_cx8_perm (g : SMGL 8) (hg : SMIsPerm g) :
    ggLinConj hdRo7SmConjAux_cx8 g = g := by
  have hτ : ∀ v, hdRo7SmConjAux_cx8.symm v = hdRo7SmConjAux_cx8 v := fun v =>
    hdRo7SmConjAux_cx8.injective (by rw [LinearEquiv.apply_symm_apply, hdRo7SmConjAux_cx8_invol])
  ext v i
  rw [ggLinConj_apply, hτ]
  have hgcx : g (hdRo7SmConjAux_cx8 v) = g v - (∑ j, v j) • smOnes 8 := by
    rw [hdRo7SmConjAux_cx8_apply, map_sub, map_smul, hdRo7SmConjAux_perm_ones hg]
  rw [hgcx, hdRo7SmConjAux_cx8_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smOnes, Pi.one_apply, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hdRo7SmConjAux_perm_sum hg v]
  ring_nf
  have h6 : (6 : ZMod 3) = 0 := by decide
  rw [h6, mul_zero, add_zero]

private lemma hdRo7SmConjAux_smClass_smDot {m : ℕ} {p q : SMV m × SMV m} (h : SMClass p q) :
    smDot q.2 q.1 = smDot p.2 p.1 := by
  obtain ⟨π, s, hs, hπ⟩ := h
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  simp only [smDot]
  rw [show (∑ i, p.2 i * p.1 i) = ∑ i, q.2 (π i) * q.1 (π i) from
    Finset.sum_congr rfl (fun i _ => by
      rw [(hπ i).2, (hπ i).1]
      calc (s * q.2 (π i)) * (s * q.1 (π i))
          = s * s * (q.2 (π i) * q.1 (π i)) := by rw [mul_mul_mul_comm]
        _ = q.2 (π i) * q.1 (π i) := by rw [hs2, one_mul])]
  exact (Equiv.sum_comp π (fun j => q.2 j * q.1 j)).symm
private lemma hdRo7SmConjAux_refl_unique {m : ℕ} {r₁ r₂ : SMGL m} {u w : SMV m}
    (h₁ : SMRefl r₁ u (smDual w)) (h₂ : SMRefl r₂ u (smDual w)) : r₁ = r₂ := by
  ext v
  rw [h₁.2 v, h₂.2 v]
private lemma hdRo7SmConjAux_transport {m : ℕ} (τ : SMGL m)
    (hsymm : ∀ w v, smDot w (τ v) = smDot (τ w) v) (hinv : ∀ v, τ (τ v) = v)
    {r : SMGL m} {u w : SMV m} (h : SMRefl r u (smDual w)) :
    SMRefl (ggLinConj τ r) (τ u) (smDual (τ w)) := by
  have hτ : ∀ v, τ.symm v = τ v := fun v =>
    τ.injective (by rw [LinearEquiv.apply_symm_apply, hinv])
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_apply]
    have h2 : smDot (τ w) (τ u) = smDot w u := by rw [← hsymm w (τ u), hinv u]
    rw [h2, ← hdRo7SmAAux_smDual_apply]
    exact h.1
  · intro v
    rw [ggLinConj_apply, hτ, h.2 (τ v), map_sub, map_smul, hinv, hdRo7SmAAux_smDual_apply,
      hsymm w v, hdRo7SmAAux_smDual_apply]
private lemma hdRo7SmConjAux_conj_mem {m : ℕ} {H : Subgroup (SMGL m)} {a b : SMGL m}
    (ha : a ∈ H) (hb : b ∈ H) : ggLinConj b a ∈ H := by
  have heq : ggLinConj b a = b * a * b⁻¹ := by
    ext v
    simp [ggLinConj_apply]
  rw [heq]
  exact H.mul_mem (H.mul_mem hb ha) (H.inv_mem hb)
private lemma hdRo7SmConjAux_conj_permLin {m : ℕ} (π : Equiv.Perm (Fin m))
    {r : SMGL m} {u w : SMV m} (h : SMRefl r u (smDual w)) :
    SMRefl (ggLinConj (hdRo7SmAAux_permLin m π.symm) r)
      (fun i => u (π i)) (smDual (fun i => w (π i))) := by
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_apply]
    simp only [smDot]
    rw [Equiv.sum_comp π (fun j => w j * u j)]
    simpa [smDot, hdRo7SmAAux_smDual_apply] using h.1
  · intro v
    rw [ggLinConj_apply, h.2 ((hdRo7SmAAux_permLin m π.symm).symm v), map_sub, map_smul,
      LinearEquiv.apply_symm_apply]
    have hgu : hdRo7SmAAux_permLin m π.symm u = fun i => u (π i) := by
      ext i; simp [hdRo7SmAAux_permLin_apply]
    have hgs : (hdRo7SmAAux_permLin m π.symm).symm v = fun i => v (π.symm i) := by
      rw [LinearEquiv.symm_apply_eq]
      ext i
      simp [hdRo7SmAAux_permLin_apply]
    have hscalar : smDual w ((hdRo7SmAAux_permLin m π.symm).symm v) =
        smDual (fun i => w (π i)) v := by
      rw [hgs, hdRo7SmAAux_smDual_apply, hdRo7SmAAux_smDual_apply]
      simpa [smDot] using (Equiv.sum_comp π (fun j => w j * v (π.symm j))).symm
    rw [hgu, hscalar]
private lemma hdRo7SmConjAux_refl_smul {m : ℕ} {r : SMGL m} {u w : SMV m}
    (h : SMRefl r u (smDual w)) {s : ZMod 3} (hs : s = 1 ∨ s = -1) :
    SMRefl r (s • u) (smDual (s • w)) := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have hpair : smDot (s • w) (s • u) = smDot w u := by
    have h1 : smDot (s • w) (s • u) = (s * s) * smDot w u := by
      simp only [smDot, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [h1, hs2, one_mul]
  have hdotL : ∀ v, smDot (s • w) v = s * smDot w v := by
    intro v
    simp only [smDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hsm : ∀ c : ZMod 3, (s * c) • (s • u) = c • u := by
    intro c
    rw [smul_smul, show (s * c) * s = c by
      rw [mul_assoc, mul_comm c s, ← mul_assoc, hs2, one_mul]]
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_apply, hpair, ← hdRo7SmAAux_smDual_apply]
    exact h.1
  · intro v
    rw [h.2 v]
    simp only [hdRo7SmAAux_smDual_apply]
    rw [hdotL]
    congr 1
    exact (hsm (smDot w v)).symm
private theorem hdRo7SmConjAux_map_le {m : ℕ} (τ : SMGL m)
    (hperm : ∀ g, SMIsPerm g → ggLinConj τ g = g)
    (hsymm : ∀ w v, smDot w (τ v) = smDot (τ w) v) (hinv : ∀ v, τ (τ v) = v)
    {X Y : List (SMV m × SMV m)}
    (hclass : ∀ q ∈ X, ∃ q' ∈ Y, SMClass (τ q.1, τ q.2) q') :
    (smGroup m X).map (ggLinConj τ).toMonoidHom ≤ smGroup m Y := by
  rw [Subgroup.map_le_iff_le_comap, smGroup, Subgroup.closure_le]
  rintro y (hy | hy)
  · change (ggLinConj τ).toMonoidHom y ∈ smGroup m Y
    show ggLinConj τ y ∈ smGroup m Y
    rw [hperm y hy]
    exact Subgroup.subset_closure (Or.inl hy)
  · change ggLinConj τ y ∈ smGroup m Y
    obtain ⟨q, hqX, hqrefl⟩ := hy
    obtain ⟨q', hq'Y, π, s, hs, hπ⟩ := hclass q hqX
    have hpair : smDot q'.2 q'.1 = 2 := by
      have h1 : smDot q'.2 q'.1 = smDot (τ q.2) (τ q.1) :=
        hdRo7SmConjAux_smClass_smDot ⟨π, s, hs, hπ⟩
      have h2 : smDot (τ q.2) (τ q.1) = smDot q.2 q.1 := by
        rw [← hsymm q.2 (τ q.1), hinv q.1]
      have h3 : smDot q.2 q.1 = 2 := by
        have := hqrefl.1; rwa [hdRo7SmAAux_smDual_apply] at this
      rw [h1, h2, h3]
    have hdot : (smDual q'.2) q'.1 = 2 := by rwa [hdRo7SmAAux_smDual_apply]
    let r' : SMGL m := Module.reflection hdot
    have hr' : SMRefl r' q'.1 (smDual q'.2) :=
      ⟨hdot, fun v => Module.reflection_apply v hdot⟩
    have hr'mem : r' ∈ smGroup m Y :=
      Subgroup.subset_closure (Or.inr ⟨q', hq'Y, hr'⟩)
    have hg : hdRo7SmAAux_permLin m π.symm ∈ smGroup m Y :=
      Subgroup.subset_closure (Or.inl (hdRo7SmAAux_isPerm_permLin π.symm))
    have hτ1 : τ q.1 = s • (fun i => q'.1 (π i)) := by ext i; exact (hπ i).1
    have hτ2 : τ q.2 = s • (fun i => q'.2 (π i)) := by ext i; exact (hπ i).2
    have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> decide
    have htrans : SMRefl (ggLinConj τ y) (τ q.1) (smDual (τ q.2)) :=
      hdRo7SmConjAux_transport τ hsymm hinv hqrefl
    have htrans' : SMRefl (ggLinConj τ y) (fun i => q'.1 (π i))
        (smDual (fun i => q'.2 (π i))) := by
      have h := hdRo7SmConjAux_refl_smul htrans hs
      rw [hτ1, hτ2] at h
      simpa [smul_smul, hs2] using h
    have hpermconj : SMRefl (ggLinConj (hdRo7SmAAux_permLin m π.symm) r')
        (fun i => q'.1 (π i)) (smDual (fun i => q'.2 (π i))) :=
      hdRo7SmConjAux_conj_permLin π hr'
    have heq : ggLinConj τ y = ggLinConj (hdRo7SmAAux_permLin m π.symm) r' :=
      hdRo7SmConjAux_refl_unique htrans' hpermconj
    rw [heq]
    exact hdRo7SmConjAux_conj_mem hr'mem hg
private theorem hdRo7SmConjAux_smGroup_map_eq {m : ℕ} (τ : SMGL m)
    (hperm : ∀ g, SMIsPerm g → ggLinConj τ g = g)
    (hsymm : ∀ w v, smDot w (τ v) = smDot (τ w) v) (hinv : ∀ v, τ (τ v) = v)
    {X Y : List (SMV m × SMV m)}
    (hclass : ∀ q ∈ X, ∃ q' ∈ Y, SMClass (τ q.1, τ q.2) q')
    (hclass_rev : ∀ q' ∈ Y, ∃ q ∈ X, SMClass (τ q'.1, τ q'.2) q) :
    (smGroup m X).map (ggLinConj τ).toMonoidHom = smGroup m Y := by
  refine le_antisymm (hdRo7SmConjAux_map_le τ hperm hsymm hinv hclass) ?_
  have h2 : (smGroup m Y).map (ggLinConj τ).toMonoidHom ≤ smGroup m X :=
    hdRo7SmConjAux_map_le τ hperm hsymm hinv hclass_rev
  have hcomp : (ggLinConj τ).toMonoidHom.comp (ggLinConj τ).toMonoidHom =
      MonoidHom.id (SMGL m) := by
    have hτ : ∀ v, τ.symm v = τ v := fun v =>
      τ.injective (by rw [LinearEquiv.apply_symm_apply, hinv])
    apply MonoidHom.ext
    intro g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    apply LinearEquiv.ext
    intro v
    change ggLinConj τ (ggLinConj τ g) v = g v
    rw [ggLinConj_apply, ggLinConj_apply]
    simp only [hτ, hinv]
  calc smGroup m Y = ((smGroup m Y).map (ggLinConj τ).toMonoidHom).map
        (ggLinConj τ).toMonoidHom := by rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    _ ≤ (smGroup m X).map (ggLinConj τ).toMonoidHom := Subgroup.map_mono h2
private lemma hdRo7SmConjAux_transport_wl {m : ℕ} (τ : SMGL m) {X Y : List (SMV m × SMV m)}
    (hmap : (smGroup m X).map (ggLinConj τ).toMonoidHom = smGroup m Y)
    (h : ZS.LinWeyl 3 (smGroup m X)) : ZS.LinWeyl 3 (smGroup m Y) := by
  have h2 := linWeyl_map_ggLinConj τ (smGroup m X) h
  rwa [hmap] at h2

private lemma hdRo7SmConjAux_cls7_A7a_A7b :
    SMClass (hdRo7SmConjAux_cx7 sm7A7a.1, hdRo7SmConjAux_cx7 sm7A7a.2) sm7A7b := by
  refine ⟨Equiv.ofBijective ![6,0,1,2,3,4,5] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7A7a, sm7A7b]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_A7b_A7a :
    SMClass (hdRo7SmConjAux_cx7 sm7A7b.1, hdRo7SmConjAux_cx7 sm7A7b.2) sm7A7a := by
  refine ⟨Equiv.ofBijective ![1,2,3,4,5,6,0] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7A7b, sm7A7a]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_D7a_D7b :
    SMClass (hdRo7SmConjAux_cx7 sm7D7a.1, hdRo7SmConjAux_cx7 sm7D7a.2) sm7D7b := by
  refine ⟨Equiv.ofBijective ![5,6,0,1,2,3,4] (by decide), 2, Or.inr rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7D7a, sm7D7b]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_D7b_D7a :
    SMClass (hdRo7SmConjAux_cx7 sm7D7b.1, hdRo7SmConjAux_cx7 sm7D7b.2) sm7D7a := by
  refine ⟨Equiv.ofBijective ![2,3,4,5,6,0,1] (by decide), 2, Or.inr rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7D7b, sm7D7a]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_B7a_B7b :
    SMClass (hdRo7SmConjAux_cx7 sm7B7a.1, hdRo7SmConjAux_cx7 sm7B7a.2) sm7B7b := by
  refine ⟨Equiv.ofBijective ![6,0,1,2,3,4,5] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7B7a, sm7B7b]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_B7b_B7a :
    SMClass (hdRo7SmConjAux_cx7 sm7B7b.1, hdRo7SmConjAux_cx7 sm7B7b.2) sm7B7a := by
  refine ⟨Equiv.ofBijective ![1,2,3,4,5,6,0] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7B7b, sm7B7a]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_E7a_E7b :
    SMClass (hdRo7SmConjAux_cx7 sm7E7a.1, hdRo7SmConjAux_cx7 sm7E7a.2) sm7E7b := by
  refine ⟨Equiv.ofBijective ![3,4,5,6,0,1,2] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7E7a, sm7E7b]; decide +kernel)
private lemma hdRo7SmConjAux_cls7_E7b_E7a :
    SMClass (hdRo7SmConjAux_cx7 sm7E7b.1, hdRo7SmConjAux_cx7 sm7E7b.2) sm7E7a := by
  refine ⟨Equiv.ofBijective ![4,5,6,0,1,2,3] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx7_apply, smOnes, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm7E7b, sm7E7a]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_A8a_A8b :
    SMClass (hdRo7SmConjAux_cx8 sm8A8a.1, hdRo7SmConjAux_cx8 sm8A8a.2) sm8A8b := by
  refine ⟨Equiv.ofBijective ![0,1,2,3,4,5,6,7] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8A8a, sm8A8b]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_A8b_A8a :
    SMClass (hdRo7SmConjAux_cx8 sm8A8b.1, hdRo7SmConjAux_cx8 sm8A8b.2) sm8A8a := by
  refine ⟨Equiv.ofBijective ![0,1,2,3,4,5,6,7] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8A8b, sm8A8a]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_D8a_D8b :
    SMClass (hdRo7SmConjAux_cx8 sm8D8a.1, hdRo7SmConjAux_cx8 sm8D8a.2) sm8D8b := by
  refine ⟨Equiv.ofBijective ![0,1,2,3,4,5,6,7] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8D8a, sm8D8b]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_D8b_D8a :
    SMClass (hdRo7SmConjAux_cx8 sm8D8b.1, hdRo7SmConjAux_cx8 sm8D8b.2) sm8D8a := by
  refine ⟨Equiv.ofBijective ![0,1,2,3,4,5,6,7] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8D8b, sm8D8a]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_B8a_B8b :
    SMClass (hdRo7SmConjAux_cx8 sm8B8a.1, hdRo7SmConjAux_cx8 sm8B8a.2) sm8B8b := by
  refine ⟨Equiv.ofBijective ![7,0,1,2,3,4,5,6] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8B8a, sm8B8b]; decide +kernel)
private lemma hdRo7SmConjAux_cls8_B8b_B8a :
    SMClass (hdRo7SmConjAux_cx8 sm8B8b.1, hdRo7SmConjAux_cx8 sm8B8b.2) sm8B8a := by
  refine ⟨Equiv.ofBijective ![1,2,3,4,5,6,7,0] (by decide), 1, Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> (simp only [hdRo7SmConjAux_cx8_apply, smOnes, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, sm8B8b, sm8B8a]; decide +kernel)


private lemma hdRo7SmConjAux_map_D7a :
    (smGroup 7 [sm7D7b]).map (ggLinConj hdRo7SmConjAux_cx7).toMonoidHom = smGroup 7 [sm7D7a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx7 hdRo7SmConjAux_cx7_perm hdRo7SmConjAux_cx7_symm hdRo7SmConjAux_cx7_invol ?_ ?_
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm7D7a, by simp, hdRo7SmConjAux_cls7_D7b_D7a⟩
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm7D7b, by simp, hdRo7SmConjAux_cls7_D7a_D7b⟩
private lemma hdRo7SmConjAux_map_A7a :
    (smGroup 7 [sm7A7b]).map (ggLinConj hdRo7SmConjAux_cx7).toMonoidHom = smGroup 7 [sm7A7a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx7 hdRo7SmConjAux_cx7_perm hdRo7SmConjAux_cx7_symm hdRo7SmConjAux_cx7_invol ?_ ?_
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm7A7a, by simp, hdRo7SmConjAux_cls7_A7b_A7a⟩
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm7A7b, by simp, hdRo7SmConjAux_cls7_A7a_A7b⟩
private lemma hdRo7SmConjAux_map_B7D7a :
    (smGroup 7 [sm7B7b, sm7D7b]).map (ggLinConj hdRo7SmConjAux_cx7).toMonoidHom = smGroup 7 [sm7B7a, sm7D7a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx7 hdRo7SmConjAux_cx7_perm hdRo7SmConjAux_cx7_symm hdRo7SmConjAux_cx7_invol ?_ ?_
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm7B7a, by simp, hdRo7SmConjAux_cls7_B7b_B7a⟩
    · exact ⟨sm7D7a, by simp, hdRo7SmConjAux_cls7_D7b_D7a⟩
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm7B7b, by simp, hdRo7SmConjAux_cls7_B7a_B7b⟩
    · exact ⟨sm7D7b, by simp, hdRo7SmConjAux_cls7_D7a_D7b⟩
private lemma hdRo7SmConjAux_map_EA7a :
    (smGroup 7 [sm7E7b, sm7A7a]).map (ggLinConj hdRo7SmConjAux_cx7).toMonoidHom = smGroup 7 [sm7A7b, sm7E7a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx7 hdRo7SmConjAux_cx7_perm hdRo7SmConjAux_cx7_symm hdRo7SmConjAux_cx7_invol ?_ ?_
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm7E7a, by simp, hdRo7SmConjAux_cls7_E7b_E7a⟩
    · exact ⟨sm7A7b, by simp, hdRo7SmConjAux_cls7_A7a_A7b⟩
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm7A7a, by simp, hdRo7SmConjAux_cls7_A7b_A7a⟩
    · exact ⟨sm7E7b, by simp, hdRo7SmConjAux_cls7_E7a_E7b⟩
private lemma hdRo7SmConjAux_map_B8D8a :
    (smGroup 8 [sm8B8b, sm8D8b]).map (ggLinConj hdRo7SmConjAux_cx8).toMonoidHom = smGroup 8 [sm8B8a, sm8D8a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx8 hdRo7SmConjAux_cx8_perm hdRo7SmConjAux_cx8_symm hdRo7SmConjAux_cx8_invol ?_ ?_
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm8B8a, by simp, hdRo7SmConjAux_cls8_B8b_B8a⟩
    · exact ⟨sm8D8a, by simp, hdRo7SmConjAux_cls8_D8b_D8a⟩
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨sm8B8b, by simp, hdRo7SmConjAux_cls8_B8a_B8b⟩
    · exact ⟨sm8D8b, by simp, hdRo7SmConjAux_cls8_D8a_D8b⟩
private lemma hdRo7SmConjAux_map_A8b :
    (smGroup 8 [sm8A8a]).map (ggLinConj hdRo7SmConjAux_cx8).toMonoidHom = smGroup 8 [sm8A8b] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx8 hdRo7SmConjAux_cx8_perm hdRo7SmConjAux_cx8_symm hdRo7SmConjAux_cx8_invol ?_ ?_
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm8A8b, by simp, hdRo7SmConjAux_cls8_A8a_A8b⟩
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm8A8a, by simp, hdRo7SmConjAux_cls8_A8b_A8a⟩
private lemma hdRo7SmConjAux_map_D8a :
    (smGroup 8 [sm8D8b]).map (ggLinConj hdRo7SmConjAux_cx8).toMonoidHom = smGroup 8 [sm8D8a] := by
  refine hdRo7SmConjAux_smGroup_map_eq hdRo7SmConjAux_cx8 hdRo7SmConjAux_cx8_perm hdRo7SmConjAux_cx8_symm hdRo7SmConjAux_cx8_invol ?_ ?_
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm8D8a, by simp, hdRo7SmConjAux_cls8_D8b_D8a⟩
  · intro q hq; rw [List.mem_singleton] at hq; subst q
    exact ⟨sm8D8b, by simp, hdRo7SmConjAux_cls8_D8a_D8b⟩
theorem smConj_holds : SMConjLeaf := by
  intro hBD hA hE
  have h7nil : ZS.LinWeyl 3 (smGroup 7 []) := hA.1
  have h8nil : ZS.LinWeyl 3 (smGroup 8 []) := hA.2.1
  have hA7b : ZS.LinWeyl 3 (smGroup 7 [sm7A7b]) := hA.2.2.1
  have hA7cx : ZS.LinWeyl 3 (smGroup 7 [sm7A7b, sm7A7a, sm7cx]) := hA.2.2.2.1
  have hA8a : ZS.LinWeyl 3 (smGroup 8 [sm8A8a]) := hA.2.2.2.2
  have hD7b : ZS.LinWeyl 3 (smGroup 7 [sm7D7b]) := hBD.1
  have hB7D7b : ZS.LinWeyl 3 (smGroup 7 [sm7B7b, sm7D7b]) := hBD.2.1
  have hD8b : ZS.LinWeyl 3 (smGroup 8 [sm8D8b]) := hBD.2.2.1
  have hB8D8b : ZS.LinWeyl 3 (smGroup 8 [sm8B8b, sm8D8b]) := hBD.2.2.2
  have hEA : ZS.LinWeyl 3 (smGroup 7 [sm7E7b, sm7A7a]) := hE
  refine ⟨?_, ?_⟩
  · intro X hX hne
    simp only [smAllowed7, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h7nil
    · exact hB7D7b
    · exact hD7b
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx7 hdRo7SmConjAux_map_D7a hD7b
    · exact hA7b
    · exact hEA
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx7 hdRo7SmConjAux_map_A7a hA7b
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx7 hdRo7SmConjAux_map_EA7a hEA
    · exact absurd rfl hne
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx7 hdRo7SmConjAux_map_B7D7a hB7D7b
    · exact hA7cx
  · intro X hX hne
    simp only [smAllowed8, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h8nil
    · exact hB8D8b
    · exact hD8b
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx8 hdRo7SmConjAux_map_B8D8a hB8D8b
    · exact hA8a
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx8 hdRo7SmConjAux_map_A8b hA8a
    · exact absurd rfl hne
    · exact hdRo7SmConjAux_transport_wl hdRo7SmConjAux_cx8 hdRo7SmConjAux_map_D8a hD8b

end CFSG.StandardType.HdRo7SU.Small
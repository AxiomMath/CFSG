module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallRulesAxis
import CFSG.LocalAnalysis.StandardType.GGQTwoTransvectionFreeRules

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SmRulesAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7SmRulesAux_smDual_apply {m : ℕ} (w v : SMV m) :
    smDual w v = smDot w v := by
  simp only [smDual, smDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

private lemma hdRo7SmRulesAux_smDot_single_left {m : ℕ} (i : Fin m) (v : SMV m) :
    smDot (Pi.single i 1) v = v i := by
  rw [← hdRo7SmRulesAux_smDual_apply]
  have h : smDual (Pi.single i (1 : ZMod 3)) = LinearMap.proj i := by
    simp only [smDual]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_eq_of_ne hji, zero_smul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  rw [h, LinearMap.proj_apply]

private lemma hdRo7SmRulesAux_smDot_single_right {m : ℕ} (w : SMV m) (i : Fin m) :
    smDot w (Pi.single i 1) = w i := by
  simp only [smDot]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by rw [Pi.single_eq_of_ne hji, mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

private lemma hdRo7SmRulesAux_smDot_sub_left {m : ℕ} (a b v : SMV m) :
    smDot (a - b) v = smDot a v - smDot b v := by
  simp only [smDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hdRo7SmRulesAux_smDot_smul_left {m : ℕ} (c : ZMod 3) (a v : SMV m) :
    smDot (c • a) v = c * smDot a v := by
  simp only [smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma hdRo7SmRulesAux_smDot_sub_right {m : ℕ} (a b v : SMV m) :
    smDot a (b - v) = smDot a b - smDot a v := by
  simp only [smDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma hdRo7SmRulesAux_smDot_smul_right {m : ℕ} (c : ZMod 3) (a v : SMV m) :
    smDot a (c • v) = c * smDot a v := by
  simp only [smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma hdRo7SmRulesAux_smDot_neg_neg {m : ℕ} (w u : SMV m) :
    smDot (-w) (-u) = smDot w u := by
  simp only [smDot, Pi.neg_apply, neg_mul, mul_neg, neg_neg]

private lemma hdRo7SmRulesAux_smDual_neg {m : ℕ} (w : SMV m) :
    smDual (-w) = -smDual w := by
  apply LinearMap.ext; intro v
  rw [hdRo7SmRulesAux_smDual_apply, LinearMap.neg_apply, hdRo7SmRulesAux_smDual_apply]
  simp only [smDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private lemma hdRo7SmRulesAux_smDual_sub {m : ℕ} (a b : SMV m) :
    smDual (a - b) = smDual a - smDual b := by
  apply LinearMap.ext; intro v
  rw [hdRo7SmRulesAux_smDual_apply, LinearMap.sub_apply, hdRo7SmRulesAux_smDual_apply,
    hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDot_sub_left]

private lemma hdRo7SmRulesAux_smDual_smul {m : ℕ} (c : ZMod 3) (a : SMV m) :
    smDual (c • a) = c • smDual a := by
  apply LinearMap.ext; intro v
  rw [hdRo7SmRulesAux_smDual_apply, LinearMap.smul_apply, hdRo7SmRulesAux_smDual_apply,
    hdRo7SmRulesAux_smDot_smul_left, smul_eq_mul]

private lemma hdRo7SmRulesAux_smDual_injective {m : ℕ} :
    Function.Injective (smDual (m := m)) := by
  intro w w' h
  funext i
  have := congrArg (fun f : Module.Dual (ZMod 3) (SMV m) => f (Pi.single i 1)) h
  rw [hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDual_apply,
    hdRo7SmRulesAux_smDot_single_right, hdRo7SmRulesAux_smDot_single_right] at this
  exact this

private noncomputable def hdRo7SmRulesAux_permGL {m : ℕ} (π : Equiv.Perm (Fin m)) : SMGL m where
  toFun v := v ∘ π
  invFun v := v ∘ π.symm
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := by funext i; rfl
  map_smul' c v := by funext i; rfl

private lemma hdRo7SmRulesAux_permGL_apply {m : ℕ} (π : Equiv.Perm (Fin m)) (v : SMV m) (i : Fin m) :
    (hdRo7SmRulesAux_permGL π) v i = v (π i) := rfl

private lemma hdRo7SmRulesAux_smisPerm_permGL {m : ℕ} (π : Equiv.Perm (Fin m)) :
    SMIsPerm (hdRo7SmRulesAux_permGL π) :=
  ⟨π.symm, fun v i => by rw [hdRo7SmRulesAux_permGL_apply]; rfl⟩

private lemma hdRo7SmRulesAux_refl_involution {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) : r * r = 1 := by
  have h1 : r = Module.reflection hr.1 := LinearEquiv.ext fun v => by
    rw [hr.2 v, Module.reflection_apply]
  rw [h1]
  nth_rewrite 1 [← Module.reflection_symm hr.1]
  exact inv_mul_cancel _

private lemma hdRo7SmRulesAux_norm {m : ℕ} {H : Subgroup (SMGL m)} :
    ∀ p ∈ smRefSet H, smDot p.2 p.1 = 2 := by
  rintro ⟨u, w⟩ ⟨r, _hrH, hr⟩
  rw [← hdRo7SmRulesAux_smDual_apply]
  exact hr.1

private lemma hdRo7SmRulesAux_neg {m : ℕ} {H : Subgroup (SMGL m)} :
    ∀ p ∈ smRefSet H, ((-p.1, -p.2) : SMV m × SMV m) ∈ smRefSet H := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩
  refine ⟨r, hrH, ?_, ?_⟩
  · rw [hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDot_neg_neg,
      ← hdRo7SmRulesAux_smDual_apply]
    exact hr.1
  · intro v
    rw [hr.2 v, hdRo7SmRulesAux_smDual_neg, LinearMap.neg_apply]
    simp only [neg_smul, neg_neg, smul_neg]

private lemma hdRo7SmRulesAux_permGL_conj {m : ℕ} (π : Equiv.Perm (Fin m)) {r : SMGL m}
    {u w : SMV m} (hr : SMRefl r u (smDual w)) :
    SMRefl (hdRo7SmRulesAux_permGL π * r * (hdRo7SmRulesAux_permGL π)⁻¹)
      (fun i => u (π i)) (smDual (fun i => w (π i))) := by
  constructor
  · rw [hdRo7SmRulesAux_smDual_apply]
    change (∑ i, w (π i) * u (π i)) = 2
    rw [Equiv.sum_comp π (fun i => w i * u i)]
    change smDot w u = 2
    rw [← hdRo7SmRulesAux_smDual_apply w u]
    exact hr.1
  · intro v
    have hg : (hdRo7SmRulesAux_permGL π * r * (hdRo7SmRulesAux_permGL π)⁻¹) v =
        v - (smDual w (v ∘ π.symm)) • (fun i => u (π i)) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      change (hdRo7SmRulesAux_permGL π) (r ((hdRo7SmRulesAux_permGL π)⁻¹ v)) = _
      rw [hr.2 ((hdRo7SmRulesAux_permGL π)⁻¹ v), map_sub, map_smul,
        show (hdRo7SmRulesAux_permGL π) ((hdRo7SmRulesAux_permGL π)⁻¹ v) = v from by simp]
      rfl
    have hfun : smDual w (v ∘ π.symm) = smDual (fun i => w (π i)) v := by
      rw [hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDual_apply, smDot, smDot]
      exact Fintype.sum_equiv π.symm (fun i => w i * v (π.symm i)) (fun j => w (π j) * v j)
        (fun i => by simp)
    rw [hg, hfun]

private lemma hdRo7SmRulesAux_perm {m : ℕ} {H : Subgroup (SMGL m)}
    (hP : ∀ g, SMIsPerm g → g ∈ H) :
    ∀ p ∈ smRefSet H, ∀ π : Equiv.Perm (Fin m),
      ((fun i => p.1 (π i), fun i => p.2 (π i)) : SMV m × SMV m) ∈ smRefSet H := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ π
  have hgH : hdRo7SmRulesAux_permGL π ∈ H := hP _ (hdRo7SmRulesAux_smisPerm_permGL π)
  exact ⟨hdRo7SmRulesAux_permGL π * r * (hdRo7SmRulesAux_permGL π)⁻¹,
    H.mul_mem (H.mul_mem hgH hrH) (H.inv_mem hgH),
    hdRo7SmRulesAux_permGL_conj π hr⟩

private lemma hdRo7SmRulesAux_dot_conj {m : ℕ} (u w v z : SMV m)
    (hu : smDot w u = 2) (hv : smDot z v = 2) :
    smDot (z - smDot z u • w) (v - smDot w v • u) = 2 := by
  simp only [hdRo7SmRulesAux_smDot_sub_left, hdRo7SmRulesAux_smDot_sub_right,
    hdRo7SmRulesAux_smDot_smul_left, hdRo7SmRulesAux_smDot_smul_right]
  rw [hu, hv]
  ring

private lemma hdRo7SmRulesAux_conj {m : ℕ} {H : Subgroup (SMGL m)} :
    ∀ p ∈ smRefSet H, ∀ q ∈ smRefSet H,
      ((q.1 - smDot p.2 q.1 • p.1, q.2 - smDot q.2 p.1 • p.2) : SMV m × SMV m) ∈ smRefSet H := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ ⟨v, z⟩ ⟨t, htH, ht⟩
  refine ⟨r * t * r⁻¹, H.mul_mem (H.mul_mem hrH htH) (H.inv_mem hrH), ?_, ?_⟩
  · rw [hdRo7SmRulesAux_smDual_apply]
    exact hdRo7SmRulesAux_dot_conj u w v z
      (by rw [← hdRo7SmRulesAux_smDual_apply w u]; exact hr.1)
      (by rw [← hdRo7SmRulesAux_smDual_apply z v]; exact ht.1)
  · intro x
    have hinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hdRo7SmRulesAux_refl_involution hr)
    rw [hinv]
    rw [show (r * t * r) x =
        x - (smDual (z - smDot z u • w) x) • (v - smDot w v • u) by
      simp only [LinearEquiv.mul_apply, hr.2, ht.2, map_sub, map_smul, hr.1, ht.1,
        hdRo7SmRulesAux_smDual_sub, hdRo7SmRulesAux_smDual_smul,
        hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDot_sub_left,
        hdRo7SmRulesAux_smDot_smul_left, hdRo7SmRulesAux_smDot_sub_right,
        hdRo7SmRulesAux_smDot_smul_right, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      module]

private lemma hdRo7SmRulesAux_swap_mem {m : ℕ} {H : Subgroup (SMGL m)}
    (hP : ∀ g, SMIsPerm g → g ∈ H) {i j : Fin m} (hij : i ≠ j) :
    ((Pi.single i 1 - Pi.single j 1, Pi.single i 1 - Pi.single j 1) : SMV m × SMV m) ∈
      smRefSet H := by
  change ∃ r ∈ H, SMRefl r (Pi.single i 1 - Pi.single j 1)
    (smDual (Pi.single i 1 - Pi.single j 1))
  refine ⟨hdRo7SmRulesAux_permGL (Equiv.swap i j), hP _ (hdRo7SmRulesAux_smisPerm_permGL _),
    ?_, ?_⟩
  · rw [hdRo7SmRulesAux_smDual_apply, hdRo7SmRulesAux_smDot_sub_left,
      hdRo7SmRulesAux_smDot_single_left, hdRo7SmRulesAux_smDot_single_left]
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm]
    decide
  · intro v
    have hdot : smDot (Pi.single i 1 - Pi.single j 1) v = v i - v j := by
      rw [hdRo7SmRulesAux_smDot_sub_left, hdRo7SmRulesAux_smDot_single_left,
        hdRo7SmRulesAux_smDot_single_left]
    ext k
    rw [hdRo7SmRulesAux_permGL_apply, hdRo7SmRulesAux_smDual_apply, hdot]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left]
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        smul_eq_mul]
      ring
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right]
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
          Pi.single_eq_of_ne hij.symm, smul_eq_mul]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hki,
          Pi.single_eq_of_ne hkj, sub_zero, mul_zero, sub_zero, smul_eq_mul]

private lemma hdRo7SmRulesAux_smtClass_mem {m : ℕ} {H : Subgroup (SMGL m)}
    (hP : ∀ g, SMIsPerm g → g ∈ H) :
    ∀ p : SMV m × SMV m, SMTClass p → p ∈ smRefSet H := by
  rintro ⟨u, w⟩ ⟨i, j, s, hij, hs, hu, hw⟩
  have hu' : u = s • (Pi.single i 1 - Pi.single j 1) := hu
  have hw' : w = s • (Pi.single i 1 - Pi.single j 1) := hw
  have hbase : ∃ r ∈ H, SMRefl r (Pi.single i 1 - Pi.single j 1)
      (smDual (Pi.single i 1 - Pi.single j 1)) := hdRo7SmRulesAux_swap_mem hP hij
  show ∃ r ∈ H, SMRefl r u (smDual w)
  rcases hs with rfl | rfl
  · simpa [hu', hw'] using hbase
  · have hneg : ∃ r ∈ H, SMRefl r (-(Pi.single i 1 - Pi.single j 1))
        (smDual (-(Pi.single i 1 - Pi.single j 1))) :=
      hdRo7SmRulesAux_neg (H := H)
        (p := (Pi.single i 1 - Pi.single j 1, Pi.single i 1 - Pi.single j 1)) hbase
    simpa [hu', hw', neg_one_smul] using hneg

private lemma hdRo7SmRulesAux_zero {m : ℕ} {H : Subgroup (SMGL m)}
    (hT : QTwoLin.TransvectionFree H) :
    ∀ p ∈ smRefSet H, ∀ q ∈ smRefSet H, smDot p.2 q.1 = 0 ↔ smDot q.2 p.1 = 0 := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ ⟨v, z⟩ ⟨t, htH, ht⟩
  have h := QTwoLin.zero_pair_iff_of_transvectionFree (K := ZMod 3) hT hrH htH hr.1 ht.1
    (fun x => hr.2 x) (fun x => ht.2 x)
  simpa only [hdRo7SmRulesAux_smDual_apply] using h

private lemma hdRo7SmRulesAux_transvection_of_same_functional {m : ℕ} {r t : SMGL m}
    {u v w : SMV m} (hr : SMRefl r u (smDual w)) (ht : SMRefl t v (smDual w)) (huv : u ≠ v) :
    QTwoLin.IsTransvectionLin (r * t) := by
  refine ⟨u - v, smDual w, sub_ne_zero.mpr huv, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun f : Module.Dual (ZMod 3) (SMV m) => f u) h0
    rw [hr.1, LinearMap.zero_apply] at h1
    exact hdRo7SmRulesAux_two_ne_zero h1
  · rw [map_sub, hr.1, ht.1, sub_self]
  · intro x
    simp only [LinearEquiv.mul_apply, hr.2, ht.2, map_sub, map_smul, hr.1, ht.1,
      LinearMap.sub_apply, smul_eq_mul]
    module

private lemma hdRo7SmRulesAux_same_root {m : ℕ} {H : Subgroup (SMGL m)}
    (hT : QTwoLin.TransvectionFree H) :
    ∀ p ∈ smRefSet H, ∀ q ∈ smRefSet H, p.1 = q.1 → p.2 = q.2 := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ ⟨v, z⟩ ⟨t, htH, ht⟩ huv
  change u = v at huv
  have ht1 : smDual z u = 2 := by rw [huv]; exact ht.1
  have hφψ : smDual w = smDual z :=
    QTwoLin.eq_form_of_same_root_of_transvectionFree (K := ZMod 3) hT hrH htH hr.1 ht1
      (fun x => hr.2 x) (fun x => by rw [ht.2 x, huv])
  exact hdRo7SmRulesAux_smDual_injective hφψ

private lemma hdRo7SmRulesAux_same_functional {m : ℕ} {H : Subgroup (SMGL m)}
    (hT : QTwoLin.TransvectionFree H) :
    ∀ p ∈ smRefSet H, ∀ q ∈ smRefSet H, p.2 = q.2 → p.1 = q.1 := by
  rintro ⟨u, w⟩ ⟨r, hrH, hr⟩ ⟨v, z⟩ ⟨t, htH, ht⟩ hwz
  change w = z at hwz
  by_contra huv
  change u ≠ v at huv
  have ht' : SMRefl t v (smDual w) := by rw [hwz]; exact ht
  have htrans := hdRo7SmRulesAux_transvection_of_same_functional hr ht' huv
  exact hT (r * t) (H.mul_mem hrH htH) htrans

private theorem hdRo7SmRulesAux_rules {m : ℕ} (hN : SUNormalizerLeaf) (hm : m = 7 ∨ m = 8)
    {H : Subgroup (SMGL m)} (hP : ∀ g, SMIsPerm g → g ∈ H)
    (hT : QTwoLin.TransvectionFree H)
    (hS : ∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s → SMIsPerm (g * s * g⁻¹)) :
    SMRCl (smRefSet H) :=
  ⟨hdRo7SmRulesAux_norm, hdRo7SmRulesAux_perm hP, hdRo7SmRulesAux_neg,
   hdRo7SmRulesAux_conj, hdRo7SmRulesAux_smtClass_mem hP, hdRo7SmRulesAux_zero hT,
   hdRo7SmRulesAux_same_root hT, hdRo7SmRulesAux_same_functional hT,
   hdRo7SmAxis_axis hN hm hP hS⟩

theorem smRules_holds : SMRulesLeaf := by
  intro hN m hm H hP hT hS
  exact hdRo7SmRulesAux_rules hN hm hP hT hS

end CFSG.StandardType.HdRo7SU.Small

module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.Universal.Spin.Twisted.Generation
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict
public import CFSG.LocalAnalysis.StandardType.GGKGPosSULevi
public import Mathlib.Algebra.CharP.Algebra
public import CFSG.Sporadic.Th.Chain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityAlternating
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.StandardType.KGPosOm

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted QuadraticMap
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup mem_commSpace
  one_le_finrank_commSpace finrank_commSpace_reflection)
open scoped Matrix

section Fix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] [CharP F 2] in
theorem planeVec_ne_zero {w : Fin 2 → F} (hw0 : w ≠ 0) : planeVec 4 w ≠ 0 := fun h0 =>
  hw0 (planeVec_injective 4 (h0.trans (planeVec_zero 4).symm))

include hirr in
theorem eq_one_of_fix {g : spinGroup (quadMinus 4 F b c)}
    (hfix : ∀ i s, spinAction (quadMinus 4 F b c) g (minusVec 4 i s) = minusVec 4 i s)
    {w : Fin 2 → F} (hw0 : w ≠ 0)
    (hw : spinAction (quadMinus 4 F b c) g (planeVec 4 w) = planeVec 4 w) : g = 1 := by
  have hn0 : 0 < 4 - 1 := by decide
  apply RootCentOmega.spinAction_quadMinus_injective hirr
  rw [map_one]
  by_contra hne
  have h1 := one_le_finrank_commSpace hne
  have hwT : planeVec 4 w ∈ tailSpace (minusFamily F b c hn0) (4 - 1) :=
    RootCentOmega.mem_tailSpace_of_polar_minusVec hn0 fun k u =>
      polar_minusVec_planeVec 4 b c k u w
  have hle : commSpace (spinAction (quadMinus 4 F b c) g) ≤ F ∙ planeVec 4 w := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    have hxT : spinAction (quadMinus 4 F b c) g v - v ∈
        tailSpace (minusFamily F b c hn0) (4 - 1) := by
      refine RootCentOmega.mem_tailSpace_of_polar_minusVec hn0 fun k u => ?_
      have h := polar_spinAction (quadMinus 4 F b c) g (minusVec 4 k u) v
      rw [hfix] at h
      rw [polar_sub_right, h, sub_self]
    have hxw : polar (quadMinus 4 F b c) (planeVec 4 w)
        (spinAction (quadMinus 4 F b c) g v - v) = 0 := by
      have h := polar_spinAction (quadMinus 4 F b c) g (planeVec 4 w) v
      rw [hw] at h
      rw [polar_sub_right, h, sub_self]
    obtain ⟨a, ha⟩ := exists_eq_smul_of_mem_tailSpace_minusFamily CharTwo.two_eq_zero hirr hn0
      hwT (planeVec_ne_zero hw0) hxT hxw
    rw [ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  have hle1 := (Submodule.finrank_mono hle).trans (finrank_span_singleton (planeVec_ne_zero hw0)).le
  have hE : spinAction (quadMinus 4 F b c) g ∈ omegaGroup (quadMinus 4 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 4 F hirr) :=
    RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup hirr (by decide)
      (by rw [← range_spinAction_quadMinus (by decide) hirr]; exact ⟨g, rfl⟩)
  have heven := (mem_omegaGroup.mp hE).2
  rw [le_antisymm hle1 h1] at heven
  exact Nat.not_even_one heven

omit [Finite F] in
theorem exists_fix_planeVec {g : spinGroup (quadMinus 4 F b c)}
    (hP : ∀ p : Fin 2 → F, ∃ p', spinAction (quadMinus 4 F b c) g (planeVec 4 p) = planeVec 4 p')
    {N : ℕ} (hN : g ^ (2 ^ N) = 1) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ spinAction (quadMinus 4 F b c) g (planeVec 4 w) = planeVec 4 w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (Module.End F (Vm 4 F)) 2 :=
    charP_of_injective_algebraMap (algebraMap F (Module.End F (Vm 4 F))).injective 2
  set A : Module.End F (Vm 4 F) := (spinAction (quadMinus 4 F b c) g).toLinearMap with hAdef
  have hpow : ∀ n v, (A ^ n) v = spinAction (quadMinus 4 F b c) (g ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', map_mul, LinearEquiv.mul_apply]
      rfl
  have hA : A ^ (2 ^ N) = 1 := LinearMap.ext fun v => by rw [hpow, hN, map_one]; rfl
  have hD : (A - 1) ^ (2 ^ N) = 0 := by
    rw [sub_pow_char_pow_of_commute 2 N (Commute.one_right A), hA, one_pow, sub_self]
  have hstep : ∀ p : Fin 2 → F, ∃ p', (A - 1) (planeVec 4 p) = planeVec 4 p' := fun p => by
    obtain ⟨p', hp'⟩ := hP p
    refine ⟨p' - p, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, planeVec_sub]
    exact congrArg (· - planeVec 4 p) hp'
  have hiter : ∀ k, ∃ p : Fin 2 → F,
      ((A - 1) ^ k : Module.End F (Vm 4 F)) (planeVec 4 planeOne) = planeVec 4 p := by
    intro k
    induction k with
    | zero => exact ⟨planeOne, by rw [pow_zero, Module.End.one_apply]⟩
    | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨p', hp'⟩ := hstep p
      exact ⟨p', by rw [pow_succ', Module.End.mul_apply, hp, hp']⟩
  have hz : planeVec 4 (planeOne : Fin 2 → F) ≠ 0 := fun h => by
    have h1 := quadMinus_planeOne 4 b c (K := F)
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  have hex : ∃ k, ((A - 1) ^ k : Module.End F (Vm 4 F)) (planeVec 4 planeOne) = 0 :=
    ⟨2 ^ N, by rw [hD, LinearMap.zero_apply]⟩
  have hk₀ : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    rw [h0, pow_zero, Module.End.one_apply] at h
    exact hz h
  obtain ⟨w, hw⟩ := hiter (Nat.find hex - 1)
  refine ⟨w, fun h0 => ?_, ?_⟩
  · have h := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk₀) one_pos)
    rw [hw, h0, planeVec_zero] at h
    exact h rfl
  · have h := Nat.find_spec hex
    rw [show Nat.find hex = (Nat.find hex - 1) + 1 by omega, pow_succ', Module.End.mul_apply, hw,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h

end Fix

section EvenSub

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [Finite K] [CharP K 2] [FiniteDimensional K V]

open RootCentOmega

theorem evenSub_le_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) (W : Submodule K V) : evenSub Q W ≤ elementaryGroup Q := by
  rw [evenSub, Subgroup.closure_le]
  rintro g (⟨u, -, w, -, rfl⟩ | ⟨a, -, b, -, hQa, hQb, rfl⟩)
  · exact eichler_mem_elementaryGroup Q u w
  · exact reflect_mul_reflect_mem_elementaryGroup hQ h₁₂ hQa hQb

theorem mem_evenSub_of_fix (hQ : (polarBilin Q).Nondegenerate)
    (hE : elementaryGroup Q ≤ omegaGroup Q hQ)
    {m : ℕ} (hm : 2 ≤ m) {Pf : ℕ → HypPair Q}
    (hPf : ∀ i j, i < m → j < m → i ≠ j → (Pf i).Orth (Pf j))
    {P : ℕ → HypPair Q} {r : ℕ} (hr : 1 ≤ r)
    (hPW : ∀ k, (P k).e ∈ tailSpace Pf m ∧ (P k).f ∈ tailSpace Pf m)
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ tailSpace Pf m, (∀ k < r, x ∈ (P k).perp) → Q x = 0 → x = 0)
    (hA' : ∀ x ∈ tailSpace Pf m, (∀ k < r, x ∈ (P k).perp) → x ≠ 0 →
      ∀ y ∈ tailSpace Pf m, (∀ k < r, y ∈ (P k).perp) → polar Q x y = 0 →
        ∃ c : K, y = c • x)
    {g : V ≃ₗ[K] V} (hgE : g ∈ elementaryGroup Q)
    (hfix : ∀ i < m, g (Pf i).e = (Pf i).e ∧ g (Pf i).f = (Pf i).f) :
    g ∈ evenSub Q (tailSpace Pf m) := by
  set W := tailSpace Pf m with hWdef
  have hgO := elementaryGroup_le_orthogonalGroup Q hgE
  have hWnd : PolarNondegOn Q W := polarNondegOn_tailSpace hPf hQ le_rfl
  let P' : ℕ → HypPair (Q.restrict W) := fun k => restrictPair (P k) (hPW k).1 (hPW k).2
  have hP' : ∀ i j, i < r → j < r → i ≠ j → (P' i).Orth (P' j) := fun i j hi hj hij =>
    orth_restrictPair (hP i j hi hj hij) _ _ _ _
  have htail : ∀ x : W, x ∈ tailSpace P' r ↔ ∀ k < r, (x : V) ∈ (P k).perp := by
    intro x
    rw [mem_tailSpace]
    refine forall₂_congr fun k _ => ?_
    rw [HypPair.mem_perp, polar_restrict, polar_restrict]
    rfl
  have hAR : ∀ x ∈ tailSpace P' r, Q.restrict W x = 0 → x = 0 := fun x hx hQx =>
    Subtype.ext (hA x x.2 ((htail x).mp hx) hQx)
  have hA'R : ∀ x ∈ tailSpace P' r, x ≠ 0 → ∀ y ∈ tailSpace P' r,
      polar (Q.restrict W) x y = 0 → ∃ c : K, y = c • x := by
    intro x hx hx0 y hy hxy
    obtain ⟨c, hc⟩ := hA' x x.2 ((htail x).mp hx) (fun h => hx0 (Subtype.ext h)) y y.2
      ((htail y).mp hy) (by rwa [polar_restrict] at hxy)
    exact ⟨c, Subtype.ext hc⟩
  have hgW : ∀ x ∈ W, g x ∈ W := fun x hx => apply_mem_tailSpace hgO hfix hx
  have hgW' : ∀ x ∈ W, g.symm x ∈ W := fun x hx =>
    apply_mem_tailSpace (inv_mem hgO)
      (fun i hi => ⟨inv_apply_eq_of_apply_eq (hfix i hi).1,
        inv_apply_eq_of_apply_eq (hfix i hi).2⟩) hx
  set g' := CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv W g hgW hgW' with hg'
  have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    exact map_of_mem hgO x
  have hcl := orthogonalGroup_le_closure_of_two_eq_zero hP'
    (nondegenerate_polarBilin_restrict hWnd) CharTwo.two_eq_zero hAR hA'R hr hg'O
  obtain ⟨g₀, hg₀, hg₀x, hg₀z⟩ := exists_extend_of_mem_closure hcl
  have hfix₀ : ∀ i < m, (g₀⁻¹ * g) (Pf i).e = (Pf i).e ∧
      (g₀⁻¹ * g) (Pf i).f = (Pf i).f := by
    intro i hi
    have he : g₀ (Pf i).e = (Pf i).e := hg₀z _ fun x hx => polar_e_tailSpace hi hx
    have hf : g₀ (Pf i).f = (Pf i).f := hg₀z _ fun x hx => polar_f_tailSpace hi hx
    exact ⟨by rw [LinearEquiv.mul_apply, (hfix i hi).1, inv_apply_eq_of_apply_eq he],
      by rw [LinearEquiv.mul_apply, (hfix i hi).2, inv_apply_eq_of_apply_eq hf]⟩
  have hWfix : ∀ x ∈ W, (g₀⁻¹ * g) x = x := by
    intro x hx
    have hx' : g₀ x = g x :=
      (hg₀x ⟨x, hx⟩).trans
        (CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv W g hgW hgW' ⟨x, hx⟩)
    rw [LinearEquiv.mul_apply, ← hx']
    exact LinearEquiv.inv_apply_apply' g₀ x
  have heq : g₀⁻¹ * g = 1 :=
    CFSG.ClassicalGroups.Orthogonal.eq_one_of_fix hPf (g₀⁻¹ * g) hfix₀ hWfix
  have hg₀eq : g = g₀ := by
    calc g = g₀ * (g₀⁻¹ * g) := by group
      _ = g₀ * 1 := by rw [heq]
      _ = g₀ := by group
  rw [hg₀eq]
  have h₁₂ : (Pf 0).Orth (Pf 1) := hPf 0 1 (by omega) (by omega) (by omega)
  rcases mem_evenSub_or_of_mem_closure hg₀ with h | ⟨a, ha, hQa, h⟩
  · exact h
  · exfalso
    have hsub : evenSub Q W ≤ elementaryGroup Q := evenSub_le_elementaryGroup hQ h₁₂ W
    have hN : g₀ * reflect Q a ∈ elementaryGroup Q := hsub h
    have hg₀E : g₀ ∈ elementaryGroup Q := hg₀eq ▸ hgE
    have hrE : reflect Q a ∈ omegaGroup Q hQ := by
      have e : reflect Q a = g₀⁻¹ * (g₀ * reflect Q a) := by group
      rw [e]
      exact mul_mem (inv_mem (hE hg₀E)) (hE hN)
    let _ : Invertible (Q a) := invertibleOfNonzero hQa
    have hev := (mem_omegaGroup.mp hrE).2
    rw [reflect_eq_reflection, finrank_commSpace_reflection hQ a] at hev
    exact Nat.not_even_one hev

theorem evenSub_le_of_eichler (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} {Pf : ℕ → HypPair Q}
    (hPf : ∀ i j, i < m → j < m → i ≠ j → (Pf i).Orth (Pf j))
    (hW3 : 3 ≤ Module.finrank K (tailSpace Pf m))
    {H : Subgroup (V ≃ₗ[K] V)}
    (hH : ∀ u ∈ tailSpace Pf m, ∀ w ∈ tailSpace Pf m, eichler Q u w ∈ H) :
    evenSub Q (tailSpace Pf m) ≤ H := by
  set W := tailSpace Pf m with hWdef
  have hnorm : ∀ a ∈ W, Q a ≠ 0 → ∃ z ∈ W, Q z = 1 ∧ reflect Q z = reflect Q a ∧
      ∃ s : K, s ≠ 0 ∧ z = s • a := by
    intro a ha hQa
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q a)⁻¹
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero, inv_eq_zero] at hs
      exact hQa hs
    refine ⟨s • a, W.smul_mem s ha, ?_, reflect_smul_of_ne_zero hs0 a, s, hs0, rfl⟩
    rw [map_smul_eq_sq, pow_two, ← hs, inv_mul_cancel₀ hQa]
  have horth : ∀ a ∈ W, ∀ b ∈ W, Q a ≠ 0 → Q b ≠ 0 → polar Q a b = 0 →
      reflect Q a * reflect Q b ∈ H := by
    intro a ha b hb hQa hQb hab
    obtain ⟨z, hzW, hz1, hrz, s, -, rfl⟩ := hnorm a ha hQa
    obtain ⟨v, hvW, hv1, hrv, t, -, rfl⟩ := hnorm b hb hQb
    rw [← hrz, ← hrv,
      CFSG.ComponentClassification.UnbalancedCatalog.reflect_mul_reflect_eq_eichler hz1 hv1
      (by rw [polar_smul_left_eq, polar_smul_right_eq, hab, mul_zero, mul_zero])]
    exact hH _ (W.add_mem hzW hvW) _ hzW
  have hWnd : PolarNondegOn Q W := polarNondegOn_tailSpace hPf hQ le_rfl
  rw [RootCentOmega.evenSub, Subgroup.closure_le]
  rintro g (⟨u, hu, w, hw, rfl⟩ | ⟨a, ha, b, hb, hQa, hQb, rfl⟩)
  · exact hH u hu w hw
  · by_cases hab : polar Q a b = 0
    · exact horth a ha b hb hQa hQb hab
    obtain ⟨c, hcW, hQc, hac, hbc⟩ := RootCentOmega.exists_anisotropic_perp hWnd
      (RootCentOmega.exists_ne_zero_perp_of_three_le hW3) ha hb hab
    have e : reflect Q a * reflect Q b =
        reflect Q a * reflect Q c * (reflect Q c * reflect Q b) := by
      rw [mul_assoc, ← mul_assoc (reflect Q c), reflect_mul_self, one_mul]
    rw [e]
    exact mul_mem (horth a ha c hcW hQa hQc hac)
      (horth c hcW b hb hQc hQb (by rw [polar_comm]; exact hbc))

end EvenSub

section Short

theorem coe_eichler_restrict {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {W : Submodule K V} {u w : V} (hu : u ∈ W) (hw : w ∈ W) (x : W) :
    ((eichler (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ x : W) : V) = eichler Q u w x := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q.restrict W ⟨u, hu⟩ = 0 := h.1
    have hw' : polar (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ = 0 := by rw [polar_restrict]; exact h.2
    rw [eichler_apply hu' hw', eichler_apply h.1 h.2]
    simp [polar_restrict]
  · have h' : ¬(Q.restrict W ⟨u, hu⟩ = 0 ∧ polar (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ = 0) := by
      rwa [polar_restrict]
    rw [eichler_of_not h, eichler_of_not h']
    rfl

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] [CharP F 2] in
theorem mem_perp_minusPair_iff {n : ℕ} {i : Fin (n - 1)} {x : Vm n F} :
    x ∈ (minusPair F b c i : HypPair (quadMinus n F b c)).perp ↔
      ∀ u, polar (quadMinus n F b c) (minusVec n i u) x = 0 := by
  rw [HypPair.mem_perp]
  exact ⟨fun h u => by cases u; exacts [h.2, h.1], fun h => ⟨h true, h false⟩⟩

omit [Finite F] [CharP F 2] in
theorem minusVec_mem_perp_minusPair {n : ℕ} {i j : Fin (n - 1)} (hij : i ≠ j) (s : Bool) :
    minusVec n j s ∈ (minusPair F b c i : HypPair (quadMinus n F b c)).perp :=
  mem_perp_minusPair_iff.mpr fun u => by
    rw [polar_minusVec_minusVec, if_neg fun h => hij h.1]

omit [Finite F] [CharP F 2] in
theorem planeVec_mem_perp_minusPair {n : ℕ} (i : Fin (n - 1)) (p : Fin 2 → F) :
    planeVec n p ∈ (minusPair F b c i : HypPair (quadMinus n F b c)).perp :=
  mem_perp_minusPair_iff.mpr fun u => polar_minusVec_planeVec n b c i u p

omit [Finite F] [CharP F 2] in
theorem polar_minusVec_of_mem_perp {n : ℕ} (hn : 4 ≤ n) {x : Vm n F}
    (hx : x ∈ tailSpace (minusFamily F b c (by omega)) (n - 2))
    (hlast : x ∈ (minusPair F b c ⟨n - 2, by omega⟩).perp)
    (k : Fin (n - 1)) (u : Bool) : polar (quadMinus n F b c) (minusVec n k u) x = 0 := by
  by_cases hk : k.val = n - 2
  · have hke : k = ⟨n - 2, by omega⟩ := Fin.ext hk
    rw [hke]
    exact mem_perp_minusPair_iff.mp hlast u
  · have hlt : k.val < n - 2 := by omega
    have hmem := mem_tailSpace.mp hx k.val hlt
    rw [minusFamily_of_lt (by omega) (by omega)] at hmem
    cases u
    · exact hmem.2
    · exact hmem.1

omit [Finite F] [CharP F 2] in
include hirr in
theorem eichler_mem_map_rankOne_short {n : ℕ} (hn : 4 ≤ n) {u w : Vm n F}
    (hu : u ∈ tailSpace (minusFamily F b c (by omega)) (n - 2))
    (hw : w ∈ tailSpace (minusFamily F b c (by omega)) (n - 2)) :
    eichler (quadMinus n F b c) u w ∈
      (rankOne (minusRootGroup n hirr) ⟨n - 2, by omega⟩).map
        (spinAction (quadMinus n F b c)) := by
  set Pf : ℕ → HypPair (quadMinus n F b c) := minusFamily F b c (by omega) with hPfdef
  set W := tailSpace Pf (n - 2) with hWdef
  set k : Fin (n - 1) := ⟨n - 2, by omega⟩ with hkdef
  set H₂ := (rankOne (minusRootGroup n hirr) k).map (spinAction (quadMinus n F b c)) with hH₂
  have hn0 : 0 < n - 1 := by omega
  have hPf : ∀ i j, i < n - 2 → j < n - 2 → i ≠ j → (Pf i).Orth (Pf j) := fun i j hi hj hij =>
    minusFamily_orth hn0 i j (by omega) (by omega) hij
  have he : ∀ s, minusVec n k s ∈ W := fun s =>
    mem_tailSpace.mpr fun i hi => by
      have hlt : i < n - 1 := by omega
      have hik : (⟨i, hlt⟩ : Fin (n - 1)) ≠ k := by
        intro h
        have h1 : k.val = i := (congrArg Fin.val h).symm
        rw [hkdef] at h1
        simp only [Fin.val_mk] at h1
        omega
      have h' : ∀ u, polar (quadMinus n F b c) (minusVec n ⟨i, hlt⟩ u)
          (minusVec n k s) = 0 :=
        mem_perp_minusPair_iff.mp
          (minusVec_mem_perp_minusPair (i := ⟨i, hlt⟩) (j := k) hik s)
      rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 hlt]
      exact ⟨h' true, h' false⟩
  have hpW : ∀ p, planeVec n p ∈ W := fun p =>
    mem_tailSpace.mpr fun i hi => by
      have hlt : i < n - 1 := by omega
      have h' : ∀ u, polar (quadMinus n F b c) (minusVec n ⟨i, hlt⟩ u) (planeVec n p) = 0 :=
        mem_perp_minusPair_iff.mp (planeVec_mem_perp_minusPair (i := ⟨i, hlt⟩) p)
      rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 hlt]
      exact ⟨h' true, h' false⟩
  have hplane : ∀ v ∈ W, (∀ s, polar (quadMinus n F b c) v (minusVec n k s) = 0) →
      v = planeVec n (fun t => v (.inr (.inr t))) := by
    intro v hv hvk
    refine eq_planeVec_of_polar_minusVec n b c fun j r => ?_
    rw [polar_comm]
    exact polar_minusVec_of_mem_perp hn hv (mem_perp_minusPair_iff.mpr fun u => by
      rw [polar_comm]; exact hvk u) j r
  let FW : HypFrame ((quadMinus n F b c).restrict W) 1 :=
    { vec := fun _ s => ⟨minusVec n k s, he s⟩
      map_vec := fun _ s => quadMinus_minusVec n b c k s
      polar_vec_of_ne := fun i j hij => absurd (Subsingleton.elim i j) hij
      polar_vec_not := fun _ s => by
        rw [polar_restrict]
        change polar (quadMinus n F b c) (minusVec n k s) (minusVec n k (!s)) = 1
        rw [polar_minusVec_minusVec, if_pos ⟨rfl, by rw [Bool.not_not]⟩]
      exists_aux := fun _ _ => ⟨⟨planeVec n planeOne, hpW _⟩, by
          change IsUnit ((quadMinus n F b c) (planeVec n planeOne))
          rw [quadMinus_planeOne]
          exact isUnit_one,
        fun s => ⟨by rw [polar_restrict]; exact polar_minusVec_planeVec n b c k s planeOne,
          by rw [polar_restrict]; exact polar_minusVec_planeVec n b c k s planeOne⟩⟩ }
  let HW : Subgroup (W ≃ₗ[F] W) :=
    { carrier := {h' | ∃ h ∈ H₂, (∀ x : W, h x = h' x) ∧
        ∀ z, (∀ x ∈ W, polar (quadMinus n F b c) z x = 0) → h z = z}
      one_mem' := ⟨1, one_mem _, fun x => rfl, fun z _ => rfl⟩
      mul_mem' := by
        rintro a a' ⟨h, hh, hx, hz⟩ ⟨h', hh', hx', hz'⟩
        refine ⟨h * h', mul_mem hh hh', fun x => ?_, fun z hz0 => ?_⟩
        · rw [LinearEquiv.mul_apply, hx', hx]
          rfl
        · rw [LinearEquiv.mul_apply, hz' z hz0, hz z hz0]
      inv_mem' := by
        rintro a ⟨h, hh, hx, hz⟩
        refine ⟨h⁻¹, inv_mem hh, fun x => ?_, fun z hz0 => ?_⟩
        · apply h.injective
          rw [LinearEquiv.apply_inv_apply', hx, LinearEquiv.apply_inv_apply']
        · apply h.injective
          rw [LinearEquiv.apply_inv_apply', hz z hz0] }
  have hperp : ∀ (i : Fin 1) (s : Bool) (v : W),
      (∀ k r, polar ((quadMinus n F b c).restrict W) v (FW.vec k r) = 0) →
        eichler ((quadMinus n F b c).restrict W) (FW.vec i s) v ∈ HW := by
    intro i s v hv
    have hv2 : ∀ s, polar (quadMinus n F b c) v (minusVec n k s) = 0 := fun s => by
      have h := hv 0 s
      rwa [polar_restrict] at h
    have hvp := hplane v v.2 hv2
    refine ⟨spinAction (quadMinus n F b c) (twShortRoot n hirr k s
      (.ofAdd fun t => (v : Vm n F) (.inr (.inr t)))), ?_, fun x => ?_, fun z hz => ?_⟩
    · refine Subgroup.mem_map_of_mem _ ?_
      rw [rankOne_minusRootGroup_of_not_lt n hirr (by rw [hkdef, Fin.val_mk]; omega)]
      cases s
      · exact Subgroup.mem_sup_right ⟨_, by rw [twShortRoot_false]⟩
      · exact Subgroup.mem_sup_left ⟨_, by rw [twShortRoot_true]⟩
    · rw [spinAction_twShortRoot_eq_eichler, ← hvp]
      exact (coe_eichler_restrict (he s) v.2 x).symm
    · rw [spinAction_twShortRoot_eq_eichler, ← hvp]
      exact eichler_apply_of_polar_eq_zero (hz _ (he s)) (hz _ v.2)
  have hrest : ∀ v : W, (∀ k r, polar ((quadMinus n F b c).restrict W) v (FW.vec k r) = 0) →
      (quadMinus n F b c).restrict W v = 0 → v = 0 := by
    intro v hv hQv
    have hv2 : ∀ s, polar (quadMinus n F b c) v (minusVec n k s) = 0 := fun s => by
      have h := hv 0 s
      rwa [polar_restrict] at h
    have hvp := hplane v v.2 hv2
    have hQv' : (quadMinus n F b c) v = 0 := hQv
    rw [hvp, quadMinus_planeVec'] at hQv'
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hp => h0 (Subtype.ext ?_)) hQv'
    rw [hvp, hp, planeVec_zero]
    rfl
  have hHW : elementaryGroup ((quadMinus n F b c).restrict W) ≤ HW :=
    FW.elementaryGroup_le (H := HW) (fun {i j} hij => absurd (Subsingleton.elim i j) hij) hperp
      hrest
  obtain ⟨hV, hhV, hhVx, hhVz⟩ :=
    hHW (eichler_mem_elementaryGroup ((quadMinus n F b c).restrict W) ⟨u, hu⟩ ⟨w, hw⟩)
  have hfixE : ∀ i < n - 2, (hV⁻¹ * eichler (quadMinus n F b c) u w) (Pf i).e = (Pf i).e ∧
      (hV⁻¹ * eichler (quadMinus n F b c) u w) (Pf i).f = (Pf i).f := by
    intro i hi
    have he1 : hV (Pf i).e = (Pf i).e := hhVz _ fun x hx => polar_e_tailSpace hi hx
    have hf1 : hV (Pf i).f = (Pf i).f := hhVz _ fun x hx => polar_f_tailSpace hi hx
    have he2 : eichler (quadMinus n F b c) u w (Pf i).e = (Pf i).e :=
      eichler_apply_of_polar_eq_zero (polar_e_tailSpace hi hu) (polar_e_tailSpace hi hw)
    have hf2 : eichler (quadMinus n F b c) u w (Pf i).f = (Pf i).f :=
      eichler_apply_of_polar_eq_zero (polar_f_tailSpace hi hu) (polar_f_tailSpace hi hw)
    exact ⟨by rw [LinearEquiv.mul_apply, he2, RootCentOmega.inv_apply_eq_of_apply_eq he1],
      by rw [LinearEquiv.mul_apply, hf2, RootCentOmega.inv_apply_eq_of_apply_eq hf1]⟩
  have hWeq : ∀ x ∈ W, (hV⁻¹ * eichler (quadMinus n F b c) u w) x = x := by
    intro x hx
    have hx1 : hV x = eichler (quadMinus n F b c) u w x :=
      (hhVx ⟨x, hx⟩).trans (coe_eichler_restrict hu hw ⟨x, hx⟩)
    rw [LinearEquiv.mul_apply, ← hx1]
    exact LinearEquiv.inv_apply_apply' hV x
  have heq : hV⁻¹ * eichler (quadMinus n F b c) u w = 1 :=
    CFSG.ClassicalGroups.Orthogonal.eq_one_of_fix hPf
      (hV⁻¹ * eichler (quadMinus n F b c) u w) hfixE hWeq
  have heq' : eichler (quadMinus n F b c) u w = hV := by
    calc eichler (quadMinus n F b c) u w = hV * (hV⁻¹ * eichler (quadMinus n F b c) u w) := by group
      _ = hV * 1 := by rw [heq]
      _ = hV := by group
  rw [heq']
  exact hhV

include hirr in
theorem mem_rankOne_short_of_fix_lt {n : ℕ} (hn : 4 ≤ n) {g : spinGroup (quadMinus n F b c)}
    (hfix : ∀ i : Fin (n - 1), i.val + 1 < n - 1 → ∀ s,
      spinAction (quadMinus n F b c) g (minusVec n i s) = minusVec n i s) :
    g ∈ rankOne (minusRootGroup n hirr) ⟨n - 2, by omega⟩ := by
  set Pf : ℕ → HypPair (quadMinus n F b c) := minusFamily F b c (by omega) with hPfdef
  set W := tailSpace Pf (n - 2) with hWdef
  set k : Fin (n - 1) := ⟨n - 2, by omega⟩ with hkdef
  have hn0 : 0 < n - 1 := by omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n F hirr
  have hPf : ∀ i j, i < n - 2 → j < n - 2 → i ≠ j → (Pf i).Orth (Pf j) := fun i j hi hj hij =>
    minusFamily_orth hn0 i j (by omega) (by omega) hij
  have hgE : spinAction (quadMinus n F b c) g ∈ elementaryGroup (quadMinus n F b c) := by
    rw [← range_spinAction_quadMinus hn hirr]
    exact ⟨g, rfl⟩
  have he : ∀ s, minusVec n k s ∈ W := fun s =>
    mem_tailSpace.mpr fun i hi => by
      have hlt : i < n - 1 := by omega
      have hik : (⟨i, hlt⟩ : Fin (n - 1)) ≠ k := by
        intro h
        have h1 : k.val = i := (congrArg Fin.val h).symm
        rw [hkdef] at h1
        simp only [Fin.val_mk] at h1
        omega
      have h' : ∀ u, polar (quadMinus n F b c) (minusVec n ⟨i, hlt⟩ u)
          (minusVec n k s) = 0 :=
        mem_perp_minusPair_iff.mp
          (minusVec_mem_perp_minusPair (i := ⟨i, hlt⟩) (j := k) hik s)
      rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 hlt]
      exact ⟨h' true, h' false⟩
  have hpW : planeVec n (planeOne : Fin 2 → F) ∈ W :=
    mem_tailSpace.mpr fun i hi => by
      have hlt : i < n - 1 := by omega
      have h' : ∀ u, polar (quadMinus n F b c) (minusVec n ⟨i, hlt⟩ u)
          (planeVec n (planeOne : Fin 2 → F)) = 0 :=
        mem_perp_minusPair_iff.mp (planeVec_mem_perp_minusPair (i := ⟨i, hlt⟩) planeOne)
      rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 hlt]
      exact ⟨h' true, h' false⟩
  have hz0 : planeVec n (planeOne : Fin 2 → F) ≠ 0 := fun h => by
    have h1 := quadMinus_planeOne n b c (K := F)
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  have hW3 : 3 ≤ Module.finrank F W :=
    RootCentOmega.three_le_finrank_of_hypPair (minusPair F b c k) (he true) (he false) hpW
      (planeVec_mem_perp_minusPair k planeOne) hz0
  have htail : ∀ x ∈ W, x ∈ (minusPair F b c k).perp → x ∈ tailSpace Pf (n - 1) := by
    intro x hx hlast
    rw [mem_tailSpace]
    intro i hi
    rcases lt_or_eq_of_le (show i ≤ n - 2 by omega) with hlt | heq
    · exact mem_tailSpace.mp hx i hlt
    · have hik : (⟨i, by omega⟩ : Fin (n - 1)) = k := by
        rw [hkdef, Fin.ext_iff]
        exact heq
      have h := mem_perp_minusPair_iff.mp hlast
      rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 hi, hik]
      exact ⟨h true, h false⟩
  have hfixPf : ∀ i < n - 2, (spinAction (quadMinus n F b c) g) (Pf i).e = (Pf i).e ∧
      (spinAction (quadMinus n F b c) g) (Pf i).f = (Pf i).f := by
    intro i hi
    have hi' : i + 1 < n - 1 := by omega
    have h1 := hfix ⟨i, by omega⟩ hi' true
    have h2 := hfix ⟨i, by omega⟩ hi' false
    rw [hPfdef, minusFamily_of_lt (K := F) (b := b) (c := c) hn0 (by omega)]
    exact ⟨h1, h2⟩
  have hmem := mem_evenSub_of_fix hQ (RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup hirr hn)
    (m := n - 2) (by omega) (Pf := Pf) hPf (P := fun _ => minusPair F b c k) (r := 1) le_rfl
    (fun _ => ⟨he true, he false⟩)
    (fun i j hi hj hij => absurd (by omega) hij)
    (fun x hx hlast hQx => eq_zero_of_mem_tailSpace_minusFamily hirr hn0
      (htail x hx (hlast 0 one_pos)) hQx)
    (fun x hx hlast hx0 y hy hlast' hxy =>
      exists_eq_smul_of_mem_tailSpace_minusFamily CharTwo.two_eq_zero hirr hn0
        (htail x hx (hlast 0 one_pos)) hx0 (htail y hy (hlast' 0 one_pos)) hxy)
    hgE hfixPf
  obtain ⟨l, hl, hlg⟩ := evenSub_le_of_eichler hQ hPf hW3
    (fun u hu w hw => eichler_mem_map_rankOne_short hirr hn hu hw) hmem
  rw [← RootCentOmega.spinAction_quadMinus_injective hirr hlg]
  exact hl

include hirr in
theorem mem_rankOne_short_of_fix {g : spinGroup (quadMinus 4 F b c)}
    (hfix : ∀ i : Fin (4 - 1), i.val < 2 → ∀ s,
      spinAction (quadMinus 4 F b c) g (minusVec 4 i s) = minusVec 4 i s) :
    g ∈ rankOne (minusRootGroup 4 hirr) ⟨2, by decide⟩ := by
  simpa using mem_rankOne_short_of_fix_lt hirr (n := 4) (by decide)
    (fun i hi s => hfix i (by omega) s)

end Short

section Long

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] def pairVec (i j : Fin (4 - 1)) (s : Bool) (v : Fin 2 → F) : Vm 4 F :=
  v 0 • minusVec 4 i s + v 1 • minusVec 4 j s

omit [Finite F] [CharP F 2] in
theorem polar_pairVec_minusVec {i j : Fin (4 - 1)} (hij : i ≠ j) (s : Bool) (v : Fin 2 → F) :
    polar (quadMinus 4 F b c) (pairVec i j s v) (minusVec 4 i (!s)) = v 0 ∧
      polar (quadMinus 4 F b c) (pairVec i j s v) (minusVec 4 j (!s)) = v 1 := by
  simp only [pairVec, polar_add_left, polar_smul_left, polar_minusVec_minusVec, Bool.not_not,
    smul_eq_mul, and_true, if_neg hij, if_neg hij.symm, mul_zero, mul_one, if_true,
    add_zero, zero_add]

include hirr in
theorem mem_rankOne_long_of_block {k : Fin (4 - 1)} (hk : k.val + 1 < 4 - 1)
    {g : spinGroup (quadMinus 4 F b c)} (A : Matrix (Fin 2) (Fin 2) F)
    (hA : ∀ v, spinAction (quadMinus 4 F b c) g (pairVec k ⟨k.val + 1, hk⟩ true v) =
      pairVec k ⟨k.val + 1, hk⟩ true (A *ᵥ v))
    (hf : ∀ v, ∃ v', spinAction (quadMinus 4 F b c) g (pairVec k ⟨k.val + 1, hk⟩ false v) =
      pairVec k ⟨k.val + 1, hk⟩ false v')
    (hm : ∀ m : Fin (4 - 1), m ≠ k → m ≠ ⟨k.val + 1, hk⟩ → ∀ u,
      spinAction (quadMinus 4 F b c) g (minusVec 4 m u) = minusVec 4 m u)
    (hP : ∀ p : Fin 2 → F, ∃ p', spinAction (quadMinus 4 F b c) g (planeVec 4 p) = planeVec 4 p')
    {N : ℕ} (hN : g ^ (2 ^ N) = 1) :
    g ∈ rankOne (minusRootGroup 4 hirr) k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set j : Fin (4 - 1) := ⟨k.val + 1, hk⟩ with hj
  have hkj : k ≠ j := succ_ne_of_lt 4 hk
  let x : F → spinGroup (quadMinus 4 F b c) := fun a =>
    (minusFrame 4 b c).longRoot hkj true false (.ofAdd a)
  let y : F → spinGroup (quadMinus 4 F b c) := fun a =>
    (minusFrame 4 b c).longRoot hkj.symm true false (.ofAdd a)
  have hxL : ∀ a, x a ∈ rankOne (minusRootGroup 4 hirr) k := fun a =>
    Subgroup.mem_sup_left (by rw [minusRootGroup_single_of_lt 4 hirr hk]; exact ⟨_, rfl⟩)
  have hyL : ∀ a, y a ∈ rankOne (minusRootGroup 4 hirr) k := fun a =>
    Subgroup.mem_sup_right (by rw [minusRootGroup_neg_single_of_lt 4 hirr hk]; exact ⟨_, rfl⟩)
  have hxe : ∀ a v, spinAction (quadMinus 4 F b c) (x a) (pairVec k j true v) =
      pairVec k j true (!![1, a; 0, 1] *ᵥ v) := by
    intro a v
    have h1 : spinAction (quadMinus 4 F b c) (x a) (minusVec 4 k true) = minusVec 4 k true :=
      (minusFrame 4 b c).spinAction_longRoot_vec_left hkj true false a
    have h2 : spinAction (quadMinus 4 F b c) (x a) (minusVec 4 j true) =
        minusVec 4 j true + a • minusVec 4 k true :=
      (minusFrame 4 b c).spinAction_longRoot_vec_not_right hkj true false a
    simp only [pairVec, map_add, map_smul, h1, h2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    module
  have hye : ∀ a v, spinAction (quadMinus 4 F b c) (y a) (pairVec k j true v) =
      pairVec k j true (!![1, 0; a, 1] *ᵥ v) := by
    intro a v
    have h1 : spinAction (quadMinus 4 F b c) (y a) (minusVec 4 j true) = minusVec 4 j true :=
      (minusFrame 4 b c).spinAction_longRoot_vec_left hkj.symm true false a
    have h2 : spinAction (quadMinus 4 F b c) (y a) (minusVec 4 k true) =
        minusVec 4 k true + a • minusVec 4 j true :=
      (minusFrame 4 b c).spinAction_longRoot_vec_not_right hkj.symm true false a
    simp only [pairVec, map_add, map_smul, h1, h2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    module
  have hxf : ∀ a v, spinAction (quadMinus 4 F b c) (x a) (pairVec k j false v) =
      pairVec k j false (!![1, 0; -a, 1] *ᵥ v) := by
    intro a v
    have h1 : spinAction (quadMinus 4 F b c) (x a) (minusVec 4 k false) =
        minusVec 4 k false - a • minusVec 4 j false :=
      (minusFrame 4 b c).spinAction_longRoot_vec_not_left hkj true false a
    have h2 : spinAction (quadMinus 4 F b c) (x a) (minusVec 4 j false) = minusVec 4 j false :=
      (minusFrame 4 b c).spinAction_longRoot_vec_right hkj true false a
    simp only [pairVec, map_add, map_smul, h1, h2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    module
  have hyf : ∀ a v, spinAction (quadMinus 4 F b c) (y a) (pairVec k j false v) =
      pairVec k j false (!![1, -a; 0, 1] *ᵥ v) := by
    intro a v
    have h1 : spinAction (quadMinus 4 F b c) (y a) (minusVec 4 j false) =
        minusVec 4 j false - a • minusVec 4 k false :=
      (minusFrame 4 b c).spinAction_longRoot_vec_not_left hkj.symm true false a
    have h2 : spinAction (quadMinus 4 F b c) (y a) (minusVec 4 k false) = minusVec 4 k false :=
      (minusFrame 4 b c).spinAction_longRoot_vec_right hkj.symm true false a
    simp only [pairVec, map_add, map_smul, h1, h2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    module
  have hxm : ∀ a (m : Fin (4 - 1)), m ≠ k → m ≠ j → ∀ u,
      spinAction (quadMinus 4 F b c) (x a) (minusVec 4 m u) = minusVec 4 m u := fun a m hmk hmj u =>
    (minusFrame 4 b c).spinAction_longRoot_vec_of_ne hkj true false a hmk hmj u
  have hym : ∀ a (m : Fin (4 - 1)), m ≠ k → m ≠ j → ∀ u,
      spinAction (quadMinus 4 F b c) (y a) (minusVec 4 m u) = minusVec 4 m u := fun a m hmk hmj u =>
    (minusFrame 4 b c).spinAction_longRoot_vec_of_ne hkj.symm true false a hmj hmk u
  have hxp : ∀ a p, spinAction (quadMinus 4 F b c) (x a) (planeVec 4 p) = planeVec 4 p :=
    fun a p => spinAction_longRoot_planeVec 4 hkj true false a p
  have hyp : ∀ a p, spinAction (quadMinus 4 F b c) (y a) (planeVec 4 p) = planeVec 4 p :=
    fun a p => spinAction_longRoot_planeVec 4 hkj.symm true false a p
  have hxinv : ∀ a, (x a)⁻¹ = x (-a) := fun a => by
    rw [← map_inv]
    rfl
  have hyinv : ∀ a, (y a)⁻¹ = y (-a) := fun a => by
    rw [← map_inv]
    rfl
  have hAn : ∀ n v, spinAction (quadMinus 4 F b c) (g ^ n) (pairVec k j true v) =
      pairVec k j true ((A ^ n) *ᵥ v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hA, ih, Matrix.mulVec_mulVec, ← pow_succ]
  have hinj : ∀ v v' : Fin 2 → F, pairVec k j true v = pairVec k j true v' → v = v' := by
    intro v v' h
    have h0 := (polar_pairVec_minusVec (b := b) (c := c) hkj true v).1
    have h1 := (polar_pairVec_minusVec (b := b) (c := c) hkj true v).2
    rw [h] at h0 h1
    funext t
    fin_cases t
    · exact h0.symm.trans (polar_pairVec_minusVec hkj true v').1
    · exact h1.symm.trans (polar_pairVec_minusVec hkj true v').2
  have hApow : A ^ (2 ^ N) = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    apply hinj
    rw [← hAn, hN, map_one]
    rfl
  have hdet : A.det = 1 := by
    have hd : A.det ^ (2 ^ N) = 1 := by rw [← Matrix.det_pow, hApow, Matrix.det_one]
    have h2 := sub_pow_char_pow A.det 1 (p := 2) (n := N)
    rw [hd, one_pow, sub_self] at h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)
  obtain ⟨e₁, e₂, e₃, e₄, -, hAd⟩ := KGPosSU.exists_sl2_decomp A hdet
  set l := y e₁ * x e₂ * y e₃ * x e₄ with hldef
  have hl : l ∈ rankOne (minusRootGroup 4 hirr) k :=
    mul_mem (mul_mem (mul_mem (hyL _) (hxL _)) (hyL _)) (hxL _)
  have hle : ∀ v, spinAction (quadMinus 4 F b c) l (pairVec k j true v) =
      pairVec k j true (A *ᵥ v) := by
    intro v
    simp only [hldef, map_mul, LinearEquiv.mul_apply, hxe, hye, Matrix.mulVec_mulVec, hAd,
      mul_assoc]
  have hlinv : l⁻¹ = x (-e₄) * y (-e₃) * x (-e₂) * y (-e₁) := by
    simp only [hldef, mul_inv_rev, hxinv, hyinv, mul_assoc]
  set h := l⁻¹ * g with hhdef
  have hhe : ∀ v, spinAction (quadMinus 4 F b c) h (pairVec k j true v) = pairVec k j true v := by
    intro v
    rw [hhdef, map_mul, LinearEquiv.mul_apply, hA, ← hle, map_inv, LinearEquiv.inv_apply_apply']
  have hhm : ∀ (m : Fin (4 - 1)), m ≠ k → m ≠ j → ∀ u,
      spinAction (quadMinus 4 F b c) h (minusVec 4 m u) = minusVec 4 m u := by
    intro m hmk hmj u
    rw [hhdef, hlinv]
    simp only [map_mul, LinearEquiv.mul_apply, hm m hmk hmj u, hxm _ m hmk hmj u,
      hym _ m hmk hmj u]
  have hPres : ∀ v, ∃ v', spinAction (quadMinus 4 F b c) h (pairVec k j false v) =
      pairVec k j false v' := by
    intro v
    obtain ⟨v', hv'⟩ := hf v
    rw [hhdef, hlinv]
    simp only [map_mul, LinearEquiv.mul_apply, hv', hxf, hyf]
    exact ⟨_, rfl⟩
  have hhf : ∀ (i : Fin (4 - 1)), (i = k ∨ i = j) →
      spinAction (quadMinus 4 F b c) h (minusVec 4 i false) = minusVec 4 i false := by
    intro i hi
    let v : Fin 2 → F := if i = k then ![1, 0] else ![0, 1]
    have hv : pairVec k j false v = minusVec 4 i false := by
      rcases hi with rfl | rfl
      · simp [v, pairVec]
      · simp [v, pairVec, hkj.symm]
    obtain ⟨v', hv'⟩ := hPres v
    have hpol : ∀ t, polar (quadMinus 4 F b c) (spinAction (quadMinus 4 F b c) h
        (pairVec k j false v)) (pairVec k j true t) =
        polar (quadMinus 4 F b c) (pairVec k j false v) (pairVec k j true t) := fun t => by
      have := polar_spinAction (quadMinus 4 F b c) h (pairVec k j false v) (pairVec k j true t)
      rwa [hhe t] at this
    have hcoef : ∀ (w t : Fin 2 → F), polar (quadMinus 4 F b c) (pairVec k j false w)
        (pairVec k j true t) = w 0 * t 0 + w 1 * t 1 := by
      intro w t
      simp only [pairVec, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
        polar_minusVec_minusVec, smul_eq_mul]
      simp [hkj, hkj.symm]
      ring
    have h0 := hpol ![1, 0]
    have h1 := hpol ![0, 1]
    rw [hv', hcoef, hcoef] at h0 h1
    simp at h0 h1
    rw [← hv, hv']
    congr 1
    funext t
    fin_cases t
    · simpa using h0
    · simpa using h1
  obtain ⟨w, hw0, hw⟩ := exists_fix_planeVec hP hN
  have hhw : spinAction (quadMinus 4 F b c) h (planeVec 4 w) = planeVec 4 w := by
    rw [hhdef, hlinv]
    simp only [map_mul, LinearEquiv.mul_apply, hw, hxp, hyp]
  have hfix : ∀ i s, spinAction (quadMinus 4 F b c) h (minusVec 4 i s) = minusVec 4 i s := by
    intro i s
    by_cases hik : i = k
    · cases s
      · exact hhf i (Or.inl hik)
      · have := hhe ![1, 0]
        simpa [pairVec, hik] using this
    by_cases hij : i = j
    · cases s
      · exact hhf i (Or.inr hij)
      · have := hhe ![0, 1]
        simpa [pairVec, hij] using this
    exact hhm i hik hij s
  have h1 : h = 1 := eq_one_of_fix hirr hfix hw0 hhw
  rw [hhdef, inv_mul_eq_one] at h1
  rw [← h1]
  exact hl

end Long

end CFSG.StandardType.KGPosOm

end

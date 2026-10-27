module

public import CFSG.RankThree.PartTwo.Toolkit.BloomMono
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom
public import CFSG.RankThree.PartTwo.KFacts.K74Normal
public import CFSG.RankThree.PartTwo.KFacts.K74Irreducible
public import CFSG.RankThree.PartTwo.KFacts.K74Plane
public import Certificates.Certificate8171
public import Certificates.Certificate8172

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
  CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

section Raw

@[expose] def vneg (v : V3) : V3 := ⟨-v.x, -v.y, -v.z⟩

@[expose] def vent (v : V3) : ℕ → ZMod 3
  | 0 => v.x
  | 1 => v.y
  | _ => v.z

theorem mono_check_four : ∀ M ∈ monRaw, rpowR M 4 = rone → rpowR M 2 ≠ rone →
    ∀ v ∈ allV3, v ≠ vzero → inSpanR (rmv M v) v = true →
      ∃ j : Fin 3, inSpanR v (unitV j) = true := by
  decide

theorem mono_check_three : ∀ M ∈ monRaw, rpowR M 3 = rone → M ≠ rone →
    ∀ u ∈ allV3, ∀ w ∈ allV3, u ≠ vzero → rmv M u = u → rmv M w = w →
      inSpanR w u = true := by
  decide

theorem mono_check_nil : ∀ M ∈ monRaw, rpowR M 3 = rone → ∀ w ∈ allV3, w ≠ vzero →
    rmv M w = w ∨
      (vsub (rmv M w) w ≠ vzero ∧ rmv M (vsub (rmv M w) w) = vsub (rmv M w) w) ∨
      (vsub (rmv M (vsub (rmv M w) w)) (vsub (rmv M w) w) ≠ vzero ∧
        rmv M (vsub (rmv M (vsub (rmv M w) w)) (vsub (rmv M w) w)) =
          vsub (rmv M (vsub (rmv M w) w)) (vsub (rmv M w) w)) := by
  decide

theorem mono_check_refl : ∀ i : Fin 3, ∀ v ∈ allV3, vent v i = 0 → v ≠ vzero →
    ∃ R ∈ n0Raw, rmv R (unitV i) = vneg (unitV i) ∧ rmv R v = v ∧ rpowR R 2 = rone ∧
      ∃ w ∈ allV3, vent w i = 0 ∧ inSpanR w v = false ∧ rmv R w = vneg w := by
  decide

theorem mono_check_sq : ∀ M ∈ monRaw, rpowR M 4 = rone → rpowR M 2 ≠ rone →
    ∀ i : Fin 3, rmv M (unitV i) = unitV i → rdet M = 1 ∧
      ∀ j : Fin 3, rmv (rpowR M 2) (unitV j) = if j = i then unitV j else vneg (unitV j) := by
  decide

theorem mono_check_trans : ∀ i j : Fin 3, ∃ R ∈ n0Raw,
    inSpanR (rmv R (unitV i)) (unitV j) = true := by
  decide

@[expose] def m13 : R9 := ⟨0, 0, 1, 1, 0, 1, 0, 1, 0⟩

theorem m13_check : rdet m13 = 1 ∧ rpowR m13 13 = rone ∧ m13 ≠ rone := by
  decide

theorem a4_no_four : ∀ y : alternatingGroup (Fin 4), y ^ 4 = 1 → y ^ 2 = 1 := by
  decide

theorem s4_no_q8 : ∀ s t : Equiv.Perm (Fin 4), s ^ 4 = 1 → s ^ 2 = t ^ 2 →
    t * s * t⁻¹ = s⁻¹ → s ^ 2 = 1 := by
  decide

end Raw

section Mono

theorem ofVec_neg (v : Fin 3 → ZMod 3) : ofVec (-v) = vneg (ofVec v) :=
  rfl

theorem vent_ofVec (v : Fin 3 → ZMod 3) (i : Fin 3) : vent (ofVec v) i = v i := by
  fin_cases i <;> rfl

theorem ofVec_ne_zero {v : Fin 3 → ZMod 3} (hv : v ≠ 0) : ofVec v ≠ vzero := by
  rw [← ofVec_zero]
  exact fun h => hv (ofVec_injective h)

theorem ofMat_pow_eq_rone {g : GL33} {n : ℕ} (h : g ^ n = 1) :
    rpowR (ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) n = rone := by
  rw [← ofMat_glPow, h, ofMat_glOne]

theorem ofMat_pow_ne_rone {g : GL33} {n : ℕ} (h : g ^ n ≠ 1) :
    rpowR (ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) n ≠ rone := by
  rw [← ofMat_glPow, ← ofMat_glOne]
  exact fun e => h (gl_eq_iff.mpr e)

theorem mem_Lstd_of_order_four {g : GL33} (hg : g ∈ linePermuting Lstd) (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 ≠ 1) {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    (hgv : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ Submodule.span (ZMod 3) {v}) :
    ∃ j, v ∈ Lstd j := by
  rw [mem_span_iff_inSpanR, ofVec_mulVec] at hgv
  obtain ⟨j, hj⟩ := mono_check_four _ (mem_monRaw_of_mem hg) (ofMat_pow_eq_rone h4)
    (ofMat_pow_ne_rone h2) _ (mem_allV3 _) (ofVec_ne_zero hv) hgv
  exact ⟨j, (mem_Lstd_iff v j).mpr hj⟩

theorem mem_span_of_order_three {g : GL33} (hg : g ∈ linePermuting Lstd) (h3 : g ^ 3 = 1)
    (h1 : g ≠ 1) {u w : Fin 3 → ZMod 3} (hu : u ≠ 0)
    (hgu : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u = u)
    (hgw : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w) :
    w ∈ Submodule.span (ZMod 3) {u} := by
  rw [mem_span_iff_inSpanR]
  refine mono_check_three _ (mem_monRaw_of_mem hg) (ofMat_pow_eq_rone h3) ?_ _ (mem_allV3 _) _
    (mem_allV3 _) (ofVec_ne_zero hu) (by rw [← ofVec_mulVec, hgu]) (by rw [← ofVec_mulVec, hgw])
  rw [← ofMat_glOne]
  exact fun e => h1 (gl_eq_iff.mpr e)

theorem exists_fixed_of_cube {g : GL33} (hg : g ∈ linePermuting Lstd) (h3 : g ^ 3 = 1)
    {U : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hU : ∀ u ∈ U, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u ∈ U) {w : Fin 3 → ZMod 3}
    (hw : w ∈ U) (hw0 : w ≠ 0) :
    ∃ w' ∈ U, w' ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w' = w' := by
  set M := (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) with hM
  have hN : ∀ u ∈ U, M *ᵥ u - u ∈ U := fun u hu => U.sub_mem (hU u hu) hu
  have hne : ∀ u : Fin 3 → ZMod 3, ofVec u ≠ vzero → u ≠ 0 := fun u h h0 => h (by rw [h0]; rfl)
  rcases mono_check_nil _ (mem_monRaw_of_mem hg) (ofMat_pow_eq_rone h3) _ (mem_allV3 _)
      (ofVec_ne_zero hw0) with h | ⟨h0, h⟩ | ⟨h0, h⟩
  · exact ⟨w, hw, hw0, ofVec_injective (by rw [ofVec_mulVec, h])⟩
  · refine ⟨M *ᵥ w - w, hN w hw, hne _ (by rw [ofVec_sub, ofVec_mulVec]; exact h0), ?_⟩
    apply ofVec_injective
    rw [ofVec_mulVec, ofVec_sub, ofVec_mulVec]
    exact h
  · refine ⟨M *ᵥ (M *ᵥ w - w) - (M *ᵥ w - w), hN _ (hN w hw),
      hne _ (by rw [ofVec_sub, ofVec_mulVec, ofVec_sub, ofVec_mulVec]; exact h0), ?_⟩
    apply ofVec_injective
    rw [ofVec_mulVec, ofVec_sub, ofVec_mulVec, ofVec_sub, ofVec_mulVec]
    exact h

theorem exists_mem_N0std_of_raw {R : R9} (hR : R ∈ n0Raw) :
    ∃ r ∈ monomialDetOne Lstd, ofMat (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) = R := by
  have hdet : rdet R ≠ 0 := by rw [(n0Raw_iff.1 hR).2]; exact one_ne_zero
  obtain ⟨r, hr⟩ := exists_gl hdet
  exact ⟨r, (mem_N0std_iff r).2 (hr ▸ hR), hr⟩

theorem exists_reflection (i : Fin 3) {v : Fin 3 → ZMod 3} (hvi : v i = 0) (hv : v ≠ 0) :
    ∃ r ∈ monomialDetOne Lstd,
      (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = -Pi.single i 1 ∧
      (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v ∧ r ^ 2 = 1 ∧
      ∃ w : Fin 3 → ZMod 3, w i = 0 ∧ w ∉ Submodule.span (ZMod 3) {v} ∧
        (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = -w := by
  obtain ⟨R, hR, hRi, hRv, hR2, w, -, hwi, hwv, hRw⟩ :=
    mono_check_refl i (ofVec v) (mem_allV3 _) (by rw [vent_ofVec, hvi]) (ofVec_ne_zero hv)
  obtain ⟨r, hr, rfl⟩ := exists_mem_N0std_of_raw hR
  refine ⟨r, hr, ofVec_injective ?_, ofVec_injective ?_, ?_, toVec w, ?_, ?_, ofVec_injective ?_⟩
  · rw [ofVec_mulVec, ofVec_single, hRi, ofVec_neg, ofVec_single]
  · rw [ofVec_mulVec, hRv]
  · rw [gl_eq_iff, ofMat_glPow, hR2, ofMat_glOne]
  · rw [← vent_ofVec (toVec w) i, ofVec_toVec]
    exact hwi
  · rw [mem_span_iff_inSpanR, ofVec_toVec, hwv]
    exact Bool.false_ne_true
  · rw [ofVec_mulVec, ofVec_toVec, hRw, ofVec_neg, ofVec_toVec]

theorem sq_of_order_four {g : GL33} (hg : g ∈ linePermuting Lstd) (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 ≠ 1) {i : Fin 3}
    (hgi : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single i 1) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 ∧ ∀ j : Fin 3,
      ((g ^ 2 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single j 1 =
        if j = i then Pi.single j 1 else -Pi.single j 1 := by
  obtain ⟨hdet, hsq⟩ := mono_check_sq _ (mem_monRaw_of_mem hg) (ofMat_pow_eq_rone h4)
    (ofMat_pow_ne_rone h2) i (by rw [← ofVec_single, ← ofVec_mulVec, hgi])
  refine ⟨by rw [← rdet_ofMat, hdet], fun j => ofVec_injective ?_⟩
  rw [ofVec_mulVec, ofMat_glPow, ofVec_single, hsq j]
  split_ifs
  · rw [ofVec_single]
  · rw [ofVec_neg, ofVec_single]

theorem exists_mem_N0std_mulVec (i j : Fin 3) :
    ∃ r ∈ monomialDetOne Lstd, (r : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 ∈ Lstd j := by
  obtain ⟨R, hR, hRij⟩ := mono_check_trans i j
  obtain ⟨r, hr, rfl⟩ := exists_mem_N0std_of_raw hR
  refine ⟨r, hr, ?_⟩
  rw [mem_Lstd_iff, ofVec_mulVec, ofVec_single]
  exact hRij

theorem exists_orderOf_thirteen :
    ∃ g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3), orderOf g = 13 := by
  obtain ⟨h1, h13, hne⟩ := m13_check
  obtain ⟨g, hg⟩ := exists_gl (r := m13) (by rw [h1]; exact one_ne_zero)
  refine ⟨g, (mem_statedSL_iff g).2 (by rw [← rdet_ofMat, hg, h1]), ?_⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [gl_eq_iff, ofMat_glPow, hg, h13, ofMat_glOne]
  · intro h
    apply hne
    rw [← hg, h, ofMat_glOne]

end Mono


section Sym7


@[expose] def y7 : Equiv.Perm (Fin 7) :=
  ⟨![1, 2, 0, 3, 4, 5, 6], ![2, 0, 1, 3, 4, 5, 6], by decide, by decide⟩

@[expose] def z7 : Equiv.Perm (Fin 7) :=
  ⟨![0, 1, 2, 4, 5, 3, 6], ![0, 1, 2, 5, 3, 4, 6], by decide, by decide⟩

theorem card_support_y7_z7 : ∀ i j : Fin 3, ((y7 ^ (i : ℕ) * z7 ^ (j : ℕ)).support.card = 3 →
    i = 0 ∨ j = 0) := by
  decide

@[expose] def f7 (a b c : Fin 7) : Fin 7 → Fin 7 :=
  ![a, y7 a, y7 (y7 a), b, z7⁻¹ b, z7⁻¹ (z7⁻¹ b), c]

theorem f7_check : ∀ a b c : Fin 7, (∀ i, f7 a b c (y7 i) = y7 (f7 a b c i)) →
    (∀ i, f7 a b c (z7 i) = z7⁻¹ (f7 a b c i)) → (∀ i j, f7 a b c i = f7 a b c j → i = j) →
      (Finset.univ.filter fun i => f7 a b c (f7 a b c (f7 a b c i)) ≠ i).card = 2 := by
  decide

theorem isSwap_pow_three {σ : Equiv.Perm (Fin 7)} (hy : σ * y7 = y7 * σ)
    (hz : σ * z7 * σ⁻¹ = z7⁻¹) : (σ ^ 3).IsSwap := by
  have hy' : ∀ i, σ (y7 i) = y7 (σ i) := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin 7) => τ i) hy
    simpa using this
  have hz' : ∀ i, σ (z7 i) = z7⁻¹ (σ i) := fun i => by
    have h1 : σ * z7 = z7⁻¹ * σ := by rw [← hz, inv_mul_cancel_right]
    have := congrArg (fun τ : Equiv.Perm (Fin 7) => τ i) h1
    simpa using this
  have hF : ∀ i, σ i = f7 (σ 0) (σ 3) (σ 6) i := by
    intro i
    fin_cases i
    · rfl
    · show σ 1 = y7 (σ 0)
      exact hy' 0
    · show σ 2 = y7 (y7 (σ 0))
      rw [← hy', ← hy']
      rfl
    · rfl
    · show σ 4 = z7⁻¹ (σ 3)
      exact hz' 3
    · show σ 5 = z7⁻¹ (z7⁻¹ (σ 3))
      rw [← hz', ← hz']
      rfl
    · rfl
  have hcard := f7_check (σ 0) (σ 3) (σ 6)
    (fun i => by rw [← hF (y7 i), ← hF i, hy'])
    (fun i => by rw [← hF (z7 i), ← hF i, hz'])
    (fun i j h => σ.injective (by rw [hF i, hF j]; exact h))
  have hsupp : (σ ^ 3).support = Finset.univ.filter fun i =>
      f7 (σ 0) (σ 3) (σ 6) (f7 (σ 0) (σ 3) (σ 6) (f7 (σ 0) (σ 3) (σ 6) i)) ≠ i := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hF i, ← hF (σ i), ← hF (σ (σ i))]
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
  rw [← Equiv.Perm.card_support_eq_two, hsupp]
  exact hcard

end Sym7

section ESeven

theorem y7_mem : y7 ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem z7_mem : z7 ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem y7_z7_closed : ∀ i j k l : Fin 3, ∃ m n : Fin 3,
    y7 ^ (i : ℕ) * z7 ^ (j : ℕ) * (y7 ^ (k : ℕ) * z7 ^ (l : ℕ)) =
      y7 ^ (m : ℕ) * z7 ^ (n : ℕ) := by
  decide

theorem y7_z7_inv : ∀ i j : Fin 3, ∃ m n : Fin 3,
    (y7 ^ (i : ℕ) * z7 ^ (j : ℕ))⁻¹ = y7 ^ (m : ℕ) * z7 ^ (n : ℕ) := by
  decide

theorem y7_z7_injective : ∀ i j k l : Fin 3,
    y7 ^ (i : ℕ) * z7 ^ (j : ℕ) = y7 ^ (k : ℕ) * z7 ^ (l : ℕ) → i = k ∧ j = l := by
  decide

theorem y7_z7_mem : ∀ i j : Fin 3, y7 ^ (i : ℕ) * z7 ^ (j : ℕ) ∈ alternatingGroup (Fin 7) :=
  fun _ _ => Subgroup.mul_mem _ (Subgroup.pow_mem _ y7_mem _) (Subgroup.pow_mem _ z7_mem _)

@[expose] def eStd : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | ∃ i j : Fin 3, (g : Equiv.Perm (Fin 7)) = y7 ^ (i : ℕ) * z7 ^ (j : ℕ)}
  mul_mem' := by
    rintro a b ⟨i, j, hij⟩ ⟨k, l, hkl⟩
    obtain ⟨m, n, h⟩ := y7_z7_closed i j k l
    exact ⟨m, n, by rw [Subgroup.coe_mul, hij, hkl, h]⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro a ⟨i, j, hij⟩
    obtain ⟨m, n, h⟩ := y7_z7_inv i j
    exact ⟨m, n, by rw [Subgroup.coe_inv, hij, h]⟩

theorem mem_eStd_iff {g : alternatingGroup (Fin 7)} :
    g ∈ eStd ↔ ∃ i j : Fin 3, (g : Equiv.Perm (Fin 7)) = y7 ^ (i : ℕ) * z7 ^ (j : ℕ) :=
  Iff.rfl

theorem card_eStd : Nat.card eStd = 9 := by
  let φ : Fin 3 × Fin 3 → eStd := fun ij =>
    ⟨⟨y7 ^ (ij.1 : ℕ) * z7 ^ (ij.2 : ℕ), y7_z7_mem ij.1 ij.2⟩, ij.1, ij.2, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => ?_, fun g => ?_⟩
    · have h' := congrArg (fun x : eStd => ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) h
      obtain ⟨h1, h2⟩ := y7_z7_injective _ _ _ _ h'
      exact Prod.ext h1 h2
    · obtain ⟨i, j, hij⟩ := g.2
      exact ⟨(i, j), Subtype.ext (Subtype.ext hij.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_fin]

@[expose] def y7A : alternatingGroup (Fin 7) := ⟨y7, y7_mem⟩

theorem y7A_mem : y7A ∈ eStd := ⟨1, 0, by simp [y7A]⟩

theorem y7_z7_pow_three : ∀ i j : Fin 3, (y7 ^ (i : ℕ) * z7 ^ (j : ℕ)) ^ 3 = 1 := by
  decide

theorem pow_three_of_mem_eStd {g : alternatingGroup (Fin 7)} (hg : g ∈ eStd) : g ^ 3 = 1 := by
  obtain ⟨i, j, hij⟩ := hg
  apply Subtype.ext
  rw [Subgroup.coe_pow, hij, y7_z7_pow_three, Subgroup.coe_one]

theorem y7A_ne_one : y7A ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)

theorem conj_z7_eq_inv {σ : Equiv.Perm (Fin 7)} (hy : σ * y7 = y7 * σ)
    (hN : ∀ g ∈ eStd, ∃ g' ∈ eStd,
      σ * (g : Equiv.Perm (Fin 7)) * σ⁻¹ = (g' : Equiv.Perm (Fin 7)))
    (hne : ∃ g ∈ eStd, σ * (g : Equiv.Perm (Fin 7)) * σ⁻¹ ≠ g) :
    σ * z7 * σ⁻¹ = z7⁻¹ := by
  have hzmem : (⟨z7, z7_mem⟩ : alternatingGroup (Fin 7)) ∈ eStd := ⟨0, 1, by simp⟩
  obtain ⟨g', hg', hσz⟩ := hN _ hzmem
  obtain ⟨i, j, hij⟩ := hg'
  have hsupp : (y7 ^ (i : ℕ) * z7 ^ (j : ℕ)).support.card = 3 := by
    rw [← hij, ← hσz, Equiv.Perm.card_support_conj]
    decide
  have hy' : ∀ k : ℕ, σ * y7 ^ k * σ⁻¹ = y7 ^ k := fun k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hy, mul_inv_cancel_right]
  rcases card_support_y7_z7 i j hsupp with rfl | rfl
  ·
    simp only [Fin.val_zero, pow_zero, one_mul] at hij
    rw [hij] at hσz
    change σ * z7 * σ⁻¹ = z7 ^ (j : ℕ) at hσz
    fin_cases j
    · exfalso
      have : z7 = 1 := by
        have h1 : σ * z7 * σ⁻¹ = σ * 1 * σ⁻¹ := by rw [hσz]; simp
        simpa using h1
      exact absurd this (by decide)
    ·
      exfalso
      obtain ⟨g, ⟨k, l, hkl⟩, hgne⟩ := hne
      apply hgne
      rw [hkl]
      have hz' : ∀ k : ℕ, σ * z7 ^ k * σ⁻¹ = z7 ^ k := fun k => by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
        simpa using congrArg (· ^ k) hσz
      calc σ * (y7 ^ (k : ℕ) * z7 ^ (l : ℕ)) * σ⁻¹ =
          (σ * y7 ^ (k : ℕ) * σ⁻¹) * (σ * z7 ^ (l : ℕ) * σ⁻¹) := by group
        _ = y7 ^ (k : ℕ) * z7 ^ (l : ℕ) := by rw [hy', hz']
    · simpa [show z7 ^ 2 = z7⁻¹ by decide] using hσz
  ·
    exfalso
    simp only [Fin.val_zero, pow_zero, mul_one] at hij
    rw [hij] at hσz
    change σ * z7 * σ⁻¹ = y7 ^ (i : ℕ) at hσz
    rw [← hy' i] at hσz
    have : z7 = y7 ^ (i : ℕ) := by
      have h1 := congrArg (fun τ => σ⁻¹ * τ * σ) hσz
      simpa [mul_assoc] using h1
    revert this
    fin_cases i <;> decide

end ESeven

section Plane

variable {G : Type} [Group G]

theorem no_eigen_of_order_four : ∀ a b c d : ZMod 3,
    !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] = 1 →
    !![a, b; c, d] * !![a, b; c, d] ≠ 1 →
    ∀ x y e : ZMod 3, a * x + b * y = e * x → c * x + d * y = e * y → x = 0 ∧ y = 0 := by
  decide +kernel

theorem isIrreducibleOn_of_order_four {B : Subgroup G} [Finite B]
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h9 : Nat.card B = 9) {T : Subgroup (MulAut B)}
    {τ : MulAut B} (hτ : τ ∈ T) (h4 : τ ^ 4 = 1) (h2 : τ ^ 2 ≠ 1) :
    Sec21.IsIrreducibleOn T := by
  intro D hD
  have hdvd : Nat.card D ∣ 3 ^ 2 := by
    rw [show 3 ^ 2 = 9 by norm_num, ← h9]
    exact Subgroup.card_subgroup_dvd_card D
  obtain ⟨k, hk, hDk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · left
    exact Subgroup.eq_bot_of_card_eq D (by simpa using hDk)
  · exfalso
    have hD3 : Nat.card D = 3 := by simpa using hDk
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra h
      push Not at h
      have : D = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
      rw [this, Subgroup.card_bot] at hD3
      norm_num at hD3
    have hd3 : orderOf d = 3 := by
      refine orderOf_eq_prime ?_ hd1
      exact Subtype.ext (by simpa using hB.2 _ d.2)
    have hDz : D = Subgroup.zpowers d := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD) ?_).symm
      rw [hD3, Nat.card_zpowers, hd3]
    have hτd : τ d ∈ Subgroup.zpowers d := by
      rw [← hDz, ← hD τ hτ]
      exact ⟨d, hdD, rfl⟩
    obtain ⟨f⟩ := Sec12.exists_coords hB (n := 2) (by rw [h9]; norm_num)
    set g := Sec12.coordHom f τ with hgdef
    have hg4 : g ^ 4 = 1 := by rw [hgdef, ← map_pow, h4, map_one]
    have hg2 : g ^ 2 ≠ 1 := by
      rw [hgdef, ← map_pow]
      intro h
      apply h2
      apply Sec12.coordHom_injective f
      rw [h, map_one]
    set v := Sec12.coordVec f d with hvdef
    have hv0 : v ≠ 0 := Sec12.coordVec_ne_zero f hd1
    have hgv : g v ∈ Submodule.span (ZMod 3) ({v} : Set (Fin 2 → ZMod 3)) := by
      rw [hgdef, hvdef, KFacts.coordHom_coordVec]
      exact (KFacts.coordVec_mem_span_iff f).mpr hτd
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hgv
    have hM4 := KFacts.toMatrix'_pow_eq_one_V2 hg4
    rw [KFacts.toMatrix'_eq_V2] at hM4
    have hM2 : !![(g : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) (Pi.single 0 1) 0,
        (g : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) (Pi.single 1 1) 0;
        (g : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) (Pi.single 0 1) 1,
        (g : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) (Pi.single 1 1) 1] ^ 2 ≠ 1 := by
      intro h
      apply hg2
      have h1 : LinearMap.toMatrix' ((g ^ 2 : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) :
          (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) = LinearMap.toMatrix' LinearMap.id := by
        rw [KFacts.toMatrix'_pow_V2, KFacts.toMatrix'_eq_V2, h, LinearMap.toMatrix'_id]
      have h2' := LinearMap.toMatrix'.injective h1
      exact LinearEquiv.ext fun w => by
        have := congrArg (fun φ : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3) => φ w) h2'
        simpa using this
    have hvv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    have happ := KFacts.apply_eq_V2 (g : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) (v 0) (v 1)
    rw [← hvv] at happ
    have h0 := congrFun happ 0
    have h1 := congrFun happ 1
    simp only [LinearEquiv.coe_coe] at h0 h1
    rw [← he] at h0 h1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    obtain ⟨hx, hy⟩ := no_eigen_of_order_four _ _ _ _ (by simpa [pow_succ] using hM4)
      (by simpa [sq] using hM2) (v 0) (v 1) e h0.symm h1.symm
    apply hv0
    ext i
    fin_cases i
    · exact hx
    · exact hy
  · right
    exact Subgroup.eq_top_of_card_eq D (by rw [hDk, h9]; norm_num)

theorem sq_eq_one_of_q8_rel {K : Type*} [Group K]
    {φ : K →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)} (hφ : Function.Injective φ)
    {x y : K} (h4 : x ^ 4 = 1) (hxy : x ^ 2 = y ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) : x ^ 2 = 1 := by
  have hs := s4_no_q8 (φ x).2 (φ y).2
    (by
      have := congrArg Prod.snd (show φ (x ^ 4) = φ 1 by rw [h4])
      simpa using this)
    (by
      have := congrArg Prod.snd (show φ (x ^ 2) = φ (y ^ 2) by rw [hxy])
      simpa using this)
    (by
      have := congrArg (fun k => (φ k).2) hyx
      simpa using this)
  have hz : ((φ x).1) ^ 2 = 1 := by
    generalize (φ x).1 = z
    revert z
    decide
  apply hφ
  rw [map_pow, map_one]
  exact Prod.ext hz hs

theorem false_of_quaternion {K : Type*} [Group K]
    {φ : K →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)} (hφ : Function.Injective φ)
    {Q : Subgroup K} (e : Q ≃* QuaternionGroup 2) : False := by
  have h := sq_eq_one_of_q8_rel (φ := φ.comp Q.subtype) (hφ.comp Subtype.val_injective)
    (x := e.symm (QuaternionGroup.a 1)) (y := e.symm (QuaternionGroup.xa 0))
    (by rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one])
    (by rw [← map_pow, ← map_pow,
      show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.xa 0 ^ 2 by decide])
    (by rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      show QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
        ((QuaternionGroup.a 1)⁻¹ : QuaternionGroup 2) by decide])
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h
  exact absurd h (by decide)

@[expose] def slI : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![0, 1; -1, 0], by decide⟩

@[expose] def slJ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 1, -1], by decide⟩

theorem slI_rel : slI ^ 4 = 1 ∧ slI ^ 2 = slJ ^ 2 ∧ slJ * slI * slJ⁻¹ = slI⁻¹ ∧ slI ^ 2 ≠ 1 := by
  decide

theorem false_of_SL23 {K : Type*} [Group K]
    {φ : K →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)} (hφ : Function.Injective φ)
    {Q : Subgroup K} (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : False := by
  obtain ⟨h4, h2, h3, hne⟩ := slI_rel
  have h := sq_eq_one_of_q8_rel (φ := φ.comp Q.subtype) (hφ.comp Subtype.val_injective)
    (x := e.symm slI) (y := e.symm slJ) (by rw [← map_pow, h4, map_one])
    (by rw [← map_pow, ← map_pow, h2])
    (by rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, h3])
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h
  exact hne h

end Plane

section Coords

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def coordChange (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (B : GL33) :
    Multiplicative (Fin 3 → ZMod 3) ≃* A :=
  (AddEquiv.toMultiplicative (KFacts.glEquiv B).toAddEquiv).trans f

theorem glEquiv_symm_apply' (B : GL33) (w : Fin 3 → ZMod 3) :
    (KFacts.glEquiv B).symm w = ((B⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w := by
  rw [← KFacts.glEquiv_apply, map_inv]
  rfl

theorem glHom_coordChange (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (B : GL33)
    (σ : MulAut A) : KFacts.glHom (coordChange f B) σ = B⁻¹ * KFacts.glHom f σ * B := by
  apply KFacts.glEquiv.injective
  apply LinearEquiv.ext
  intro v
  rw [KFacts.glEquiv_glHom, KFacts.glEquiv_apply, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← glEquiv_symm_apply',
    ← KFacts.glEquiv_apply (KFacts.glHom f σ), KFacts.glEquiv_glHom, ← KFacts.glEquiv_apply B]
  rfl

theorem glHom_mulVec_coordVec (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (σ : MulAut A)
    (a : A) : ((KFacts.glHom f σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ
      Sec12.coordVec f a = Sec12.coordVec f (σ a) := by
  rw [← KFacts.glEquiv_apply, KFacts.glEquiv_glHom, KFacts.coordHom_coordVec]

theorem exists_std_coords [Finite A] (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {S : Subgroup (MulAut A)} (hirr : Sec21.IsIrreducibleOn S)
    (h4 : 4 ∣ Nat.card S) (h13 : ¬ 13 ∣ Nat.card S) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A, S.map (KFacts.glHom f) ≤ linePermuting Lstd ∧
      G0std ≤ S.map (KFacts.glHom f) := by
  obtain ⟨f0⟩ := Sec12.exists_coords hA (n := 3) (by rw [h27]; norm_num)
  set H := S.map (KFacts.glHom f0) with hH
  have hcard : Nat.card H = Nat.card S :=
    (Nat.card_congr (S.equivMapOfInjective _ (KFacts.glHom_injective f0)).toEquiv).symm
  have hHirr : IsIrreducibleOn H := KFacts.isIrreducibleOn_map_glHom f0 hirr
  have hSL : ¬ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ H := by
    intro hle
    obtain ⟨g, hg, hg13⟩ := exists_orderOf_thirteen
    have := orderOf_dvd_natCard (⟨g, hle hg⟩ : H)
    rw [Subgroup.orderOf_mk, hg13, hcard] at this
    exact h13 this
  obtain ⟨L, hL, h1, hperm, htr, -⟩ := KFacts.bloomCaseC_of hHirr (hcard ▸ h4) hSL
  obtain ⟨B, hB⟩ := exists_basis_gl hL h1
  refine ⟨coordChange f0 B, ?_⟩
  have hmap : S.map (KFacts.glHom (coordChange f0 B)) = H.map (MulAut.conj B⁻¹).toMonoidHom := by
    rw [hH, Subgroup.map_map]
    congr 1
    ext σ : 1
    simp [glHom_coordChange]
  have hlp : ∀ g ∈ H, g ∈ linePermuting L := fun g hg i =>
    ⟨hperm g hg i, hperm g⁻¹ (H.inv_mem hg) i⟩
  have hG'le : H.map (MulAut.conj B⁻¹).toMonoidHom ≤ linePermuting Lstd := by
    intro x hx
    rw [mem_map_conj_inv_iff] at hx
    have := (mem_linePermuting_conj_iff hB (B * x * B⁻¹)).2 (hlp _ hx)
    rwa [show B⁻¹ * (B * x * B⁻¹) * B = x by group] at this
  have htr' : ∀ i j, ∃ x ∈ H.map (MulAut.conj B⁻¹).toMonoidHom,
      translate x (Lstd i) = Lstd j := by
    intro i j
    obtain ⟨g, hg, hgij⟩ := htr i j
    refine ⟨B⁻¹ * g * B, ?_, (translate_conj_eq_iff hB g i j).2 hgij⟩
    rw [mem_map_conj_inv_iff, show B * (B⁻¹ * g * B) * B⁻¹ = g by group]
    exact hg
  have hirr' : IsIrreducibleOn (H.map (MulAut.conj B⁻¹).toMonoidHom) :=
    isIrreducibleOn_map_conj hHirr B
  rw [hmap]
  exact ⟨hG'le, G0std_le_of hG'le htr' hirr'⟩

end Coords

section Monomial

@[expose] def diagI : ℕ → R9
  | 0 => ⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩
  | 1 => ⟨2, 0, 0, 0, 1, 0, 0, 0, 2⟩
  | _ => ⟨2, 0, 0, 0, 2, 0, 0, 0, 1⟩

theorem mono_check_diag : ∀ M ∈ monRaw, rpowR M 4 = rone → rpowR M 2 ≠ rone →
    ∀ i : Fin 3, rmv M (unitV i) = unitV i → rpowR M 2 = diagI i := by
  decide

theorem diag_check : ∀ i : Fin 3, ∀ v ∈ allV3,
    vadd v (rmv (diagI i) v) = vsmulR (2 * vent v i) (unitV i) := by
  decide

theorem unitV_inSpan : ∀ j k : Fin 3, inSpanR (unitV j) (unitV k) = true → j = k := by
  decide

theorem card_coord_zero (i : Fin 3) : Nat.card {v : Fin 3 → ZMod 3 // v i = 0} = 9 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i <;> rfl

theorem add_sq_mulVec {g : GL33} (hg : g ∈ linePermuting Lstd) (h4 : g ^ 4 = 1)
    (h2 : g ^ 2 ≠ 1) {i : Fin 3}
    (hgi : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single i 1)
    (v : Fin 3 → ZMod 3) :
    v + ((g ^ 2 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = (2 * v i) • Pi.single i 1 := by
  have hd := mono_check_diag _ (mem_monRaw_of_mem hg) (ofMat_pow_eq_rone h4)
    (ofMat_pow_ne_rone h2) i (by rw [← ofVec_single, ← ofVec_mulVec, hgi])
  apply ofVec_injective
  rw [ofVec_add, ofVec_mulVec, ofMat_glPow, hd, diag_check i _ (mem_allV3 _), ofVec_smul,
    ofVec_single, vent_ofVec]

theorem N0std_le_of {G' : Subgroup GL33} (hle : G' ≤ linePermuting Lstd) (hG0 : G0std ≤ G')
    {g : GL33} (hg : g ∈ G') (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) {i : Fin 3}
    (hgi : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single i 1) :
    monomialDetOne Lstd ≤ G' := by
  have hgN : g ∈ monomialDetOne Lstd :=
    ⟨hle hg, (mem_statedSL_iff g).2 (sq_of_order_four (hle hg) h4 h2 hgi).1⟩
  have hgG0 : g ∉ G0std := by
    intro h
    apply h2
    have h4' : (G0Equiv ⟨g, h⟩) ^ 4 = 1 := by
      rw [← map_pow, show (⟨g, h⟩ : G0std) ^ 4 = 1 from Subtype.ext h4, map_one]
    have h2' := a4_no_four _ h4'
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h2'
    exact congrArg Subtype.val h2'
  intro n hn
  by_cases hnG : n ∈ G0std
  · exact hG0 hnG
  · have hmem : (⟨n, hn⟩ : monomialDetOne Lstd) * (⟨g, hgN⟩ : monomialDetOne Lstd)⁻¹ ∈
        G0std.subgroupOf (monomialDetOne Lstd) := by
      rw [Subgroup.mul_mem_iff_of_index_two index_G0std, Subgroup.inv_mem_iff,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => absurd h hnG, fun h => absurd h hgG0⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    have h1 : n = (n * g⁻¹) * g := by group
    rw [h1]
    exact G'.mul_mem (hG0 hmem) hg

theorem nonempty_N0std_sup_equiv :
    Nonempty ((monomialDetOne Lstd ⊔ Subgroup.zpowers (-1 : GL33) : Subgroup GL33) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  set N₀ := monomialDetOne Lstd with hN₀
  set Z := Subgroup.zpowers (-1 : GL33) with hZ
  let ψ : N₀ × Z →* GL33 :=
    N₀.subtype.noncommCoprod Z.subtype fun n z =>
      (KFacts.commute_of_mem_zpowers_neg_one z.2 n).symm
  have hψ : ∀ x : N₀ × Z, ψ x = (x.1 : GL33) * x.2 := fun x => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨n, z⟩ h1
    rw [hψ] at h1
    have hnz : (n : GL33) = (z : GL33)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : (n : GL33) ∈ N₀ ⊓ Z := ⟨n.2, hnz ▸ Subgroup.inv_mem _ z.2⟩
    rw [N0_inf_neg_one, Subgroup.mem_bot] at hmem
    have hz : (z : GL33) = 1 := by
      rw [hmem, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hz)
  have hrange : ψ.range = N₀ ⊔ Z := by
    have := KFacts.normal_zpowers_neg_one
    apply le_antisymm
    · rintro _ ⟨⟨n, z⟩, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right z.2)
    · intro g hg
      have hg' : g ∈ ((N₀ ⊔ Z : Subgroup GL33) : Set GL33) := hg
      rw [Subgroup.mul_normal, Set.mem_mul] at hg'
      obtain ⟨n, hn, z, hz, rfl⟩ := hg'
      exact ⟨(⟨n, hn⟩, ⟨z, hz⟩), rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eZ : Z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq KFacts.card_zpowers_neg_one (by simp)
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((MonoidHom.ofInjective hψinj).symm.trans ((psiEquiv.prodCongr eZ).trans MulEquiv.prodComm))⟩

theorem nonempty_equiv_of_N0std_le {G' : Subgroup GL33} (hle : G' ≤ linePermuting Lstd)
    (hN : monomialDetOne Lstd ≤ G') :
    Nonempty (G' ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (G' ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  have hsup := le_N0std_sup hle
  by_cases hneg : (-1 : GL33) ∈ G'
  · right
    have heq : G' = monomialDetOne Lstd ⊔ Subgroup.zpowers (-1 : GL33) :=
      le_antisymm hsup (sup_le hN (Subgroup.zpowers_le.mpr hneg))
    obtain ⟨e⟩ := nonempty_N0std_sup_equiv
    exact ⟨(MulEquiv.subgroupCongr heq).trans e⟩
  · left
    have heq : G' = monomialDetOne Lstd := by
      refine le_antisymm (fun g hg => ?_) hN
      have := KFacts.normal_zpowers_neg_one
      have hg' : g ∈ ((monomialDetOne Lstd ⊔ Subgroup.zpowers (-1 : GL33) : Subgroup GL33) :
          Set GL33) := hsup hg
      rw [Subgroup.mul_normal, Set.mem_mul] at hg'
      obtain ⟨n, hn, z, hz, rfl⟩ := hg'
      rcases mem_zpowers_neg_one_iff.1 hz with rfl | rfl
      · rwa [mul_one]
      · exfalso
        apply hneg
        have : (-1 : GL33) = n⁻¹ * (n * -1) := by group
        rw [this]
        exact G'.mul_mem (G'.inv_mem (hN hn)) hg
    exact ⟨(MulEquiv.subgroupCongr heq).trans psiEquiv⟩

end Monomial

section Points

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def coordPt (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (j : Fin 3) :
    G :=
  (f (Multiplicative.ofAdd (Pi.single j 1)) : G)

theorem coordVec_coordPt (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (j : Fin 3) :
    Sec12.coordVec f (f (Multiplicative.ofAdd (Pi.single j 1))) = Pi.single j 1 := by
  simp [Sec12.coordVec]

theorem zpowers_eq_coordPt (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {a : A} (ha : a ≠ 1)
    {j : Fin 3} (hj : Sec12.coordVec f a ∈ Lstd j) :
    Subgroup.zpowers (a : G) = Subgroup.zpowers (coordPt f j) := by
  set p := f (Multiplicative.ofAdd (Pi.single j 1)) with hp
  have h1 : a ∈ Subgroup.zpowers p := by
    rw [← KFacts.coordVec_mem_span_iff f, hp, coordVec_coordPt]
    exact hj
  have h2 : p ∈ Subgroup.zpowers a := by
    rw [← KFacts.coordVec_mem_span_iff f, hp, coordVec_coordPt]
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hj
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact Sec12.coordVec_ne_zero f ha hμ.symm
    rw [Submodule.mem_span_singleton]
    exact ⟨μ⁻¹, by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]⟩
  have hsub : ∀ {x y : A}, x ∈ Subgroup.zpowers y → (x : G) ∈ Subgroup.zpowers (y : G) := by
    intro x y hxy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩
  exact le_antisymm (Subgroup.zpowers_le.mpr (hsub h1)) (Subgroup.zpowers_le.mpr (hsub h2))

theorem coordPt_injective (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {j k : Fin 3}
    (h : Subgroup.zpowers (coordPt f j) = Subgroup.zpowers (coordPt f k)) : j = k := by
  have hmem : coordPt f j ∈ Subgroup.zpowers (coordPt f k) := h ▸ Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hA : f (Multiplicative.ofAdd (Pi.single j 1)) ∈
      Subgroup.zpowers (f (Multiplicative.ofAdd (Pi.single k 1))) :=
    Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [coordPt] using hn)⟩
  rw [← KFacts.coordVec_mem_span_iff f, coordVec_coordPt, coordVec_coordPt,
    mem_span_iff_inSpanR, ofVec_single, ofVec_single] at hA
  exact unitV_inSpan j k hA

end Points

end CFSG.RankThree.PartTwo.Sec13

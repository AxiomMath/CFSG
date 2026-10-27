module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoACore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerE8
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCA
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private lemma ggQ2xFN_alg (a : ZMod 3) (ha : a * a = 1) : 2 * a + a * (a * a) = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination a * ha + a * h3

private lemma ggQ2xFN_isometry {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0) (u v : GGBCV n) :
    (ggBCRefl z hz).toFun u ⬝ᵥ (ggBCRefl z hz).toFun v = u ⬝ᵥ v := by
  rw [ggQ2_DW_bc_apply, ggQ2_DW_bc_apply]
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm u z]
  have h0 : z ⬝ᵥ u * (z ⬝ᵥ z) * (z ⬝ᵥ v)
      + z ⬝ᵥ v * (z ⬝ᵥ z) * (z ⬝ᵥ u + z ⬝ᵥ u * (z ⬝ᵥ z) * (z ⬝ᵥ z)) = 0 := by
    linear_combination (z ⬝ᵥ u * (z ⬝ᵥ v)) *
      ggQ2xFN_alg (z ⬝ᵥ z) (ggQ2_DW_sq (z ⬝ᵥ z) hz)
  rw [add_assoc, h0, add_zero]



private lemma ggQ2xFN_isometry' {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0) (u v : GGBCV n) :
    ggBCRefl z hz u ⬝ᵥ ggBCRefl z hz v = u ⬝ᵥ v := by
  change (ggBCRefl z hz).toFun u ⬝ᵥ (ggBCRefl z hz).toFun v = _
  exact ggQ2xFN_isometry z hz u v


private lemma ggQ2xFN_wt_smul {n : ℕ} (v : GGBCV n) (μ : ZMod 3) (hμ : μ ≠ 0) :
    ggBCWt (μ • v) = ggBCWt v := by
  rw [ggBCWt, ggBCWt]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hμ, h⟩⟩

private lemma ggQ2xFN_root_smul {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRoots n := by
  simp only [ggBCRoots, Set.mem_setOf_eq] at hv ⊢
  rw [ggQ2xFN_wt_smul v μ hμ]
  exact hv

private lemma ggQ2xFN_lam1_smul {n : ℕ} [NeZero n] {v : GGBCV n} (hv : v ∈ ggBCRootsLam1 n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRootsLam1 n := by
  simp only [ggBCRootsLam1, Set.mem_setOf_eq] at hv ⊢
  refine ⟨ggQ2xFN_root_smul hv.1 μ hμ, ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hv.2, mul_zero]

private lemma ggQ2xFN_lamN_smul {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRootsLamN n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRootsLamN n := by
  simp only [ggBCRootsLamN, Set.mem_setOf_eq] at hv ⊢
  refine ⟨?_, ?_⟩
  · rw [ggQ2xFN_wt_smul v μ hμ, hv.1]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hv.2, mul_zero]

private lemma ggQ2xFN_wt_single_of_ne_zero {n : ℕ} (i : Fin n) (s : ZMod 3) (hs : s ≠ 0) :
    ggBCWt (Pi.single i s : GGBCV n) = 1 := by
  unfold ggBCWt
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hne
    exact hj (Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne s)
  · rintro rfl
    rw [Pi.single_eq_same]
    exact hs

private lemma ggQ2xFN_wt_eq_one_iff {n : ℕ} {v : GGBCV n} :
    ggBCWt v = 1 ↔ ∃ i s, s ≠ 0 ∧ v = Pi.single i s := by
  constructor
  · intro hv
    unfold ggBCWt at hv
    obtain ⟨i, h⟩ := Finset.card_eq_one.mp hv
    refine ⟨i, v i, ?_, ?_⟩
    · have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
        rw [h]; exact Finset.mem_singleton_self i
      simpa using this
    · ext k
      by_cases hk : k = i
      · subst hk; rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
        have : k ∉ Finset.univ.filter (fun l => v l ≠ 0) := by
          rw [h]; simp [hk]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using this
  · rintro ⟨i, s, hs, rfl⟩
    exact ggQ2xFN_wt_single_of_ne_zero i s hs

private lemma ggQ2xFN_root_dot_ne_zero {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n) :
    v ⬝ᵥ v ≠ 0 := by
  simp only [ggBCRoots, Set.mem_setOf_eq] at hv
  rw [ggQ2_DW_A_dot_self_eq_wt]
  have hw : ggBCWt v = 1 ∨ ggBCWt v = 2 := by
    have h1 : 1 ≤ ggBCWt v := hv.1
    have h2 : ggBCWt v ≤ 2 := hv.2
    omega
  rcases hw with h | h <;> rw [h] <;> decide


private lemma ggQ2xFN_bc_apply_self {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc c = -c := by
  rw [ggQ2_DW_bc_apply']
  rw [ggQ2_DW_sq (c ⬝ᵥ c) hc, one_smul]
  rw [← two_smul (ZMod 3) c]
  rw [show (2 : ZMod 3) = -1 by decide]
  exact neg_one_smul (ZMod 3) c

private lemma ggQ2xFN_bc_eq_span {n : ℕ} (c d : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (hd : d ⬝ᵥ d ≠ 0)
    (heq : ggBCRefl c hc = ggBCRefl d hd) :
    c ∈ Submodule.span (ZMod 3) {d} := by
  refine Submodule.mem_span_singleton.mpr ⟨(d ⬝ᵥ c) * (d ⬝ᵥ d), ?_⟩
  have h := congrArg (fun e : GGBCV n ≃ₗ[ZMod 3] GGBCV n => e c) heq
  rw [ggQ2xFN_bc_apply_self c hc, ggQ2_DW_bc_apply' d hd c] at h
  change ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = c
  have h1 : (2 : ZMod 3) • c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = 0 := by
    rw [two_smul]
    calc c + c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d
        = c + (c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d) := by rw [add_assoc]
      _ = c + (-c) := by rw [← h]
      _ = 0 := add_neg_cancel c
  have h2 : ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = -((2 : ZMod 3) • c) :=
    eq_neg_of_add_eq_zero_right h1
  have h2c : (2 : ZMod 3) • c = -c := by
    rw [show (2 : ZMod 3) = -1 by decide]
    exact neg_one_smul (ZMod 3) c
  rw [h2c] at h2
  rw [h2]
  exact neg_neg c


private lemma ggQ2xFN_conj_reflection {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {ψ : Dual K V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[K] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xFN_isReflLin_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (a t : V ≃ₗ[ZMod 3] V) (ht : IsReflLin t) : IsReflLin (a * t * a⁻¹) := by
  obtain ⟨cc, ψ, hψ, rfl⟩ := ht
  refine ⟨a cc, ψ.comp (a.symm : V →ₗ[ZMod 3] V), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hψ
  · rw [show a⁻¹ = a.symm from rfl]
    exact ggQ2xFN_conj_reflection a hψ


private lemma ggQ2xFN_isReflLin_bc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2_DW_Dualc n), ?_, ?_⟩
  · change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) c) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  · rfl


private lemma ggQ2xFN_refl_conj_isom {n : ℕ} (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0)
    (ha : ∀ u v, (a u) ⬝ᵥ (a v) = u ⬝ᵥ v) :
    ∃ hz' : (a z) ⬝ᵥ (a z) ≠ 0, a * ggBCRefl z hz * a.symm = ggBCRefl (a z) hz' := by
  have haz : (a z) ⬝ᵥ (a z) ≠ 0 := by rw [ha z z]; exact hz
  refine ⟨haz, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2_DW_bc_apply', ggQ2_DW_bc_apply',
    map_add, LinearEquiv.apply_symm_apply, map_smul]
  have h1 : (a z) ⬝ᵥ v = z ⬝ᵥ a.symm v := by
    calc (a z) ⬝ᵥ v = (a z) ⬝ᵥ a (a.symm v) := by rw [LinearEquiv.apply_symm_apply]
      _ = z ⬝ᵥ a.symm v := ha z (a.symm v)
  have h2 : (a z) ⬝ᵥ (a z) = z ⬝ᵥ z := ha z z
  rw [h1, h2]

private lemma ggQ2xFN_refl_eq_bc {n : ℕ} {c : GGBCV n}
    {φ : Module.Dual (ZMod 3) (GGBCV n)} (hφ : φ c = 2) (ε : ZMod 3)
    (hφv : ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∃ hc : c ⬝ᵥ c ≠ 0, Module.reflection hφ = ggBCRefl c hc := by
  have hc : c ⬝ᵥ c ≠ 0 := by
    intro h0
    have h := hφv c
    rw [hφ, h0, mul_zero] at h
    exact two_ne_zero_of_charP_three h
  refine ⟨hc, ?_⟩
  have he : ε = 2 / (c ⬝ᵥ c) := by
    have h : ε * (c ⬝ᵥ c) = 2 := by
      rw [← hφv c, hφ]
    field_simp
    exact h
  let ψ : Module.Dual (ZMod 3) (GGBCV n) := (2 / (c ⬝ᵥ c)) • ggBCDot c
  have hf : φ = ψ := by
    apply LinearMap.ext
    intro v
    rw [hφv v, LinearMap.smul_apply, ggQ2_DW_dot_apply, he, smul_eq_mul]
  subst φ
  rfl


private lemma ggQ2xFN_root_ne_zero {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n) :
    v ≠ 0 := by
  intro h0
  simp only [ggBCRoots, Set.mem_setOf_eq, h0, ggBCWt, Pi.zero_apply, ne_eq,
    not_true_eq_false, Finset.filter_false, Finset.card_empty] at hv
  omega

private lemma ggQ2xFN_dot_single {n : ℕ} [NeZero n] (z : GGBCV n) (i : Fin n) (a : ZMod 3) :
    z ⬝ᵥ Pi.single i a = z i * a := by
  rw [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xFN_dot_one {n : ℕ} (z : GGBCV n) :
    z ⬝ᵥ (fun _ => (1 : ZMod 3)) = ∑ i, z i := by
  simp [dotProduct]



private noncomputable def ggQ2xFN_sgn (p m : ℕ) (j : Fin m) : ZMod p :=
  if (j:ℕ) = 0 ∨ (j:ℕ) = m-1 then (-1:ZMod p) else 1

private noncomputable def ggQ2xFN_H (p m : ℕ) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) where
  toFun v := fun j => ggQ2xFN_sgn p m j * v j
  invFun v := fun j => ggQ2xFN_sgn p m j * v j
  left_inv v := by
    funext j
    by_cases h : (j:ℕ) = 0 ∨ (j:ℕ) = m-1
    · simp only [ggQ2xFN_sgn, if_pos h]; ring
    · simp only [ggQ2xFN_sgn, if_neg h]; ring
  right_inv v := by
    funext j
    by_cases h : (j:ℕ) = 0 ∨ (j:ℕ) = m-1
    · simp only [ggQ2xFN_sgn, if_pos h]; ring
    · simp only [ggQ2xFN_sgn, if_neg h]; ring
  map_add' u v := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma ggQ2xFN_H_apply (p m : ℕ) (v : Fin m → ZMod p) (j : Fin m) :
    ggQ2xFN_H p m v j = ggQ2xFN_sgn p m j * v j := rfl

private lemma ggQ2xFN_H_fvec (p m : ℕ) (k : Fin m) :
    ggQ2xFN_H p m (ggQ2_DW_fvec p m k) = ggQ2xFN_sgn p m k • ggQ2_DW_fvec p m k := by
  funext j
  rw [ggQ2xFN_H_apply, Pi.smul_apply]
  by_cases hjk : j = k
  · subst hjk; simp [ggQ2_DW_fvec, Pi.single_eq_same]
  · simp [ggQ2_DW_fvec, Pi.single_eq_of_ne hjk]

private lemma ggQ2xFN_H_u_fix (p m : ℕ) (i : Fin m) (hi1 : 1 ≤ (i:ℕ)) (hi3 : (i:ℕ)+3 ≤ m) :
    ggQ2xFN_H p m (ggDSimple p m i) = ggDSimple p m i := by
  funext j
  simp only [ggQ2xFN_H_apply, ggQ2xFN_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xFN_H_u_m2 (p m : ℕ) (hm : 4 ≤ m) :
    ggQ2xFN_H p m (ggDSimple p m ⟨m-2, by omega⟩) =
      ggDSimple p m ⟨m-1, by omega⟩ := by
  funext j
  simp only [ggQ2xFN_H_apply, ggQ2xFN_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xFN_H_u_m1 (p m : ℕ) (hm : 4 ≤ m) :
    ggQ2xFN_H p m (ggDSimple p m ⟨m-1, by omega⟩) =
      ggDSimple p m ⟨m-2, by omega⟩ := by
  funext j
  simp only [ggQ2xFN_H_apply, ggQ2xFN_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xFN_dotLin_add_left (p m : ℕ) (u w v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (u + w) v = ggQ2_DW_dotLin p m u v + ggQ2_DW_dotLin p m w v := by
  simp only [ggQ2_DW_dotLin_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by simp only [Pi.add_apply]; ring)

private lemma ggQ2xFN_dotLin_fvec_fvec (p m : ℕ) (a b : Fin m) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a) (ggQ2_DW_fvec p m b) =
      if a = b then (1:ZMod p) else 0 := by
  rw [ggQ2_DW_dotLin_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp [ggQ2_DW_fvec]
    · intro c _ hc; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · rw [if_neg h, Finset.sum_eq_single a]
    · rw [ggQ2_DW_fvec, ggQ2_DW_fvec, Pi.single_eq_same, Pi.single_eq_of_ne h]
      ring
    · intro c _ hc; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh

private lemma ggQ2xFN_dotLin_fvec (p m : ℕ) (u : Fin m → ZMod p) (k : Fin m) :
    ggQ2_DW_dotLin p m u (ggQ2_DW_fvec p m k) = u k := by
  rw [ggQ2_DW_dotLin_apply, Finset.sum_eq_single k]
  · simp [ggQ2_DW_fvec]
  · intro b _ hb; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma ggQ2xFN_dotLin_fvec_add (p m : ℕ) (a b : Fin m) (v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a + ggQ2_DW_fvec p m b) v = v a + v b := by
  rw [ggQ2xFN_dotLin_add_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

private noncomputable def ggQ2xFN_s (p m : ℕ) (c : Fin m → ZMod p)
    (hc : ggQ2_DW_dotLin p m c c = 2) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) :=
  Module.reflection (x := c) hc

private lemma ggQ2xFN_s_apply (p m : ℕ) (c : Fin m → ZMod p)
    (hc : ggQ2_DW_dotLin p m c c = 2) (v : Fin m → ZMod p) :
    ggQ2xFN_s p m c hc v = v - (ggQ2_DW_dotLin p m c v) • c :=
  Module.reflection_apply v hc

private lemma ggQ2xFN_dconj_reflection (p m : ℕ)
    (P : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p))
    (c : Fin m → ZMod p) (hc : ggQ2_DW_dotLin p m c c = 2)
    (hP : ∀ u v, ggQ2_DW_dotLin p m (P u) (P v) = ggQ2_DW_dotLin p m u v) :
    P * ggQ2xFN_s p m c hc * P.symm = ggQ2xFN_s p m (P c) (by rw [hP c c, hc]) := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2xFN_s_apply, ggQ2xFN_s_apply,
    map_sub, map_smul, LinearEquiv.apply_symm_apply]
  rw [← hP c (P.symm v), LinearEquiv.apply_symm_apply]

private lemma ggQ2xFN_dot_sub_self (p m : ℕ) (a b : Fin m) (hab : a ≠ b) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a - ggQ2_DW_fvec p m b)
      (ggQ2_DW_fvec p m a - ggQ2_DW_fvec p m b) = 2 := by
  rw [map_sub, ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_sub_left]
  simp only [ggQ2xFN_dotLin_fvec_fvec, if_true, if_false]
  rw [if_neg hab, if_neg (Ne.symm hab)]
  ring

private lemma ggQ2xFN_dot_add_self (p m : ℕ) (a b : Fin m) (hab : a ≠ b) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a + ggQ2_DW_fvec p m b)
      (ggQ2_DW_fvec p m a + ggQ2_DW_fvec p m b) = 2 := by
  rw [map_add, ggQ2xFN_dotLin_add_left, ggQ2xFN_dotLin_add_left]
  simp only [ggQ2xFN_dotLin_fvec_fvec, if_true, if_false]
  rw [if_neg hab, if_neg (Ne.symm hab)]
  ring

private lemma ggQ2xFN_dot_opp (p m : ℕ) (hm : 2 ≤ m) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m ⟨0, by omega⟩ - ggQ2_DW_fvec p m ⟨m-1, by omega⟩)
      (ggQ2_DW_fvec p m ⟨0, by omega⟩ + ggQ2_DW_fvec p m ⟨m-1, by omega⟩) = 0 := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨m-1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [ggQ2_DW_dotLin_sub_left, map_add, map_add, ggQ2xFN_dotLin_fvec_fvec,
    ggQ2xFN_dotLin_fvec_fvec, ggQ2xFN_dotLin_fvec_fvec, ggQ2xFN_dotLin_fvec_fvec]
  simp only [if_true, if_false]
  rw [if_neg hne, if_neg (Ne.symm hne)]
  ring

private lemma ggQ2xFN_H_eq_reflections (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2xFN_H p m =
      ggQ2xFN_s p m (ggQ2_DW_fvec p m ⟨0, by omega⟩ - ggQ2_DW_fvec p m ⟨m-1, by omega⟩)
        (ggQ2xFN_dot_sub_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) *
      ggQ2xFN_s p m (ggQ2_DW_fvec p m ⟨0, by omega⟩ + ggQ2_DW_fvec p m ⟨m-1, by omega⟩)
        (ggQ2xFN_dot_add_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨m-1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  ext v j
  rw [ggQ2xFN_H_apply, LinearEquiv.mul_apply, ggQ2xFN_s_apply, ggQ2xFN_s_apply,
    ggQ2xFN_dotLin_fvec_add]
  have hd : ggQ2_DW_dotLin p m
      (ggQ2_DW_fvec p m ⟨0, by omega⟩ - ggQ2_DW_fvec p m ⟨m-1, by omega⟩)
      (v - (v ⟨0, by omega⟩ + v ⟨m-1, by omega⟩) •
        (ggQ2_DW_fvec p m ⟨0, by omega⟩ + ggQ2_DW_fvec p m ⟨m-1, by omega⟩)) =
      v ⟨0, by omega⟩ - v ⟨m-1, by omega⟩ := by
    rw [map_sub, map_smul, ggQ2_DW_dotLin_fvec_sub, ggQ2xFN_dot_opp p m (by omega)]
    ring
  rw [hd]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ggQ2_DW_fvec, Pi.add_apply,
    Pi.single_eq_same, Pi.sub_apply]
  by_cases h0 : j = ⟨0, by omega⟩
  · subst h0
    have h' : ¬ (⟨0, by omega⟩ : Fin m) = ⟨m-1, by omega⟩ := hne
    simp [Pi.single_eq_of_ne (Ne.symm h'), h', ggQ2xFN_sgn]
    ring
  · by_cases h1 : j = ⟨m-1, by omega⟩
    · subst h1
      simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne (Ne.symm hne), ggQ2xFN_sgn]
      ring
    · have hj0 : (j:ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      have hj1 : (j:ℕ) ≠ m-1 := fun h => h1 (Fin.ext h)
      simp [Pi.single_eq_of_ne (by exact fun h => h0 h),
        Pi.single_eq_of_ne (by exact fun h => h1 h), ggQ2xFN_sgn, hj0, hj1]


private noncomputable def ggQ2xFN_conj {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p)) :
    (D.V ≃ₗ[ZMod p] D.V) ≃* ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) where
  toFun g := τ.symm.trans (g.trans τ)
  invFun k := τ.trans (k.trans τ.symm)
  left_inv g := by ext x; simp [LinearEquiv.trans_apply]
  right_inv k := by ext y; simp [LinearEquiv.trans_apply]
  map_mul' g h := by ext y; simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply]

private lemma ggQ2xFN_conj_simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j)
    (i : Fin m) :
    ggQ2xFN_conj D τ (D.simpleRefl (e i)) = ggQ2_DW_r p m hm i := by
  apply LinearEquiv.ext
  intro y
  change τ (D.simpleRefl (e i) (τ.symm y)) = ggQ2_DW_r p m hm i y
  rw [ggQ2_DW_r_apply, ggQ2_DW_dotLin_apply]
  have hsr : D.simpleRefl (e i) (τ.symm y) =
      τ.symm y - (D.root (e i) (τ.symm y)) • D.coroot (e i) := by
    rw [show D.simpleRefl (e i) = Module.reflection (D.root_coroot_self (e i)) from rfl,
      Module.reflection_apply]
  rw [hsr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hτ i, hroot i (τ.symm y),
    LinearEquiv.apply_symm_apply]

private lemma ggQ2xFN_weylMap {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j) :
    (D.weyl).map (ggQ2xFN_conj D τ).toMonoidHom = ggQ2_DW_Wc p m hm := by
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, -, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    exact ⟨i, (ggQ2xFN_conj_simpleRefl D hm e τ hτ hroot i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D.simpleRefl (e i), ⟨e i, Set.mem_univ _, rfl⟩,
      ggQ2xFN_conj_simpleRefl D hm e τ hτ hroot i⟩


private lemma ggQ2xFN_Wt_single {n : ℕ} (i : Fin n) (x : ZMod 3) (hx : x ≠ 0) :
    ggBCWt (Pi.single i x : GGBCV n) = 1 := by
  unfold ggBCWt
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases hji : j = i
  · subst hji; simp [Pi.single_eq_same, hx]
  · simp [Pi.single_eq_of_ne hji, hji]

private lemma ggQ2xFN_scalar_b : ∀ x y : ZMod 3, x + x * -1 - y * -1 = y := by decide

private lemma ggQ2xFN_Q_mem_chain (p m : ℕ) (hm : 4 ≤ m) (σ : Equiv.Perm (Fin m)) :
    ggQ2_DW_Q p m σ ∈ Subgroup.closure
      (Set.range (fun i : {i : Fin m // (i : ℕ) ≠ m - 1} => ggQ2_DW_r p m hm i.1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hle : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤
      (Subgroup.closure
        (Set.range (fun i : {i : Fin (n + 1) // (i : ℕ) ≠ n} =>
          ggQ2_DW_r p (n + 1) hm i.1))).comap (ggQ2_DW_Q p (n + 1)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hi : (i.castSucc : Fin (n + 1)).val + 1 < n + 1 := by
      simp only [Fin.val_castSucc]; omega
    change ggQ2_DW_Q p (n + 1) (Equiv.swap i.castSucc i.succ) ∈
      Subgroup.closure (Set.range (fun i : {i : Fin (n + 1) // (i : ℕ) ≠ n} =>
        ggQ2_DW_r p (n + 1) hm i.1))
    have hidx : i.succ = (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc]
    rw [hidx, ← ggQ2_DW_r_eq_swap p (n + 1) hm i.castSucc hi]
    exact Subgroup.subset_closure
      ⟨⟨i.castSucc, by simp only [Fin.val_castSucc]; omega⟩, rfl⟩
  have htop : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  have hσ : σ ∈ Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
    rw [htop]; exact Subgroup.mem_top σ
  exact hle hσ

private lemma ggQ2xFN_sum_single {m : ℕ} (k : Fin m) (a : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m)) i = a := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_pi_single', mul_one]

private lemma ggQ2xFN_sum_pair {m : ℕ} (k l : Fin m) (a b : ZMod 3) :
    ∑ i, (a • (Pi.single k 1 : GGBCV m) + b • (Pi.single l 1 : GGBCV m)) i = a + b := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2xFN_sum_single, ggQ2xFN_sum_single]

private lemma ggQ2xFN_aroots_classify {m : ℕ} {v : GGBCV m} (hv : v ∈ ggARoots m) :
    ∃ (i j : Fin m), i ≠ j ∧ ∃ a : ZMod 3, a ≠ 0 ∧
      v = a • (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
  obtain ⟨hw, hsum⟩ := hv
  obtain ⟨i, j, a, b, hij, ha, hb, hvij⟩ := ggQ2_DW_weight_two hw
  have hab : a + b = 0 := by
    rw [hvij] at hsum
    rw [ggQ2xFN_sum_pair] at hsum
    exact hsum
  refine ⟨i, j, hij, a, ha, ?_⟩
  have hb_eq : b = -a := (neg_eq_of_add_eq_zero_right hab).symm
  rw [hvij, hb_eq, smul_sub, sub_eq_add_neg]
  congr 1
  exact neg_smul a (Pi.single j 1 : GGBCV m)

private theorem ggQ2xFN_cartan_symm {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (e : Fin m ≃ D.ι) (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) :
    ∀ i j : D.ι, D.cartan i j = D.cartan j i := by
  intro i j
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  rw [ggQ2_DW_cartan_D D e he i' j', ggQ2_DW_cartan_D D e he j' i']
  exact ((CartanMatrix.D_isSymm m).apply i' j').symm

private lemma ggQ2xFN_refl_smul {n : ℕ} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hlc : (l • c) ⬝ᵥ (l • c) ≠ 0) :
    ggBCRefl (l • c) hlc = ggBCRefl c hc := by
  rcases ggQ2_DW_eq_one_or_neg_one l hl with rfl | rfl
  · exact ggQ2_DW_refl_congr (one_smul (ZMod 3) c) hlc hc
  · exact (ggQ2_DW_refl_congr (neg_one_smul (ZMod 3) c) hlc
      (by rw [ggQ2_DW_neg_dot_self]; exact hc)).trans (ggQ2_DW_refl_neg c hc _)

private lemma ggQ2xFN_sum_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ∑ i, ((Pi.single a (1 : ZMod 3) : GGBCV n) - (Pi.single b (1 : ZMod 3) : GGBCV n)) i
      = 0 := by
  have h : (Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b (1 : ZMod 3) =
      (1 : ZMod 3) • (Pi.single a 1 : GGBCV n) + (-1 : ZMod 3) • (Pi.single b 1 : GGBCV n) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    exact (ggQ2_DW_scalar_f ((Pi.single a (1 : ZMod 3) : GGBCV n) i)
      ((Pi.single b (1 : ZMod 3) : GGBCV n) i)).symm
  rw [h, ggQ2xFN_sum_pair a b (1 : ZMod 3) (-1 : ZMod 3)]
  decide

private lemma ggQ2xFN_dsimple_chain {m : ℕ} (i : Fin m) (hlt : (i : ℕ) + 1 < m) :
    ggDSimple 3 m i =
      (Pi.single i (1 : ZMod 3) : GGBCV m) -
        (Pi.single ⟨(i : ℕ) + 1, hlt⟩ (1 : ZMod 3) : GGBCV m) := by
  funext l
  simp only [ggDSimple, hlt, if_true, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> simp_all

private lemma ggQ2xFN_dsimple_mem_aroots {m : ℕ} (i : Fin m) (hi : (i : ℕ) ≠ m - 1) :
    ggDSimple 3 m i ∈ ggARoots m := by
  have hlt : (i : ℕ) + 1 < m := by have := i.isLt; omega
  have hv := ggQ2xFN_dsimple_chain i hlt
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact ggQ2_DW_Wt_sub_single i ⟨(i : ℕ) + 1, hlt⟩ (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
  · have hsum := ggQ2_DW_sum_ggDSimple 3 m i hlt (fun _ : Fin m => (1 : ZMod 3))
    simpa using hsum

private lemma ggQ2xFN_parab_eq (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (ha : D.a = e ⟨m - 1, by omega⟩) :
    Subgroup.map (ggLinConj τ).toMonoidHom (D.parab {k | k ≠ D.a}) =
      ggBCReflGp (ggARoots m) := by
  have hm4 : 4 ≤ m := by omega
  have hmap : Subgroup.map (ggLinConj τ).toMonoidHom (D.parab {k | k ≠ D.a}) =
      Subgroup.closure (Set.range (fun i : {i : Fin m // (i : ℕ) ≠ m - 1} =>
        ggQ2_DW_r 3 m hm4 i.1)) := by
    rw [GGQ2Lin.parab, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
      obtain ⟨i0, rfl⟩ := e.surjective k
      have hi : (i0 : ℕ) ≠ m - 1 := by
        intro h
        exact hk (by rw [ha]; exact congrArg e (Fin.ext h))
      exact ⟨⟨i0, hi⟩, (ggQ2_DW_linConj_simpleRefl D hm4 e τ hτ hroot i0).symm⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨D.simpleRefl (e i), ⟨e i, ?_, rfl⟩,
        ggQ2_DW_linConj_simpleRefl D hm4 e τ hτ hroot i⟩
      rw [ha]
      intro h
      exact hi (by have := congrArg Fin.val (e.injective h); simpa using this)
  rw [hmap]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro t ⟨⟨i, hi⟩, rfl⟩
    change ggQ2_DW_r 3 m hm4 i ∈ ggBCReflGp (ggARoots m)
    rw [ggQ2_DW_r_eq_bc hm4 i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 m i, ggQ2xFN_dsimple_mem_aroots i hi,
        by rw [ggQ2_DW_simple_norm hm4 i]; decide, rfl⟩
  · rw [ggBCReflGp, Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    obtain ⟨i, j, hij, a, ha_ne, hc_eq⟩ := ggQ2xFN_aroots_classify hc
    subst hc_eq
    have hcsub : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
        ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0 := by
      rw [ggQ2_DW_sub_norm i j hij]; decide
    rw [ggQ2xFN_refl_smul a ha_ne _ hcsub hcc,
      ggQ2_DW_sub_refl_eq_swap i j hij hcsub]
    exact ggQ2xFN_Q_mem_chain 3 m hm4 (Equiv.swap i j)

private lemma ggQ2xFN_fixed_aroots {m : ℕ} (hm : 5 ≤ m) (v : GGBCV m) :
    (∀ g ∈ ggBCReflGp (ggARoots m), g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} := by
  constructor
  · intro hv
    have hdiff_mem : ∀ a b : Fin m, a ≠ b →
        ((Pi.single a (1 : ZMod 3) : GGBCV m) - Pi.single b 1) ∈ ggARoots m := by
      intro a b hab
      exact ⟨ggQ2_DW_Wt_sub_single a b hab, ggQ2xFN_sum_sub_single a b hab⟩
    have hconst : ∀ a b : Fin m, v a = v b := by
      intro a b
      by_cases hab : a = b
      · subst hab; rfl
      · have hcsub : ((Pi.single a (1 : ZMod 3) : GGBCV m) - Pi.single b 1) ⬝ᵥ
            ((Pi.single a (1 : ZMod 3) : GGBCV m) - Pi.single b 1) ≠ 0 := by
          rw [ggQ2_DW_sub_norm a b hab]; decide
        have hmem : ggQ2_DW_Q 3 m (Equiv.swap a b) ∈ ggBCReflGp (ggARoots m) := by
          rw [ggBCReflGp]
          exact Subgroup.subset_closure
            ⟨_, hdiff_mem a b hab, hcsub, (ggQ2_DW_sub_refl_eq_swap a b hab hcsub).symm⟩
        have hfixv := hv (ggQ2_DW_Q 3 m (Equiv.swap a b)) hmem
        have hval := congrArg (fun w : GGBCV m => w a) hfixv
        rw [ggQ2_DW_Q_apply, Equiv.symm_swap, Equiv.swap_apply_left] at hval
        exact hval.symm
    rw [Submodule.mem_span_singleton]
    refine ⟨v ⟨0, by omega⟩, ?_⟩
    funext i
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact hconst ⟨0, by omega⟩ i
  · rintro hvsp
    rw [Submodule.mem_span_singleton] at hvsp
    obtain ⟨a, rfl⟩ := hvsp
    have hbase : ∀ t ∈ ggBCReflSet (ggARoots m),
        t (fun _ : Fin m => (1 : ZMod 3)) = (fun _ : Fin m => (1 : ZMod 3)) := by
      rintro t ⟨c, hcroot, hc, rfl⟩
      rw [ggQ2_DW_bc_apply']
      have hdot : c ⬝ᵥ (fun _ : Fin m => (1 : ZMod 3)) = 0 := by
        rw [show c ⬝ᵥ (fun _ : Fin m => (1 : ZMod 3)) = ∑ i, c i by
          simp only [dotProduct, Pi.one_apply, mul_one]]
        exact hcroot.2
      rw [hdot, zero_mul, zero_smul, add_zero]
    have hfix : ∀ g ∈ ggBCReflGp (ggARoots m),
        g (fun _ : Fin m => (1 : ZMod 3)) = (fun _ : Fin m => (1 : ZMod 3)) := by
      intro g hg
      rw [ggBCReflGp] at hg
      refine Subgroup.closure_induction (fun x hx => hbase x hx) ?_ ?_ ?_ hg
      · rfl
      · intro x y hx hy ihx ihy
        rw [LinearEquiv.mul_apply, ihy, ihx]
      · intro x hx ihx
        change x.symm (fun _ : Fin m => (1 : ZMod 3)) = (fun _ : Fin m => (1 : ZMod 3))
        have h := congrArg (fun w => x.symm w) ihx
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm
    intro g hg
    rw [map_smul, hfix g hg]

private lemma ggQ2xFN_S1 (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A.map (ggLinConj τ).toMonoidHom →
      ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v) := by
  intro c φ h ht
  obtain ⟨ε, hε, hφv⟩ := ggQ2_S1_transport D hbas
    (by rw [← Fintype.card_congr e, Fintype.card_fin]; omega)
    (ggQ2xFN_cartan_symm D e hD) τ (ggQ2_DW_dotBilin m)
    (ggQ2_DW_hB' D hbas (by omega) e hD τ hτ) A hW hTF h ht
  refine ⟨ε, hε, fun v => ?_⟩
  rw [hφv v, ggQ2_DW_dotBilin_apply]

private lemma ggQ2xFN_reflSet_eq (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ggReflSet (A.map (ggLinConj τ).toMonoidHom) =
      ggBCReflSet {z : GGBCV m |
        ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  ext t
  constructor
  · rintro ⟨htA, c, φ, hφ, rfl⟩
    obtain ⟨ε, hε, hφv⟩ := ggQ2xFN_S1 D hbas hm e hD τ hτ A hW hTF c φ hφ htA
    obtain ⟨hc, heq⟩ := ggQ2xFN_refl_eq_bc hφ ε hφv
    exact ⟨c, ⟨hc, heq ▸ htA⟩, hc, heq⟩
  · rintro ⟨c, ⟨hc, hcA⟩, hc', rfl⟩
    refine ⟨?_, ggQ2xFN_isReflLin_bc c hc'⟩
    rw [show ggBCRefl c hc' = ggBCRefl c hc from ggQ2_DW_refl_congr rfl hc' hc]
    exact hcA

private lemma ggQ2xFN_tau_x (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (ha : D.a = e ⟨m - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    Submodule.span (ZMod 3) {τ x} =
      Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} := by
  have hparab := ggQ2xFN_parab_eq D hbas hm e hD τ hτ hroot ha
  have hsub : Submodule.span (ZMod 3) {τ x} ≤
      Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change τ x ∈ Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))}
    rw [← (ggQ2xFN_fixed_aroots hm (τ x))]
    intro g hg
    have hg' : g ∈ Subgroup.map (ggLinConj τ).toMonoidHom (D.parab {k | k ≠ D.a}) := by
      rw [hparab]; exact hg
    obtain ⟨g', hg'P, rfl⟩ := Subgroup.mem_map.mp hg'
    have hfix : g' x = x := ((hx x).mpr (Submodule.mem_span_singleton_self x)) g' hg'P
    change (ggLinConj τ g') (τ x) = τ x
    rw [ggLinConj_apply, LinearEquiv.symm_apply_apply, hfix]
  refine le_antisymm hsub ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have hfix : ∀ t ∈ ggBCReflGp (ggARoots m),
      t (fun _ : Fin m => (1 : ZMod 3)) = (fun _ : Fin m => (1 : ZMod 3)) :=
    (ggQ2xFN_fixed_aroots hm (fun _ : Fin m => (1 : ZMod 3))).mpr
      (Submodule.mem_span_singleton_self _)
  have hpre : τ.symm (fun _ : Fin m => (1 : ZMod 3)) ∈ Submodule.span (ZMod 3) {x} := by
    rw [← hx]
    intro g hg
    have hg' : ggLinConj τ g ∈ ggBCReflGp (ggARoots m) := by
      rw [← hparab]; exact ⟨g, hg, rfl⟩
    have hthis := hfix (ggLinConj τ g) hg'
    rw [ggLinConj_apply] at hthis
    apply τ.injective
    rw [hthis, LinearEquiv.apply_symm_apply]
  obtain ⟨a, ha'⟩ := Submodule.mem_span_singleton.mp hpre
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  have : a • τ x = τ (a • x) := by rw [map_smul]
  rw [this, ha', LinearEquiv.apply_symm_apply]

private lemma ggQ2xFN_HL (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (ha : D.a = e ⟨m - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) := by
  have hspan := ggQ2xFN_tau_x D hbas hm e hD τ hτ hroot ha x hx
  have hparab := ggQ2xFN_parab_eq D hbas hm e hD τ hτ hroot ha
  intro φ hφ hφone
  have hτx : τ x ∈ Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} := by
    rw [← hspan]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hτx
  have hφτ : φ (τ x) ∈ Submodule.span (ZMod 3) {τ x} := by
    rw [hspan, ← hc, map_smul]
    exact Submodule.smul_mem _ c hφone
  have hmem := (ggLinConj_HL τ A (D.parab {k | k ≠ D.a}) x).mpr hHL φ hφ hφτ
  rwa [hparab] at hmem

private lemma ggQ2xFN_hZroots (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) :
    ggDRoots m ⊆ {z : GGBCV m |
      ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  intro z hz
  have hz0 : z ⬝ᵥ z ≠ 0 := by
    rw [ggQ2_DW_A_dot_self_eq_wt, show ggBCWt z = 2 from hz]; decide
  refine ⟨hz0, ?_⟩
  exact ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW
    (Subgroup.subset_closure ⟨z, hz, hz0, rfl⟩)

private lemma ggQ2xFN_hZcl (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom},
      ∀ w ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom},
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈
        {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  intro z hzZ w hwZ hz
  obtain ⟨hw0, hwA⟩ := hwZ
  have hzA : ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom := by
    rw [show ggBCRefl z hz = ggBCRefl z hzZ.1 from ggQ2_DW_refl_congr rfl hz hzZ.1]
    exact hzZ.2
  let ee : ggQ2_DW_LEc m := ggQ2_DW_reflc z hz
  let ψ : ggQ2_DW_Dualc m := (2 / (w ⬝ᵥ w)) • (ggBCDot w : ggQ2_DW_Dualc m)
  have hψ : ψ w = 2 := by
    change (2 / (w ⬝ᵥ w)) * ((ggBCDot w : ggQ2_DW_Dualc m) w) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  let φ : ggQ2_DW_Dualc m := ψ.comp ee.symm.toLinearMap
  have hφ : φ (ee w) = 2 := by
    change ψ (ee.symm (ee w)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  have hconj : ee * Module.reflection hψ * ee.symm = Module.reflection hφ :=
    ggQ2xFN_conj_reflection ee hψ
  have htA : ee * Module.reflection hψ * ee.symm ∈ A.map (ggLinConj τ).toMonoidHom := by
    change ggBCRefl z hz * ggBCRefl w hw0 * (ggBCRefl z hz)⁻¹ ∈ A.map (ggLinConj τ).toMonoidHom
    exact (A.map (ggLinConj τ).toMonoidHom).mul_mem
      ((A.map (ggLinConj τ).toMonoidHom).mul_mem hzA hwA)
      ((A.map (ggLinConj τ).toMonoidHom).inv_mem hzA)
  have hreflA : Module.reflection hφ ∈ A.map (ggLinConj τ).toMonoidHom := by
    rw [← hconj]; exact htA
  obtain ⟨ε, hε, hφv⟩ := ggQ2xFN_S1 D hbas hm e hD τ hτ A hW hTF (ee w) φ hφ hreflA
  obtain ⟨hc, heq⟩ := ggQ2xFN_refl_eq_bc hφ ε hφv
  refine ⟨hc, ?_⟩
  change ggBCRefl (ee w) hc ∈ A.map (ggLinConj τ).toMonoidHom
  rw [← heq]
  exact hreflA

private lemma ggQ2xFN_hHL_Z (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    ∀ z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom},
      (∑ i, z i = 0) → ∀ ρ ∈ ggARoots m, ∀ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ρ ∈ ggARoots m := by
  intro z hzZ hzsum ρ hρ hz
  have hzA : ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom := by
    rw [show ggBCRefl z hz = ggBCRefl z hzZ.1 from ggQ2_DW_refl_congr rfl hz hzZ.1]
    exact hzZ.2
  have hfix : ggBCRefl z hz (fun _ : Fin m => (1 : ZMod 3)) ∈
      Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} := by
    rw [ggQ2_DW_bc_apply']
    have hdot : z ⬝ᵥ (fun _ : Fin m => (1 : ZMod 3)) = 0 := by
      rw [ggQ2xFN_dot_one]; exact hzsum
    rw [hdot, zero_mul, zero_smul, add_zero]
    exact Submodule.mem_span_singleton_self _
  have hnorm := hHL (ggBCRefl z hz) hzA hfix
  have hρwt : ggBCWt ρ = 2 := hρ.1
  have hρroot : ρ ∈ ggBCRoots m := by
    simp only [ggBCRoots, Set.mem_setOf_eq]
    exact ⟨by omega, by omega⟩
  have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := ggQ2xFN_root_dot_ne_zero hρroot
  have hρA : ggBCRefl ρ hρ0 ∈ A.map (ggLinConj τ).toMonoidHom :=
    ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW
      (Subgroup.subset_closure ⟨ρ, show ggBCWt ρ = 2 from hρ.1, hρ0, rfl⟩)
  let ee : ggQ2_DW_LEc m := ggQ2_DW_reflc z hz
  let ψ : ggQ2_DW_Dualc m := (2 / (ρ ⬝ᵥ ρ)) • (ggBCDot ρ : ggQ2_DW_Dualc m)
  have hψ : ψ ρ = 2 := by
    change (2 / (ρ ⬝ᵥ ρ)) * ((ggBCDot ρ : ggQ2_DW_Dualc m) ρ) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  let φ : ggQ2_DW_Dualc m := ψ.comp ee.symm.toLinearMap
  have hφ : φ (ee ρ) = 2 := by
    change ψ (ee.symm (ee ρ)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  have hconj : ee * Module.reflection hψ * ee.symm = Module.reflection hφ :=
    ggQ2xFN_conj_reflection ee hψ
  have htA : ee * Module.reflection hψ * ee.symm ∈ A.map (ggLinConj τ).toMonoidHom := by
    change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈
      A.map (ggLinConj τ).toMonoidHom
    exact (A.map (ggLinConj τ).toMonoidHom).mul_mem
      ((A.map (ggLinConj τ).toMonoidHom).mul_mem hzA hρA)
      ((A.map (ggLinConj τ).toMonoidHom).inv_mem hzA)
  have hreflA : Module.reflection hφ ∈ A.map (ggLinConj τ).toMonoidHom := by
    rw [← hconj]; exact htA
  have hconjΛ : Module.reflection hφ ∈ ggBCReflGp (ggARoots m) := by
    rw [← hconj]
    change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈ ggBCReflGp (ggARoots m)
    exact (Subgroup.mem_normalizer_iff.mp hnorm (ggBCRefl ρ hρ0)).mp
      (Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩)
  have htRefl : IsReflLin (Module.reflection hφ) := ⟨ee ρ, φ, hφ, rfl⟩
  obtain ⟨lam, hlam, hlam0, heqLam⟩ :=
    ggQ2_bc_LamN_refl m hm (Module.reflection hφ) hconjΛ htRefl
  obtain ⟨ε, hε, hφv⟩ := ggQ2xFN_S1 D hbas hm e hD τ hτ A hW hTF (ee ρ) φ hφ hreflA
  obtain ⟨hc, heqρ⟩ := ggQ2xFN_refl_eq_bc hφ ε hφv
  have heq : ggBCRefl (ee ρ) hc = ggBCRefl lam hlam0 := by rw [← heqρ, heqLam]
  have hspan : ee ρ ∈ Submodule.span (ZMod 3) {lam} :=
    ggQ2xFN_bc_eq_span (ee ρ) lam hc hlam0 heq
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
  have heρ_ne : ee ρ ≠ 0 := by
    intro h0
    have he0 : ee 0 = 0 := by
      change (ggBCRefl z hz) 0 = 0
      rw [ggQ2_DW_bc_apply']; simp
    have hρzero : ρ = 0 := by
      apply ee.injective
      rw [h0, he0]
    exact ggQ2xFN_root_ne_zero hρroot hρzero
  have hμne : μ ≠ 0 := by
    intro h0
    apply heρ_ne
    rw [← hμ, h0, zero_smul]
  have hres := ggQ2xFN_lamN_smul hlam μ hμne
  rw [hμ] at hres
  exact hres

private lemma ggQ2xFN_Z_wt_le_two (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    ∀ z ∈ {z : GGBCV m |
        ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom},
      ggBCWt z ≤ 2 :=
  ggQ2_D_Z_aN m hm _
    (fun z hz => hz.1)
    (ggQ2xFN_hZroots D hbas hm e hD τ hτ hroot A hW)
    (ggQ2xFN_hZcl D hbas hm e hD τ hτ A hW hTF)
    (ggQ2xFN_hHL_Z D hbas hm e hD τ hτ hroot A hW hTF hHL)

private lemma ggQ2xFN_Z_subset_roots (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆
      ggBCRoots m := by
  intro z hz
  have hwt := ggQ2xFN_Z_wt_le_two D hbas hm e hD τ hτ hroot A hW hTF hHL z hz
  have hne : ggBCWt z ≠ 0 := by
    intro h0
    have hz0 := hz.1
    rw [ggQ2_DW_A_dot_self_eq_wt, h0] at hz0
    exact hz0 rfl
  exact ⟨by omega, hwt⟩

private lemma ggQ2xFN_caseA (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)))
    (hZ : ggBCRoots m ⊆
      {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom})
    (u : GGBCV m) :
    ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ r ∈ reflGp (A.map (ggLinConj τ).toMonoidHom),
        Submodule.span (ZMod 3) {φ u} =
          Submodule.span (ZMod 3) {r u} := by
  have hZsub := ggQ2xFN_Z_subset_roots D hbas hm e hD τ hτ hroot A hW hTF hHL
  have hZeq : {z : GGBCV m |
      ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} = ggBCRoots m :=
    le_antisymm hZsub hZ
  have hrefl := ggQ2xFN_reflSet_eq D hbas hm e hD τ hτ A hW hTF
  have hreflGp : reflGp (A.map (ggLinConj τ).toMonoidHom) = ggBCW m := by
    rw [reflGp]
    change Subgroup.closure (ggReflSet (A.map (ggLinConj τ).toMonoidHom)) = ggBCW m
    rw [hrefl, hZeq]
    rfl
  have hconj : ∀ a ∈ A.map (ggLinConj τ).toMonoidHom,
      ∀ g ∈ ggBCW m, a * g * a⁻¹ ∈ ggBCW m := by
    intro a ha g hg
    rw [← hreflGp] at hg ⊢
    have hle : Subgroup.map (MulAut.conj a)
        (reflGp (A.map (ggLinConj τ).toMonoidHom)) ≤
        reflGp (A.map (ggLinConj τ).toMonoidHom) := by
      rw [reflGp, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro t ⟨u, ⟨huA, huR⟩, rfl⟩
      have hmemA : a * u * a⁻¹ ∈ A.map (ggLinConj τ).toMonoidHom :=
        (A.map (ggLinConj τ).toMonoidHom).mul_mem
          ((A.map (ggLinConj τ).toMonoidHom).mul_mem ha huA)
          ((A.map (ggLinConj τ).toMonoidHom).inv_mem ha)
      have hreflA : IsReflLin (a * u * a⁻¹) := ggQ2xFN_isReflLin_conj a u huR
      simpa only [MulAut.conj_apply] using ⟨hmemA, hreflA⟩
    have hmem : (MulAut.conj a) g ∈ Subgroup.map (MulAut.conj a)
        (reflGp (A.map (ggLinConj τ).toMonoidHom)) := Subgroup.mem_map_of_mem _ hg
    rw [MulAut.conj_apply] at hmem
    exact hle hmem
  intro φ hφ
  have hnorm : φ ∈ Subgroup.normalizer
      (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj φ hφ h
    · intro hh
      have hmem := hconj φ⁻¹ ((A.map (ggLinConj τ).toMonoidHom).inv_mem hφ)
        (φ * h * φ⁻¹) hh
      simpa [mul_assoc] using hmem
  have hmem := ggQ2_bc_normalizer m (by omega) φ hnorm
  rw [← hreflGp] at hmem
  exact ⟨φ, hmem, rfl⟩

private lemma ggQ2xFN_P3_of_roots (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)))
    (x : D.V)
    (hZ : ggBCRoots m ⊆
      {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom}) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} :=
  (ggLinConj_P3 τ A x).mp
    (ggQ2xFN_caseA D hbas hm e hD τ hτ hroot A hW hTF hHL hZ (τ x))

private lemma ggQ2xFN_bc_refl_invol {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (v : GGBCV n) : ggBCRefl c hc (ggBCRefl c hc v) = v := by
  have hψ : ((2 / (c ⬝ᵥ c)) • ggBCDot c : Module.Dual (ZMod 3) (GGBCV n)) c = 2 := by
    rw [LinearMap.smul_apply, ggQ2_DW_dot_apply, smul_eq_mul]
    exact div_mul_cancel₀ 2 hc
  have h1 : ggBCRefl c hc = Module.reflection hψ := by
    unfold ggBCRefl
    congr 1
  simpa [h1] using Module.involutive_reflection hψ v

private lemma ggQ2xFN_bc_refl_mul_self {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc * ggBCRefl c hc = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply]
  change ggBCRefl c hc (ggBCRefl c hc v) = v
  exact ggQ2xFN_bc_refl_invol c hc v

private lemma ggQ2xFN_Q_single {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) (s : ZMod 3) :
    ggQ2_DW_Q 3 m σ (Pi.single i s : GGBCV m) = Pi.single (σ i) s := by
  ext j
  rw [ggQ2_DW_Q_apply]
  by_cases h : j = σ i
  · subst h
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · have h' : σ.symm j ≠ i := by
      intro hh; apply h; rw [← hh, Equiv.apply_symm_apply]
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

private lemma ggQ2xFN_Q_swap_mem_DR {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ggQ2_DW_Q 3 m (Equiv.swap i j) ∈ ggBCReflGp (ggDRoots m) := by
  have hc : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0 := by
    rw [ggQ2_DW_sub_norm i j hij]; decide
  rw [← ggQ2_DW_sub_refl_eq_swap i j hij hc]
  exact Subgroup.subset_closure
    ⟨(Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1,
      ggQ2_DW_Wt_sub_single i j hij, hc, rfl⟩

private lemma ggQ2xFN_DR_orbit_wt_one {m : ℕ} (hm : 5 ≤ m) {z w : GGBCV m}
    (hzroot : z ∈ ggBCRoots m) (hzw : ggBCWt z = 1)
    (hwroot : w ∈ ggBCRoots m) (hww : ggBCWt w = 1) :
    ∃ r ∈ ggBCReflGp (ggDRoots m), ∃ μ : ZMod 3, μ ≠ 0 ∧ w = μ • (r z) := by
  obtain ⟨i, s, hs, rfl⟩ := ggQ2xFN_wt_eq_one_iff.mp hzw
  obtain ⟨j, t, ht, rfl⟩ := ggQ2xFN_wt_eq_one_iff.mp hww
  by_cases hij : i = j
  · subst hij
    refine ⟨1, (ggBCReflGp (ggDRoots m)).one_mem, t * s⁻¹, mul_ne_zero ht (inv_ne_zero hs), ?_⟩
    change Pi.single i t = (t * s⁻¹) • (Pi.single i s : GGBCV m)
    ext k
    by_cases hk : k = i
    · subst hk
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hs]
    · simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hk, hk]
  · refine ⟨ggQ2_DW_Q 3 m (Equiv.swap i j), ggQ2xFN_Q_swap_mem_DR i j hij,
      t * s⁻¹, mul_ne_zero ht (inv_ne_zero hs), ?_⟩
    rw [ggQ2xFN_Q_single, Equiv.swap_apply_left]
    ext k
    by_cases hk : k = j
    · subst hk
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hs]
    · simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hk, hk]

private lemma ggQ2xFN_Z_inv_R (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) :
    ∀ r ∈ ggBCReflGp (ggDRoots m),
      ∀ z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom},
      r z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  let Z : Set (GGBCV m) := {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom}
  change ∀ r ∈ ggBCReflGp (ggDRoots m), ∀ z ∈ Z, r z ∈ Z
  have hDle := ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW
  have hgen : ∀ t ∈ ggBCReflSet (ggDRoots m), ∀ z ∈ Z, t z ∈ Z := by
    rintro t ⟨c, hcroot, hc, rfl⟩ z hzZ
    obtain ⟨hz, hzA⟩ := hzZ
    have hcA : ggBCRefl c hc ∈ A.map (ggLinConj τ).toMonoidHom :=
      hDle (Subgroup.subset_closure ⟨c, hcroot, hc, rfl⟩)
    have hcinv : (ggBCRefl c hc).symm ∈ A.map (ggLinConj τ).toMonoidHom :=
      (A.map (ggLinConj τ).toMonoidHom).inv_mem hcA
    have hconj : ggBCRefl c hc * ggBCRefl z hz * (ggBCRefl c hc).symm ∈
        A.map (ggLinConj τ).toMonoidHom :=
      (A.map (ggLinConj τ).toMonoidHom).mul_mem
        ((A.map (ggLinConj τ).toMonoidHom).mul_mem hcA hzA) hcinv
    obtain ⟨hz', heq⟩ := ggQ2xFN_refl_conj_isom (ggBCRefl c hc) z hz (ggQ2xFN_isometry c hc)
    rw [heq] at hconj
    exact ⟨hz', hconj⟩
  intro r hr
  rw [ggBCReflGp] at hr
  refine Subgroup.closure_induction_left (p := fun w _ => ∀ z ∈ Z, w z ∈ Z) ?_ ?_ ?_ hr
  · intro z hz
    simpa using hz
  · intro a ha b hbmem hb z hz
    rw [LinearEquiv.mul_apply]
    exact hgen a ha (b z) (hb z hz)
  · intro a ha b hbmem hb z hz
    obtain ⟨c, hcroot, hc, rfl⟩ := ha
    have hinv : (ggBCRefl c hc)⁻¹ = ggBCRefl c hc :=
      inv_eq_of_mul_eq_one_right (ggQ2xFN_bc_refl_mul_self c hc)
    rw [LinearEquiv.mul_apply, hinv]
    exact hgen (ggBCRefl c hc) ⟨c, hcroot, hc, rfl⟩ (b z) (hb z hz)

private lemma ggQ2xFN_wt_one_mem_Z (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    ∀ {z w : GGBCV m},
      z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} →
      ggBCWt z = 1 → w ∈ ggBCRoots m → ggBCWt w = 1 →
      w ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  intro z w hzZ hzw hwroot hww
  have hZsub := ggQ2xFN_Z_subset_roots D hbas hm e hD τ hτ hroot A hW hTF hHL
  obtain ⟨r, hr, μ, hμ, hw⟩ := ggQ2xFN_DR_orbit_wt_one hm (hZsub hzZ) hzw hwroot hww
  have hrz := ggQ2xFN_Z_inv_R D hbas hm e hD τ hτ hroot A hW r hr z hzZ
  obtain ⟨hc, hcA⟩ := hrz
  have hsz : (μ • (r z)) ⬝ᵥ (μ • (r z)) ≠ 0 := by
    rw [ggQ2_DW_A_dot_self_eq_wt, ggQ2xFN_wt_smul _ _ hμ, ← ggQ2_DW_A_dot_self_eq_wt]
    exact hc
  have hzw' : w ⬝ᵥ w ≠ 0 := by rw [hw]; exact hsz
  refine ⟨hzw', ?_⟩
  rw [ggQ2_DW_refl_congr hw hzw' hsz, ggQ2xFN_refl_smul μ hμ (r z) hc hsz]
  exact hcA

private lemma ggQ2xFN_Z_dichotomy (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (fun _ : Fin m => (1 : ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin m => (1 : ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggARoots m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    (∀ z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom}, ggBCWt z ≠ 1) ∨
      ggBCRoots m ⊆ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  have hZroots := ggQ2xFN_hZroots D hbas hm e hD τ hτ hroot A hW
  by_cases h : ∃ z ∈ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom}, ggBCWt z = 1
  · right
    intro w hw
    have hwr : 1 ≤ ggBCWt w ∧ ggBCWt w ≤ 2 := hw
    rcases (by omega : ggBCWt w = 1 ∨ ggBCWt w = 2) with h1 | h2
    · obtain ⟨z, hzZ, hzw⟩ := h
      exact ggQ2xFN_wt_one_mem_Z D hbas hm e hD τ hτ hroot A hW hTF hHL hzZ hzw hw h1
    · exact hZroots h2
  · left
    intro z hzZ hz1
    exact h ⟨z, hzZ, hz1⟩

private lemma ggQ2xFN_reflGp_eq_DR (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZ : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    reflGp (A.map (ggLinConj τ).toMonoidHom) = ggBCReflGp (ggDRoots m) := by
  have hZroots := ggQ2xFN_hZroots D hbas hm e hD τ hτ hroot A hW
  have hrefl := ggQ2xFN_reflSet_eq D hbas hm e hD τ hτ A hW hTF
  have hZeq : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} = ggDRoots m :=
    le_antisymm hZ hZroots
  rw [reflGp]
  change Subgroup.closure (ggReflSet (A.map (ggLinConj τ).toMonoidHom)) =
    ggBCReflGp (ggDRoots m)
  rw [hrefl, hZeq]
  rfl

private lemma ggQ2xFN_single_dot_left {m : ℕ} (i : Fin m) (v : GGBCV m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v = v i := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i) v = v i
  exact ggQ2_DW_dotLin_fvec_left 3 m i v

private lemma ggQ2xFN_single_dot_self {m : ℕ} (i : Fin m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ Pi.single i 1 = 1 := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i) (ggQ2_DW_fvec 3 m i) = 1
  rw [ggQ2xFN_dotLin_fvec_fvec]; simp

private lemma ggQ2xFN_short_ne {m : ℕ} (i : Fin m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ Pi.single i 1 ≠ 0 := by
  rw [ggQ2xFN_single_dot_self]; decide

private noncomputable def ggQ2xFN_short {m : ℕ} (i : Fin m) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl (Pi.single i (1 : ZMod 3)) (ggQ2xFN_short_ne i)

private lemma ggQ2xFN_short_apply {m : ℕ} (i : Fin m) (v : GGBCV m) :
    ggQ2xFN_short i v = v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2xFN_short, ggQ2_DW_bc_apply', ggQ2xFN_single_dot_left, ggQ2xFN_single_dot_self, mul_one]

private noncomputable def ggQ2xFN_sub_refl {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)
    (by rw [ggQ2_DW_sub_norm i j hij]; decide)

private noncomputable def ggQ2xFN_add_refl {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)
    (by rw [ggQ2_DW_add_norm i j hij]; decide)

private lemma ggQ2xFN_single_sub_dot {m : ℕ} (i j : Fin m) (v : GGBCV m) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ v = v i - v j := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j) v = v i - v j
  rw [ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

private lemma ggQ2xFN_single_add_dot {m : ℕ} (i j : Fin m) (v : GGBCV m) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ v = v i + v j := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) v = v i + v j
  rw [ggQ2xFN_dotLin_add_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

private lemma ggQ2xFN_sub_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    ggQ2xFN_sub_refl i j hij v =
      v + ((((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ v) * 2) •
        ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) := by
  unfold ggQ2xFN_sub_refl
  rw [ggQ2_DW_bc_apply', ggQ2_DW_sub_norm i j hij]

private lemma ggQ2xFN_add_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    ggQ2xFN_add_refl i j hij v =
      v + ((((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ v) * 2) •
        ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) := by
  unfold ggQ2xFN_add_refl
  rw [ggQ2_DW_bc_apply', ggQ2_DW_add_norm i j hij]

private lemma ggQ2xFN_short_mul_short_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    (ggQ2xFN_short i * ggQ2xFN_short j) v =
      v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
  rw [LinearEquiv.mul_apply, ggQ2xFN_short_apply, ggQ2xFN_short_apply]
  have hc : (v + (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m)) i = v i := by
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, mul_zero, add_zero]
  rw [hc]
  abel

private lemma ggQ2xFN_sub_mul_add_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    (ggQ2xFN_sub_refl i j hij * ggQ2xFN_add_refl i j hij) v =
      v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
  rw [LinearEquiv.mul_apply, ggQ2xFN_add_apply i j hij, ggQ2xFN_single_add_dot i j v,
    ggQ2xFN_sub_apply i j hij]
  have h0 : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) = 0 := by
    change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
      (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) = 0
    rw [map_add, ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_sub_left,
      ggQ2xFN_dotLin_fvec_fvec, ggQ2xFN_dotLin_fvec_fvec,
      ggQ2xFN_dotLin_fvec_fvec, ggQ2xFN_dotLin_fvec_fvec]
    simp [hij, Ne.symm hij]
  have hdot : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      (v + ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) =
      v i - v j := by
    change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
      (v + ((v i + v j) * 2) • (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j)) = v i - v j
    rw [map_add, map_smul, ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_fvec_left,
      ggQ2_DW_dotLin_fvec_left,
      show ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
        (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) = 0 from h0,
      smul_zero, add_zero]
  rw [hdot]
  have hsum : ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) +
        ((v i - v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) =
      (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
    calc ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) +
          ((v i - v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)
        = (((v i + v j) * 2) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
            ((v i - v j) * 2) • (Pi.single i (1 : ZMod 3) : GGBCV m)) +
          (((v i + v j) * 2) • (Pi.single j (1 : ZMod 3) : GGBCV m) -
            ((v i - v j) * 2) • (Pi.single j (1 : ZMod 3) : GGBCV m)) := by
          rw [smul_add, smul_sub]; abel
      _ = (((v i + v j) * 2) + ((v i - v j) * 2)) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
          (((v i + v j) * 2) - ((v i - v j) * 2)) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
          rw [add_smul, sub_smul]
      _ = (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
          (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
          rw [show ((v i + v j) * 2) + ((v i - v j) * 2) = v i from
                (by decide : ∀ x y : ZMod 3, (x + y) * 2 + (x - y) * 2 = x) (v i) (v j),
              show ((v i + v j) * 2) - ((v i - v j) * 2) = v j from
                (by decide : ∀ x y : ZMod 3, (x + y) * 2 - (x - y) * 2 = y) (v i) (v j)]
  rw [add_assoc, hsum]
  abel

private lemma ggQ2xFN_short_mul_short_eq {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ggQ2xFN_short i * ggQ2xFN_short j = ggQ2xFN_sub_refl i j hij * ggQ2xFN_add_refl i j hij := by
  apply LinearEquiv.ext
  intro v
  rw [ggQ2xFN_short_mul_short_apply i j hij, ggQ2xFN_sub_mul_add_apply i j hij]

private lemma ggQ2xFN_wt_short {m : ℕ} (i : Fin m) (v : GGBCV m) :
    ggBCWt (ggQ2xFN_short i v) = ggBCWt v := by
  unfold ggBCWt
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [ggQ2xFN_short_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    rw [Pi.single_eq_same, mul_one]
    exact (by decide : ∀ x : ZMod 3, x + x ≠ 0 ↔ x ≠ 0) (v k)
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, mul_zero, add_zero]

private lemma ggQ2xFN_short_mul_short_mem_DR {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ggQ2xFN_short i * ggQ2xFN_short j ∈ ggBCReflGp (ggDRoots m) := by
  rw [ggQ2xFN_short_mul_short_eq i j hij]
  apply (ggBCReflGp (ggDRoots m)).mul_mem
  · unfold ggQ2xFN_sub_refl
    exact Subgroup.subset_closure
      ⟨(Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1,
        ggQ2_DW_Wt_sub_single i j hij, _, rfl⟩
  · unfold ggQ2xFN_add_refl
    exact Subgroup.subset_closure
      ⟨(Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1,
        ggQ2_DW_Wt_add_single i j hij, _, rfl⟩

private lemma ggQ2xFN_short_inv {m : ℕ} (i : Fin m) :
    (ggQ2xFN_short i)⁻¹ = ggQ2xFN_short i :=
  inv_eq_of_mul_eq_one_right (ggQ2xFN_bc_refl_mul_self _ (ggQ2xFN_short_ne i))

private lemma ggQ2xFN_short_normalizes_DR {m : ℕ} (i : Fin m) :
    ∀ g ∈ ggBCReflGp (ggDRoots m),
      ggQ2xFN_short i * g * (ggQ2xFN_short i)⁻¹ ∈ ggBCReflGp (ggDRoots m) := by
  have hle : Subgroup.map (MulAut.conj (ggQ2xFN_short i)) (ggBCReflGp (ggDRoots m)) ≤
      ggBCReflGp (ggDRoots m) := by
    rw [ggBCReflGp, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro t ⟨u, ⟨c, hcroot, hc, rfl⟩, rfl⟩
    obtain ⟨hc', heq⟩ :=
      ggQ2xFN_refl_conj_isom (ggQ2xFN_short i) c hc
        (ggQ2xFN_isometry (Pi.single i (1 : ZMod 3)) (ggQ2xFN_short_ne i))
    refine ⟨ggQ2xFN_short i c, ?_, hc', ?_⟩
    · rw [ggDRoots]
      change ggBCWt (ggQ2xFN_short i c) = 2
      rw [ggQ2xFN_wt_short, hcroot]
    · change ggQ2xFN_short i * ggBCRefl c hc * (ggQ2xFN_short i).symm =
        ggBCRefl (ggQ2xFN_short i c) hc'
      exact heq
  intro g hg
  exact hle (Subgroup.mem_map_of_mem _ hg)

private lemma ggQ2xFN_short_mul_i0_mem_DR {m : ℕ} (j i₀ : Fin m) :
    ggQ2xFN_short j * ggQ2xFN_short i₀ ∈ ggBCReflGp (ggDRoots m) := by
  by_cases h : j = i₀
  · rw [h, show ggQ2xFN_short i₀ * ggQ2xFN_short i₀ = 1 from
      ggQ2xFN_bc_refl_mul_self _ (ggQ2xFN_short_ne i₀)]
    exact Subgroup.one_mem _
  · exact ggQ2xFN_short_mul_short_mem_DR j i₀ h

private lemma ggQ2xFN_Wc_le_R_union_Rs {m : ℕ} (i₀ : Fin m) :
    ∀ g ∈ ggBCW m,
      g ∈ ggBCReflGp (ggDRoots m) ∨
        ∃ r ∈ ggBCReflGp (ggDRoots m), g = r * ggQ2xFN_short i₀ := by
  have hs2 : ggQ2xFN_short i₀ * ggQ2xFN_short i₀ = 1 :=
    ggQ2xFN_bc_refl_mul_self _ (ggQ2xFN_short_ne i₀)
  have hgen : ∀ t ∈ ggBCReflSet (ggBCRoots m),
      t ∈ ggBCReflGp (ggDRoots m) ∨
        ∃ r ∈ ggBCReflGp (ggDRoots m), t = r * ggQ2xFN_short i₀ := by
    rintro t ⟨c, hcroot, hc, rfl⟩
    rcases (by have h1 := hcroot.1; have h2 := hcroot.2; omega : ggBCWt c = 1 ∨ ggBCWt c = 2)
      with h1 | h2
    · right
      obtain ⟨j, s, hs, rfl⟩ := ggQ2xFN_wt_eq_one_iff.mp h1
      have hsj : (Pi.single j s : GGBCV m) = s • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
        ext k
        by_cases hk : k = j
        · subst hk; simp [Pi.smul_apply, smul_eq_mul]
        · simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, Pi.smul_apply]
      have hs' : (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) ⬝ᵥ
          (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) ≠ 0 := by
        rw [← hsj]; exact hc
      refine ⟨ggQ2xFN_short j * ggQ2xFN_short i₀, ggQ2xFN_short_mul_i0_mem_DR j i₀, ?_⟩
      rw [mul_assoc, hs2, mul_one]
      rw [show ggBCRefl (Pi.single j s) hc =
          ggBCRefl (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) hs' from
        ggQ2_DW_refl_congr hsj hc hs']
      rw [ggQ2xFN_refl_smul s hs (Pi.single j (1 : ZMod 3)) (ggQ2xFN_short_ne j) hs']
      rfl
    · left
      exact Subgroup.subset_closure ⟨c, h2, hc, rfl⟩
  intro g hg
  rw [ggBCW] at hg
  refine Subgroup.closure_induction (fun t ht => hgen t ht) ?_ ?_ ?_ hg
  · exact Or.inl (Subgroup.one_mem _)
  · intro x y hxmem hymem hx hy
    rcases hx with hx | ⟨rx, hrx, rfl⟩
    · rcases hy with hy | ⟨ry, hry, rfl⟩
      · exact Or.inl (mul_mem hx hy)
      · exact Or.inr ⟨x * ry, mul_mem hx hry, by rw [mul_assoc]⟩
    · rcases hy with hy | ⟨ry, hry, rfl⟩
      · refine Or.inr ⟨rx * (ggQ2xFN_short i₀ * y * ggQ2xFN_short i₀),
          mul_mem hrx (by
            have h := ggQ2xFN_short_normalizes_DR i₀ y hy
            rwa [ggQ2xFN_short_inv i₀] at h), ?_⟩
        rw [mul_assoc rx (ggQ2xFN_short i₀ * y * ggQ2xFN_short i₀) (ggQ2xFN_short i₀),
          show ggQ2xFN_short i₀ * y * ggQ2xFN_short i₀ * ggQ2xFN_short i₀ =
            ggQ2xFN_short i₀ * y from by
            rw [show ggQ2xFN_short i₀ * y * ggQ2xFN_short i₀ * ggQ2xFN_short i₀ =
              ggQ2xFN_short i₀ * y * (ggQ2xFN_short i₀ * ggQ2xFN_short i₀) from by group,
              hs2, mul_one],
          mul_assoc]
      · have h := ggQ2xFN_short_normalizes_DR i₀ ry hry
        rw [ggQ2xFN_short_inv i₀] at h
        refine Or.inl ?_
        convert mul_mem hrx h using 1
        group
  · intro x hxmem hx
    rcases hx with hx | ⟨rx, hrx, rfl⟩
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨ggQ2xFN_short i₀ * rx⁻¹ * ggQ2xFN_short i₀, ?_, ?_⟩
      · have h := ggQ2xFN_short_normalizes_DR i₀ rx⁻¹ (inv_mem hrx)
        rwa [ggQ2xFN_short_inv i₀] at h
      · rw [mul_inv_rev, ggQ2xFN_short_inv i₀]
        calc ggQ2xFN_short i₀ * rx⁻¹
            = ggQ2xFN_short i₀ * rx⁻¹ * 1 := by rw [mul_one]
          _ = ggQ2xFN_short i₀ * rx⁻¹ * (ggQ2xFN_short i₀ * ggQ2xFN_short i₀) := by rw [hs2]
          _ = (ggQ2xFN_short i₀ * rx⁻¹ * ggQ2xFN_short i₀) * ggQ2xFN_short i₀ := by group

private lemma ggQ2xFN_short_apply_self {m : ℕ} (i : Fin m) :
    ggQ2xFN_short i (Pi.single i (1 : ZMod 3) : GGBCV m) = -Pi.single i 1 := by
  rw [ggQ2xFN_short_apply, Pi.single_eq_same, one_smul]
  ext k
  by_cases hk : k = i
  · rw [hk]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, one_mul,
      Pi.neg_apply]
    exact (by decide : ∀ x : ZMod 3, x + x = -x) 1
  · simp only [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, Pi.smul_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, mul_zero, add_zero, Pi.neg_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, neg_zero]

private lemma ggQ2xFN_short_apply_of_ne {m : ℕ} (i j : Fin m) (hij : j ≠ i) :
    ggQ2xFN_short i (Pi.single j (1 : ZMod 3) : GGBCV m) = Pi.single j 1 := by
  rw [ggQ2xFN_short_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), zero_smul,
    add_zero]

private lemma ggQ2xFN_neg_one_smul {m : ℕ} (x : GGBCV m) :
    (-1 : ZMod 3) • x = -x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact (by decide : ∀ a : ZMod 3, (-1) * a = -a) (x i)

private lemma ggQ2xFN_neg_one_smul_neg {m : ℕ} (x : GGBCV m) :
    (-1 : ZMod 3) • (-x) = x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact (by decide : ∀ a : ZMod 3, (-1) * (-a) = a) (x i)

private lemma ggQ2xFN_diag_mem_W_aux {m : ℕ} (k : ℕ) :
    ∀ (S : Finset (Fin m)) (b : GGBCV m ≃ₗ[ZMod 3] GGBCV m),
      S.card ≤ k →
      (∀ j, b (Pi.single j (1 : ZMod 3)) =
        (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) →
      b ∈ ggBCW m := by
  induction k with
  | zero =>
    intro S b hk hb
    have hScard : S.card = 0 := Nat.eq_zero_of_le_zero hk
    have hS : S = ∅ := Finset.card_eq_zero.mp hScard
    subst hS
    have hb1 : b = 1 := by
      apply (Pi.basisFun (ZMod 3) (Fin m)).ext'
      intro j
      rw [Pi.basisFun_apply, hb j]
      simp
    rw [hb1]; exact (ggBCW m).one_mem
  | succ k ih =>
    intro S b hk hb
    by_cases hle : S.card ≤ k
    · exact ih S b hle hb
    · have hpos : 0 < S.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hcard : (S.erase i).card ≤ k := by
        rw [Finset.card_erase_of_mem hi]; omega
      have hb' : ∀ j, (ggQ2xFN_short i * b) (Pi.single j (1 : ZMod 3)) =
          (if j ∈ S.erase i then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3) := by
        intro j
        rw [LinearEquiv.mul_apply, hb j, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [if_pos hi, ggQ2xFN_short_apply_self, if_neg (by simp)]
          calc (-1 : ZMod 3) • (-Pi.single j (1 : ZMod 3)) = Pi.single j 1 :=
                ggQ2xFN_neg_one_smul_neg _
            _ = (1 : ZMod 3) • Pi.single j (1 : ZMod 3) := (one_smul _ _).symm
        · rw [ggQ2xFN_short_apply_of_ne i j hji]
          by_cases hjS : j ∈ S
          · rw [if_pos hjS, if_pos (by rw [Finset.mem_erase]; exact ⟨hji, hjS⟩)]
          · rw [if_neg hjS, if_neg (by rw [Finset.mem_erase]; exact fun h => hjS h.2)]
      have hmem : ggQ2xFN_short i * b ∈ ggBCW m := ih (S.erase i) (ggQ2xFN_short i * b) hcard hb'
      have hshort : ggQ2xFN_short i ∈ ggBCW m := by
        rw [ggQ2xFN_short]
        exact Subgroup.subset_closure
          ⟨_, (by
            rw [ggBCRoots]
            simp only [Set.mem_setOf_eq]
            rw [ggQ2xFN_wt_single_of_ne_zero i 1 one_ne_zero]
            decide), ggQ2xFN_short_ne i, rfl⟩
      have hb_eq : b = (ggQ2xFN_short i)⁻¹ * (ggQ2xFN_short i * b) := by group
      rw [hb_eq]
      exact mul_mem (inv_mem hshort) hmem

private lemma ggQ2xFN_diag_mem_W {m : ℕ} (S : Finset (Fin m))
    (b : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (hb : ∀ j, b (Pi.single j (1 : ZMod 3)) =
      (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) :
    b ∈ ggBCW m :=
  ggQ2xFN_diag_mem_W_aux S.card S b le_rfl hb

private lemma ggQ2xFN_neg_one_mem_Wc {m : ℕ} :
    (LinearEquiv.neg (ZMod 3) : GGBCV m ≃ₗ[ZMod 3] GGBCV m) ∈ ggBCW m := by
  refine ggQ2xFN_diag_mem_W Finset.univ (LinearEquiv.neg (ZMod 3)) ?_
  intro j
  rw [LinearEquiv.neg_apply, if_pos (Finset.mem_univ j),
    show -Pi.single j (1 : ZMod 3) = (-1 : ZMod 3) • Pi.single j (1 : ZMod 3) from
      (ggQ2xFN_neg_one_smul _).symm]

private lemma ggQ2xFN_reflSet_conj {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V)) :
    ∀ s ∈ ggReflSet A, ∀ t ∈ ggReflSet A, s * t * s⁻¹ ∈ ggReflSet A := by
  rintro s ⟨hsA, -⟩ t ⟨htA, htR⟩
  exact ⟨A.mul_mem (A.mul_mem hsA htA) (A.inv_mem hsA), ggQ2_isReflLin_conj s t htR⟩

private lemma ggQ2xFN_inner_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    GGQ2QuandleInner (ggReflSet A)
      (ggLinConj τ.symm '' (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) := by
  have hZroots := ggQ2xFN_hZroots D hbas hm e hD τ hτ hroot A hW
  have hZeq : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} = ggDRoots m :=
    le_antisymm hZPhi hZroots
  have hrefl := ggQ2xFN_reflSet_eq D hbas hm e hD τ hτ A hW hTF
  have hcirc : ggLinConj τ.symm '' ggReflSet (A.map (ggLinConj τ).toMonoidHom) = ggReflSet A := by
    rw [show ggReflSet (A.map (ggLinConj τ).toMonoidHom) = (ggLinConj τ) '' ggReflSet A from
      ggLinConj_reflSet τ A]
    ext g
    constructor
    · rintro ⟨h, ⟨a, ha, rfl⟩, rfl⟩
      simpa [show ggLinConj τ.symm (ggLinConj τ a) = a from
        (ggLinConj τ).symm_apply_apply a] using ha
    · intro hg
      exact ⟨ggLinConj τ g, ⟨g, hg, rfl⟩, (ggLinConj τ).symm_apply_apply g⟩
  have hcoord : GGQ2QuandleInner (ggBCReflSet (ggDRoots m)) (ggBCW m) := ggQ2_D_inner_phi m hm
  have hmap := ggQ2_inner_map (ggLinConj τ.symm) hcoord
  rw [← hZeq, ← hrefl, hcirc] at hmap
  exact hmap

private lemma ggQ2xFN_A_le_pm_Gamma (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a ∈ A, ∃ g ∈ (ggLinConj τ.symm '' (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))),
      (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  have h4 : 4 ≤ Fintype.card D.ι := by rw [← Fintype.card_congr e, Fintype.card_fin]; omega
  have hinner := ggQ2xFN_inner_Phi D hbas hm e hD τ hτ hroot A hW hTF hZPhi
  exact ggQ2_transfer (p := 3) (by decide) D hbas h4 A hW _ hinner

private lemma ggQ2xFN_short_not_mem_of_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ}
    (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ggQ2xFN_short i₀ ∉ A.map (ggLinConj τ).toMonoidHom := by
  intro hs
  have hmem : (Pi.single i₀ (1 : ZMod 3) : GGBCV m) ∈
      {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} :=
    ⟨ggQ2xFN_short_ne i₀, by
      change ggBCRefl (Pi.single i₀ (1 : ZMod 3)) (ggQ2xFN_short_ne i₀) ∈
        A.map (ggLinConj τ).toMonoidHom
      exact hs⟩
  have h2 : ggBCWt (Pi.single i₀ (1 : ZMod 3) : GGBCV m) = 2 := hZPhi hmem
  rw [ggQ2xFN_wt_single_of_ne_zero i₀ 1 one_ne_zero] at h2
  norm_num at h2

private lemma ggQ2xFN_coord_pm_Wc (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ w ∈ ggBCW m, (∀ v, a' v = w v) ∨ (∀ v, a' v = -(w v)) := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨g, hg, hgpm⟩ := ggQ2xFN_A_le_pm_Gamma D hbas hm e hD τ hτ hroot A hW hTF hZPhi a ha
  obtain ⟨w, hw, rfl⟩ := hg
  refine ⟨w, hw, ?_⟩
  rcases hgpm with h | h
  · left
    intro v
    change ggLinConj τ a v = w v
    rw [ggLinConj_apply, h (τ.symm v), ggLinConj_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  · right
    intro v
    change ggLinConj τ a v = -(w v)
    rw [ggLinConj_apply, h (τ.symm v), map_neg, ggLinConj_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

private lemma ggQ2xFN_pm_R_of_Wc (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ w ∈ ggBCW m, ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ((∀ v, a' v = w v) ∨ (∀ v, a' v = -(w v))) →
      ∃ r ∈ ggBCReflGp (ggDRoots m),
        (∀ v, a' v = r v) ∨ (∀ v, a' v = -(r v)) := by
  have hDle := ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW
  have hs2 : ggQ2xFN_short i₀ * ggQ2xFN_short i₀ = 1 :=
    ggQ2xFN_bc_refl_mul_self _ (ggQ2xFN_short_ne i₀)
  have hsinv : (ggQ2xFN_short i₀)⁻¹ = ggQ2xFN_short i₀ := ggQ2xFN_short_inv i₀
  intro w hw a' ha' hwpm
  rcases ggQ2xFN_Wc_le_R_union_Rs i₀ w hw with hwR | ⟨r0, hr0, rfl⟩
  · rcases hwpm with h | h
    · exact ⟨w, hwR, Or.inl h⟩
    · exact ⟨w, hwR, Or.inr h⟩
  · rcases hwpm with h | h
    · exfalso
      have haeq : a' = r0 * ggQ2xFN_short i₀ := LinearEquiv.ext h
      have hmul : a' * ggQ2xFN_short i₀ = r0 := by rw [haeq, mul_assoc, hs2, mul_one]
      have hsA : ggQ2xFN_short i₀ ∈ A.map (ggLinConj τ).toMonoidHom := by
        have hmem : a'⁻¹ * r0 ∈ A.map (ggLinConj τ).toMonoidHom :=
          mul_mem (inv_mem ha') (hDle hr0)
        have heq : ggQ2xFN_short i₀ = a'⁻¹ * r0 := by rw [← hmul]; group
        rwa [heq]
      exact ggQ2xFN_short_not_mem_of_Phi D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi hsA
    · by_cases hneg : (LinearEquiv.neg (ZMod 3) : GGBCV m ≃ₗ[ZMod 3] GGBCV m) ∈
          ggBCReflGp (ggDRoots m)
      · exfalso
        have haeq : a' = LinearEquiv.neg (ZMod 3) * r0 * ggQ2xFN_short i₀ := by
          ext v
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply, h v,
            LinearEquiv.mul_apply]
        have hmul : a' * ggQ2xFN_short i₀ = LinearEquiv.neg (ZMod 3) * r0 := by
          rw [haeq,
            show (LinearEquiv.neg (ZMod 3) * r0 * ggQ2xFN_short i₀) * ggQ2xFN_short i₀ =
              (LinearEquiv.neg (ZMod 3) * r0) * (ggQ2xFN_short i₀ * ggQ2xFN_short i₀) from by
              group,
            hs2, mul_one]
        have hsA : ggQ2xFN_short i₀ ∈ A.map (ggLinConj τ).toMonoidHom := by
          have hmem : a'⁻¹ * (LinearEquiv.neg (ZMod 3) * r0) ∈
              A.map (ggLinConj τ).toMonoidHom :=
            mul_mem (inv_mem ha') (mul_mem (hDle hneg) (hDle hr0))
          have heq : ggQ2xFN_short i₀ = a'⁻¹ * (LinearEquiv.neg (ZMod 3) * r0) := by
            rw [← hmul]; group
          rwa [heq]
        exact ggQ2xFN_short_not_mem_of_Phi D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi hsA
      · rcases ggQ2xFN_Wc_le_R_union_Rs i₀ (LinearEquiv.neg (ZMod 3))
            (ggQ2xFN_neg_one_mem_Wc) with hnegR | ⟨r0', hr0', hnegeq⟩
        · exact absurd hnegR hneg
        · have haeq : a' = r0' * (ggQ2xFN_short i₀ * r0 * ggQ2xFN_short i₀) := by
            have haeq0 : a' = LinearEquiv.neg (ZMod 3) * r0 * ggQ2xFN_short i₀ := by
              ext v
              rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply, h v,
                LinearEquiv.mul_apply]
            rw [haeq0, hnegeq]
            group
          refine ⟨r0' * (ggQ2xFN_short i₀ * r0 * ggQ2xFN_short i₀), ?_, Or.inl ?_⟩
          · refine mul_mem hr0' ?_
            have h := ggQ2xFN_short_normalizes_DR i₀ r0 hr0
            rwa [hsinv] at h
          · intro v
            rw [haeq]

private lemma ggQ2xFN_coord_pm_R_of_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ r ∈ ggBCReflGp (ggDRoots m),
        (∀ v, a' v = r v) ∨ (∀ v, a' v = -(r v)) := by
  intro a' ha'
  obtain ⟨w, hw, hwpm⟩ :=
    ggQ2xFN_coord_pm_Wc D hbas hm e hD τ hτ hroot A hW hTF hZPhi a' ha'
  exact ggQ2xFN_pm_R_of_Wc D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi w hw a' ha' hwpm

private lemma ggQ2xFN_P3_of_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m) (x : D.V)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  have hpm : ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ r ∈ reflGp (A.map (ggLinConj τ).toMonoidHom),
        (∀ v, a' v = r v) ∨ (∀ v, a' v = -(r v)) := by
    intro a' ha'
    obtain ⟨r, hr, hpm⟩ :=
      ggQ2xFN_coord_pm_R_of_Phi D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi a' ha'
    refine ⟨r, ?_, hpm⟩
    rw [ggQ2xFN_reflGp_eq_DR D hbas hm e hD τ hτ hroot A hW hTF hZPhi]
    exact hr
  exact (ggLinConj_P3 τ A x).mp (ggQ2_P3_of_pm (A.map (ggLinConj τ).toMonoidHom) (τ x) hpm)

private lemma ggQ2xFN_direct_aN (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (ha : D.a = e ⟨m - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  obtain ⟨τ, hτ, hroot⟩ :=
    ggQ2_D_coordinates (p := 3) (by decide) D hbas (by omega) e hD
  have hHL' := ggQ2xFN_HL D hbas hm e hD τ hτ hroot ha x hx A hHL
  have hZsub := ggQ2xFN_Z_subset_roots D hbas hm e hD τ hτ hroot A hW hTF hHL'
  by_cases hAZ : ggBCRoots m ⊆ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom}
  · exact ggQ2xFN_P3_of_roots D hbas hm e hD τ hτ hroot A hW hTF hHL' x hAZ
  · have hdich := ggQ2xFN_Z_dichotomy D hbas hm e hD τ hτ hroot A hW hTF hHL'
    have hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m := by
      rcases hdich with h | h
      · intro z hz
        have h1 := hZsub hz
        have h2 := h z hz
        have h1a : 1 ≤ ggBCWt z := (h1 : 1 ≤ ggBCWt z ∧ ggBCWt z ≤ 2).1
        have h1b : ggBCWt z ≤ 2 := (h1 : 1 ≤ ggBCWt z ∧ ggBCWt z ≤ 2).2
        show ggBCWt z = 2
        omega
      · exact absurd h hAZ
    exact ggQ2xFN_P3_of_Phi D hbas hm e hD τ hτ hroot A hW hTF ⟨0, by omega⟩ x hZPhi

private lemma ggQ2xFN_fork_aN (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (ha : D.a = e ⟨m - 2, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hD' : D.coxeter = (ggCoxeterMatrixD m).reindex
      ((Equiv.swap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩).trans e)) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  have ha' : D.a = ((Equiv.swap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩).trans e)
      ⟨m - 1, by omega⟩ := by
    rw [ha, Equiv.trans_apply, Equiv.swap_apply_right]
  exact ggQ2xFN_direct_aN D hbas hm _ hD' ha' x hx A hW hTF hHL

private lemma ggQ2xFN_cartan_D_swap {m : ℕ} (a b : Fin m) (ha : (a:ℕ) = m-2)
    (hb : (b:ℕ) = m-1) (i j : Fin m) :
    CartanMatrix.D m (Equiv.swap a b i) (Equiv.swap a b j) = CartanMatrix.D m i j := by
  have hfork : ∀ x : Fin m, x ≠ a → x ≠ b → CartanMatrix.D m a x = CartanMatrix.D m b x := by
    intro x hx1 hx2
    simp only [CartanMatrix.D, Matrix.of_apply]
    split_ifs <;> omega
  have hfork' : ∀ x : Fin m, x ≠ a → x ≠ b → CartanMatrix.D m x a = CartanMatrix.D m x b := by
    intro x hx1 hx2
    rw [show CartanMatrix.D m x a = CartanMatrix.D m a x from (CartanMatrix.D_isSymm m).apply a x,
      show CartanMatrix.D m x b = CartanMatrix.D m b x from (CartanMatrix.D_isSymm m).apply b x,
      hfork x hx1 hx2]
  have hfix : ∀ x : Fin m, x ≠ a → x ≠ b → Equiv.swap a b x = x := by
    intro x hxa hxb
    rw [Equiv.swap_apply_def]
    simp [hxa, hxb]
  by_cases hi : i = a
  · rw [hi, Equiv.swap_apply_left]
    by_cases hj : j = a
    · rw [hj, Equiv.swap_apply_left]
      simp only [CartanMatrix.D, Matrix.of_apply]; split_ifs <;> omega
    · by_cases hj' : j = b
      · rw [hj', Equiv.swap_apply_right]
        simp only [CartanMatrix.D, Matrix.of_apply]; split_ifs <;> omega
      · rw [hfix j hj hj']
        exact (hfork j hj hj').symm
  · by_cases hi' : i = b
    · rw [hi', Equiv.swap_apply_right]
      by_cases hj : j = a
      · rw [hj, Equiv.swap_apply_left]
        simp only [CartanMatrix.D, Matrix.of_apply]; split_ifs <;> omega
      · by_cases hj' : j = b
        · rw [hj', Equiv.swap_apply_right]
          simp only [CartanMatrix.D, Matrix.of_apply]; split_ifs <;> omega
        · rw [hfix j hj hj']
          exact hfork j hj hj'
    · rw [hfix i hi hi']
      by_cases hj : j = a
      · rw [hj, Equiv.swap_apply_left]
        exact (hfork' i hi hi').symm
      · by_cases hj' : j = b
        · rw [hj', Equiv.swap_apply_right]
          exact hfork' i hi hi'
        · rw [hfix j hj hj']

private lemma ggQ2xFN_coxeter_reindex_swap (m : ℕ) (hm : 3 ≤ m) :
    (ggCoxeterMatrixD m).reindex (Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩) =
      ggCoxeterMatrixD m := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, Equiv.symm_swap]
  rw [show (ggCoxeterMatrixD m).M (Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ i)
        (Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ j) =
      ggCoxeterMatrixD m (Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ i)
        (Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ j) from rfl,
    show (ggCoxeterMatrixD m).M i j = ggCoxeterMatrixD m i j from rfl]
  rw [ggCoxeterMatrixD_apply, ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]
  · have hσ : Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ i ≠
        Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ j :=
      fun h => hij ((Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩).injective h)
    rw [if_neg hσ, if_neg hij]
    rw [ggQ2xFN_cartan_D_swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by rfl) (by rfl) i j]

private lemma ggQ2xFN_coxeter_reindex_trans_swap {κ : Type*} (m : ℕ) (hm : 3 ≤ m)
    (e : Fin m ≃ κ) :
    (ggCoxeterMatrixD m).reindex
        ((Equiv.swap ⟨m-2, by omega⟩ ⟨m-1, by omega⟩).trans e) =
      (ggCoxeterMatrixD m).reindex e := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, Equiv.symm_trans, Equiv.symm_swap,
    Equiv.trans_apply, Equiv.trans_apply]
  exact congrFun (congrFun (congrArg (fun M : CoxeterMatrix (Fin m) => M.M)
    (ggQ2xFN_coxeter_reindex_swap m hm)) (e.symm i)) (e.symm j)

theorem ggQ2_thmB_D_aN (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (ha : D.a = e ⟨m - 2, by omega⟩ ∨ D.a = e ⟨m - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  rcases ha with ha | ha
  · have hD' : D.coxeter = (ggCoxeterMatrixD m).reindex
        ((Equiv.swap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩).trans e) := by
      rw [hD, ggQ2xFN_coxeter_reindex_trans_swap m (by omega) e]
    exact ggQ2xFN_fork_aN D hbas hm e hD ha x hx A hW hTF hHL hD'
  · exact ggQ2xFN_direct_aN D hbas hm e hD ha x hx A hW hTF hHL

end CFSG.StandardType

end

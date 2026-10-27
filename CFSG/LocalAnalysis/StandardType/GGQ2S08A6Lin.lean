module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Defs
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.A6

open Matrix

private lemma a6_eq_sum_single (v : V6) : v = ∑ i, v i • e6 i := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [e6]
  · intro b _ hb
    simp [e6, Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

@[expose] def dualVec (g : V6 →ₗ[ZMod 3] V6) (a : V6) : V6 := fun j => a ⬝ᵥ g (e6 j)

theorem dualVec_dotProduct (g : V6 →ₗ[ZMod 3] V6) (a v : V6) :
    dualVec g a ⬝ᵥ v = a ⬝ᵥ g v := by
  have hL : dualVec g a ⬝ᵥ v = ∑ j, (a ⬝ᵥ g (e6 j)) * v j := rfl
  rw [hL]
  conv_rhs => rw [a6_eq_sum_single v]
  simp only [map_sum, map_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conj_refl6 (g : V6 ≃ₗ[ZMod 3] V6) (c a : V6) (h : a ⬝ᵥ c = 2) :
    g * refl6 c a h * g⁻¹ =
      refl6 (g c) (dualVec (g.symm : V6 →ₗ[ZMod 3] V6) a) (by
        rw [dualVec_dotProduct]; simpa using h) := by
  ext v
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, refl6_apply, map_sub, map_smul,
    LinearEquiv.apply_symm_apply, dualVec_dotProduct]
  rfl

private lemma a6_perm6_symm (σ : Equiv.Perm (Fin 6)) : (perm6 σ).symm = perm6 σ⁻¹ := by
  rw [perm6, perm6, LinearEquiv.funCongrLeft_symm]
  rfl

private lemma a6_perm6_symm_apply (σ : Equiv.Perm (Fin 6)) (v : V6) (i : Fin 6) :
    (perm6 σ).symm v i = v (σ i) := by
  rw [a6_perm6_symm, perm6_apply]
  rfl

private lemma a6_perm6_e6 (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    perm6 σ (e6 i) = e6 (σ i) := by
  funext j
  rw [perm6_apply]
  simp only [e6, Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_symm]

private lemma a6_dualVec_perm6 (σ : Equiv.Perm (Fin 6)) (a : V6) :
    dualVec ((perm6 σ).symm : V6 →ₗ[ZMod 3] V6) a = fun i => a (σ.symm i) := by
  funext i
  rw [dualVec]
  have h : (perm6 σ).symm (e6 i) = e6 (σ.symm i) := by
    funext j
    rw [a6_perm6_symm_apply]
    simp only [e6, Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]
  change a ⬝ᵥ (perm6 σ).symm (e6 i) = a (σ.symm i)
  rw [h]
  simp [e6, dotProduct_single]

theorem perm6_conj_refl6 (σ : Equiv.Perm (Fin 6)) (c a : V6) (h : a ⬝ᵥ c = 2) :
    perm6 σ * refl6 c a h * (perm6 σ)⁻¹ =
      refl6 (c ∘ σ.symm) (a ∘ σ.symm) (by
        rw [dotProduct_comp_equiv_symm]
        simpa [Function.comp_def] using h) := by
  rw [conj_refl6]
  apply LinearEquiv.ext
  intro v
  have h1 : (perm6 σ) c = fun i => c (σ.symm i) := by
    funext i
    rw [perm6_apply]
  have h2 : dualVec ((perm6 σ).symm : V6 →ₗ[ZMod 3] V6) a = fun i => a (σ.symm i) :=
    a6_dualVec_perm6 σ a
  simp only [refl6_apply, h1, h2]
  rfl

theorem perm6_mul (σ τ : Equiv.Perm (Fin 6)) : perm6 (σ * τ) = perm6 σ * perm6 τ := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, perm6_apply, perm6_apply, perm6_apply]
  have h : (σ * τ).symm i = τ.symm (σ.symm i) := by
    rw [Equiv.symm_apply_eq]
    simp [Equiv.Perm.mul_apply]
  rw [h]

theorem perm6_inv (σ : Equiv.Perm (Fin 6)) : (perm6 σ)⁻¹ = perm6 σ⁻¹ :=
  a6_perm6_symm σ

theorem perm6_one6 (σ : Equiv.Perm (Fin 6)) : perm6 σ one6 = one6 := by
  funext i
  rw [perm6_apply]
  rfl

theorem perm6_e6 (σ : Equiv.Perm (Fin 6)) (i : Fin 6) : perm6 σ (e6 i) = e6 (σ i) :=
  a6_perm6_e6 σ i

theorem eq_refl6_of_isRefl6 {g : V6 ≃ₗ[ZMod 3] V6} (hg : IsRefl6 g) :
    ∃ (c a : V6) (h : a ⬝ᵥ c = 2), g = refl6 c a h := by
  obtain ⟨c, a, h, hv⟩ := hg
  exact ⟨c, a, h, LinearEquiv.ext hv⟩

theorem isRefl6_refl6 (c a : V6) (h : a ⬝ᵥ c = 2) : IsRefl6 (refl6 c a h) :=
  ⟨c, a, h, fun _ => rfl⟩

private lemma a6_noTransv_forward {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hA : ∀ g ∈ A, ¬ IsTransv6 g) {c a c' a' : V6} (h : a ⬝ᵥ c = 2) (h' : a' ⬝ᵥ c' = 2)
    (hs : refl6 c a h ∈ A) (hs' : refl6 c' a' h' ∈ A) (hcc : a ⬝ᵥ c' = 0) :
    a' ⬝ᵥ c = 0 := by
  by_contra hne
  have hc'0 : c' ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at h'
    exact (by decide : (2 : ZMod 3) ≠ 0) h'.symm
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_dotProduct] at h
    exact (by decide : (2 : ZMod 3) ≠ 0) h.symm
  have hTapply : ∀ v : V6, (refl6 c a h * refl6 c' a' h') v
      = v - (a' ⬝ᵥ v) • c' - (a ⬝ᵥ v) • c := by
    intro v
    rw [LinearEquiv.mul_apply, refl6_apply, refl6_apply, dotProduct_sub, dotProduct_smul,
      hcc, smul_zero, sub_zero]
  have hT2apply : ∀ v : V6,
      ((refl6 c a h * refl6 c' a' h') * (refl6 c a h * refl6 c' a' h')) v
        = v + ((a' ⬝ᵥ c) * (a ⬝ᵥ v)) • c' := by
    intro v
    rw [LinearEquiv.mul_apply, hTapply, hTapply]
    simp only [dotProduct_sub, dotProduct_smul, h', h, hcc, smul_eq_mul, mul_zero, sub_zero]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htrans : IsTransv6 (refl6 c a h * refl6 c' a' h' *
      (refl6 c a h * refl6 c' a' h')) := by
    refine ⟨(a' ⬝ᵥ c) • c', a, ?_, ha0, ?_, ?_⟩
    · intro h0
      have hkey : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
      rcases hkey _ hne with h1 | h1
      · rw [h1, one_smul] at h0
        exact hc'0 h0
      · rw [h1, neg_smul, one_smul] at h0
        exact hc'0 (neg_eq_zero.mp h0)
    · rw [dotProduct_smul, hcc, smul_zero]
    · intro v
      rw [hT2apply v, smul_smul, mul_comm]
  have hmem : (refl6 c a h * refl6 c' a' h') * (refl6 c a h * refl6 c' a' h') ∈ A :=
    A.mul_mem (A.mul_mem hs hs') (A.mul_mem hs hs')
  exact hA _ hmem htrans

theorem sym_of_noTransv {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hA : ∀ g ∈ A, ¬ IsTransv6 g) {c a c' a' : V6} (h : a ⬝ᵥ c = 2) (h' : a' ⬝ᵥ c' = 2)
    (hs : refl6 c a h ∈ A) (hs' : refl6 c' a' h' ∈ A) :
    a ⬝ᵥ c' = 0 ↔ a' ⬝ᵥ c = 0 :=
  ⟨a6_noTransv_forward hA h h' hs hs', a6_noTransv_forward hA h' h hs' hs⟩

private lemma a6_six_eq_zero : ((6 : ℕ) : ZMod 3) = 0 := by
  rw [← ZMod.natCast_mod 6 3]
  norm_num

private lemma a6_sum_add_const (v : V6) (t : ZMod 3) :
    (∑ i, (v i + t)) = ∑ i, v i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h6 : (6 : ℕ) • t = 0 := by
    rw [nsmul_eq_mul, a6_six_eq_zero, zero_mul]
  rw [h6, add_zero]

private lemma a6_sum_sub_const (v : V6) (t : ZMod 3) :
    (∑ i, (v i - t)) = ∑ i, v i := by
  simp only [sub_eq_add_neg]
  exact a6_sum_add_const v (-t)

private lemma a6_sum_smul (c : ZMod 3) (v : V6) :
    (∑ i, c * v i) = c * ∑ i, v i := by
  rw [Finset.mul_sum]

@[expose] def phi6 (b : ZMod 3) : V6 ≃ₗ[ZMod 3] V6 where
  toFun v := v + (b * ∑ i, v i) • one6
  invFun v := v - (b * ∑ i, v i) • one6
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, one6, smul_eq_mul, mul_one,
      Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c v := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one6, mul_one,
      RingHom.id_apply, a6_sum_smul]
    ring
  left_inv v := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, one6, smul_eq_mul,
      mul_one]
    rw [a6_sum_add_const v (b * ∑ j, v j)]
    ring
  right_inv v := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, one6, smul_eq_mul,
      mul_one]
    rw [a6_sum_sub_const v (b * ∑ j, v j)]
    ring

theorem phi6_apply (b : ZMod 3) (v : V6) : phi6 b v = v + (b * ∑ i, v i) • one6 := rfl

theorem phi6_perm6 (b : ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    phi6 b * perm6 σ = perm6 σ * phi6 b := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, phi6_apply, phi6_apply]
  have hsum : (∑ j, v (σ.symm j)) = ∑ j, v j := Equiv.sum_comp σ.symm v
  simp only [perm6_apply, Pi.add_apply, Pi.smul_apply, one6, smul_eq_mul,
    mul_one, hsum]

theorem phi6_one6 (b : ZMod 3) : phi6 b one6 = one6 := by
  funext i
  rw [phi6_apply]
  have h6 : (∑ j : Fin 6, (1 : ZMod 3)) = 0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      a6_six_eq_zero, zero_mul]
  simp only [Pi.add_apply, Pi.smul_apply, one6, smul_eq_mul, mul_one, h6,
    mul_zero, add_zero]

private lemma a6_isTransv6_conj {g : V6 ≃ₗ[ZMod 3] V6} (κ : V6 ≃ₗ[ZMod 3] V6)
    (hg : IsTransv6 g) : IsTransv6 (κ * g * κ⁻¹) := by
  obtain ⟨c, a, hc, ha, hac, hv⟩ := hg
  refine ⟨κ c, dualVec (κ.symm : V6 →ₗ[ZMod 3] V6) a, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hc (by simpa using congrArg κ.symm h0)
  · intro h0
    apply ha
    funext j
    have h1 : a ⬝ᵥ e6 j = 0 := by
      have h2 : (dualVec (κ.symm : V6 →ₗ[ZMod 3] V6) a) ⬝ᵥ κ (e6 j) = 0 := by
        rw [h0, zero_dotProduct]
      rw [dualVec_dotProduct] at h2
      simpa using h2
    simpa [e6, dotProduct_single] using h1
  · rw [dualVec_dotProduct]
    simpa using hac
  · intro v
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [hv, map_add, map_smul, LinearEquiv.apply_symm_apply, dualVec_dotProduct]
    rfl

private lemma a6_isTransv6_conj_iff (κ : V6 ≃ₗ[ZMod 3] V6) (g : V6 ≃ₗ[ZMod 3] V6) :
    IsTransv6 (κ * g * κ⁻¹) ↔ IsTransv6 g := by
  constructor
  · intro h
    have h' := a6_isTransv6_conj (κ := κ⁻¹) h
    have heq : κ⁻¹ * (κ * g * κ⁻¹) * (κ⁻¹)⁻¹ = g := by group
    rwa [heq] at h'
  · exact a6_isTransv6_conj κ

private lemma a6_fixesLine6_conj (κ : V6 ≃ₗ[ZMod 3] V6) (hκ1 : κ one6 = one6)
    (g : V6 ≃ₗ[ZMod 3] V6) : FixesLine6 (κ * g * κ⁻¹) ↔ FixesLine6 g := by
  have hκ1' : κ.symm one6 = one6 := by
    have := congrArg κ.symm hκ1
    simpa using this.symm
  have happ : (κ * g * κ⁻¹) one6 = κ (g one6) := by
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [hκ1']
  constructor
  · rintro (h | h)
    · left
      apply κ.injective
      rw [← happ, h, hκ1]
    · right
      apply κ.injective
      rw [← happ, h, map_neg, hκ1]
  · rintro (h | h)
    · left
      rw [happ, h, hκ1]
    · right
      rw [happ, h, map_neg, hκ1]

theorem A6Hyp.map {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (hAM : A6Hyp A M)
    (κ : V6 ≃ₗ[ZMod 3] V6) (hκ : ∀ σ, ∃ τ, κ * perm6 σ * κ⁻¹ = perm6 τ)
    (hκ' : ∀ σ, ∃ τ, κ⁻¹ * perm6 σ * κ = perm6 τ) (hκ1 : κ one6 = one6) :
    A6Hyp (A.map (MulAut.conj κ).toMonoidHom) (M.map (MulAut.conj κ).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono hAM.le
  · intro σ
    obtain ⟨τ, hτ⟩ := hκ' σ
    refine Subgroup.mem_map.mpr ⟨perm6 τ, hAM.perm_mem τ, ?_⟩
    show MulAut.conj κ (perm6 τ) = perm6 σ
    rw [MulAut.conj_apply, ← hτ]
    group
  · intro g hg htrans
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    apply hAM.noTransv a ha
    have htrans' : IsTransv6 (MulAut.conj κ a) := hga.symm ▸ htrans
    rw [MulAut.conj_apply] at htrans'
    exact (a6_isTransv6_conj_iff κ a).mp htrans'
  · intro g hg hfix σ'
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    have hga' : MulAut.conj κ a = g := hga
    have hfixa : FixesLine6 a := by
      have hfix' : FixesLine6 (MulAut.conj κ a) := hga'.symm ▸ hfix
      rw [MulAut.conj_apply] at hfix'
      exact (a6_fixesLine6_conj κ hκ1 a).mp hfix'
    obtain ⟨ρ, hρ⟩ := hκ' σ'
    have hρc : MulAut.conj κ (perm6 ρ) = perm6 σ' := by
      rw [MulAut.conj_apply, ← hρ]
      group
    obtain ⟨τ, hτ⟩ := hAM.normW a ha hfixa ρ
    obtain ⟨τ', hτ'⟩ := hκ τ
    refine ⟨τ', ?_⟩
    rw [← hga', ← hρc]
    rw [show MulAut.conj κ a * MulAut.conj κ (perm6 ρ) * (MulAut.conj κ a)⁻¹
        = MulAut.conj κ (a * perm6 ρ * a⁻¹) by
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group]
    rw [hτ, MulAut.conj_apply, hτ']
  · intro g hg hfix
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    have hfixa : FixesLine6 a := by
      have hfix' : FixesLine6 (MulAut.conj κ a) := hga.symm ▸ hfix
      rw [MulAut.conj_apply] at hfix'
      exact (a6_fixesLine6_conj κ hκ1 a).mp hfix'
    exact Subgroup.mem_map.mpr ⟨a, hAM.stab_mem a ha hfixa, hga⟩

theorem exists_perm_sorted (c : V6) :
    ∃ σ : Equiv.Perm (Fin 6), Monotone (fun i => (c (σ i)).val) :=
  ⟨Tuple.sort (fun i => (c i).val), by
    simpa only [Function.comp_def] using Tuple.monotone_sort (fun i => (c i).val)⟩

private lemma a6_exists_perm_pair (i j : Fin 6) (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin 6), τ 4 = i ∧ τ 5 = j := by
  by_cases hi4 : i = 4
  · subst hi4
    by_cases hj5 : j = 5
    · subst hj5
      exact ⟨1, by simp, by simp⟩
    · refine ⟨Equiv.swap 5 j, ?_, ?_⟩
      · rw [Equiv.swap_apply_of_ne_of_ne (show (4 : Fin 6) ≠ 5 by decide) hij]
      · rw [Equiv.swap_apply_left]
  by_cases hi5 : i = 5
  · subst hi5
    by_cases hj4 : j = 4
    · subst hj4
      exact ⟨Equiv.swap 4 5, by simp, by simp⟩
    · refine ⟨Equiv.swap 4 5 * Equiv.swap 5 j, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (show (4 : Fin 6) ≠ 5 by decide)
            (fun h => hj4 h.symm), Equiv.swap_apply_left]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hj4 (fun h => hij h.symm)]
  by_cases hj5 : j = 5
  · subst hj5
    refine ⟨Equiv.swap 4 i, ?_, ?_⟩
    · rw [Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne (show (5 : Fin 6) ≠ 4 by decide) (Ne.symm hi5)]
  by_cases hj4 : j = 4
  · subst hj4
    refine ⟨Equiv.swap 5 4 * Equiv.swap 4 i, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hi5 hi4]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show (5 : Fin 6) ≠ 4 by decide) (Ne.symm hi5),
        Equiv.swap_apply_left]
  refine ⟨Equiv.swap 4 i * Equiv.swap 5 j, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (show (4 : Fin 6) ≠ 5 by decide) (fun h => hj4 h.symm),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hj4 (fun h => hij h.symm)]

private def a6diag (s : Finset (Fin 6)) : V6 ≃ₗ[ZMod 3] V6 where
  toFun v := fun i => (if i ∈ s then -1 else 1) * v i
  invFun v := fun i => (if i ∈ s then -1 else 1) * v i
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    funext i
    have h : (if i ∈ s then (-1 : ZMod 3) else 1) * (if i ∈ s then (-1 : ZMod 3) else 1) = 1 := by
      split <;> norm_num
    change (if i ∈ s then (-1 : ZMod 3) else 1) *
      ((if i ∈ s then (-1 : ZMod 3) else 1) * v i) = v i
    rw [← mul_assoc, h, one_mul]
  right_inv v := by
    funext i
    have h : (if i ∈ s then (-1 : ZMod 3) else 1) * (if i ∈ s then (-1 : ZMod 3) else 1) = 1 := by
      split <;> norm_num
    change (if i ∈ s then (-1 : ZMod 3) else 1) *
      ((if i ∈ s then (-1 : ZMod 3) else 1) * v i) = v i
    rw [← mul_assoc, h, one_mul]

private lemma a6diag_apply (s : Finset (Fin 6)) (v : V6) (i : Fin 6) :
    a6diag s v i = (if i ∈ s then -1 else 1) * v i := rfl

private lemma a6diag_single (s : Finset (Fin 6)) (i : Fin 6) :
    a6diag s (e6 i) = (if i ∈ s then (-1 : ZMod 3) else 1) • e6 i := by
  funext k
  rw [a6diag_apply, Pi.smul_apply, Algebra.smul_def]
  simp
  by_cases hk : k = i
  · subst hk
    simp [e6]
  · simp [e6, hk]

private lemma a6diag_empty : a6diag (∅ : Finset (Fin 6)) = 1 := by
  apply LinearEquiv.ext
  intro v
  funext i
  simp [a6diag_apply]

private lemma a6diag_union {s t : Finset (Fin 6)} (h : Disjoint s t) :
    a6diag (s ∪ t) = a6diag s * a6diag t := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, a6diag_apply, a6diag_apply, a6diag_apply]
  by_cases hs : i ∈ s
  · have ht : i ∉ t := Finset.disjoint_left.mp h hs
    rw [if_pos (Finset.mem_union_left t hs), if_pos hs, if_neg ht]
    ring
  · by_cases ht : i ∈ t
    · rw [if_pos (Finset.mem_union_right s ht), if_neg hs, if_pos ht]
      ring
    · rw [if_neg (by simp [hs, ht]), if_neg hs, if_neg ht]
      ring

private lemma a6diag_insert_insert {i j : Fin 6} {t : Finset (Fin 6)}
    (hi : i ∉ t) (hj : j ∉ t) (hij : i ≠ j) :
    a6diag (insert i (insert j t)) = a6diag ({i, j} : Finset (Fin 6)) * a6diag t := by
  have hdisj : Disjoint ({i, j} : Finset (Fin 6)) t := by
    rw [Finset.disjoint_left]
    intro k hk hkt
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi hkt
    · rw [Finset.mem_singleton] at hk
      exact hj (hk ▸ hkt)
  rw [← a6diag_union hdisj]
  congr 1
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

private lemma a6_rD_apply (v : V6) (k : Fin 6) :
    rD v k = v k - (v 4 + v 5) * (e6 4 + e6 5) k := by
  have hdot : (e6 4 + e6 5) ⬝ᵥ v = v 4 + v 5 := by
    rw [add_dotProduct]
    simp [e6, single_dotProduct]
  simp only [rD, refl6_apply, hdot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private lemma a6_rD_apply_four (v : V6) : rD v 4 = -v 5 := by
  rw [a6_rD_apply]
  have h : (e6 (4 : Fin 6) + e6 5) 4 = 1 := by simp [e6]
  rw [h, mul_one]
  ring

private lemma a6_rD_apply_five (v : V6) : rD v 5 = -v 4 := by
  rw [a6_rD_apply]
  have h : (e6 (4 : Fin 6) + e6 5) 5 = 1 := by simp [e6]
  rw [h, mul_one]
  ring

private lemma a6_rD_apply_of_ne (v : V6) {k : Fin 6} (hk4 : k ≠ 4) (hk5 : k ≠ 5) :
    rD v k = v k := by
  rw [a6_rD_apply]
  have h : (e6 (4 : Fin 6) + e6 5) k = 0 := by simp [e6, hk4, hk5]
  rw [h, mul_zero, sub_zero]

private lemma a6diag45 :
    a6diag ({4, 5} : Finset (Fin 6)) = perm6 (Equiv.swap 4 5) * rD := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [LinearEquiv.mul_apply, a6diag_apply]
  by_cases hk4 : k = 4
  · subst hk4
    have h45 : (Equiv.swap (4 : Fin 6) 5).symm 4 = 5 := by decide
    rw [perm6_apply, h45, a6_rD_apply_five]
    simp
  · by_cases hk5 : k = 5
    · subst hk5
      have h54 : (Equiv.swap (4 : Fin 6) 5).symm 5 = 4 := by decide
      rw [perm6_apply, h54, a6_rD_apply_four]
      simp
    · have hks : (Equiv.swap (4 : Fin 6) 5).symm k = k := by
        rw [Equiv.symm_apply_eq, Equiv.swap_apply_of_ne_of_ne hk4 hk5]
      rw [perm6_apply, hks, a6_rD_apply_of_ne v hk4 hk5]
      simp [hk4, hk5]

private lemma a6diag_conj45 (τ : Equiv.Perm (Fin 6)) :
    perm6 τ * a6diag ({4, 5} : Finset (Fin 6)) * (perm6 τ)⁻¹ =
      a6diag ({τ 4, τ 5} : Finset (Fin 6)) := by
  rw [perm6_inv]
  apply LinearEquiv.ext
  intro v
  funext k
  simp only [LinearEquiv.mul_apply, perm6_apply, a6diag_apply]
  have hkk : (τ⁻¹).symm (τ.symm k) = k := by
    change (τ.symm).symm (τ.symm k) = k
    rw [Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [hkk]
  have hcond : (τ.symm k ∈ ({4, 5} : Finset (Fin 6))) ↔ k ∈ ({τ 4, τ 5} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.symm_apply_eq]
  by_cases h : τ.symm k ∈ ({4, 5} : Finset (Fin 6))
  · have hk : k ∈ ({τ 4, τ 5} : Finset (Fin 6)) := hcond.mp h
    simp [h, hk]
  · have hk : k ∉ ({τ 4, τ 5} : Finset (Fin 6)) := fun hh => h (hcond.mpr hh)
    simp [h, hk]

private lemma a6diag_pair_mem {M : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hW : ∀ σ, perm6 σ ∈ M) (hD : rD ∈ M) {i j : Fin 6} (hij : i ≠ j) :
    a6diag ({i, j} : Finset (Fin 6)) ∈ M := by
  obtain ⟨τ, hτ4, hτ5⟩ := a6_exists_perm_pair i j hij
  rw [← hτ4, ← hτ5, ← a6diag_conj45 τ, a6diag45, perm6_inv]
  have h1 : perm6 τ * perm6 (Equiv.swap (4 : Fin 6) 5) ∈ M :=
    M.mul_mem (hW τ) (hW (Equiv.swap 4 5))
  have h2 : perm6 τ * perm6 (Equiv.swap (4 : Fin 6) 5) * rD ∈ M := M.mul_mem h1 hD
  have h3 : perm6 τ * perm6 (Equiv.swap (4 : Fin 6) 5) * rD * perm6 τ⁻¹ ∈ M :=
    M.mul_mem h2 (hW τ⁻¹)
  simpa only [mul_assoc] using h3

private lemma a6diag_mem {M : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hW : ∀ σ, perm6 σ ∈ M) (hD : rD ∈ M) (s : Finset (Fin 6)) (hs : Even s.card) :
    a6diag s ∈ M := by
  have key : ∀ n, ∀ s : Finset (Fin 6), s.card = n → Even s.card → a6diag s ∈ M := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro m ih s hcard hEven
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0, a6diag_empty]
      exact M.one_mem
    · obtain ⟨k, hk⟩ := hEven
      have h2 : 2 ≤ s.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
      have hpos' : 0 < (s.erase i).card := by omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos'
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hje : j ∈ s.erase i := hj
      set u : Finset (Fin 6) := (s.erase i).erase j with hu
      have hiu : i ∉ u := by simp [hu]
      have hju : j ∉ u := by simp [hu]
      have hsu : s = insert i (insert j u) := by
        have h1 : insert j u = s.erase i := by
          rw [hu]
          exact Finset.insert_erase hje
        rw [h1]
        exact (Finset.insert_erase hi).symm
      have hucard : u.card = s.card - 2 := by
        rw [hu, Finset.card_erase_of_mem hje, herase]
        omega
      have huEven : Even u.card := by
        rw [hucard]
        refine ⟨k - 1, ?_⟩
        omega
      have hult : u.card < m := by omega
      rw [hsu, a6diag_insert_insert hiu hju (Ne.symm hji)]
      exact M.mul_mem (a6diag_pair_mem hW hD (Ne.symm hji)) (ih u.card hult u rfl huEven)
  exact key s.card s rfl hs

private lemma a6_apply_eq_sum {f : V6 →ₗ[ZMod 3] V6} {w : Fin 6 → V6}
    (h : ∀ i, f (e6 i) = w i) (v : V6) : f v = ∑ i, v i • w i := by
  conv_lhs => rw [a6_eq_sum_single v]
  rw [map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun i _ => by rw [h i])

theorem monoEven_mem {M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (hW : ∀ σ, perm6 σ ∈ M) (hD : rD ∈ M)
    (g : V6 ≃ₗ[ZMod 3] V6) (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ZMod 3) (hε : ∀ i, ε i ≠ 0)
    (hprod : ∏ i, ε i = 1) (hg : ∀ i, g (e6 i) = ε i • e6 (σ i)) : g ∈ M := by
  have hε1 : ∀ i, ε i = 1 ∨ ε i = -1 := by
    have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
    intro i
    exact key (ε i) (hε i)
  set S : Finset (Fin 6) := Finset.univ.filter (fun i => ε i = -1) with hS
  have hmemS : ∀ i, i ∈ S ↔ ε i = -1 := by
    intro i
    rw [hS]
    simp
  have hsign : ∀ i, ε i = if i ∈ S then -1 else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact (hmemS i).mp hi
    · rw [if_neg hi]
      rcases hε1 i with h | h
      · exact h
      · exact absurd ((hmemS i).mpr h) hi
  have hprodS : ∏ i, ε i = (-1 : ZMod 3) ^ S.card := by
    calc ∏ i, ε i = ∏ i, (if i ∈ S then (-1 : ZMod 3) else 1) :=
          Finset.prod_congr rfl (fun i _ => hsign i)
      _ = (∏ i ∈ Finset.univ.filter (fun i : Fin 6 => i ∈ S), (-1 : ZMod 3)) *
            ∏ i ∈ Finset.univ.filter (fun i : Fin 6 => ¬ i ∈ S), (1 : ZMod 3) :=
          Finset.prod_ite _ _
      _ = (-1 : ZMod 3) ^ S.card := by
          have hfilter : Finset.univ.filter (fun i : Fin 6 => i ∈ S) = S := by
            ext i
            simp
          rw [Finset.prod_const, Finset.prod_const_one, mul_one, hfilter]
  have hpow : (-1 : ZMod 3) ^ S.card = 1 := by
    rw [← hprodS]
    exact hprod
  have heven : Even S.card :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hpow
  have hgdiag : g = perm6 σ * a6diag S := by
    apply LinearEquiv.ext
    intro v
    have hb : ∀ i, g (e6 i) = (if i ∈ S then (-1 : ZMod 3) else 1) • e6 (σ i) := by
      intro i
      rw [hg i, hsign i]
    have hb2 : ∀ i, (perm6 σ * a6diag S) (e6 i) =
        (if i ∈ S then (-1 : ZMod 3) else 1) • e6 (σ i) := by
      intro i
      rw [LinearEquiv.mul_apply, a6diag_single, LinearEquiv.map_smul, a6_perm6_e6]
    change (g : V6 →ₗ[ZMod 3] V6) v =
      ((perm6 σ * a6diag S : V6 ≃ₗ[ZMod 3] V6) : V6 →ₗ[ZMod 3] V6) v
    rw [a6_apply_eq_sum hb v, a6_apply_eq_sum hb2 v]
  rw [hgdiag]
  exact M.mul_mem (hW σ) (a6diag_mem hW hD S heven)

end CFSG.StandardType.A6

end

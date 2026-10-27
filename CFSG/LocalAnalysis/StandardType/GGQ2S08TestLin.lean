module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

abbrev Vn (n : ℕ) : Type := Fin n → ZMod 3

@[expose] def refl (c a : Vn n) (h : a ⬝ᵥ c = 2) : Vn n ≃ₗ[ZMod 3] Vn n where
  toFun v := v - (a ⬝ᵥ v) • c
  invFun v := v - (a ⬝ᵥ v) • c
  map_add' v w := by
    rw [dotProduct_add, add_smul]
    abel
  map_smul' s v := by
    rw [dotProduct_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sub]
  left_inv v := by
    simp only [dotProduct_sub, dotProduct_smul, h, smul_eq_mul]
    rw [sub_sub, ← add_smul, sub_eq_self]
    have h3 : (a ⬝ᵥ v) + ((a ⬝ᵥ v) - (a ⬝ᵥ v) * 2) = 0 := by
      ring_nf
    rw [h3, zero_smul]
  right_inv v := by
    simp only [dotProduct_sub, dotProduct_smul, h, smul_eq_mul]
    rw [sub_sub, ← add_smul, sub_eq_self]
    have h3 : (a ⬝ᵥ v) + ((a ⬝ᵥ v) - (a ⬝ᵥ v) * 2) = 0 := by
      ring_nf
    rw [h3, zero_smul]

theorem refl_apply (c a : Vn n) (h : a ⬝ᵥ c = 2) (v : Vn n) :
    refl c a h v = v - (a ⬝ᵥ v) • c :=
  rfl

@[expose] def IsRefl (g : Vn n ≃ₗ[ZMod 3] Vn n) : Prop :=
  ∃ c a : Vn n, a ⬝ᵥ c = 2 ∧ ∀ v, g v = v - (a ⬝ᵥ v) • c

@[expose] def IsTransv (g : Vn n ≃ₗ[ZMod 3] Vn n) : Prop :=
  ∃ c a : Vn n, c ≠ 0 ∧ a ≠ 0 ∧ a ⬝ᵥ c = 0 ∧ ∀ v, g v = v + (a ⬝ᵥ v) • c

@[expose] def FixesLine (x : Vn n) (g : Vn n ≃ₗ[ZMod 3] Vn n) : Prop :=
  g x = x ∨ g x = -x

structure TestHyp (W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)) (x : Vn n)
    (A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)) : Prop where
  le : M ≤ A
  W_le : W ≤ M
  noTransv : ∀ g ∈ A, ¬ IsTransv g
  normW : ∀ g ∈ A, FixesLine x g → ∀ w ∈ W, g * w * g⁻¹ ∈ W
  stab_mem : ∀ g ∈ A, FixesLine x g → g ∈ M

@[expose] def dualVec (g : Vn n →ₗ[ZMod 3] Vn n) (a : Vn n) : Vn n :=
  fun j => a ⬝ᵥ g (Pi.single j 1)

private lemma eq_sum_single (v : Vn n) : v = ∑ i, v i • Pi.single i 1 := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem dualVec_dotProduct (g : Vn n →ₗ[ZMod 3] Vn n) (a v : Vn n) :
    dualVec g a ⬝ᵥ v = a ⬝ᵥ g v := by
  have hL : dualVec g a ⬝ᵥ v = ∑ j, (a ⬝ᵥ g (Pi.single j 1)) * v j := rfl
  rw [hL]
  conv_rhs => rw [eq_sum_single v]
  simp only [map_sum, map_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conj_refl (g : Vn n ≃ₗ[ZMod 3] Vn n) (c a : Vn n) (h : a ⬝ᵥ c = 2) :
    g * refl c a h * g⁻¹ =
      refl (g c) (dualVec (g.symm : Vn n →ₗ[ZMod 3] Vn n) a) (by
        rw [dualVec_dotProduct]; simpa using h) := by
  ext v
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, refl_apply, map_sub, map_smul,
    LinearEquiv.apply_symm_apply, dualVec_dotProduct]
  rfl

theorem eq_refl_of_isRefl {g : Vn n ≃ₗ[ZMod 3] Vn n} (hg : IsRefl g) :
    ∃ (c a : Vn n) (h : a ⬝ᵥ c = 2), g = refl c a h := by
  obtain ⟨c, a, h, hv⟩ := hg
  exact ⟨c, a, h, LinearEquiv.ext hv⟩

theorem refl_mul_self (c a : Vn n) (h : a ⬝ᵥ c = 2) : refl c a h * refl c a h = 1 := by
  apply LinearEquiv.ext
  intro v
  change refl c a h (refl c a h v) = v
  rw [refl_apply, refl_apply, dotProduct_sub, dotProduct_smul, h, smul_eq_mul]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma sym_forward {A : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (hA : ∀ g ∈ A, ¬ IsTransv g) {c a c' a' : Vn n} (h : a ⬝ᵥ c = 2) (h' : a' ⬝ᵥ c' = 2)
    (hs : refl c a h ∈ A) (hs' : refl c' a' h' ∈ A) (hcc : a ⬝ᵥ c' = 0) :
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
  have hTapply : ∀ v : Vn n, (refl c a h * refl c' a' h') v
      = v - (a' ⬝ᵥ v) • c' - (a ⬝ᵥ v) • c := by
    intro v
    rw [LinearEquiv.mul_apply, refl_apply, refl_apply, dotProduct_sub, dotProduct_smul,
      hcc, smul_zero, sub_zero]
  have hT2apply : ∀ v : Vn n,
      ((refl c a h * refl c' a' h') * (refl c a h * refl c' a' h')) v
        = v + ((a' ⬝ᵥ c) * (a ⬝ᵥ v)) • c' := by
    intro v
    rw [LinearEquiv.mul_apply, hTapply, hTapply]
    simp only [dotProduct_sub, dotProduct_smul, h', h, hcc, smul_eq_mul, mul_zero, sub_zero]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htrans : IsTransv (refl c a h * refl c' a' h' *
      (refl c a h * refl c' a' h')) := by
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
  have hmem : (refl c a h * refl c' a' h') * (refl c a h * refl c' a' h') ∈ A :=
    A.mul_mem (A.mul_mem hs hs') (A.mul_mem hs hs')
  exact hA _ hmem htrans

theorem sym_of_noTransv {A : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (hA : ∀ g ∈ A, ¬ IsTransv g) {c a c' a' : Vn n} (h : a ⬝ᵥ c = 2) (h' : a' ⬝ᵥ c' = 2)
    (hs : refl c a h ∈ A) (hs' : refl c' a' h' ∈ A) :
    a ⬝ᵥ c' = 0 ↔ a' ⬝ᵥ c = 0 :=
  ⟨sym_forward hA h h' hs hs', sym_forward hA h' h hs' hs⟩

theorem TestHyp.mem_of_orbit {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x : Vn n}
    (hT : TestHyp W x A M) {t m : Vn n ≃ₗ[ZMod 3] Vn n} (ht : t ∈ A) (hm : m ∈ M)
    (hmt : m x = t x ∨ m x = -t x) : t ∈ M := by
  have hmA : m ∈ A := hT.le hm
  have hgA : m⁻¹ * t ∈ A := A.mul_mem (A.inv_mem hmA) ht
  have hgfix : FixesLine x (m⁻¹ * t) := by
    rcases hmt with h | h
    · left
      rw [LinearEquiv.mul_apply, ← h]
      simp only [LinearEquiv.coe_inv]
      rw [LinearEquiv.symm_apply_apply]
    · right
      have ht' : t x = -(m x) := by rw [h, neg_neg]
      rw [LinearEquiv.mul_apply, ht', map_neg]
      simp only [LinearEquiv.coe_inv]
      rw [LinearEquiv.symm_apply_apply]
  have hgM : m⁻¹ * t ∈ M := hT.stab_mem _ hgA hgfix
  rw [show t = m * (m⁻¹ * t) from (mul_inv_cancel_left m t).symm]
  exact M.mul_mem hm hgM

theorem TestHyp.false_of_witness {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x : Vn n}
    (hT : TestHyp W x A M) (S : Set (Vn n)) (hS : ∀ w ∈ W, ∀ s ∈ S, w s ∈ S)
    {h w : Vn n ≃ₗ[ZMod 3] Vn n} (hh : h ∈ A) (hfix : FixesLine x h) (hw : w ∈ W) {s : Vn n}
    (hs : s ∈ S) (hout : (h * w * h⁻¹) s ∉ S) : False :=
  hout (hS _ (hT.normW h hh hfix w hw) s hs)

private lemma line_fixing_conj (κ : Vn n ≃ₗ[ZMod 3] Vn n) (x : Vn n) (hκx : κ x = x)
    (g : Vn n ≃ₗ[ZMod 3] Vn n) : FixesLine x (κ * g * κ⁻¹) ↔ FixesLine x g := by
  have hκx' : κ.symm x = x := by
    have := congrArg κ.symm hκx
    simpa using this.symm
  have happ : (κ * g * κ⁻¹) x = κ (g x) := by
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [hκx']
  constructor
  · rintro (h | h)
    · left
      apply κ.injective
      rw [← happ, h, hκx]
    · right
      apply κ.injective
      rw [← happ, h, map_neg, hκx]
  · rintro (h | h)
    · left
      rw [happ, h, hκx]
    · right
      rw [happ, h, map_neg, hκx]

private lemma isTransv_conj {g : Vn n ≃ₗ[ZMod 3] Vn n} (κ : Vn n ≃ₗ[ZMod 3] Vn n)
    (hg : IsTransv g) : IsTransv (κ * g * κ⁻¹) := by
  obtain ⟨c, a, hc, ha, hac, hv⟩ := hg
  refine ⟨κ c, dualVec (κ.symm : Vn n →ₗ[ZMod 3] Vn n) a, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hc (by simpa using congrArg κ.symm h0)
  · intro h0
    apply ha
    funext j
    have h1 : a ⬝ᵥ Pi.single j 1 = 0 := by
      have h2 : (dualVec (κ.symm : Vn n →ₗ[ZMod 3] Vn n) a) ⬝ᵥ κ (Pi.single j 1) = 0 := by
        rw [h0, zero_dotProduct]
      rw [dualVec_dotProduct] at h2
      simpa using h2
    simpa [dotProduct_single] using h1
  · rw [dualVec_dotProduct]
    simpa using hac
  · intro v
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [hv, map_add, map_smul, LinearEquiv.apply_symm_apply, dualVec_dotProduct]
    rfl

private lemma isTransv_conj_iff (κ : Vn n ≃ₗ[ZMod 3] Vn n) (g : Vn n ≃ₗ[ZMod 3] Vn n) :
    IsTransv (κ * g * κ⁻¹) ↔ IsTransv g := by
  constructor
  · intro h
    have h' := isTransv_conj (κ := κ⁻¹) h
    have heq : κ⁻¹ * (κ * g * κ⁻¹) * (κ⁻¹)⁻¹ = g := by group
    rwa [heq] at h'
  · exact isTransv_conj κ

private lemma conj_mem_of_mem {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (κ : Vn n ≃ₗ[ZMod 3] Vn n) (hκW : W.map (MulAut.conj κ).toMonoidHom = W)
    {u : Vn n ≃ₗ[ZMod 3] Vn n} (hu : u ∈ W) : MulAut.conj κ u ∈ W := by
  have hmem : MulAut.conj κ u ∈ W.map (MulAut.conj κ).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  rwa [hκW] at hmem

theorem TestHyp.map {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x : Vn n}
    (hT : TestHyp W x A M) (κ : Vn n ≃ₗ[ZMod 3] Vn n)
    (hκW : W.map (MulAut.conj κ).toMonoidHom = W) (hκx : κ x = x) :
    TestHyp W x (A.map (MulAut.conj κ).toMonoidHom) (M.map (MulAut.conj κ).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono hT.le
  · rw [← hκW]
    exact Subgroup.map_mono hT.W_le
  · intro g hg htrans
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    apply hT.noTransv a ha
    have htrans' : IsTransv (MulAut.conj κ a) := hga.symm ▸ htrans
    rw [MulAut.conj_apply] at htrans'
    exact (isTransv_conj_iff κ a).mp htrans'
  · intro g hg hfix w hw
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    have hga' : MulAut.conj κ a = g := hga
    have hfixa : FixesLine x a := by
      have hfix' : FixesLine x (MulAut.conj κ a) := hga'.symm ▸ hfix
      rw [MulAut.conj_apply] at hfix'
      exact (line_fixing_conj κ x hκx a).mp hfix'
    have hwW : w ∈ W.map (MulAut.conj κ).toMonoidHom := by
      rw [hκW]
      exact hw
    obtain ⟨w', hw', hw'w⟩ := Subgroup.mem_map.mp hwW
    have hinner : a * w' * a⁻¹ ∈ W := hT.normW a ha hfixa w' hw'
    have hw_eq : MulAut.conj κ w' = w := hw'w
    rw [← hga', ← hw_eq]
    have heq : MulAut.conj κ a * MulAut.conj κ w' * (MulAut.conj κ a)⁻¹
        = MulAut.conj κ (a * w' * a⁻¹) := by
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [heq]
    exact conj_mem_of_mem κ hκW hinner
  · intro g hg hfix
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg
    have hga' : MulAut.conj κ a = g := hga
    have hfixa : FixesLine x a := by
      have hfix' : FixesLine x (MulAut.conj κ a) := hga'.symm ▸ hfix
      rw [MulAut.conj_apply] at hfix'
      exact (line_fixing_conj κ x hκx a).mp hfix'
    exact Subgroup.mem_map.mpr ⟨a, hT.stab_mem a ha hfixa, hga⟩

end CFSG.StandardType.TestLin

end

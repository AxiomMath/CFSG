module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaBasic
public import CFSG.LieType.Universal.Spin.Chevalley.Frame

public section

namespace CFSG.StandardType

namespace RootCentOmega

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def framePair {N : ℕ} (F : HypFrame Q N) (i : Fin N) (s : Bool) : HypPair Q where
  e := F.vec i s
  f := F.vec i (!s)
  Q_e := F.map_vec i s
  Q_f := F.map_vec i (!s)
  polar_ef := F.polar_vec_not i s

@[expose] def smulPair (P : HypPair Q) {c : K} (hc : c ≠ 0) : HypPair Q where
  e := c • P.e
  f := c⁻¹ • P.f
  Q_e := by rw [QuadraticMap.map_smul, P.Q_e, smul_zero]
  Q_f := by rw [QuadraticMap.map_smul, P.Q_f, smul_zero]
  polar_ef := by
    rw [polar_smul_left_eq, polar_smul_right_eq, P.polar_ef, mul_one, mul_inv_cancel₀ hc]

theorem mem_perp_smulPair (P : HypPair Q) {c : K} (hc : c ≠ 0) {x : V} :
    x ∈ (smulPair P hc).perp ↔ x ∈ P.perp := by
  rw [HypPair.mem_perp, HypPair.mem_perp]
  change polar Q (c • P.e) x = 0 ∧ polar Q (c⁻¹ • P.f) x = 0 ↔ _
  rw [polar_smul_left_eq, polar_smul_left_eq, mul_eq_zero, mul_eq_zero,
    or_iff_right hc, or_iff_right (inv_ne_zero hc)]

theorem mem_perp_framePair {N : ℕ} (F : HypFrame Q N) (i : Fin N) (s : Bool) {x : V} :
    x ∈ (framePair F i s).perp ↔ ∀ u, polar Q (F.vec i u) x = 0 := by
  rw [HypPair.mem_perp]
  change polar Q (F.vec i s) x = 0 ∧ polar Q (F.vec i (!s)) x = 0 ↔ _
  constructor
  · rintro ⟨h1, h2⟩ u
    rcases Bool.eq_or_eq_not u s with rfl | rfl
    · exact h1
    · exact h2
  · intro h
    exact ⟨h s, h (!s)⟩

theorem framePair_orth {N : ℕ} (F : HypFrame Q N) {i j : Fin N} (hij : i ≠ j) (s t : Bool) :
    (framePair F i s).Orth (framePair F j t) where
  ee := F.polar_vec_of_ne hij _ _
  ef := F.polar_vec_of_ne hij _ _
  fe := F.polar_vec_of_ne hij _ _
  ff := F.polar_vec_of_ne hij _ _

theorem orth_smulPair {P P' : HypPair Q} (h : P.Orth P') {c : K} (hc : c ≠ 0) :
    P.Orth (smulPair P' hc) where
  ee := by change polar Q P.e (c • P'.e) = 0; rw [polar_smul_right_eq, h.ee, mul_zero]
  ef := by change polar Q P.e (c⁻¹ • P'.f) = 0; rw [polar_smul_right_eq, h.ef, mul_zero]
  fe := by change polar Q P.f (c • P'.e) = 0; rw [polar_smul_right_eq, h.fe, mul_zero]
  ff := by change polar Q P.f (c⁻¹ • P'.f) = 0; rw [polar_smul_right_eq, h.ff, mul_zero]

theorem exists_enum_compl {N : ℕ} (hN : 3 ≤ N) {i j : Fin N} (hij : i ≠ j) :
    ∃ e : ℕ → Fin N, (∀ m, e m ≠ i ∧ e m ≠ j) ∧
      (∀ m m', m < N - 2 → m' < N - 2 → e m = e m' → m = m') ∧
      ∀ k, k ≠ i → k ≠ j → ∃ m < N - 2, e m = k := by
  set o : Fin N := ⟨0, by omega⟩ with ho
  set l : Fin N := ⟨1, by omega⟩ with hl
  set σ : Equiv.Perm (Fin N) := Equiv.swap o j * Equiv.swap l (Equiv.swap o j i) with hσ
  have hσl : σ l = i := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]
  have hσo : σ o = j := by
    have h1 : Equiv.swap o j i ≠ o := by
      intro h
      apply hij
      have := congrArg (Equiv.swap o j) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    have h2 : o ≠ l := by simp [ho, hl, Fin.ext_iff]
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2 h1.symm, Equiv.swap_apply_left]
  refine ⟨fun m => σ ⟨min (m + 2) (N - 1), by omega⟩, fun m => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← hσl]
    intro h
    have := congrArg Fin.val (σ.injective h)
    simp only [hl] at this
    omega
  · rw [← hσo]
    intro h
    have := congrArg Fin.val (σ.injective h)
    simp only [ho] at this
    omega
  · intro m m' hm hm' h
    have := congrArg Fin.val (σ.injective h)
    simp only at this
    omega
  · intro k hki hkj
    set p := σ.symm k with hp
    have hkp : σ p = k := by rw [hp, Equiv.apply_symm_apply]
    have hp0 : p.val ≠ 0 := by
      intro h0
      apply hkj
      rw [← hkp, ← hσo]
      exact congrArg σ (Fin.ext h0)
    have hp1 : p.val ≠ 1 := by
      intro h1
      apply hki
      rw [← hkp, ← hσl]
      exact congrArg σ (Fin.ext h1)
    have hpN := p.isLt
    refine ⟨p.val - 2, by omega, ?_⟩
    rw [← hkp]
    exact congrArg σ (Fin.ext (show min (p.val - 2 + 2) (N - 1) = p.val by omega))

section Frame

variable [Finite K] [CharP K 2] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)

include hQ in
theorem centralizer_frame_le_ggOTwoPrime (hE : elementaryGroup Q ≤ omegaGroup Q hQ) {N : ℕ}
    (hN : 3 ≤ N) (F : HypFrame Q N)
    (hA : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → Q x = 0 → x = 0)
    (hA' : ∀ x y : V, (∀ k u, polar Q (F.vec k u) x = 0) → (∀ k u, polar Q (F.vec k u) y = 0) →
      x ≠ 0 → polar Q x y = 0 → ∃ a : K, y = a • x)
    (h3 : 4 ≤ N ∨ ∃ x : V, x ≠ 0 ∧ ∀ k u, polar Q (F.vec k u) x = 0)
    {i j : Fin N} (hij : i ≠ j) (s t : Bool) {c : K} (hc : c ≠ 0) :
    centralizer {eichler Q (F.vec j t) (c • F.vec i s)} ⊓ elementaryGroup Q ≤
      ggOTwoPrime (centralizer {eichler Q (F.vec j t) (c • F.vec i s)} ⊓ elementaryGroup Q) := by
  set P₁ := framePair F j t with hP₁
  set P₂ := smulPair (framePair F i s) hc with hP₂
  have h₁₂ : P₁.Orth P₂ := orth_smulPair (framePair_orth F hij.symm t s) hc
  have hW : ∀ x : V, x ∈ P₁.perp ⊓ P₂.perp ↔
      (∀ u, polar Q (F.vec j u) x = 0) ∧ ∀ u, polar Q (F.vec i u) x = 0 := by
    intro x
    rw [Submodule.mem_inf, hP₂, mem_perp_smulPair, hP₁, mem_perp_framePair, mem_perp_framePair]
  obtain ⟨e, hei, heinj, hesurj⟩ := exists_enum_compl hN hij
  set P : ℕ → HypPair Q := fun m => framePair F (e m) true with hP
  have hPW : ∀ m, (P m).e ∈ P₁.perp ⊓ P₂.perp ∧ (P m).f ∈ P₁.perp ⊓ P₂.perp := fun m =>
    ⟨(hW _).mpr ⟨fun u => F.polar_vec_of_ne (hei m).2.symm _ _,
        fun u => F.polar_vec_of_ne (hei m).1.symm _ _⟩,
      (hW _).mpr ⟨fun u => F.polar_vec_of_ne (hei m).2.symm _ _,
        fun u => F.polar_vec_of_ne (hei m).1.symm _ _⟩⟩
  have hP' : ∀ a b, a < N - 2 → b < N - 2 → a ≠ b → (P a).Orth (P b) := fun a b ha hb hab =>
    framePair_orth F (fun h => hab (heinj a b ha hb h)) true true
  have htail : ∀ x ∈ P₁.perp ⊓ P₂.perp, (∀ m < N - 2, x ∈ (P m).perp) →
      ∀ k u, polar Q (F.vec k u) x = 0 := by
    intro x hx hxP k u
    obtain ⟨hxj, hxi⟩ := (hW x).mp hx
    by_cases hki : k = i
    · rw [hki]
      exact hxi u
    by_cases hkj : k = j
    · rw [hkj]
      exact hxj u
    obtain ⟨m, hm, rfl⟩ := hesurj k hki hkj
    exact (mem_perp_framePair F (e m) true).mp (hxP m hm) u
  refine centralizer_le_ggOTwoPrime hQ h₁₂ hE ?_ (P := P) (r := N - 2) (by omega) hPW hP'
    (fun x hx hxP hQx => hA x (htail x hx hxP) hQx)
    (fun x hx hxP hx0 y hy hyP hxy => hA' x y (htail x hx hxP) (htail y hy hyP) hx0 hxy)
  rcases h3 with h4 | ⟨z, hz0, hz⟩
  · have h01 : e 0 ≠ e 1 := fun h => absurd (heinj 0 1 (by omega) (by omega) h) (by omega)
    exact three_le_finrank_of_hypPair (P 0) (hPW 0).1 (hPW 0).2 (hPW 1).1
      ((mem_perp_framePair F (e 0) true).mpr fun u => F.polar_vec_of_ne h01 u true)
      (P 1).e_ne_zero
  · exact three_le_finrank_of_hypPair (P 0) (hPW 0).1 (hPW 0).2
      ((hW z).mpr ⟨fun u => hz j u, fun u => hz i u⟩)
      ((mem_perp_framePair F (e 0) true).mpr fun u => hz (e 0) u) hz0

end Frame

end RootCentOmega

end CFSG.StandardType

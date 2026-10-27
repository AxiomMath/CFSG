module

public import CFSG.LocalAnalysis.StandardType.GGCartanReflLift
public import CFSG.LocalAnalysis.StandardType.GGResIIWStar
public import CFSG.LocalAnalysis.StandardType.GGSmallDepLeafDefs
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Frame
public import CFSG.LocalAnalysis.StandardType.GGWitOrthSpin
public import CFSG.Mathlib.LinearAlgebra.Matrix.GramDetModP
public import CFSG.Mathlib.LinearAlgebra.Matrix.SignedPathDet
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE6Three_A5_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (t : Fin 6 → V) (β : Fin 6 → Module.Dual (ZMod 3) V) (hβ : LinearIndependent (ZMod 3) β)
    (htβ : ∀ i j, β i (t j) = (CartanMatrix.E 6 i j : ZMod 3))
    (s : Fin 6 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - β i v • t i) (hRC : GGReflClosed s)
    (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 5 i j : ZMod 3))
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hr : ∀ j v, r j v = v - α j v • h j)
    (hrW : ∀ j, r j ∈ Subgroup.closure (Set.range s)) :
    LinearIndependent (ZMod 3) α := by
  classical
  let C : Matrix (Fin 6) (Fin 6) ℤ := CartanMatrix.E 6
  have hCt : C.transpose = C := CartanMatrix.E_isSymm 6
  have hCd : ∀ i, C i i = 2 := fun i => by simp [C, CartanMatrix.E]
  have hα : ∀ j, α j (h j) = 2 := fun j => by
    rw [hpair]
    simp [CartanMatrix.A]
  have hconj : ∀ j, r j ∈ ggReflConj s := fun j =>
    ggReflConj_of_reflClosed (p := 3) (by decide) hRC (hα j) (hr j) (hrW j)
  obtain ⟨b, c, hc, hb2, hh, hαeq⟩ :=
    ggCartanRefl_root_data (p := 3) (by decide) hCt hCd t β htβ s hs h α hα r hr hconj
  let G : Matrix (Fin 5) (Fin 5) ℤ := fun j k => b j ⬝ᵥ (C *ᵥ b k)
  have hGsym : ∀ j k, G k j = G j k := fun j k => by
    simpa [G, hCt] using dotProduct_transpose_mulVec C (b k) (b j)
  have hGdiag : ∀ j, G j j = 2 := fun j => by
    simpa [G] using hb2 j
  have hpos : ∀ j k, -2 ≤ G j k ∧ G j k ≤ 2 ∧ (G j k = 2 → b k = b j) ∧
      (G j k = -2 → b k = -b j) := fun j k => by
    have := ggPosDef_root_inner hCt TauCeti.posDef_map_intCast_cartanMatrix_E6 (hb2 j) (hb2 k)
    simpa [G] using this
  have hpairG : ∀ j k, α j (h k) = (c j)⁻¹ * c k * ((G j k : ℤ) : ZMod 3) := fun j k => by
    rw [hαeq j, hh k]
    simp only [LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
    rw [ggCartanRefl_pair_apply t β htβ (b j) (b k)]
    ring
  have hfar : ∀ j k : Fin 5, j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val → G j k = 0 := by
    intro j k hjk
    have hjne : j ≠ k := by intro h; subst h; omega
    have hcond : ¬ (j.val + 1 = k.val ∨ k.val + 1 = j.val) := by omega
    have hA : (CartanMatrix.A 5 j k : ZMod 3) = 0 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hjne, if_neg hcond]
      norm_num
    have hrel : (c j)⁻¹ * c k * ((G j k : ℤ) : ZMod 3) = 0 := by
      rw [← hpairG j k, hpair]
      exact hA
    have hcprod : (c j)⁻¹ * c k ≠ 0 := mul_ne_zero (inv_ne_zero (hc j)) (hc k)
    have hGzero : ((G j k : ℤ) : ZMod 3) = 0 := (mul_eq_zero.mp hrel).resolve_left hcprod
    have hdvd : (3 : ℤ) ∣ G j k := (ZMod.intCast_zmod_eq_zero_iff_dvd (G j k) 3).mp hGzero
    have hb1 : -2 ≤ G j k := (hpos j k).1
    have hb2 : G j k ≤ 2 := (hpos j k).2.1
    omega
  have hnear : ∀ j k : Fin 5, k.val = j.val + 1 →
      (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k := by
    intro j k hjk
    have hsym : G k j = G j k := hGsym j k
    refine ⟨?_, hsym⟩
    have hAj : (CartanMatrix.A 5 j k : ZMod 3) = -1 := by
      have hjne : j ≠ k := by intro h; subst h; omega
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hjne, if_pos (Or.inl hjk.symm)]
      norm_num
    have hAk : (CartanMatrix.A 5 k j : ZMod 3) = -1 := by
      have hkne : k ≠ j := by intro h; subst h; omega
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hkne, if_pos (Or.inr hjk.symm)]
      norm_num
    have hrel1 : (c j)⁻¹ * c k * ((G j k : ℤ) : ZMod 3) = -1 := by
      rw [← hpairG j k, hpair]
      exact hAj
    have hrel2 : (c k)⁻¹ * c j * ((G k j : ℤ) : ZMod 3) = -1 := by
      rw [← hpairG k j, hpair]
      exact hAk
    have hrel2' : (c k)⁻¹ * c j * ((G j k : ℤ) : ZMod 3) = -1 := by
      simpa [hsym] using hrel2
    have hsq : ((G j k : ℤ) : ZMod 3) * ((G j k : ℤ) : ZMod 3) = 1 := by
      have e1 : c k * ((G j k : ℤ) : ZMod 3) = -c j := by
        have h := congrArg (fun t => c j * t) hrel1
        rw [mul_neg, mul_one] at h
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (hc j), one_mul] at h
        exact h
      have e2 : c j * ((G j k : ℤ) : ZMod 3) = -c k := by
        have h := congrArg (fun t => c k * t) hrel2'
        rw [mul_neg, mul_one] at h
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (hc k), one_mul] at h
        exact h
      have hcancel : c j * c k * (((G j k : ℤ) : ZMod 3) * ((G j k : ℤ) : ZMod 3)) =
          c j * c k * 1 := by
        calc c j * c k * (((G j k : ℤ) : ZMod 3) * ((G j k : ℤ) : ZMod 3))
            = (c k * ((G j k : ℤ) : ZMod 3)) * (c j * ((G j k : ℤ) : ZMod 3)) := by ring
          _ = (-c j) * (-c k) := by rw [e1, e2]
          _ = c j * c k := by ring
          _ = c j * c k * 1 := by ring
      exact mul_left_cancel₀ (mul_ne_zero (hc j) (hc k)) hcancel
    by_contra hcontra
    push Not at hcontra
    have hne1 : G j k ≠ 1 := hcontra.1
    have hne2 : G j k ≠ -1 := hcontra.2
    have hb1 : -2 ≤ G j k := (hpos j k).1
    have hb2 : G j k ≤ 2 := (hpos j k).2.1
    set n : ℤ := G j k with hn
    have hb1' : -2 ≤ n := by simpa [hn] using hb1
    have hb2' : n ≤ 2 := by simpa [hn] using hb2
    have hsqn : ((n : ZMod 3) * (n : ZMod 3)) = 1 := by simpa [hn] using hsq
    have hne1' : n ≠ 1 := by simpa [hn] using hne1
    have hne2' : n ≠ -1 := by simpa [hn] using hne2
    have hval : n = 2 ∨ n = -2 := by
      interval_cases n
      · right; rfl
      · exact absurd rfl hne2'
      · simp at hsqn
      · exact absurd rfl hne1'
      · left; rfl
    have hGval : G j k = 2 ∨ G j k = -2 := by simpa [hn] using hval
    fin_cases j
    · have hk : k = 1 := by ext; simp; omega
      subst hk
      rcases hGval with h2 | h2
      · have hb : b 1 = b 0 := (hpos 0 1).2.2.1 h2
        have hfar20 : G 2 0 = 0 := by
          apply hfar
          right
          simp
        have hG_eq : G 2 1 = G 2 0 := by simp [G, hb]
        have hG21 : G 2 1 = 0 := by
          have h := hG_eq
          rw [hfar20] at h
          simpa using h
        have hrel : α 2 (h 1) = 0 := by rw [hpairG 2 1, hG21]; simp
        have hA : (CartanMatrix.A 5 2 1 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
      · have hb : b 1 = -b 0 := (hpos 0 1).2.2.2 h2
        have hfar20 : G 2 0 = 0 := by
          apply hfar
          right
          simp
        have hG_eq : G 2 1 = -G 2 0 := by
          simp only [G, hb]
          rw [mulVec_neg, dotProduct_neg]
        have hG21 : G 2 1 = 0 := by
          have h := hG_eq
          rw [hfar20] at h
          simpa using h
        have hrel : α 2 (h 1) = 0 := by rw [hpairG 2 1, hG21]; simp
        have hA : (CartanMatrix.A 5 2 1 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
    · have hk : k = 2 := by ext; simp; omega
      subst hk
      rcases hGval with h2 | h2
      · have hb : b 2 = b 1 := (hpos 1 2).2.2.1 h2
        have hfar02 : G 0 2 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 0 2 = G 0 1 := by simp [G, hb]
        have hG01 : G 0 1 = 0 := by
          have h := hG_eq
          rw [hfar02] at h
          simpa using h.symm
        have hrel : α 0 (h 1) = 0 := by rw [hpairG 0 1, hG01]; simp
        have hA : (CartanMatrix.A 5 0 1 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
      · have hb : b 2 = -b 1 := (hpos 1 2).2.2.2 h2
        have hfar02 : G 0 2 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 0 2 = -G 0 1 := by
          simp only [G, hb]
          rw [mulVec_neg, dotProduct_neg]
        have hG01 : G 0 1 = 0 := by
          have h := hG_eq
          rw [hfar02] at h
          simpa using h
        have hrel : α 0 (h 1) = 0 := by rw [hpairG 0 1, hG01]; simp
        have hA : (CartanMatrix.A 5 0 1 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
    · have hk : k = 3 := by ext; simp; omega
      subst hk
      rcases hGval with h2 | h2
      · have hb : b 3 = b 2 := (hpos 2 3).2.2.1 h2
        have hfar13 : G 1 3 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 1 3 = G 1 2 := by simp [G, hb]
        have hG12 : G 1 2 = 0 := by
          have h := hG_eq
          rw [hfar13] at h
          simpa using h.symm
        have hrel : α 1 (h 2) = 0 := by rw [hpairG 1 2, hG12]; simp
        have hA : (CartanMatrix.A 5 1 2 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
      · have hb : b 3 = -b 2 := (hpos 2 3).2.2.2 h2
        have hfar13 : G 1 3 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 1 3 = -G 1 2 := by
          simp only [G, hb]
          rw [mulVec_neg, dotProduct_neg]
        have hG12 : G 1 2 = 0 := by
          have h := hG_eq
          rw [hfar13] at h
          simpa using h
        have hrel : α 1 (h 2) = 0 := by rw [hpairG 1 2, hG12]; simp
        have hA : (CartanMatrix.A 5 1 2 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
    · have hk : k = 4 := by ext; simp; omega
      subst hk
      rcases hGval with h2 | h2
      · have hb : b 4 = b 3 := (hpos 3 4).2.2.1 h2
        have hfar24 : G 2 4 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 2 4 = G 2 3 := by simp [G, hb]
        have hG23 : G 2 3 = 0 := by
          have h := hG_eq
          rw [hfar24] at h
          simpa using h.symm
        have hrel : α 2 (h 3) = 0 := by rw [hpairG 2 3, hG23]; simp
        have hA : (CartanMatrix.A 5 2 3 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
      · have hb : b 4 = -b 3 := (hpos 3 4).2.2.2 h2
        have hfar24 : G 2 4 = 0 := by
          apply hfar
          left
          simp
        have hG_eq : G 2 4 = -G 2 3 := by
          simp only [G, hb]
          rw [mulVec_neg, dotProduct_neg]
        have hG23 : G 2 3 = 0 := by
          have h := hG_eq
          rw [hfar24] at h
          simpa using h
        have hrel : α 2 (h 3) = 0 := by rw [hpairG 2 3, hG23]; simp
        have hA : (CartanMatrix.A 5 2 3 : ZMod 3) = -1 := by simp [CartanMatrix.A]
        rw [hpair, hA] at hrel
        norm_num at hrel
    · have hk : k.val = 4 + 1 := hjk
      have hlt := k.isLt
      omega
  have hdet : G.det = 5 + 1 := CFSG.MatrixDet.det_signedPath G hGdiag hfar hnear
  have hdet6 : G.det = 6 := by rw [hdet]; norm_num
  let v : Matrix (Fin 5) (Fin 6) ℤ := Matrix.of b
  have hvCv : v * C * v.transpose = G := by
    ext j k
    simp only [G, v, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, mulVec]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hnotdvd : ¬ (3 : ℤ) ^ 2 ∣ G.det := by rw [hdet6]; norm_num
  have hindep_rows : LinearIndependent (ZMod 3) (fun j => (v.map (Int.cast : ℤ → ZMod 3)) j) := by
    apply CFSG.MatrixDet.linearIndependent_zmod_of_not_sq_dvd_det_gram C v
    rw [hvCv]
    exact hnotdvd
  let γ : Fin 5 → Module.Dual (ZMod 3) V := fun j => ∑ l, ((b j l : ℤ) : ZMod 3) • β l
  have hγeq : γ = fun j =>
      Fintype.linearCombination (ZMod 3) β ((v.map (Int.cast : ℤ → ZMod 3)) j) := by
    funext j
    simp [γ, v, Fintype.linearCombination_apply, Matrix.of_apply]
  have hker : LinearMap.ker (Fintype.linearCombination (ZMod 3) β) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hβ.fintypeLinearCombination_injective
  have hindγ : LinearIndependent (ZMod 3) γ := by
    have h := hindep_rows.map' (Fintype.linearCombination (ZMod 3) β) hker
    rw [hγeq]
    exact h
  let w : Fin 5 → (ZMod 3)ˣ := fun j => Units.mk0 ((c j)⁻¹) (inv_ne_zero (hc j))
  have hαγ : α = w • γ := by
    funext j
    rw [hαeq j]
    simp [w, γ]
  rw [hαγ]
  exact hindγ.units_smul w

theorem ggHeart_restrict {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V} (hTA : ∀ a ∈ A, ∀ v, a v - v ∈ T)
    {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A) :
    ∃ q : ↥T ≃ₗ[ZMod p] ↥T, ∀ w : ↥T, ((q w : ↥T) : V) = a (w : V) := by
  have hmap : T.map (a : V →ₗ[ZMod p] V) = T := by
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_map] at hv
      obtain ⟨t, ht, rfl⟩ := hv
      have h := hTA a ha t
      simpa using T.add_mem h ht
    · intro w hw
      rw [Submodule.mem_map]
      refine ⟨a.symm w, ?_, a.apply_symm_apply w⟩
      have h := hTA a.symm (A.inv_mem ha) w
      simpa using T.add_mem h hw
  exact ⟨a.ofSubmodules T T hmap, fun w => LinearEquiv.ofSubmodules_apply a hmap w⟩

theorem ggHeart_refl_lift {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
    (hTA : ∀ a ∈ A, ∀ v, a v - v ∈ T) (hfaith : ∀ a ∈ A, (∀ v ∈ T, a v = v) → a = 1)
    {u : ↥T} {φ : Module.Dual (ZMod p) ↥T} (hφ : φ u = 2) {s : V ≃ₗ[ZMod p] V} (hsA : s ∈ A)
    (hs : ∀ w : ↥T, s (w : V) = ((Module.reflection hφ w : ↥T) : V)) :
    ∃ β : Module.Dual (ZMod p) V, (∀ v, s v = v - β v • (u : V)) ∧ ∀ w : ↥T, β (w : V) = φ w := by
  have hss : s * s = 1 := by
    apply hfaith (s * s) (A.mul_mem hsA hsA)
    intro v hv
    have h1 : s v = ((Module.reflection hφ ⟨v, hv⟩ : ↥T) : V) := hs ⟨v, hv⟩
    calc (s * s) v = s (s v) := rfl
      _ = s ((Module.reflection hφ ⟨v, hv⟩ : ↥T) : V) := by rw [h1]
      _ = ((Module.reflection hφ (Module.reflection hφ ⟨v, hv⟩) : ↥T) : V) :=
            hs (Module.reflection hφ ⟨v, hv⟩)
      _ = ((⟨v, hv⟩ : ↥T) : V) := by rw [Module.involutive_reflection hφ ⟨v, hv⟩]
      _ = v := rfl
  have hss' : ∀ v : V, s (s v) = v := fun v => by
    simpa using congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hss
  let D : V →ₗ[ZMod p] ↥T :=
    LinearMap.codRestrict T ((s : V →ₗ[ZMod p] V) - LinearMap.id)
      (fun v => by simpa using hTA s hsA v)
  have hD_apply : ∀ v : V, ((D v : ↥T) : V) = s v - v := by
    intro v
    simp only [D, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_toLinearMap]
  let β : Module.Dual (ZMod p) V := (-(2⁻¹) : ZMod p) • (φ.comp D)
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) (q := 2) (by norm_num) hp
  have hmain : ∀ v : V, s v = v - β v • (u : V) := by
    intro v
    have hA : s ((D v : ↥T) : V) = -((D v : ↥T) : V) := by
      rw [hD_apply v, map_sub, hss' v]
      abel
    have hB : Module.reflection hφ (D v) = -(D v) := by
      have h := hA
      rw [hs (D v)] at h
      exact Subtype.ext (by simpa only [Submodule.coe_neg] using h)
    have hB' : D v - φ (D v) • u = -(D v) := by
      rw [Module.reflection_apply] at hB
      exact hB
    have hC : (2 : ZMod p) • (D v) = φ (D v) • u := by
      rw [two_smul]
      have h := hB'
      rw [sub_eq_iff_eq_add] at h
      nth_rewrite 1 [h]
      abel
    have hE : D v = (2⁻¹ * φ (D v)) • u := by
      calc D v = ((2⁻¹ : ZMod p) * 2) • D v := by rw [inv_mul_cancel₀ h2, one_smul]
        _ = (2⁻¹ : ZMod p) • ((2 : ZMod p) • D v) := by rw [smul_smul]
        _ = (2⁻¹ : ZMod p) • (φ (D v) • u) := by rw [hC]
        _ = (2⁻¹ * φ (D v)) • u := by rw [smul_smul]
    have hDv : ((D v : ↥T) : V) = (2⁻¹ * φ (D v)) • (u : V) := by
      conv_lhs => rw [hE]
      rw [Submodule.coe_smul]
    calc s v = v + ((D v : ↥T) : V) := by rw [hD_apply v]; abel
      _ = v + (2⁻¹ * φ (D v)) • (u : V) := by rw [hDv]
      _ = v - β v • (u : V) := by
          have hβ : β v = -(2⁻¹ * φ (D v)) := by
            simp only [β, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
          rw [hβ, neg_smul, sub_neg_eq_add]
  refine ⟨β, hmain, ?_⟩
  intro w
  have hDw : D (w : V) = Module.reflection hφ w - w := by
    apply Subtype.ext
    simp only [hD_apply (w : V), Submodule.coe_sub, hs w]
  have hφD : φ (D (w : V)) = -(φ w * 2) := by
    rw [hDw, map_sub, Module.reflection_apply]
    simp only [map_sub, map_smul, hφ, smul_eq_mul]
    ring
  have hβ : β (w : V) = -(2⁻¹ * φ (D (w : V))) := by
    simp only [β, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
  rw [hβ, hφD, mul_neg, neg_neg, mul_comm (φ w) 2, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

theorem ggHeart_eq_closure {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
    {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)} (hTA : ∀ a ∈ A, ∀ v, a v - v ∈ T)
    (hfaith : ∀ a ∈ A, (∀ v ∈ T, a v = v) → a = 1)
    (hAT : ∀ q, q ∈ AT ↔ ∃ a ∈ A, ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V))
    {ι : Type*} (ρ : ι → (↥T ≃ₗ[ZMod p] ↥T)) (hρ : AT = Subgroup.closure (Set.range ρ))
    (s : ι → (V ≃ₗ[ZMod p] V)) (hsA : ∀ i, s i ∈ A)
    (hs : ∀ i (w : ↥T), s i (w : V) = ((ρ i w : ↥T) : V)) :
    A = Subgroup.closure (Set.range s) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨q, hq⟩ := ggHeart_restrict hTA ha
    have hq' : ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V) := fun w => (hq w).symm
    have hqAT : q ∈ AT := (hAT q).mpr ⟨a, ha, hq'⟩
    have hqclos : q ∈ Subgroup.closure (Set.range ρ) := by
      rw [← hρ]; exact hqAT
    refine Subgroup.closure_induction (k := Set.range ρ)
      (p := fun q (_ : q ∈ Subgroup.closure (Set.range ρ)) =>
        ∀ a ∈ A, (∀ w : ↥T, a (w : V) = ((q w : ↥T) : V)) →
          a ∈ Subgroup.closure (Set.range s))
      ?_ ?_ ?_ ?_ hqclos a ha hq'
    · rintro q ⟨i, rfl⟩ a ha haeq
      have h1 : (s i)⁻¹ * a = 1 := by
        apply hfaith ((s i)⁻¹ * a) (A.mul_mem (A.inv_mem (hsA i)) ha)
        intro w hw
        rw [LinearEquiv.mul_apply]
        apply (s i).injective
        change (s i) ((s i).symm (a w)) = (s i) w
        rw [LinearEquiv.apply_symm_apply, haeq ⟨w, hw⟩, hs i ⟨w, hw⟩]
      have : a = s i := by
        have h := congrArg (fun x => s i * x) h1
        simpa [mul_assoc] using h
      rw [this]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · rintro a ha haeq
      have : a = 1 := by
        apply hfaith a ha
        intro w hw
        simpa using haeq ⟨w, hw⟩
      rw [this]
      exact Subgroup.one_mem _
    · rintro x y hx hy ihx ihy a ha haeq
      have hxAT : x ∈ AT := by rw [hρ]; exact hx
      obtain ⟨a₁, ha₁A, ha₁res⟩ := (hAT x).mp hxAT
      have ha₂A : a₁⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha₁A) ha
      have ha₂res : ∀ w : ↥T, (a₁⁻¹ * a) (w : V) = ((y w : ↥T) : V) := by
        intro w
        rw [LinearEquiv.mul_apply]
        apply a₁.injective
        change a₁ (a₁.symm (a w)) = a₁ ↑(y w)
        rw [LinearEquiv.apply_symm_apply, ha₁res (y w)]
        exact haeq w
      have h₁ := ihx a₁ ha₁A ha₁res
      have h₂ := ihy (a₁⁻¹ * a) ha₂A ha₂res
      have : a = a₁ * (a₁⁻¹ * a) := (mul_inv_cancel_left a₁ a).symm
      rw [this]
      exact Subgroup.mul_mem _ h₁ h₂
    · rintro x hx ih a ha haeq
      have hinv : ∀ w : ↥T, a⁻¹ (w : V) = ((x w : ↥T) : V) := by
        intro w
        apply a.injective
        change a (a.symm (w : V)) = a ↑(x w)
        rw [LinearEquiv.apply_symm_apply, haeq (x w)]
        simp
      have hmem : a⁻¹ ∈ Subgroup.closure (Set.range s) := ih a⁻¹ (A.inv_mem ha) hinv
      simpa using Subgroup.inv_mem (Subgroup.closure (Set.range s)) hmem
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hsA i

theorem ggHeart_reflClosed {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
    {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)} (hTA : ∀ a ∈ A, ∀ v, a v - v ∈ T)
    (hfaith : ∀ a ∈ A, (∀ v ∈ T, a v = v) → a = 1)
    (hAT : ∀ q, q ∈ AT ↔ ∃ a ∈ A, ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V))
    {ι : Type} (ρ : ι → (↥T ≃ₗ[ZMod p] ↥T)) (hρ : AT = Subgroup.closure (Set.range ρ))
    (s : ι → (V ≃ₗ[ZMod p] V)) (hsA : ∀ i, s i ∈ A)
    (hs : ∀ i (w : ↥T), s i (w : V) = ((ρ i w : ↥T) : V))
    (hconj : ∀ q ∈ AT, q ^ 2 = 1 → q ≠ 1 →
      (∃ (v : ↥T) (f : Module.Dual (ZMod p) ↥T), ∀ w, q w = w - f w • v) →
        ∃ g ∈ AT, ∃ i, q = g * ρ i * g⁻¹) :
    GGReflClosed s := by
  unfold GGReflClosed ggReflConj
  intro r hr hr2 hr1 ⟨v, f, hvf⟩
  have hAle : Subgroup.closure (Set.range s) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hsA i
  have hrA : r ∈ A := hAle hr
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hr1 (LinearEquiv.ext fun w => by simp [hvf w])
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hcon
    exact hf0 (LinearMap.ext fun y => not_not.mp (not_exists.mp hcon y))
  have hmem : r x - x ∈ T := hTA r hrA x
  have hfxv : f x • v ∈ T := by
    have hneg : f x • v = -(r x - x) := by rw [hvf x]; module
    rw [hneg]
    exact T.neg_mem hmem
  have hvT : v ∈ T := by
    have h2 : (f x)⁻¹ • (f x • v) ∈ T := T.smul_mem _ hfxv
    simpa [smul_smul, inv_mul_cancel₀ hx] using h2
  obtain ⟨q, hqres⟩ := ggHeart_restrict hTA hrA
  have hqres' : ∀ w : ↥T, r (w : V) = ((q w : ↥T) : V) := fun w => (hqres w).symm
  have hqAT : q ∈ AT := (hAT q).mpr ⟨r, hrA, hqres'⟩
  have hq2 : q ^ 2 = 1 := by
    rw [pow_two]
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    show ((q (q w) : ↥T) : V) = (w : V)
    have hr2' : r * r = 1 := by rw [← pow_two]; exact hr2
    rw [hqres (q w), hqres w, ← LinearEquiv.mul_apply, hr2']
    rfl
  have hq1 : q ≠ 1 := by
    intro hqeq
    apply hr1
    apply hfaith r hrA
    intro w hw
    rw [hqres' ⟨w, hw⟩, hqeq]
    rfl
  have hqform : ∃ (v : ↥T) (f : Module.Dual (ZMod p) ↥T), ∀ w, q w = w - f w • v := by
    refine ⟨⟨v, hvT⟩, f.comp T.subtype, ?_⟩
    intro w
    apply Subtype.ext
    show ((q w : ↥T) : V) = ((w : V) - f (w : V) • v)
    rw [hqres w, hvf (w : V)]
  obtain ⟨g, hgAT, i, hqi⟩ := hconj q hqAT hq2 hq1 hqform
  obtain ⟨ĝ, hĝA, hĝres⟩ := (hAT g).mp hgAT
  have hAeq : A = Subgroup.closure (Set.range s) :=
    ggHeart_eq_closure hTA hfaith hAT ρ hρ s hsA hs
  have hĝclos : ĝ ∈ Subgroup.closure (Set.range s) := by
    rw [← hAeq]; exact hĝA
  set t : V ≃ₗ[ZMod p] V := ĝ * s i * ĝ⁻¹ with ht_def
  have htA : t ∈ A := by
    rw [ht_def]
    exact A.mul_mem (A.mul_mem hĝA (hsA i)) (A.inv_mem hĝA)
  have hginv : ∀ w : ↥T, ĝ⁻¹ (w : V) = ((g⁻¹ w : ↥T) : V) := by
    intro w
    apply ĝ.injective
    change ĝ (ĝ.symm (w : V)) = ĝ ↑(g.symm w)
    rw [LinearEquiv.apply_symm_apply, hĝres (g.symm w), LinearEquiv.apply_symm_apply]
  have htres : ∀ w : ↥T, t (w : V) = (((g * ρ i * g⁻¹) w : ↥T) : V) := by
    intro w
    rw [ht_def]
    simp only [LinearEquiv.mul_apply]
    rw [hginv w, hs i (g⁻¹ w), hĝres (ρ i (g⁻¹ w))]
  have hconc : ∀ w : ↥T, t (w : V) = r (w : V) := by
    intro w
    rw [htres w, ← hqi]
    exact hqres w
  have htr : t⁻¹ * r = 1 := by
    apply hfaith (t⁻¹ * r) (A.mul_mem (A.inv_mem htA) hrA)
    intro w hw
    rw [LinearEquiv.mul_apply]
    apply t.injective
    change t (t.symm (r w)) = t w
    rw [LinearEquiv.apply_symm_apply]
    exact (hconc ⟨w, hw⟩).symm
  have hrt : r = t := by
    rw [← mul_inv_cancel_left t r, htr, mul_one]
  exact ⟨ĝ, hĝclos, i, hrt.trans ht_def⟩

theorem ggHeart_dual_linearIndependent {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (β : Fin n → Module.Dual K V)
    (hn : Module.finrank K V = n) (h : ∀ v, (∀ i, β i v = 0) → v = 0) :
    LinearIndependent K β := by
  classical
  have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hf_inj : Function.Injective (LinearMap.pi β) := by
    intro x y hxy
    have hsub : LinearMap.pi β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hker : ∀ i, β i (x - y) = 0 := by
      intro i
      have := congrFun hsub i
      simpa using this
    have h0 := h (x - y) hker
    rwa [sub_eq_zero] at h0
  have hf_surj : Function.Surjective (LinearMap.pi β) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hn, hfin])).mp hf_inj
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨v, hv⟩ := hf_surj (Pi.single i 1)
  have hβv : ∀ j, β j v = (Pi.single i (1 : K) : Fin n → K) j := by
    intro j
    have := congrFun hv j
    simpa using this
  have hsum : (∑ j, c j • β j v) = 0 := by
    have := congrArg (fun g : V →ₗ[K] K => g v) hc
    simpa using this
  have hsum2 : (∑ j, c j • (Pi.single i (1 : K) : Fin n → K) j) = 0 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [hβv j]
  have hsum3 : (∑ j, c j • (Pi.single i (1 : K) : Fin n → K) j) = c i := by
    rw [Finset.sum_eq_single i
      (fun j _ hj => by
        rw [Pi.single_eq_of_ne (M := fun _ : Fin n => K) hj, smul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  rw [hsum3] at hsum2
  exact hsum2

theorem ggSmallE6HeartInput_holds :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
      (A : Subgroup (V ≃ₗ[ZMod 3] V)) (T : Submodule (ZMod 3) V)
      (AT : Subgroup (↥T ≃ₗ[ZMod 3] ↥T)) (Q : QuadraticForm (ZMod 3) ↥T) (c : ZMod 3)
      (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V) (r : Fin 5 → (V ≃ₗ[ZMod 3] V)),
      Module.finrank (ZMod 3) V = 6 → Module.finrank (ZMod 3) ↥T = 5 →
      (∀ a ∈ A, ∀ v, a v - v ∈ T) →
      (∀ v, (∀ a ∈ A, a v = v) → v = 0) →
      (∀ a ∈ A, (∀ v ∈ T, a v = v) → a = 1) →
      (∀ q, q ∈ AT ↔ ∃ a ∈ A, ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V)) →
      (QuadraticMap.polarBilin Q).Nondegenerate → c ≠ 0 →
      AT = Subgroup.closure (ZS.ClassRefl 3 Q c) →
      (LinearEquiv.neg (ZMod 3) : ↥T ≃ₗ[ZMod 3] ↥T) ∉ AT →
      (∀ i, r i ∈ A) → (∀ i v, r i v = v - α i v • h i) →
      (∀ i j, α i (h j) = (CartanMatrix.A 5 i j : ZMod 3)) →
      LinearIndependent (ZMod 3) α := by
  classical
  intro V _ _ _ A T AT Q c h α r hV hT hTA hfix hfaith hAT hQ hc hATeq hneg hrA hr hpair
  obtain ⟨u, φ, hφ, hK, hgen, hcl⟩ := ZS.owR35_e6Frame Q hQ hT c hc (hATeq ▸ hneg)
  let ρ : Fin 6 → (↥T ≃ₗ[ZMod 3] ↥T) := fun i => Module.reflection (hφ i)
  have hρ : AT = Subgroup.closure (Set.range ρ) := hATeq.trans hgen
  have hρAT : ∀ i, ρ i ∈ AT := fun i => hρ.symm ▸ Subgroup.subset_closure ⟨i, rfl⟩
  choose s hsA hs using fun i => (hAT (ρ i)).mp (hρAT i)
  choose β hsβ hβext using fun i =>
    ggHeart_refl_lift (p := 3) (by decide) hTA hfaith (hφ i) (hsA i) (hs i)
  have hAs : A = Subgroup.closure (Set.range s) := ggHeart_eq_closure hTA hfaith hAT ρ hρ s hsA hs
  have htβ : ∀ i j, β i ((u j : ↥T) : V) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hβext i (u j), hK i j]
  have hconjT : ∀ q ∈ AT, q ^ 2 = 1 → q ≠ 1 →
      (∃ (v : ↥T) (f : Module.Dual (ZMod 3) ↥T), ∀ w, q w = w - f w • v) →
        ∃ g ∈ AT, ∃ i, q = g * ρ i * g⁻¹ := by
    intro q hqA hq2 hq1 ⟨v, f, hvf⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hq1 (LinearEquiv.ext fun w => by rw [hvf]; simp)
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hq1 (LinearEquiv.ext fun w => by rw [hvf]; simp)
    obtain ⟨w₀, hw₀⟩ : ∃ w, f w ≠ 0 := by
      by_contra hcon
      exact hf0 (LinearMap.ext fun w => by
        by_contra hw
        exact hcon ⟨w, hw⟩)
    have hfv : f v = 2 := by
      have h1 : q (q w₀) = w₀ := by
        rw [← LinearEquiv.mul_apply, ← pow_two, hq2]; rfl
      rw [hvf (q w₀), hvf w₀, map_sub, map_smul, smul_eq_mul] at h1
      have h3 : (f w₀ * (f v - 2)) • v = 0 := by linear_combination (norm := module) h1
      have h4 := (smul_eq_zero.mp h3).resolve_right hv0
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left hw₀)
    have hIsRefl : ZS.IsRefl 3 q := ggResII_isRefl (p := 3) (by decide) hvf hfv
    have hCls : q ∈ ZS.ClassRefl 3 Q c :=
      ZS.wit_classRefl_of_mem_closure (p := 3) (by decide) (by decide) Q hQ c hc hIsRefl
        (hATeq ▸ hqA)
    obtain ⟨g, hg, i, hgi⟩ := hcl q hCls
    exact ⟨g, hρ.symm ▸ hg, i, hgi⟩
  have hRC : GGReflClosed s :=
    ggHeart_reflClosed (p := 3) hTA hfaith hAT ρ hρ s hsA hs hconjT
  have hβ : LinearIndependent (ZMod 3) β := by
    refine ggHeart_dual_linearIndependent β hV ?_
    intro v hv
    apply hfix v
    have hstab : Subgroup.closure (Set.range s) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod 3] V) v := by
      rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      show (s i) v = v
      rw [hsβ i v, hv i, zero_smul, sub_zero]
    rw [hAs]
    intro a ha
    have := hstab ha
    simpa [LinearEquiv.smul_def] using this
  exact ggE6Three_A5_linearIndependent (fun i => (u i : V)) β hβ htβ s hsβ hRC h α hpair r hr
    (fun j => hAs ▸ hrA j)

end CFSG.StandardType

end

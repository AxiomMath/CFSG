module

public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjFive
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.E9Q8

open Module Module.End Subgroup Polynomial

section Roots

variable {K : Type*} [Field K]

theorem exists_isPrimitiveRoot_three [IsAlgClosed K] (h3 : (3 : K) ≠ 0) :
    ∃ ω : K, IsPrimitiveRoot ω 3 := by
  have hdeg : (X ^ 2 + X + 1 : K[X]).degree ≠ 0 := by
    rw [show (X ^ 2 + X + 1 : K[X]).degree = 2 by compute_degree!]
    norm_num
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (X ^ 2 + X + 1 : K[X]) hdeg
  have h : ω ^ 2 + ω + 1 = 0 := by simpa [Polynomial.IsRoot] using hω
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨ω, IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime ?_ ?_)⟩
  · linear_combination (ω - 1) * h
  · intro h1
    rw [h1] at h
    apply h3
    linear_combination h

@[expose] def cr (ω : K) (s : ZMod 3) : K := ω ^ s.val

theorem cr_add {ω : K} (hω : ω ^ 3 = 1) (s t : ZMod 3) : cr ω (s + t) = cr ω s * cr ω t := by
  rw [cr, cr, cr, ZMod.val_add, ← pow_add, ← pow_mod_orderOf, ← pow_mod_orderOf ω (s.val + t.val)]
  have hdvd : orderOf ω ∣ 3 := orderOf_dvd_of_pow_eq_one hω
  rw [Nat.mod_mod_of_dvd _ hdvd]

theorem cr_two_mul {ω : K} (hω : ω ^ 3 = 1) (s : ZMod 3) : cr ω (2 * s) = cr ω s ^ 2 := by
  rw [two_mul, cr_add hω, sq]

theorem exists_cr_eq {ω c : K} (hω : IsPrimitiveRoot ω 3) (hc : c ^ 3 = 1) :
    ∃ e : ZMod 3, c = cr ω e := by
  obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one hc
  refine ⟨(i : ZMod 3), ?_⟩
  rw [cr, ZMod.val_cast_of_lt hi]

theorem cr_injective {ω : K} (hω : IsPrimitiveRoot ω 3) : Function.Injective (cr ω) := by
  intro s t h
  exact ZMod.val_injective 3 (hω.pow_inj (ZMod.val_lt s) (ZMod.val_lt t) h)

theorem cr_pow_three {ω : K} (hω : ω ^ 3 = 1) (s : ZMod 3) : cr ω s ^ 3 = 1 := by
  rw [cr, ← pow_mul, mul_comm, pow_mul, hω, one_pow]

end Roots

@[expose] def fI (e : ZMod 3 × ZMod 3) (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.2 + e.1, 2 * x.1 + e.2)

@[expose] def fJ (e : ZMod 3 × ZMod 3) (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.1 + x.2 + e.1, x.1 + 2 * x.2 + e.2)

@[expose] def closeStep (e e' : ZMod 3 × ZMod 3) (T : Finset (ZMod 3 × ZMod 3)) :
    Finset (ZMod 3 × ZMod 3) :=
  T ∪ T.image (fI e) ∪ T.image (fJ e')

theorem orbit_check : ∀ e e' x : ZMod 3 × ZMod 3, 8 ≤ ((closeStep e e')^[5] {x}).card ∨
    (fI e x = x ∧ fJ e' x = x ∧ ∀ y, fI e y = y → fJ e' y = y → y = x) := by
  decide +kernel

theorem iterate_subset {e e' : ZMod 3 × ZMod 3} {S : Finset (ZMod 3 × ZMod 3)}
    (hI : ∀ y ∈ S, fI e y ∈ S) (hJ : ∀ y ∈ S, fJ e' y ∈ S) {x : ZMod 3 × ZMod 3} (hx : x ∈ S) :
    ∀ n : ℕ, (closeStep e e')^[n] {x} ⊆ S := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro y hy
    simp only [closeStep, Finset.mem_union, Finset.mem_image] at hy
    rcases hy with (hy | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
    · exact ih hy
    · exact hI z (ih hz)
    · exact hJ z (ih hz)

theorem eq_of_mem_of_closed {e e' : ZMod 3 × ZMod 3} {S : Finset (ZMod 3 × ZMod 3)}
    (hS : S.card ≤ 7) (hI : ∀ y ∈ S, fI e y ∈ S) (hJ : ∀ y ∈ S, fJ e' y ∈ S)
    {x y : ZMod 3 × ZMod 3} (hx : x ∈ S) (hy : y ∈ S) : x = y := by
  have key : ∀ z ∈ S, fI e z = z ∧ fJ e' z = z ∧ ∀ w, fI e w = w → fJ e' w = w → w = z := by
    intro z hz
    rcases orbit_check e e' z with h8 | h
    · have := Finset.card_le_card (iterate_subset hI hJ hz 5)
      omega
    · exact h
  obtain ⟨-, -, hxu⟩ := key x hx
  obtain ⟨hyI, hyJ, -⟩ := key y hy
  exact (hxu y hyI hyJ).symm

section Joint

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def jointE (A B : End K V) (ω : K) (x : ZMod 3 × ZMod 3) : Submodule K V :=
  A.eigenspace (cr ω x.1) ⊓ B.eigenspace (cr ω x.2)

theorem mem_jointE_iff {A B : End K V} {ω : K} {x : ZMod 3 × ZMod 3} {v : V} :
    v ∈ jointE A B ω x ↔ A v = cr ω x.1 • v ∧ B v = cr ω x.2 • v := by
  simp only [jointE, Submodule.mem_inf, mem_eigenspace_iff]

theorem iSupIndep_jointE {A B : End K V} {ω : K} (hω : IsPrimitiveRoot ω 3) (hAB : Commute A B) :
    iSupIndep (jointE A B ω) := by
  let f : Fin 2 → End K V := ![A, B]
  have hf : ∀ i j : Fin 2, Commute (f j) (f i) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl A
    · exact hAB.symm
    · exact hAB
    · exact Commute.refl B
  have hind := independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => mapsTo_genEigenspace_of_comm (hf i j) φ ⊤)
  let χ : ZMod 3 × ZMod 3 → Fin 2 → K := fun x => ![cr ω x.1, cr ω x.2]
  have hχ : Function.Injective χ := by
    intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [χ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext (cr_injective hω h0) (cr_injective hω h1)
  refine (hind.comp hχ).mono (fun x => ?_)
  simp only [Function.comp_apply, jointE, χ]
  refine le_iInf fun i => ?_
  fin_cases i
  · exact inf_le_left.trans eigenspace_le_maxGenEigenspace
  · exact inf_le_right.trans eigenspace_le_maxGenEigenspace

theorem card_jointE_le_finrank [FiniteDimensional K V] {A B : End K V} {ω : K}
    (hω : IsPrimitiveRoot ω 3) (hAB : Commute A B) :
    (Finset.univ.filter (fun x => jointE A B ω x ≠ ⊥)).card ≤ finrank K V := by
  classical
  have h := (iSupIndep_jointE hω hAB).subtype_ne_bot_le_finrank
  rwa [Fintype.card_subtype] at h

theorem pow_three_of_hasEigenvector {T : End K V} (hT : T ^ 3 = 1) {μ : K} {x : V}
    (hx : T.HasEigenvector μ x) : μ ^ 3 = 1 := by
  have h := hx.pow_apply 3
  rw [hT, Module.End.one_apply] at h
  have h0 : (μ ^ 3 - 1) • x = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx.2)

theorem exists_jointE_ne_bot_of_eigenspace [IsAlgClosed K] [FiniteDimensional K V] {A B : End K V}
    {ω : K} (hω : IsPrimitiveRoot ω 3) (hAB : A * B = B * A) (hB : B ^ 3 = 1) {s : ZMod 3}
    (hs : A.eigenspace (cr ω s) ≠ ⊥) : ∃ t : ZMod 3, jointE A B ω (s, t) ≠ ⊥ := by
  have hBE : ∀ x ∈ A.eigenspace (cr ω s), B x ∈ A.eigenspace (cr ω s) := by
    intro x hx
    rw [mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply, hx, map_smul]
  haveI : Nontrivial (A.eigenspace (cr ω s)) := Submodule.nontrivial_iff_ne_bot.2 hs
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue (B.restrict hBE)
  obtain ⟨v, hv⟩ := hν.exists_hasEigenvector
  have hBv : B v = ν • (v : V) := by
    have := congrArg Subtype.val (mem_eigenspace_iff.1 hv.1)
    simpa [LinearMap.restrict_coe_apply] using this
  have hv0 : (v : V) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hν3 : ν ^ 3 = 1 :=
    pow_three_of_hasEigenvector hB (hasEigenvector_iff.2 ⟨mem_eigenspace_iff.2 hBv, hv0⟩)
  obtain ⟨t, rfl⟩ := exists_cr_eq hω hν3
  refine ⟨t, fun h => hv0 ?_⟩
  have hmem : (v : V) ∈ jointE A B ω (s, t) :=
    mem_jointE_iff.2 ⟨mem_eigenspace_iff.1 v.2, hBv⟩
  rw [h] at hmem
  exact (Submodule.mem_bot K).1 hmem

theorem exists_eigenspace_ne_bot [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V]
    {A : End K V} {ω : K} (hω : IsPrimitiveRoot ω 3) (hA : A ^ 3 = 1) :
    ∃ s : ZMod 3, A.eigenspace (cr ω s) ≠ ⊥ := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨s, rfl⟩ := exists_cr_eq hω (pow_three_of_hasEigenvector hA hv)
  exact ⟨s, hasEigenvalue_iff.1 (hasEigenvalue_of_hasEigenvector hv)⟩

end Joint


section Core

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_three_of_twist [Nontrivial V] {X Y M : End K V} {c : K} (hX : X ^ 3 = 1)
    (hY : Y ^ 3 = 1) (hM : Function.Injective M) (h : X * M = M * (c • Y)) : c ^ 3 = 1 := by
  have h3 : M * (c • Y) ^ 3 = X ^ 3 * M :=
    SemiconjBy.pow_right (show SemiconjBy M (c • Y) X from h.symm) 3
  rw [hX, one_mul, _root_.smul_pow, hY, mul_smul_comm, mul_one] at h3
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hMv : M v ≠ 0 := fun h0 => hv (hM (by rw [h0, map_zero]))
  have h4 := congrArg (fun T : End K V => T v) h3
  simp only [LinearMap.smul_apply] at h4
  have h5 : (c ^ 3 - 1) • M v = 0 := by rw [sub_smul, one_smul, h4, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_right hMv)

theorem apply_twist {X Y T : End K V} {c μ : K} {v : V} (h : X * T = T * (c • Y))
    (hv : Y v = μ • v) : X (T v) = (c * μ) • T v := by
  rw [← Module.End.mul_apply, h, Module.End.mul_apply, LinearMap.smul_apply, hv, smul_smul,
    map_smul]

theorem eq_smul_one_of_q8 [IsAlgClosed K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hV : finrank K V ≤ 7) {A B M N : End K V} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) (hM : Function.Injective M) (hN : Function.Injective N)
    {c₁ c₂ c₃ c₄ : K} (hMA : A * M = M * (c₁ • B)) (hMB : B * M = M * (c₂ • A ^ 2))
    (hNA : A * N = N * (c₃ • (A * B))) (hNB : B * N = N * (c₄ • (A * B ^ 2))) :
    ∃ μ : K, A = μ • 1 := by
  rcases subsingleton_or_nontrivial V with hV0 | hV0
  · exact ⟨1, LinearMap.ext fun x => Subsingleton.elim _ _⟩
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_three h3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hAB' : Commute A B := hAB
  have hA2 : (A ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hA, one_pow]
  have hAB3 : (A * B) ^ 3 = 1 := by rw [hAB'.mul_pow, hA, hB, one_mul]
  have hAB23 : (A * B ^ 2) ^ 3 = 1 := by
    rw [(hAB'.pow_right 2).mul_pow, hA, ← pow_mul, mul_comm, pow_mul, hB, one_pow, one_mul]
  obtain ⟨e₁, rfl⟩ := exists_cr_eq hω (pow_three_of_twist hA hB hM hMA)
  obtain ⟨e₂, rfl⟩ := exists_cr_eq hω (pow_three_of_twist hB hA2 hM hMB)
  obtain ⟨e₃, rfl⟩ := exists_cr_eq hω (pow_three_of_twist hA hAB3 hN hNA)
  obtain ⟨e₄, rfl⟩ := exists_cr_eq hω (pow_three_of_twist hB hAB23 hN hNB)
  classical
  set S := Finset.univ.filter (fun x => jointE A B ω x ≠ ⊥) with hSdef
  have hS7 : S.card ≤ 7 := (card_jointE_le_finrank hω hAB').trans hV
  have hmemS : ∀ x, x ∈ S ↔ jointE A B ω x ≠ ⊥ := fun x => by simp [hSdef]
  have hmove : ∀ T : End K V, Function.Injective T →
      ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3,
      (∀ x v, v ∈ jointE A B ω x → T v ∈ jointE A B ω (f x)) → ∀ x ∈ S, f x ∈ S := by
    intro T hT f hf x hx
    rw [hmemS] at hx ⊢
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
    intro hbot
    have h1 := hf x v hv
    rw [hbot, Submodule.mem_bot] at h1
    exact hv0 (hT (by rw [h1, map_zero]))
  have hA2v : ∀ x v, v ∈ jointE A B ω x → (A ^ 2) v = (cr ω x.1 ^ 2) • v := by
    intro x v hv
    rw [mem_jointE_iff] at hv
    rw [sq, Module.End.mul_apply, hv.1, map_smul, hv.1, smul_smul, sq]
  have hABv : ∀ x v, v ∈ jointE A B ω x → (A * B) v = (cr ω x.1 * cr ω x.2) • v := by
    intro x v hv
    rw [mem_jointE_iff] at hv
    rw [Module.End.mul_apply, hv.2, map_smul, hv.1, smul_smul, mul_comm]
  have hAB2v : ∀ x v, v ∈ jointE A B ω x →
      (A * B ^ 2) v = (cr ω x.1 * cr ω x.2 ^ 2) • v := by
    intro x v hv
    rw [mem_jointE_iff] at hv
    have hB2 : (B ^ 2) v = (cr ω x.2 ^ 2) • v := by
      rw [sq, Module.End.mul_apply, hv.2, map_smul, hv.2, smul_smul, sq]
    rw [Module.End.mul_apply, hB2, map_smul, hv.1, smul_smul, mul_comm]
  have hI : ∀ x ∈ S, fI (e₁, e₂) x ∈ S := hmove M hM _ (fun x v hv => by
    have hv' := mem_jointE_iff.1 hv
    refine mem_jointE_iff.2 ⟨?_, ?_⟩
    · rw [apply_twist hMA hv'.2, fI, cr_add hω3, mul_comm]
    · rw [apply_twist hMB (hA2v x v hv), fI, cr_add hω3, cr_two_mul hω3, mul_comm])
  have hJ : ∀ x ∈ S, fJ (e₃, e₄) x ∈ S := hmove N hN _ (fun x v hv => by
    refine mem_jointE_iff.2 ⟨?_, ?_⟩
    · rw [apply_twist hNA (hABv x v hv), fJ, cr_add hω3, cr_add hω3, mul_comm]
    · rw [apply_twist hNB (hAB2v x v hv), fJ, cr_add hω3, cr_add hω3, cr_two_mul hω3,
        mul_comm])
  obtain ⟨s₀, hs₀⟩ := exists_eigenspace_ne_bot hω hA
  obtain ⟨t₀, ht₀⟩ := exists_jointE_ne_bot_of_eigenspace hω hAB hB hs₀
  have hp : (s₀, t₀) ∈ S := (hmemS _).2 ht₀
  have honly : ∀ r : ZMod 3, r ≠ s₀ → Function.Injective (A - cr ω r • (1 : End K V)) := by
    intro r hr
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    have hAv : A v = cr ω r • v := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
    have hE : A.eigenspace (cr ω r) ≠ ⊥ := by
      intro h
      have hmem : v ∈ A.eigenspace (cr ω r) := mem_eigenspace_iff.2 hAv
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot K).1 hmem)
    obtain ⟨t, ht⟩ := exists_jointE_ne_bot_of_eigenspace hω hAB hB hE
    exact hr (congrArg Prod.fst (eq_of_mem_of_closed hS7 hI hJ ((hmemS _).2 ht) hp))
  set μ := cr ω s₀ with hμ
  set ν₁ := cr ω (s₀ + 1) with hν₁
  set ν₂ := cr ω (s₀ + 2) with hν₂
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
    have h2 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)
  have hc1 : cr ω 1 = ω := by rw [cr, show (1 : ZMod 3).val = 1 from rfl, pow_one]
  have hc2 : cr ω 2 = ω ^ 2 := by
    rw [cr, show (2 : ZMod 3).val = 2 from rfl]
  have hν₁' : ν₁ = μ * ω := by rw [hν₁, cr_add hω3, hc1]
  have hν₂' : ν₂ = μ * ω ^ 2 := by rw [hν₂, cr_add hω3, hc2]
  have hμ3 : μ ^ 3 = 1 := cr_pow_three hω3 s₀
  have hpoly : (X - C μ) * ((X - C ν₁) * (X - C ν₂)) = (X ^ 3 - 1 : K[X]) := by
    have hexp : (X - C μ) * ((X - C ν₁) * (X - C ν₂)) = X ^ 3 - C (μ + ν₁ + ν₂) * X ^ 2 +
        C (μ * ν₁ + ν₁ * ν₂ + ν₂ * μ) * X - C (μ * ν₁ * ν₂) := by
      simp only [map_add, map_mul]
      ring
    have hs1 : μ + ν₁ + ν₂ = 0 := by rw [hν₁', hν₂']; linear_combination μ * hω2
    have hs2 : μ * ν₁ + ν₁ * ν₂ + ν₂ * μ = 0 := by
      rw [hν₁', hν₂']; linear_combination μ ^ 2 * hω2 + μ ^ 2 * hω3
    have hs3 : μ * ν₁ * ν₂ = 1 := by
      rw [hν₁', hν₂']; linear_combination ω ^ 3 * hμ3 + hω3
    rw [hexp, hs1, hs2, hs3]
    simp
  have hid : (A - μ • (1 : End K V)) * ((A - ν₁ • (1 : End K V)) *
      (A - ν₂ • (1 : End K V))) = 0 := by
    have h := congrArg (aeval A) hpoly
    simp only [map_mul, map_sub, aeval_X, aeval_C, map_pow, map_one,
      Algebra.algebraMap_eq_smul_one] at h
    rw [h, hA, sub_self]
  have hQ : Function.Surjective
      ((A - ν₁ • (1 : End K V)) * (A - ν₂ • (1 : End K V))) := by
    rw [← LinearMap.injective_iff_surjective]
    have hne1 : ∀ s : ZMod 3, s + 1 ≠ s := by decide
    have hne2 : ∀ s : ZMod 3, s + 2 ≠ s := by decide
    have h1 := honly (s₀ + 1) (hne1 s₀)
    have h2 := honly (s₀ + 2) (hne2 s₀)
    exact h1.comp h2
  refine ⟨μ, LinearMap.ext fun v => ?_⟩
  obtain ⟨u, rfl⟩ := hQ v
  have h := congrArg (fun T : End K V => T u) hid
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at h
  rw [LinearMap.sub_apply] at h
  exact sub_eq_zero.1 h

end Core


section Matrix

theorem commute_of_q8_GL {F : Type*} [Field F] (h3 : (3 : F) ≠ 0) {d : ℕ} (hd : d ≤ 7)
    {A B M N : GL (Fin d) F} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hAB : A * B = B * A)
    (hMA : A * M = M * B) (hMB : B * M = M * A ^ 2) (hNA : A * N = N * (A * B))
    (hNB : B * N = N * (A * B ^ 2)) (g : GL (Fin d) F) : A * g = g * A := by
  let L := AlgebraicClosure F
  let Φ : GL (Fin d) F →* Module.End L (Fin d → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin d)).toAlgHom.toRingHom.toMonoidHom.comp
      ((algebraMap F L).mapMatrix.toMonoidHom.comp (Units.coeHom (Matrix (Fin d) (Fin d) F)))
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    exact Units.ext (Matrix.map_injective (algebraMap F L).injective
      (Matrix.toLinAlgEquiv'.injective hxy))
  have h3L : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap F L).injective
    rw [map_ofNat, h, map_zero]
  have hinj : ∀ X : GL (Fin d) F, Function.Injective (Φ X) := by
    intro X x y hxy
    have h := congrArg (Φ X⁻¹) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one] at h
  have hrel : ∀ {X Y T : GL (Fin d) F}, X * T = T * Y → Φ X * Φ T = Φ T * ((1 : L) • Φ Y) := by
    intro X Y T h
    rw [one_smul, ← map_mul, h, map_mul]
  have hMA' := hrel hMA
  have hMB' : Φ B * Φ M = Φ M * ((1 : L) • Φ A ^ 2) := by
    have := hrel hMB
    rwa [map_pow] at this
  have hNA' : Φ A * Φ N = Φ N * ((1 : L) • (Φ A * Φ B)) := by
    have := hrel hNA
    rwa [map_mul] at this
  have hNB' : Φ B * Φ N = Φ N * ((1 : L) • (Φ A * Φ B ^ 2)) := by
    have := hrel hNB
    rwa [map_mul, map_pow] at this
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_q8 h3L (by rwa [Module.finrank_fin_fun])
    (by rw [← map_pow, hA, map_one]) (by rw [← map_pow, hB, map_one])
    (by rw [← map_mul, hAB, map_mul]) (hinj M) (hinj N) hMA' hMB' hNA' hNB'
  apply hΦ
  rw [map_mul, map_mul, hμ, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end Matrix

section Lift

variable {G : Type*} [Group G]

theorem exists_lift_twist_three {Z : Subgroup G} [Z.Normal] (hZ : Z ≤ center G) (M : G)
    {x : G ⧸ Z} (hx : (M : G ⧸ Z) * x * (M : G ⧸ Z)⁻¹ = x ^ 2) (hx3 : x ^ 3 = 1) :
    ∃ X : G, (X : G ⧸ Z) = x ∧ M * X * M⁻¹ = X ^ 2 ∧ X ^ 3 = 1 := by
  obtain ⟨X₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨μ, h1⟩ : ∃ μ : G, M * X₀ * M⁻¹ = μ * X₀ ^ 2 :=
    ⟨M * X₀ * M⁻¹ * (X₀ ^ 2)⁻¹, by group⟩
  have hμZ : μ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, eq_mul_inv_of_mul_eq h1.symm, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hx, mul_inv_cancel]
  have hμc : ∀ g : G, Commute g μ := fun g => Subgroup.mem_center_iff.1 (hZ hμZ) g
  have hX : M * (μ * X₀) * M⁻¹ = (μ * X₀) ^ 2 := by
    calc M * (μ * X₀) * M⁻¹ = μ * (M * X₀ * M⁻¹) := by
          rw [← mul_assoc, (hμc M).eq]
          simp only [mul_assoc]
      _ = (μ * X₀) ^ 2 := by
          rw [h1, ((hμc X₀).symm).mul_pow, sq μ, mul_assoc]
  refine ⟨μ * X₀, ?_, hX, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff μ).2 hμZ, one_mul]
  · have hcZ : (μ * X₀) ^ 3 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff μ).2 hμZ, one_mul, hx3]
    have hcc : M * (μ * X₀) ^ 3 * M⁻¹ = (μ * X₀) ^ 3 := by
      rw [Subgroup.mem_center_iff.1 (hZ hcZ) M, mul_inv_cancel_right]
    have hc2 : M * (μ * X₀) ^ 3 * M⁻¹ = (μ * X₀) ^ 3 * (μ * X₀) ^ 3 := by
      rw [← conj_pow, hX, ← pow_mul, ← pow_add]
    rw [hcc] at hc2
    exact mul_eq_left.1 hc2.symm

theorem eq_one_of_twist {M g u w ν ρ : G} (hν : ∀ h : G, Commute h ν)
    (hρ : ∀ h : G, Commute h ρ) (hg : M * g * M⁻¹ = ρ * g) (hu : M * u * M⁻¹ = u ^ 2)
    (hw : M * w * M⁻¹ = w ^ 2) (h : g⁻¹ * u * g = ν * w) : ν = 1 := by
  have hgi : M * g⁻¹ * M⁻¹ = g⁻¹ * ρ⁻¹ := by
    have e : M * g⁻¹ * M⁻¹ = (M * g * M⁻¹)⁻¹ := by group
    rw [e, hg, mul_inv_rev]
  have h1 : M * (g⁻¹ * u * g) * M⁻¹ = (ν * w) ^ 2 := by
    calc M * (g⁻¹ * u * g) * M⁻¹ = (M * g⁻¹ * M⁻¹) * (M * u * M⁻¹) * (M * g * M⁻¹) := by group
      _ = g⁻¹ * (ρ⁻¹ * (u ^ 2 * ρ)) * g := by rw [hgi, hu, hg]; group
      _ = g⁻¹ * u ^ 2 * g := by rw [(hρ (u ^ 2)).eq]; group
      _ = (g⁻¹ * u * g) ^ 2 := by rw [sq, sq]; group
      _ = (ν * w) ^ 2 := by rw [h]
  have h2 : M * (ν * w) * M⁻¹ = ν * w ^ 2 := by
    calc M * (ν * w) * M⁻¹ = (M * ν) * w * M⁻¹ := by group
      _ = ν * (M * w * M⁻¹) := by rw [(hν M).eq]; group
      _ = ν * w ^ 2 := by rw [hw]
  rw [h, h2, ((hν w).symm).mul_pow, sq ν, mul_assoc] at h1
  have h3 : w ^ 2 = ν * w ^ 2 := mul_left_cancel h1
  have h4 : 1 * w ^ 2 = ν * w ^ 2 := by rw [one_mul]; exact h3
  exact (mul_right_cancel h4).symm


theorem mul_eq_of_twist {M g u w ρ : G} (hρ : ρ ∈ center G) (hg : M * g * M⁻¹ = ρ * g)
    (hu : M * u * M⁻¹ = u ^ 2) (hw : M * w * M⁻¹ = w ^ 2)
    (h : (u : G ⧸ center G) * g = g * w) : u * g = g * w := by
  have hνZ : g⁻¹ * u * g * w⁻¹ ∈ center G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    calc ((g : G ⧸ center G))⁻¹ * u * g * (w : G ⧸ center G)⁻¹ =
        ((g : G ⧸ center G))⁻¹ * (u * g) * (w : G ⧸ center G)⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hν := eq_one_of_twist (fun k => Subgroup.mem_center_iff.mp hνZ k)
    (fun k => Subgroup.mem_center_iff.mp hρ k) hg hu hw (show g⁻¹ * u * g = _ * w by group)
  have e : g⁻¹ * u * g = w := by
    have h2 : g⁻¹ * u * g * w⁻¹ * w = 1 * w := by rw [hν]
    rwa [one_mul, inv_mul_cancel_right] at h2
  calc u * g = g * (g⁻¹ * u * g) := by group
    _ = g * w := by rw [e]

theorem exists_lifts {a b i j : G ⧸ center G} (hab : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hia : a * i = i * b) (hib : b * i = i * a ^ 2)
    (hja : a * j = j * (a * b)) (hjb : b * j = j * (a * b ^ 2)) (hij : i * i * j = j * (i * i)) :
    ∃ x y I N : G, (x : G ⧸ center G) = a ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
      x * y * x⁻¹ * y⁻¹ ∈ center G ∧
      (x * y = y * x → x * I = I * y ∧ y * I = I * x ^ 2 ∧ x * N = N * (x * y) ∧
        y * N = N * (x * y ^ 2)) := by
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective i
  obtain ⟨N, rfl⟩ := QuotientGroup.mk_surjective j
  set M : G := (I * I)⁻¹ with hM
  have hconj : ∀ u v : G ⧸ center G, u * I = I * v →
      (M : G ⧸ center G) * u * (M : G ⧸ center G)⁻¹ = (I : G ⧸ center G)⁻¹ * v * I := by
    intro u v huv
    have e : u = I * v * (I : G ⧸ center G)⁻¹ := by rw [← huv, mul_inv_cancel_right]
    rw [hM, QuotientGroup.mk_inv, QuotientGroup.mk_mul, e]
    group
  have hb' : (I : G ⧸ center G)⁻¹ * b * I = a ^ 2 := by
    rw [mul_assoc, hib, ← mul_assoc, inv_mul_cancel, one_mul]
  have ha' : (I : G ⧸ center G)⁻¹ * a ^ 2 * I = b ^ 2 := by
    have hia2 : a ^ 2 * I = I * b ^ 2 := by
      rw [sq, sq, mul_assoc, hia, ← mul_assoc, hia, mul_assoc]
    rw [mul_assoc, hia2, ← mul_assoc, inv_mul_cancel, one_mul]
  have hMa : (M : G ⧸ center G) * a * (M : G ⧸ center G)⁻¹ = a ^ 2 := by
    rw [hconj a b hia, hb']
  have hMb : (M : G ⧸ center G) * b * (M : G ⧸ center G)⁻¹ = b ^ 2 := by
    rw [hconj b (a ^ 2) hib, ha']
  obtain ⟨x, rfl, hMx, hx3⟩ := exists_lift_twist_three le_rfl M hMa ha3
  obtain ⟨y, rfl, hMy, hy3⟩ := exists_lift_twist_three le_rfl M hMb hb3
  refine ⟨x, y, I, N, rfl, hx3, hy3, ?_, fun hxy => ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hab]
    group
  have hMI : M * I * M⁻¹ = 1 * I := by rw [hM]; group
  have hρN : M * N * M⁻¹ * N⁻¹ ∈ center G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hM, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, inv_inv]
    have e : (I : G ⧸ center G) * I * N = N * (I * I) := hij
    calc ((I : G ⧸ center G) * I)⁻¹ * N * (I * I) * (N : G ⧸ center G)⁻¹ =
        ((I : G ⧸ center G) * I)⁻¹ * (N * (I * I)) * (N : G ⧸ center G)⁻¹ := by group
      _ = 1 := by rw [← e]; group
  have hMN : M * N * M⁻¹ = (M * N * M⁻¹ * N⁻¹) * N := by group
  have hMx2 : M * x ^ 2 * M⁻¹ = (x ^ 2) ^ 2 := by rw [← conj_pow, hMx]
  have hMxy : M * (x * y) * M⁻¹ = (x * y) ^ 2 := by
    rw [show M * (x * y) * M⁻¹ = (M * x * M⁻¹) * (M * y * M⁻¹) by group, hMx, hMy,
      (Commute.mul_pow hxy 2)]
  have hMxy2 : M * (x * y ^ 2) * M⁻¹ = (x * y ^ 2) ^ 2 := by
    have hc : Commute x (y ^ 2) := Commute.pow_right hxy 2
    rw [show M * (x * y ^ 2) * M⁻¹ = (M * x * M⁻¹) * (M * y ^ 2 * M⁻¹) by group, ← conj_pow,
      hMx, hMy, hc.mul_pow, ← pow_mul]
  refine ⟨mul_eq_of_twist (Subgroup.one_mem _) hMI hMx hMy hia,
    mul_eq_of_twist (Subgroup.one_mem _) hMI hMy hMx2 (by rw [QuotientGroup.mk_pow]; exact hib),
    mul_eq_of_twist hρN hMN hMx hMxy (by rw [QuotientGroup.mk_mul]; exact hja),
    mul_eq_of_twist hρN hMN hMy hMxy2
      (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow]; exact hjb)⟩

end Lift


section Group

open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open Matrix

theorem false_of_e9q8 {F : Type*} [Field F] (h3 : (3 : F) ≠ 0) {d : ℕ} (hd : d ≤ 7)
    (hdvd : ∀ x y c : GL (Fin d) F, y * x * y⁻¹ = c * x → c * x = x * c → c * y = y * c →
      c ^ 3 = 1 → (∀ v, (c : Matrix (Fin d) (Fin d) F) *ᵥ v = v → v = 0) → False)
    {J : Subgroup (GL (Fin d) F)} (hirr : IsIrreducibleMatrixRep J.subtype)
    {a b i j : ↥J ⧸ center ↥J} (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hia : a * i = i * b) (hib : b * i = i * a ^ 2) (hja : a * j = j * (a * b))
    (hjb : b * j = j * (a * b ^ 2)) (hij : i * i * j = j * (i * i)) (ha1 : a ≠ 1) : False := by
  obtain ⟨x, y, I, N, rfl, hx3, hy3, hcen, hcomm⟩ := exists_lifts hab ha3 hb3 hia hib hja hjb hij
  have cv : ∀ {u v : ↥J}, u = v → (u : GL (Fin d) F) = v := fun h => congrArg _ h
  by_cases hxy : x * y = y * x
  · obtain ⟨h1, h2, h3', h4⟩ := hcomm hxy
    apply ha1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hc := commute_of_q8_GL h3 hd (A := (x : GL (Fin d) F)) (B := (y : GL (Fin d) F))
      (M := (I : GL (Fin d) F)) (N := (N : GL (Fin d) F)) (by simpa using cv hx3)
      (by simpa using cv hy3) (by simpa using cv hxy) (by simpa using cv h1)
      (by simpa using cv h2) (by simpa using cv h3') (by simpa using cv h4) (g : GL (Fin d) F)
    simpa using hc.symm
  · set c : ↥J := x * y * x⁻¹ * y⁻¹ with hcdef
    have hcC : ∀ g : ↥J, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hcen g
    have hconj : x * y * x⁻¹ = c * y := by rw [hcdef]; group
    have hc1 : c ≠ 1 := by
      intro h
      apply hxy
      rw [h, one_mul] at hconj
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hconj]
    have hc3 : c ^ 3 = 1 := by
      have h := UC6.ProjFive.conj_pow_pow_of_central (fun g => hcC g) hconj 3 1
      rw [hx3, inv_one, mul_one, one_mul, pow_one, mul_one] at h
      have h' : 1 * y = c ^ 3 * y := by rw [one_mul]; exact h
      exact (mul_right_cancel h').symm
    have hcm : ∀ g : ↥J, ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * ((g : GL (Fin d) F) : Matrix _ _ F) := by
      intro g
      have := congrArg (fun u : ↥J => (((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) (hcC g)
      simpa using this
    refine hdvd (y : GL (Fin d) F) (x : GL (Fin d) F) (c : GL (Fin d) F) (by simpa using cv hconj)
      (by simpa using cv (hcC y).symm) (by simpa using cv (hcC x).symm) (by simpa using cv hc3) ?_
    intro v hv
    let W : Submodule F (Fin d → F) :=
      LinearMap.ker (Matrix.toLin' (((c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1))
    have hmemW : ∀ w, w ∈ W ↔ ((c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w = w := by
      intro w
      simp only [W, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        sub_eq_zero]
    have hW : ∀ g : ↥J, ∀ w ∈ W,
        ((J.subtype g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W := by
      intro g w hw
      rw [hmemW] at hw ⊢
      rw [Subgroup.subtype_apply, Matrix.mulVec_mulVec, ← hcm g, ← Matrix.mulVec_mulVec, hw]
    rcases hirr W hW with hbot | htop
    · have hvW : v ∈ W := (hmemW v).2 hv
      rw [hbot] at hvW
      exact (Submodule.mem_bot F).1 hvW
    · exfalso
      apply hc1
      apply Subtype.ext
      apply Units.ext
      rw [OneMemClass.coe_one, Units.val_one]
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      have hw : w ∈ W := by rw [htop]; exact Submodule.mem_top
      rw [hmemW] at hw
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hw, Matrix.one_mulVec]

end Group

end CFSG.LocalAnalysis.UniquenessCase.UCK.E9Q8

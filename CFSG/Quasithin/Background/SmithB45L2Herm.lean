module

public import CFSG.Quasithin.Background.SmithB45L2Inner
public import CFSG.Quasithin.Background.JonesParshallHermitian
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFlip

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open scoped MatrixGroups Matrix

section ToMat

@[expose] def toMat {k : Type*} (z : (Fin 2 → Fin 2) → k) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.of fun p q => z ![p, q]

@[expose] def toMatEquiv (k : Type*) [Field k] :
    ((Fin 2 → Fin 2) → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k where
  toFun := toMat
  invFun X := fun x => X (x 0) (x 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext x
    show z ![x 0, x 1] = z x
    congr 1
    funext i
    fin_cases i <;> rfl
  right_inv X := by
    ext p q
    rfl

theorem toMatEquiv_apply {k : Type*} [Field k] (z : (Fin 2 → Fin 2) → k) :
    toMatEquiv k z = toMat z := rfl

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem toMat_tensorRep (e : Fin 2 → ℕ) (g : SL(2, F)) (z : (Fin 2 → Fin 2) → k) :
    toMat (tensorRep F k e g z) = twistMat k (e 0) g * toMat z * (twistMat k (e 1) g)ᵀ := by
  ext p q
  simp only [toMat, Matrix.of_apply, tensorRep_apply, Matrix.mul_apply, Matrix.transpose_apply,
    tmatE, Fin.prod_univ_two, Fin.sum_univ_two]
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ => Fin 2)).symm, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, piFinTwoEquiv]
  ring

end ToMat

section Twisted

variable {F : Type} [Field F]

@[expose] def twAct (s : ℕ) (γ X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  γ * X * (frobPow s γ)ᵀ

theorem twAct_smul (s : ℕ) (γ X : Matrix (Fin 2) (Fin 2) F) (c : F) :
    twAct s γ (c • X) = c • twAct s γ X := by
  simp [twAct]

theorem twAct_add (s : ℕ) (γ X Y : Matrix (Fin 2) (Fin 2) F) :
    twAct s γ (X + Y) = twAct s γ X + twAct s γ Y := by
  simp [twAct, Matrix.mul_add, Matrix.add_mul]

theorem twAct_u (s : ℕ) (t : F) (X : Matrix (Fin 2) (Fin 2) F) :
    twAct s !![1, t; 0, 1] X =
      !![X 0 0 + t * X 1 0 + (X 0 1 + t * X 1 1) * t ^ (2 ^ s), X 0 1 + t * X 1 1;
        X 1 0 + X 1 1 * t ^ (2 ^ s), X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [twAct, frobPow, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one] <;> simp

variable [CharP F 2]

theorem eq_zero_of_root_fixed (s : ℕ) {t : F} (ht : t ^ (2 ^ s) ≠ t)
    {X : Matrix (Fin 2) (Fin 2) F} (h1 : twAct s !![1, 1; 0, 1] X = X)
    (h2 : twAct s !![1, t; 0, 1] X = X) : X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 1 = 0 := by
  rw [twAct_u] at h1 h2
  have a01 := congrFun (congrFun h1 0) 1
  have a00 := congrFun (congrFun h1 0) 0
  have b00 := congrFun (congrFun h2 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, one_pow] at a01 a00 b00
  have h11 : X 1 1 = 0 := eq_zero_of_add_eq_self a01
  simp only [h11, mul_zero, add_zero, mul_one] at a00 b00
  have h10 : X 1 0 = X 0 1 := by
    have := eq_zero_of_add_eq_self (x := X 0 0) (by rw [← add_assoc]; exact a00)
    exact (CharTwo.add_eq_zero.mp this)
  rw [h10] at b00
  have h3 : (t + t ^ (2 ^ s)) * X 0 1 = 0 :=
    eq_zero_of_add_eq_self (x := X 0 0) (by linear_combination b00)
  have h4 : t + t ^ (2 ^ s) ≠ 0 := by
    intro h
    exact ht (CharTwo.add_eq_zero.mp h).symm
  have h01 : X 0 1 = 0 := (mul_eq_zero.mp h3).resolve_left h4
  exact ⟨h01, h10.trans h01, h11⟩

theorem smul_mem_of_herm (s : ℕ) (hσ : ∀ x : F, (x ^ (2 ^ s)) ^ (2 ^ s) = x)
    (W' : AddSubgroup (Matrix (Fin 2) (Fin 2) F))
    (hinv : ∀ γ : SL(2, F), ∀ X ∈ W', twAct s (γ : Matrix (Fin 2) (Fin 2) F) X ∈ W')
    (hK : ∀ κ : F, κ ^ (2 ^ s) = κ → ∀ X ∈ W', κ • X ∈ W') {c : F}
    (hc : c • !![1, 0; 0, 0] ∈ W') {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA s F) :
    c • X ∈ W' := by
  let w₀ : SL(2, F) := ⟨!![0, 1; 1, 0], by
    simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have hE22 : c • !![0, 0; 0, 1] ∈ W' := by
    have h := hinv w₀ _ hc
    have e : twAct s (w₀ : Matrix (Fin 2) (Fin 2) F) (c • !![1, 0; 0, 0]) = c • !![0, 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [w₀, twAct, frobPow, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
          Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.mk_one, Matrix.smul_apply, smul_eq_mul] <;> simp
    rwa [e] at h
  have hL : ∀ b : F, c • !![1, b ^ (2 ^ s); b, b * b ^ (2 ^ s)] ∈ W' := by
    intro b
    have h := hinv (lElt b) _ hc
    have e : twAct s ((lElt b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) (c • !![1, 0; 0, 0]) =
        c • !![1, b ^ (2 ^ s); b, b * b ^ (2 ^ s)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [lElt, twAct, frobPow, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Fin.zero_eta, Fin.mk_one, Matrix.smul_apply, smul_eq_mul] <;> simp <;> ring
    rwa [e] at h
  have hX00 : (X 0 0) ^ (2 ^ s) = X 0 0 := by
    have := hermA_00 (a := s) ⟨X, hX⟩
    rwa [sig_apply] at this
  have hX11 : (X 1 1) ^ (2 ^ s) = X 1 1 := by
    have := hermA_11 (a := s) ⟨X, hX⟩
    rwa [sig_apply] at this
  have hX01 : X 0 1 = (X 1 0) ^ (2 ^ s) := by
    have := hermA_10 (a := s) ⟨X, hX⟩
    rw [sig_apply] at this
    have h2 := congrArg (fun x => x ^ (2 ^ s)) this
    simp only [hσ] at h2
    exact h2.symm
  set b := X 1 0 with hb
  have hN : (b * b ^ (2 ^ s)) ^ (2 ^ s) = b * b ^ (2 ^ s) := by
    rw [mul_pow, hσ, mul_comm]
  have e : c • X = (X 0 0 - 1) • (c • !![1, 0; 0, 0]) +
      (X 1 1 - b * b ^ (2 ^ s)) • (c • !![0, 0; 0, 1]) +
      c • !![1, b ^ (2 ^ s); b, b * b ^ (2 ^ s)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX01, hb] <;> ring
  have hsub : ∀ x : F, x ^ (2 ^ s) = x → ∀ y : F, y ^ (2 ^ s) = y → (x - y) ^ (2 ^ s) = x - y :=
    fun x hx y hy => by rw [sub_pow_char_pow, hx, hy]
  rw [e]
  refine W'.add_mem (W'.add_mem (hK _ (hsub _ hX00 _ (by simp)) _ hc)
    (hK _ (hsub _ hX11 _ hN) _ hE22)) (hL b)

theorem card_le_card_hermA [Finite F] (s : ℕ) (hσ : ∀ x : F, (x ^ (2 ^ s)) ^ (2 ^ s) = x) :
    Nat.card {x : F // x ^ (2 ^ s) = x} ^ 2 * Nat.card F ≤ Nat.card (hermA s F) := by
  classical
  let f : {x : F // x ^ (2 ^ s) = x} × F × {x : F // x ^ (2 ^ s) = x} → hermA s F :=
    fun p => ⟨!![p.1.1, p.2.1 ^ (2 ^ s); p.2.1, p.2.2.1], mem_hermA_of fun i j => by
      fin_cases i <;> fin_cases j <;> simp [sig_apply, p.1.2, p.2.2.2, hσ]⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b, d⟩ ⟨a', b', d'⟩ h
    have h1 := congrArg Subtype.val h
    have h00 := congrFun (congrFun h1 0) 0
    have h10 := congrFun (congrFun h1 1) 0
    have h11 := congrFun (congrFun h1 1) 1
    simp [f] at h00 h10 h11
    simp only [Prod.mk.injEq]
    exact ⟨Subtype.ext h00, h10, Subtype.ext h11⟩
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod] at h
  calc _ = Nat.card {x : F // x ^ (2 ^ s) = x} *
        (Nat.card F * Nat.card {x : F // x ^ (2 ^ s) = x}) := by ring
    _ ≤ _ := h

end Twisted

section FieldAut

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem fieldAut_bijective (j : ℕ) : Function.Bijective (fieldAut F j) := by
  have hinj : Function.Injective (fieldAut F j) := by
    intro g h hgh
    ext a b
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) a b) hgh
    simp only [fieldAut_apply] at this
    exact frob_pow_injective j this
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

@[expose] noncomputable def fieldAutEquiv (j : ℕ) : SL(2, F) ≃* SL(2, F) :=
  MulEquiv.ofBijective (fieldAut F j) (fieldAut_bijective j)

theorem fieldAutEquiv_apply (j : ℕ) (g : SL(2, F)) : fieldAutEquiv j g = fieldAut F j g := rfl

end FieldAut

theorem exists_equiv_fin2 {J : Finset ℕ} (hJ : J.card = 2) {a b : ℕ} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ σ : Fin 2 ≃ J, (σ 0 : ℕ) = a ∧ (σ 1 : ℕ) = b := by
  classical
  let f : Fin 2 → J := ![⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    fin_cases x <;> fin_cases y <;> first | rfl | (simp [f] at h; omega)
  have hcard : Fintype.card (Fin 2) = Fintype.card J := by simp [hJ]
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩),
    rfl, rfl⟩

section Iso

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

set_option synthInstance.maxHeartbeats 400000 in
theorem orth_iso {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s))
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (hD : Nat.card (EndRing ρ) = 2 ^ s) (hdim : Module.finrank (EndRing ρ) W = 4) :
    ∃ (j : ℕ) (β : W ≃+ ↥(hermA s F)),
      ∀ g w, β (ρ g w) = hermAct s (sig_sig hF) (fieldAut F j g) (β w) := by
  classical
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hcharD : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  have hσ : ∀ x : F, (x ^ (2 ^ s)) ^ (2 ^ s) = x := fun x => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
  obtain ⟨ιD⟩ : Nonempty (EndRing ρ →+* F) := by
    let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
    have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
    have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
    have hfrD : Module.finrank (ZMod 2) (EndRing ρ) = s := by
      have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
      rw [hD, Nat.card_zmod] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    have hfrF : Module.finrank (ZMod 2) F = 2 * s := by
      have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
      rw [Nat.card_eq_fintype_card, hF, Nat.card_zmod] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := EndRing ρ)
      (L := F) (by rw [hfrD, hfrF]; exact Dvd.intro_left 2 rfl)
    exact ⟨ψ⟩
  have hιfix : ∀ δ, (ιD δ) ^ (2 ^ s) = ιD δ := by
    intro δ
    rw [← map_pow]
    congr 1
    have : Fintype (EndRing ρ) := Fintype.ofFinite _
    have h1 := FiniteField.pow_card δ
    rwa [Fintype.card_eq_nat_card, hD] at h1
  have hKcard : 2 ^ s ≤ Nat.card {x : F // x ^ (2 ^ s) = x} :=
    calc 2 ^ s = Nat.card (EndRing ρ) := hD.symm
      _ ≤ _ := Nat.card_le_card_of_injective (fun δ => ⟨ιD δ, hιfix δ⟩)
        (fun δ δ' h => ιD.injective (congrArg Subtype.val h))
  have : Fintype (EndRing ρ) := Fintype.ofFinite _
  have hK : ∀ x : F, x ^ (2 ^ s) = x → ∃ δ, ιD δ = x := by
    intro x hx
    by_contra hne
    push Not at hne
    let S : Finset F := Finset.univ.filter fun y => y ^ (2 ^ s) = y
    have h1 : S.card ≤ 2 ^ s := card_le_of_frob_fixed hs S (fun u hu => (Finset.mem_filter.mp hu).2)
    have h2 : (Finset.univ.image ιD).card = 2 ^ s := by
      rw [Finset.card_image_of_injective _ ιD.injective, Finset.card_univ, Fintype.card_eq_nat_card,
        hD]
    have h3 : insert x (Finset.univ.image ιD) ⊆ S := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      · obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hιfix δ⟩
    have h4 := Finset.card_le_card h3
    rw [Finset.card_insert_of_notMem (by
      intro hmem
      obtain ⟨δ, -, hδ⟩ := Finset.mem_image.mp hmem
      exact hne δ hδ), h2] at h4
    omega
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨J, hJne, hJn, ⟨Φ⟩, hshift, hdimJ⟩ :=
    descent_core (n := 2 * s) (by omega) hF ρ hnt hD b (RingHom.id F) ιD
  let _ : Algebra F F := (RingHom.id F).toAlgebra
  have hJ2 : J.card = 2 := by
    have h1 : 2 ^ J.card = 2 ^ 2 := by rw [← hdimJ, hdim]; rfl
    exact Nat.pow_right_injective le_rfl h1
  obtain ⟨j₀, hj₀⟩ := hJne
  have hj₀n : j₀ < 2 * s := hJn j₀ hj₀
  have hj₁ : (j₀ + s) % (2 * s) ∈ J := by
    rw [← hshift]
    exact Finset.mem_image_of_mem _ hj₀
  have hj₀₁ : j₀ ≠ (j₀ + s) % (2 * s) := by
    intro h
    have h1 : (j₀ + s) % (2 * s) = (j₀ + 0) % (2 * s) := by
      rw [← h, add_zero, Nat.mod_eq_of_lt hj₀n]
    have h2 := Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j₀ h1)
    have h3 := Nat.le_of_dvd (by omega) h2
    omega
  obtain ⟨σJ, hσ0, hσ1⟩ := exists_equiv_fin2 hJ2 hj₀ hj₁ hj₀₁
  let e : Fin 2 → ℕ := fun i => (σJ i : ℕ)
  let ψ := reindexEquiv (F := F) (k := F) σJ e (fun i : J => (i : ℕ)) (fun _ => rfl)
  let coordι : W →+ (Fin (Module.finrank (EndRing ρ) W) → F) :=
    { toFun := fun w i => ιD (b.equivFun w i)
      map_zero' := by funext i; simp
      map_add' := fun w w' => by funext i; simp }
  let φ : W →+ Matrix (Fin 2) (Fin 2) F :=
    (toMatEquiv F).toLinearMap.toAddMonoidHom.comp
      (ψ.symm.toLinearEquiv.toLinearMap.toAddMonoidHom.comp
        (Φ.toLinearEquiv.toLinearMap.toAddMonoidHom.comp coordι))
  have hφ : ∀ w, φ w = toMat (ψ.symm (Φ (fun i => ιD (b.equivFun w i)))) := fun w => rfl
  have hφinj : Function.Injective φ := by
    intro w w' h
    rw [hφ, hφ] at h
    have h1 := (toMatEquiv F).injective h
    have h2 := ψ.symm.toLinearEquiv.injective h1
    have h3 := Φ.toLinearEquiv.injective h2
    apply b.equivFun.injective
    funext i
    exact ιD.injective (congrFun h3 i)
  have hγ0 : ∀ g : SL(2, F), twistMat F (e 0) g = ((fieldAut F j₀ g : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) := by
    intro g
    ext a c
    rw [twistMat_apply, fieldAut_apply]
    simp [e, hσ0]
  have hγ1 : ∀ g : SL(2, F), twistMat F (e 1) g =
      frobPow s ((fieldAut F j₀ g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro g
    have h1 : twistMat F (e 1) g = twistMat F (j₀ + s) g := by
      simp only [e, hσ1]
      exact twistMat_mod hF _ g
    rw [h1]
    ext a c
    rw [twistMat_apply]
    simp [frobPow, fieldAut_apply, pow_add, pow_mul]
  have hequiv : ∀ g w, φ (ρ g w) =
      twAct s ((fieldAut F j₀ g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) (φ w) := by
    intro g w
    have hcoord : (matRep b g).mulVec (b.equivFun w) = b.equivFun (ρ g w) :=
      LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    have h1 : (fun i => ιD (b.equivFun (ρ g w) i)) =
        matRepE b ιD g (fun i => ιD (b.equivFun w i)) := by
      rw [matRepE_apply, ← hcoord]
      funext i
      exact RingHom.map_mulVec ιD _ _ i
    rw [hφ, hφ, h1, equiv_apply Φ]
    have h2 : ψ.symm (frobTensor F F J g (Φ fun i => ιD (b.equivFun w i))) =
        tensorRep F F e g (ψ.symm (Φ fun i => ιD (b.equivFun w i))) :=
      equiv_apply ψ.symm g _
    rw [h2, toMat_tensorRep, hγ0, hγ1]
    rfl
  let W' : AddSubgroup (Matrix (Fin 2) (Fin 2) F) := φ.range
  have hinv : ∀ γ : SL(2, F), ∀ X ∈ W', twAct s (γ : Matrix (Fin 2) (Fin 2) F) X ∈ W' := by
    intro γ X hX
    obtain ⟨w, rfl⟩ := hX
    obtain ⟨g, rfl⟩ := (fieldAut_bijective (F := F) j₀).2 γ
    exact ⟨ρ g w, hequiv g w⟩
  have hsmul : ∀ (δ : EndRing ρ) (w : W), φ (δ • w) = ιD δ • φ w := by
    intro δ w
    rw [hφ, hφ]
    have h1 : (fun i => ιD (b.equivFun (δ • w) i)) = ιD δ • (fun i => ιD (b.equivFun w i)) := by
      have h0 := b.equivFun.map_smul δ w
      funext i
      rw [h0]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [h1]
    have h2 : Φ (ιD δ • fun i => ιD (b.equivFun w i)) = ιD δ • Φ (fun i => ιD (b.equivFun w i)) :=
      Φ.toLinearEquiv.map_smul _ _
    have h3 : ψ.symm (ιD δ • Φ (fun i => ιD (b.equivFun w i))) =
        ιD δ • ψ.symm (Φ (fun i => ιD (b.equivFun w i))) := ψ.symm.toLinearEquiv.map_smul _ _
    rw [h2, h3]
    rfl
  have hK' : ∀ κ : F, κ ^ (2 ^ s) = κ → ∀ X ∈ W', κ • X ∈ W' := by
    intro κ hκ X hX
    obtain ⟨δ, rfl⟩ := hK κ hκ
    obtain ⟨w, rfl⟩ := hX
    exact ⟨δ • w, hsmul δ w⟩
  have hfixU := natCard_fixW_rootGroup ρ hF b (RingHom.id F) ιD J hJn Φ
  obtain ⟨w₀, hw₀, hw₀ne⟩ : ∃ w₀ : W, (∀ t, ρ (uElt t) w₀ = w₀) ∧ w₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {w : W // ∀ t : F, ρ (uElt t) w = w} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr
        ⟨fun x y => Subtype.ext ((hall x.1 x.2).trans (hall y.1 y.2).symm)⟩
    rw [hfixU, hD] at h1
    have h2 : 2 ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : F, t₁ ^ (2 ^ s) ≠ t₁ := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_frob_fixed hs Finset.univ (fun u _ => hall u)
    rw [Finset.card_univ, hF] at h1
    have h2 : 2 ^ s < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set X₀ := φ w₀ with hX₀def
  have hX₀fix : ∀ t : F, twAct s !![1, t ^ (2 ^ j₀); 0, 1] X₀ = X₀ := by
    intro t
    have h1 := hequiv (uElt t) w₀
    rw [hw₀ t] at h1
    have h2 : ((fieldAut F j₀ (uElt t) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        !![1, t ^ (2 ^ j₀); 0, 1] := by
      ext a c
      rw [fieldAut_apply]
      fin_cases a <;> fin_cases c <;> simp [uElt]
    rw [h2] at h1
    exact h1.symm
  obtain ⟨h01, h10, h11⟩ := eq_zero_of_root_fixed s (t := t₁ ^ (2 ^ j₀)) (by
      intro h
      apply ht₁
      apply frob_pow_injective j₀
      rw [← pow_mul, mul_comm, pow_mul]
      exact h) (by simpa using hX₀fix 1) (hX₀fix t₁)
  set c := X₀ 0 0 with hc
  have hX₀eq : X₀ = c • !![1, 0; 0, 0] := by
    ext a b'
    fin_cases a <;> fin_cases b' <;> simp [hc, h01, h10, h11]
  have hc0 : c ≠ 0 := by
    intro h0
    apply hw₀ne
    apply hφinj
    rw [map_zero, ← hX₀def, hX₀eq, h0, zero_smul]
  have hcE : c • !![1, 0; 0, 0] ∈ W' := by
    rw [← hX₀eq]
    exact ⟨w₀, rfl⟩
  have hsub : ∀ {X : Matrix (Fin 2) (Fin 2) F}, X ∈ hermA s F → c • X ∈ W' :=
    fun hX => smul_mem_of_herm s hσ W' hinv hK' hcE hX
  have hWcard : Nat.card W = 2 ^ (4 * s) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hD, hdim, ← pow_mul, mul_comm]
  have hW' : Nat.card W' = Nat.card W :=
    (Nat.card_congr (AddMonoidHom.ofInjective hφinj).toEquiv).symm
  have hH : 2 ^ (4 * s) ≤ Nat.card (hermA s F) := by
    have h1 := card_le_card_hermA (F := F) s hσ
    calc 2 ^ (4 * s) = (2 ^ s) ^ 2 * 2 ^ (2 * s) := by ring
      _ ≤ Nat.card {x : F // x ^ (2 ^ s) = x} ^ 2 * Nat.card F := by
        rw [show Nat.card F = 2 ^ (2 * s) by rw [Nat.card_eq_fintype_card, hF]]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hKcard 2)
      _ ≤ _ := h1
  let fH : hermA s F → W' := fun X => ⟨c • (X : Matrix (Fin 2) (Fin 2) F), hsub X.2⟩
  have hfH : Function.Injective fH := by
    intro X Y h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective _ hc0 h1)
  have hbij : Function.Bijective fH :=
    hfH.bijective_of_nat_card_le (by rw [hW', hWcard]; exact hH)
  have hmem : ∀ w, c⁻¹ • φ w ∈ hermA s F := by
    intro w
    obtain ⟨X, hX⟩ := hbij.2 ⟨φ w, ⟨w, rfl⟩⟩
    have h1 : c • (X : Matrix (Fin 2) (Fin 2) F) = φ w := congrArg Subtype.val hX
    rw [← h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact X.2
  let fβ : W →+ hermA s F :=
    { toFun := fun w => ⟨c⁻¹ • φ w, hmem w⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun w w' => by apply Subtype.ext; simp [smul_add] }
  have hfβinj : Function.Injective fβ := by
    intro w w' h
    have h1 : c⁻¹ • φ w = c⁻¹ • φ w' := congrArg Subtype.val h
    exact hφinj (smul_right_injective _ (inv_ne_zero hc0) h1)
  have hfβsurj : Function.Surjective fβ := by
    intro X
    obtain ⟨w, hw⟩ := hsub X.2
    refine ⟨w, Subtype.ext ?_⟩
    show c⁻¹ • φ w = (X : Matrix (Fin 2) (Fin 2) F)
    rw [hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨j₀, AddEquiv.ofBijective fβ ⟨hfβinj, hfβsurj⟩, fun g w => ?_⟩
  apply Subtype.ext
  show c⁻¹ • φ (ρ g w) = ((hermAct s (sig_sig hF) (fieldAut F j₀ g) (fβ w) : hermA s F) :
    Matrix (Fin 2) (Fin 2) F)
  rw [hermAct_coe, hequiv, ← twAct_smul]
  rfl

end Iso

end CFSG.Quasithin.B45L2

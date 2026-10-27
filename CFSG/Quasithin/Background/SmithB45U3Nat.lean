module

public import CFSG.Quasithin.Background.SmithB45U3Rank
public import CFSG.Quasithin.Background.SmithB45U3Main
public import CFSG.Quasithin.Background.SmithB45SzNat

public section

namespace CFSG.Quasithin

namespace B45U3

open CFSG.QuasithinUnique.Setup.X7a CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso fixedSub
  matIso_of_reindex permMat)
open scoped MatrixGroups Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {s : ℕ}

omit [Finite K] [CharP K 2] in
theorem cnt_of_card_eq_three {a b : Fin s → Bool} (h : Fintype.card (TIdx s a b) = 3) :
    cntS a b = 1 ∧ cntH a b = 0 := by
  rw [card_TIdx_eq] at h
  have hm : cntH a b = 0 := by
    by_contra hne
    have h8 : 8 ∣ 3 ^ cntS a b * 8 ^ cntH a b :=
      Dvd.dvd.mul_left (dvd_pow_self 8 hne) _
    rw [h] at h8
    norm_num at h8
  rw [hm, pow_zero, mul_one] at h
  exact ⟨Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (pow_one 3).symm), hm⟩

omit [Finite K] [CharP K 2] in
theorem exists_single_letter {a b : Fin s → Bool} (hS : cntS a b = 1) (hH : cntH a b = 0) :
    ∃ i₀ : Fin s, a i₀ ≠ b i₀ ∧ ∀ i ≠ i₀, a i = false ∧ b i = false := by
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hS
  have hmem : ∀ i, a i ≠ b i ↔ i = i₀ := fun i => by
    have := congrArg (i ∈ ·) hi₀
    simpa using this
  refine ⟨i₀, (hmem i₀).mpr rfl, fun i hi => ?_⟩
  have h1 : a i = b i := by
    by_contra h
    exact hi ((hmem i).mp h)
  have h2 : ¬ (a i = true ∧ b i = true) := by
    intro h
    have : i ∈ Finset.univ.filter fun i => a i = true ∧ b i = true := by simpa using h
    rw [cntH, Finset.card_eq_zero] at hH
    rw [hH] at this
    simp at this
  cases ha : a i <;> cases hb : b i <;> simp_all

omit [Finite K] [CharP K 2] in
theorem locRep_ff_apply (k : Type) [Field k] [Algebra K k] [CharP k 2] {A B : Bool}
    (hA : A = false) (hB : B = false) (n : ℕ) (g : SL(3, K)) (u v : Fin (locDim A B)) :
    locRep k A B n g u v = 1 := by
  subst hA hB
  rw [locRep_ff, MonoidHom.one_apply, fin_locDim_ff u v, Matrix.one_apply_eq]

theorem matIso_single (k : Type) [Field k] [Algebra K k] [CharP k 2] {a b : Fin s → Bool}
    {i₀ : Fin s} (h : ∀ i ≠ i₀, a i = false ∧ b i = false) (ℓ : Bool × Bool)
    (hℓ : (a i₀, b i₀) = ℓ) :
    ∃ (P : Matrix (Fin (locDim ℓ.1 ℓ.2)) (TIdx s a b) k)
      (Q : Matrix (TIdx s a b) (Fin (locDim ℓ.1 ℓ.2)) k),
      MatIso (TJ (K := K) k a b) ((locRep (F := K) k ℓ.1 ℓ.2 (i₀ : ℕ)).comp (suJ K s).subtype)
        P Q := by
  subst hℓ
  have hpos : ∀ i, 0 < locDim (a i) (b i) := fun i => by
    cases a i <;> cases b i <;> decide
  have hsub : ∀ i ≠ i₀, ∀ x y : Fin (locDim (a i) (b i)), x = y := by
    intro i hi x y
    have h1 : locDim (a i) (b i) = 1 := by rw [(h i hi).1, (h i hi).2]; rfl
    exact Fin.ext (by have := x.2; have := y.2; omega)
  let e : TIdx s a b ≃ Fin (locDim (a i₀) (b i₀)) :=
    { toFun := fun x => x i₀
      invFun := fun y i => if hi : i = i₀ then hi ▸ y else ⟨0, hpos i⟩
      left_inv := fun x => by
        funext i
        by_cases hi : i = i₀
        · subst hi
          simp
        · simp only [hi, ↓reduceDIte]
          exact hsub i hi _ _
      right_inv := fun y => by simp }
  refine ⟨_, _, matIso_of_reindex e (fun g x' x => ?_)⟩
  show locRep k (a i₀) (b i₀) (i₀ : ℕ) (g : SL(3, K)) (x' i₀) (x i₀) =
    tensorRep (F := K) k a b (g : SL(3, K)) x' x
  rw [tensorRep, tensorRepGen_apply, Finset.prod_eq_single i₀]
  · intro i _ hi
    exact locRep_ff_apply k (h i hi).1 (h i hi).2 _ _ _ _
  · simp

omit [Finite K] in
theorem map_pow_eq_mapMatrix (c : ℕ) (M : Matrix (Fin 3) (Fin 3) K) :
    M.map (· ^ 2 ^ c) = (iterateFrobenius K 2 c).mapMatrix M := by
  ext i j
  simp [iterateFrobenius_def]

omit [Finite K] [CharP K 2] in
theorem wJMat_mul_wJMat : (wJMat : Matrix (Fin 3) (Fin 3) K) * wJMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite K] [CharP K 2] in
theorem wJMat_transpose : (wJMat : Matrix (Fin 3) (Fin 3) K)ᵀ = wJMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJMat]

omit [Finite K] in
theorem iterateFrobenius_mapMatrix_wJMat (c : ℕ) :
    (iterateFrobenius K 2 c).mapMatrix (wJMat : Matrix (Fin 3) (Fin 3) K) = wJMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJMat]

theorem inv_transpose_map_eq {g : SL(3, K)} (hg : g ∈ suJ K s) (c : ℕ) :
    ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)).map (· ^ 2 ^ c))ᵀ =
      wJMat * ((g : Matrix (Fin 3) (Fin 3) K)).map (· ^ 2 ^ (c + s)) * wJMat := by
  set G := (g : Matrix (Fin 3) (Fin 3) K) with hG
  set Gi := ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) with hGi
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hiso := mem_suJ.mp hg
  rw [← hG] at hiso
  have hσ : G.map (CFSG.LieType.BorelTits.unitaryInvolution K 2 s) =
      (iterateFrobenius K 2 s).mapMatrix G := by
    ext i j
    simp [iterateFrobenius_def]
  rw [hσ] at hiso
  have h1 : ((iterateFrobenius K 2 s).mapMatrix G)ᵀ = wJMat * Gi * wJMat := by
    calc ((iterateFrobenius K 2 s).mapMatrix G)ᵀ
        = ((iterateFrobenius K 2 s).mapMatrix G)ᵀ * wJMat * (G * Gi) * wJMat := by
          rw [hGGi, Matrix.mul_one, Matrix.mul_assoc, wJMat_mul_wJMat, Matrix.mul_one]
      _ = (((iterateFrobenius K 2 s).mapMatrix G)ᵀ * wJMat * G) * Gi * wJMat := by
          simp only [Matrix.mul_assoc]
      _ = wJMat * Gi * wJMat := by rw [hiso]
  have h2 : (iterateFrobenius K 2 s).mapMatrix G = wJMat * Giᵀ * wJMat := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      wJMat_transpose] at this
    rw [this, Matrix.mul_assoc]
  have h3 : Giᵀ = wJMat * (iterateFrobenius K 2 s).mapMatrix G * wJMat := by
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, wJMat_mul_wJMat, Matrix.one_mul,
      Matrix.mul_assoc, wJMat_mul_wJMat, Matrix.mul_one]
  rw [← Matrix.transpose_map, map_pow_eq_mapMatrix, map_pow_eq_mapMatrix, h3, map_mul, map_mul,
    iterateFrobenius_mapMatrix_wJMat]
  congr 2
  ext i j
  simp [iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]

section Coords

omit [Finite K] [CharP K 2] in
theorem twistMat_apply_algebraMap (k : Type) [Field k] [Algebra K k] [CharP k 2] (i : ℕ)
    (g : SL(3, K)) (a b : Fin 3) :
    twistMat k i g a b = algebraMap K k ((g : Matrix (Fin 3) (Fin 3) K) a b ^ 2 ^ i) := by
  rw [twistMat_apply, frK_apply, map_pow]

open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE matRepE_apply repD finite_endRing)

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem u3_coords_of_three (hK : Nat.card K = (2 ^ s) ^ 2) (π : suJ K s →* (M ≃ₗ[ZMod 2] M))
    [Fact (B45Sz.repOfG π).IsIrreducible] (hnt : ∃ g, B45Sz.repOfG π g ≠ 1)
    (hdim : Module.finrank (EndRing (B45Sz.repOfG π)) M = 3) :
    ∃ (c : ℕ) (Q₀ : Matrix (Fin 3) (Fin 3) K) (φ : M ≃+ (Fin 3 → K)), Q₀ * Q₀ = 1 ∧
      ∀ g w, φ (π g w) =
        (Q₀ * ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ c) * Q₀).mulVec (φ w) := by
  classical
  set ρ := B45Sz.repOfG π with hρ
  have hs := one_le_s hK
  obtain ⟨d, hd1, hDcard, hdesc⟩ := u3_descent hK hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨E, _, _, _, ιK, ιD, a, b', hab, -, hmod, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  rw [hdim] at hdimW
  obtain ⟨hS, hH⟩ := cnt_of_card_eq_three hdimW.symm
  have hcard1 : (letJ s a b').card = 1 := by rw [card_letJ, hS, hH]
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hcard1
  have hj₀lt : j₀ < 2 * s :=
    Finset.mem_range.mp (letJ_subset a b' (by rw [hj₀]; exact Finset.mem_singleton_self _))
  have hwt : wtJ s a b' = 2 ^ j₀ := by rw [← sum_letJ, hj₀, Finset.sum_singleton]
  have h2sd : 2 * s ∣ d := dvd_of_modEq_single hs hj₀lt (by
    rw [← hwt, show 2 ^ (2 * s) = (2 ^ s) ^ 2 by rw [← pow_mul, mul_comm]]
    exact hmod)
  have hK' : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨ιK'⟩ := B42Sp4.exists_ringHom_of_dvd hK' hDcard h2sd
  let _ : Algebra K (EndRing ρ) := ιK'.toAlgebra
  let b : Module.Basis (Fin 3) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨a', b'', -, ⟨Φ⟩, hdim'⟩ := u3_exists_label hK hnt b ιK' (RingHom.id (EndRing ρ))
  obtain ⟨hS', hH'⟩ := cnt_of_card_eq_three hdim'.symm
  obtain ⟨i₁, hne, hrest⟩ := exists_single_letter hS' hH'
  have hcoord : ∀ (g : suJ K s) (w : M), b.equivFun (ρ g w) =
      matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) := by
    intro g w
    rw [matRepE_apply]
    have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.repD_apply] at this
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.matRep] using this.symm
  obtain ⟨-, hirr⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp Fact.out
  have hloc : ∀ (ℓ : Bool × Bool), (a' i₁, b'' i₁) = ℓ →
      ∃ θ : M ≃+ (Fin (locDim ℓ.1 ℓ.2) → EndRing ρ), ∀ g w,
        θ (π g w) = (locRep (F := K) (EndRing ρ) ℓ.1 ℓ.2 (i₁ : ℕ) (g : SL(3, K))).mulVec
          (θ w) := by
    intro ℓ hℓ
    obtain ⟨P, Q, hPQ⟩ := matIso_single (K := K) (EndRing ρ) hrest ℓ hℓ
    obtain ⟨Ψ⟩ := hPQ.equiv
    let Θ := Ψ.symm.trans Φ
    refine ⟨b.equivFun.toAddEquiv.trans Θ.symm.toLinearEquiv.toAddEquiv, fun g w => ?_⟩
    show Θ.symm (b.equivFun (ρ g w)) = _
    rw [hcoord, repEquiv_apply (EndRing ρ) Θ.symm g, matRep_apply]
    rfl
  have hcases : (a' i₁, b'' i₁) = (true, false) ∨ (a' i₁, b'' i₁) = (false, true) := by
    revert hne
    generalize a' i₁ = A
    generalize b'' i₁ = B
    cases A <;> cases B <;> decide
  rcases hcases with hℓ | hℓ
  ·
    obtain ⟨θ₀, hθ₀⟩ := hloc _ hℓ
    obtain ⟨θ, hθ'⟩ : ∃ θ : M ≃+ (Fin 3 → EndRing ρ), ∀ g w, θ (π g w) =
        (twistMat (EndRing ρ) (i₁ : ℕ) (g : SL(3, K))).mulVec (θ w) := ⟨θ₀, hθ₀⟩
    let R : suJ K s → Matrix (Fin 3) (Fin 3) K :=
      fun g => ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ (i₁ : ℕ))
    have hact : ∀ g w j, θ (π g w) j = ∑ c', ιK' (R g j c') * θ w c' := by
      intro g w j
      rw [hθ' g w]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [twistMat_apply_algebraMap]
      rfl
    have hsurj := B45Sz.surjective_of_coords π (fun U hU => hirr U hU) ιK' 0 R θ hact
    obtain ⟨φ, hφ⟩ := B45Sz.exists_coords_of_surjective π ιK' hsurj R θ hact
    exact ⟨i₁, 1, φ, Matrix.one_mul 1, fun g w => by
      rw [hφ, Matrix.one_mul, Matrix.mul_one]⟩
  ·
    obtain ⟨θ₀, hθ₀⟩ := hloc _ hℓ
    obtain ⟨θ, hθ'⟩ : ∃ θ : M ≃+ (Fin 3 → EndRing ρ), ∀ g w, θ (π g w) =
        (twistMat (EndRing ρ) (i₁ : ℕ) (g : SL(3, K))⁻¹)ᵀ.mulVec (θ w) := ⟨θ₀, hθ₀⟩
    let R : suJ K s → Matrix (Fin 3) (Fin 3) K :=
      fun g => ((((g⁻¹ : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map
        (· ^ 2 ^ (i₁ : ℕ)))ᵀ
    have hact : ∀ g w j, θ (π g w) j = ∑ c', ιK' (R g j c') * θ w c' := by
      intro g w j
      rw [hθ' g w]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Matrix.transpose_apply, twistMat_apply_algebraMap]
      rfl
    have hsurj := B45Sz.surjective_of_coords π (fun U hU => hirr U hU) ιK' 0 R θ hact
    obtain ⟨φ, hφ⟩ := B45Sz.exists_coords_of_surjective π ιK' hsurj R θ hact
    refine ⟨(i₁ : ℕ) + s, wJMat, φ, wJMat_mul_wJMat, fun g w => ?_⟩
    rw [hφ]
    congr 1
    exact inv_transpose_map_eq g.2 _

end Coords

section Witt

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable (K s) in
@[expose] noncomputable def suJToSU : suJ K s →* SU (unitaryInvolution K 2 s) 3 :=
  (Matrix.SpecialLinearGroup.toGL.comp (suJ K s).subtype).codRestrict _ fun g => g.2

theorem suJToSU_bijective : Function.Bijective (suJToSU K s) := by
  refine ⟨fun g g' h => ?_, fun A => ?_⟩
  · have h1 := congrArg (fun A : SU (unitaryInvolution K 2 s) 3 =>
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    exact Subtype.ext (Subtype.ext h1)
  · have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_SU.mp A.2).1
    refine ⟨⟨⟨(A : GL (Fin 3) K), hdet⟩, ?_⟩, ?_⟩
    · show Matrix.SpecialLinearGroup.toGL ⟨_, hdet⟩ ∈ SU (unitaryInvolution K 2 s) 3
      convert A.2 using 1
      exact Units.ext rfl
    · exact Subtype.ext (Units.ext rfl)

theorem exists_wittEquiv (hK : Nat.card K = (2 ^ s) ^ 2) :
    ∃ (ψJ : suJ K s ≃* StatedSU 3 (2 ^ s) K) (P Pi : Matrix (Fin 3) (Fin 3) K),
      Pi * P = 1 ∧ P * Pi = 1 ∧ ∀ g : suJ K s,
        ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          Pi * (((ψJ g : StatedSU 3 (2 ^ s) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            P := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  let ψJ : suJ K s ≃* StatedSU 3 (2 ^ s) K :=
    (MulEquiv.ofBijective _ suJToSU_bijective).trans ((conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)))
  have hPP : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨ψJ, P, ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hPP, hPP', fun g => ?_⟩
  have h1 : (((ψJ g : StatedSU 3 (2 ^ s) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rfl
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP,
    Matrix.mul_one]

end Witt

section Real

variable {V : Type} [CommGroup V]

open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor in
theorem binaryNaturalSU3_of_coords {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (θ : V ≃* Multiplicative M) {L : Subgroup (MulAut V)}
    (hK : Nat.card K = (2 ^ s) ^ 2) (ε : StatedSU 3 (2 ^ s) K →* L)
    (hε : Function.Surjective ε) (c : ℕ) (Q Q' : Matrix (Fin 3) (Fin 3) K) (hQQ' : Q' * Q = 1)
    (φ : M ≃+ (Fin 3 → K))
    (hφ : ∀ (γ : StatedSU 3 (2 ^ s) K) (w : M),
      φ (binPsi θ ((ε γ : L) : MulAut V) w) =
        (Q * ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ c) * Q').mulVec
          (φ w)) :
    BinaryNaturalSU3 L ⊤ ⊥ s := by
  have hQQ : Q * Q' = 1 := mul_eq_one_comm.mp hQQ'
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 c
  let φQ : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    { toFun := fun v => Q'.mulVec v
      invFun := fun v => Q.mulVec v
      left_inv := fun v => by simp only [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
      right_inv := fun v => by simp only [Matrix.mulVec_mulVec, hQQ', Matrix.one_mulVec]
      map_add' := fun v v' => Matrix.mulVec_add _ _ _ }
  let φ' : M ≃+ (Fin 3 → K) :=
    (φ.trans φQ).trans (AddEquiv.piCongrRight fun _ : Fin 3 => σ.symm.toAddEquiv)
  have hσ : ∀ (A : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K) (i : Fin 3),
      σ.symm ((A.map (· ^ 2 ^ c)).mulVec v i) = A.mulVec (fun j => σ.symm (v j)) i := by
    intro A v i
    have h1 : A.map (· ^ 2 ^ c) = A.map σ := by
      ext a b
      simp [σ, iterateFrobenius_def]
    rw [h1]
    have h2 : σ.symm ((A.map σ).mulVec v i) = ((A.map σ).map σ.symm).mulVec (σ.symm ∘ v) i :=
      RingHom.map_mulVec σ.symm.toRingHom (A.map σ) v i
    rw [h2, Matrix.map_map]
    congr 1
    ext a b
    simp
  have hφ' : ∀ (γ : StatedSU 3 (2 ^ s) K) (w : M),
      φ' (binPsi θ ((ε γ : L) : MulAut V) w) =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec (φ' w) := by
    intro γ w
    funext i
    show σ.symm ((Q'.mulVec (φ (binPsi θ ((ε γ : L) : MulAut V) w))) i) = _
    rw [hφ, Matrix.mulVec_mulVec]
    have h3 : Q' * (Q * ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ c) * Q') =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ c) * Q' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [h3, ← Matrix.mulVec_mulVec, hσ]
    rfl
  let β : V →* Multiplicative (Fin 3 → K) :=
    { toFun := fun v => Multiplicative.ofAdd (φ' (Multiplicative.toAdd (θ v)))
      map_one' := by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp }
  refine ⟨K, inferInstance, inferInstance, hK, ε, ?_⟩
  refine G64.realizesVia_nat_of hε le_top (fun _ _ _ => trivial)
    (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one])
    (β.comp (⊤ : Subgroup V).subtype) ?_ ?_ ?_
  · intro y
    refine ⟨⟨θ.symm (Multiplicative.ofAdd (φ'.symm (Multiplicative.toAdd y))), trivial⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [β]
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h1
      have h3 : φ' (Multiplicative.toAdd (θ u)) = 0 := congrArg Multiplicative.toAdd h1
      have h4 : Multiplicative.toAdd (θ u) = 0 := by
        rw [← map_zero φ'] at h3
        exact φ'.injective h3
      have h5 : θ u = 1 := Multiplicative.toAdd.injective h4
      simpa using congrArg θ.symm h5
    · intro h1
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, h1, map_one]
  · intro γ u hu
    apply Multiplicative.toAdd.injective
    have hθ : Multiplicative.toAdd (θ (((ε γ : L) : MulAut V) (u : V))) =
        binPsi θ ((ε γ : L) : MulAut V) (Multiplicative.toAdd (θ u)) := by
      rw [B42L2.toAdd_binPsi]
    show φ' (Multiplicative.toAdd (θ (((ε γ : L) : MulAut V) (u : V)))) =
      ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ φ' (Multiplicative.toAdd (θ u))
    rw [hθ, hφ']

end Real

end B45U3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  B45U3 in
theorem u3NaturalOfSmallDisplacement_holds :
    U3NaturalOfSmallDisplacement := by
  classical
  intro f hf K _ _ hK W _ _ hW L hperf hirr ⟨α⟩ ⟨t, htL, ht2, ht1, hidx⟩
  have : CharP K 2 := CFSG.QuasithinUnique.Setup.X7b.charP_two_of_card_pow (f := 2 * f)
    (by rw [hK, ← pow_mul, mul_comm])
  have hntW : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply ht1
    ext x
    exact Subsingleton.elim _ _
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  let α' : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU h 3 :=
    α.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨⟨ε, hεs, hεk, -, -⟩, -, -, -, -⟩ :=
    Setup.X5.irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders hf h hW L
      hperf hirr α'
  obtain ⟨ψJ, P, Pi, hPiP, hPPi, hψJ⟩ := exists_wittEquiv (s := f) hK
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW
  set ψ := binPsi θ with hψ
  let π : suJ K f →* (M ≃ₗ[ZMod 2] M) :=
    ψ.toMonoidHom.comp (L.subtype.comp (ε.comp ψJ.toMonoidHom))
  have hπ : ∀ g, π g = ψ ((ε (ψJ g) : ↥L) : MulAut W) := fun g => rfl
  have hirrM : ∀ U : Submodule (ZMod 2) M,
      (∀ g, ∀ u ∈ U, B45Sz.repOfG π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨γ, hγ⟩ := hεs ⟨l, hl⟩
    have h1 := hU (ψJ.symm γ) u hu
    rwa [B45Sz.repOfG_apply, hπ, MulEquiv.apply_symm_apply, hγ] at h1
  have hntM : Nontrivial M := by
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    refine ⟨⟨Multiplicative.toAdd (θ w), 0, fun h => hw ?_⟩⟩
    have h1 : θ w = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : Fact (B45Sz.repOfG π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mpr ⟨hntM, hirrM⟩⟩
  have htt : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := Subtype.ext ht2
  obtain ⟨γ₀, hγ₀⟩ := hεs ⟨t, htL⟩
  have hker : γ₀ ^ 2 ∈ ε.ker := by rw [MonoidHom.mem_ker, map_pow, hγ₀, sq, htt]
  obtain ⟨c₀, -, hc3, hcg⟩ := mem_unitaryScalars.mp (hεk hker)
  have hγ6 : (γ₀ ^ 2) ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hcg, ← map_pow, hc3, map_one, OneMemClass.coe_one])
  set γ₁ := γ₀ ^ 3 with hγ₁
  have hεγ₁ : ε γ₁ = ⟨t, htL⟩ := by
    rw [hγ₁, map_pow, hγ₀, pow_succ, sq, htt, one_mul]
  have hγ₁2 : γ₁ * γ₁ = 1 := by
    rw [hγ₁, ← pow_add, show 3 + 3 = 2 * 3 from rfl, pow_mul, hγ6]
  set g₁ := ψJ.symm γ₁ with hg₁
  have hπg₁ : π g₁ = ψ t := by rw [hπ, hg₁, MulEquiv.apply_symm_apply, hεγ₁]
  have hg₁2 : g₁ * g₁ = 1 := by rw [hg₁, ← map_mul, hγ₁2, map_one]
  have hg₁1 : g₁ ≠ 1 := by
    intro h1
    apply ht1
    have h2 : π g₁ = 1 := by rw [h1, map_one]
    rw [hπg₁] at h2
    exact ψ.injective (h2.trans (map_one ψ).symm)
  have hnt : ∃ g, B45Sz.repOfG π g ≠ 1 := by
    refine ⟨g₁, fun h1 => hg₁1 ?_⟩
    have h2 : π g₁ = 1 :=
      LinearEquiv.toLinearMap_injective (by rw [← B45Sz.repOfG_apply, h1]; rfl)
    rw [hπg₁] at h2
    exact absurd (ψ.injective (h2.trans (map_one ψ).symm)) ht1
  have hsmall : Module.finrank (ZMod 2) (LinearMap.range (B45Sz.repOfG π g₁ - 1)) ≤ 3 * f := by
    rw [B45Sz.index_fixV_zpowers_eq θ t] at hidx
    rw [B45Sz.repOfG_apply, hπg₁]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hidx
  have hdim := u3_finrank_eq_three_of_small hK hnt hg₁2 hg₁1 hsmall
  obtain ⟨c, Q₀, φ, hQ₀, hφ⟩ := u3_coords_of_three hK π hnt hdim
  let fr : K →+* K := iterateFrobenius K 2 c
  have hfr : ∀ A : Matrix (Fin 3) (Fin 3) K, A.map (· ^ 2 ^ c) = fr.mapMatrix A :=
    map_pow_eq_mapMatrix c
  refine binaryNaturalSU3_of_coords θ hK ε hεs c (Q₀ * fr.mapMatrix Pi) (fr.mapMatrix P * Q₀)
    ?_ φ fun γ w => ?_
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₀, hQ₀, Matrix.one_mul, ← map_mul, hPPi, map_one]
  · have h1 := hφ (ψJ.symm γ) w
    rw [hπ, MulEquiv.apply_symm_apply, hψJ, MulEquiv.apply_symm_apply, hfr, map_mul, map_mul]
      at h1
    rw [h1, hfr]
    congr 1
    simp only [Matrix.mul_assoc]

theorem asB45U3Even_holds :
    AsB45U3Even :=
  asB45U3Even_of_natural u3NaturalOfSmallDisplacement_holds

end CFSG.Quasithin

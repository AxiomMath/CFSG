module

public import CFSG.RankThree.PartOne.TCX.E.CentralClaims
public import CFSG.RankThree.PartOne.KLCE.A2Model
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SLnFamily

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open scoped MatrixGroups

section Basic

variable {ν : ℕ} {L : Type} [Field L]

theorem iterate_map_sl_n (Φ₀ : L →+* L) (k : ℕ) (Y : SL(ν, L)) (a b : Fin ν) :
    (((⇑(SpecialLinearGroup.map Φ₀))^[k] Y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) a b =
      (⇑Φ₀)^[k] ((Y : Matrix (Fin ν) (Fin ν) L) a b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp [ih]

theorem invTransposeSL_map_n {S : Type} [Field S] (f : L →+* S) (A : SL(ν, L)) :
    invTransposeSL (SpecialLinearGroup.map f A) = SpecialLinearGroup.map f (invTransposeSL A) := by
  apply Subtype.ext
  change ((invTransposeSL (SpecialLinearGroup.map f A) : SL(ν, S)) : Matrix (Fin ν) (Fin ν) S) =
    ((SpecialLinearGroup.map f (invTransposeSL A) : SL(ν, S)) : Matrix (Fin ν) (Fin ν) S)
  rw [coe_invTransposeSL, ← map_inv, SpecialLinearGroup.map_apply_coe,
    SpecialLinearGroup.map_apply_coe, coe_invTransposeSL]
  simp [RingHom.mapMatrix_apply, Matrix.transpose_map]

end Basic

section Split

variable {ν : ℕ} {K₀ K L : Type} [Field K₀] [Field K] [Finite K] [Field L]
  [Algebra K₀ L] [IsAlgClosure K₀ L] [Algebra K L] [CharP L 2]

theorem an_split_model (hν : 3 ≤ ν) {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : 1 ≤ p) (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K)
    (hσ : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c))
    (π : Equiv.Perm (Fin ν)) (Θ : SL(ν, L) ≃* SL(ν, L)) (b : Fin ν → Fin ν → Lˣ)
    (hshape : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        1 + single (π i) (π j) ((b i j : L) * iterateFrobenius L 2 f₀ t)) :
    ∃ ψ : SL(ν, K) →* SL(ν, L), Function.Injective ψ ∧
      (∀ B, Θ (ψ B) = ψ (SpecialLinearGroup.map σ.toRingHom B)) ∧
      ∀ X, (⇑Θ)^[p] X = X ↔ X ∈ ψ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀f : ⇑Φ₀ = (· ^ 2 ^ f₀) := funext hΦ₀c
  obtain ⟨⟨A, hA⟩, -⟩ := sln_root_permuting_frobenius_fixed_split (ℓ := 2) (f := f₀) (k := K₀)
    (Ω := L) Nat.prime_two hf₀ hK₀ hν π Θ b (fun i j hij t => by rw [hshape i j hij t, hΦ₀c])
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (by omega : 1 ≤ ν) A
  have hΘB : ∀ X : SL(ν, L), Θ X = B * SpecialLinearGroup.map Φ₀ X * B⁻¹ := fun X =>
    Subtype.ext (by
      rw [hA X, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hB, hΦ₀f])
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (ℓ := 2) (f := f₀) (K := K₀) (Ω := L) Nat.prime_two
    hf₀ hK₀ (by omega : 1 ≤ ν) (SpecialLinearGroup.toGL B)
  obtain ⟨H, hHdet, hBH⟩ := hlang B.2
  set Hs : SL(ν, L) := ⟨H, hHdet⟩ with hHsdef
  have hBHs : B = Hs⁻¹ * SpecialLinearGroup.map Φ₀ Hs := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      hΦ₀f, coe_inv_eq_nonsing_inv]
    change (SpecialLinearGroup.toGL B : Matrix (Fin ν) (Fin ν) L) = _
    rw [hBH, Matrix.coe_units_inv])
  have hΘH : ∀ X, Θ X = Hs⁻¹ * SpecialLinearGroup.map Φ₀ (Hs * X * Hs⁻¹) * Hs := fun X => by
    rw [hΘB, hBHs, map_mul, map_mul, map_inv]
    group
  let ι : K →+* L := algebraMap K L
  let ψ : SL(ν, K) →* SL(ν, L) :=
    (MulAut.conj Hs⁻¹).toMonoidHom.comp (SpecialLinearGroup.map ι)
  have hψ : ∀ Y, ψ Y = Hs⁻¹ * SpecialLinearGroup.map ι Y * Hs⁻¹⁻¹ := fun Y => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · exact (MulAut.conj Hs⁻¹).injective.comp (specialLinearGroup_map_injective ι.injective)
  · intro Y
    rw [hψ, hψ, hΘH, inv_inv]
    have h1 : SpecialLinearGroup.map Φ₀ (SpecialLinearGroup.map ι Y) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.map σ.toRingHom Y) := by
      ext i j
      simpa [SpecialLinearGroup.map_apply_coe] using hσ (Y i j)
    have h2 : Hs * (Hs⁻¹ * SpecialLinearGroup.map ι Y * Hs) * Hs⁻¹ =
        SpecialLinearGroup.map ι Y := by group
    rw [h2, h1]
  · intro X
    have hiter : ∀ k Y, (⇑Θ)^[k] Y =
        Hs⁻¹ * (⇑(SpecialLinearGroup.map Φ₀))^[k] (Hs * Y * Hs⁻¹) * Hs := by
      intro k
      induction k with
      | zero =>
        intro Y
        simp only [Function.iterate_zero, id_eq]
        group
      | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hΘH]
        congr 2
        group
    have hpow : ∀ Y : SL(ν, L), (⇑(SpecialLinearGroup.map Φ₀))^[p] Y = Y ↔
        ∀ a b, ((Y : Matrix (Fin ν) (Fin ν) L) a b) ^ 2 ^ (p * f₀) =
          (Y : Matrix (Fin ν) (Fin ν) L) a b := by
      intro Y
      constructor
      · intro hY a b
        have := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) a b) hY
        simp only [iterate_map_sl_n, iterate_frob_pow p Φ₀ hΦ₀c] at this
        rwa [← pow_mul, mul_comm f₀ p] at this
      · intro hY
        ext a b
        rw [iterate_map_sl_n, iterate_frob_pow p Φ₀ hΦ₀c, ← pow_mul, mul_comm f₀ p]
        exact hY a b
    rw [hiter]
    have hfix := range_eq_fixed (K := K) (L := L) (e := p * f₀) (by positivity) hK
    constructor
    · intro hX
      have hX' : (⇑(SpecialLinearGroup.map Φ₀))^[p] (Hs * X * Hs⁻¹) = Hs * X * Hs⁻¹ := by
        have := congrArg (fun Z => Hs * Z * Hs⁻¹) hX
        simpa [mul_assoc] using this
      obtain ⟨B', hB'⟩ := exists_map_eq_of_forall_mem_range ι.injective (Hs * X * Hs⁻¹)
        (fun a b => (hfix _).1 ((hpow _).1 hX' a b))
      refine ⟨B', ?_⟩
      rw [hψ, hB', inv_inv]
      group
    · rintro ⟨B', rfl⟩
      rw [hψ, inv_inv]
      have h3 : Hs * (Hs⁻¹ * SpecialLinearGroup.map ι B' * Hs) * Hs⁻¹ =
          SpecialLinearGroup.map ι B' := by group
      rw [h3]
      have h4 : (⇑(SpecialLinearGroup.map Φ₀))^[p] (SpecialLinearGroup.map ι B') =
          SpecialLinearGroup.map ι B' :=
        (hpow _).2 fun a b => (hfix _).2 ⟨B' a b, by simp [SpecialLinearGroup.map_apply_coe, ι]⟩
      rw [h4]

end Split

section UnitaryAux

variable {ν : ℕ} {L : Type} [Field L]

theorem iterate_F_even_n (Φ₀ : L →+* L) (m : ℕ) (Y : SL(ν, L)) :
    (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2 * m] Y =
      (⇑(SpecialLinearGroup.map Φ₀))^[2 * m] Y := by
  induction m generalizing Y with
  | zero => simp
  | succ m ih =>
    have h2 : (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2] Y =
        (⇑(SpecialLinearGroup.map Φ₀))^[2] Y := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id_eq]
      rw [← invTransposeSL_map_n, invTransposeSL_invTransposeSL]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, Function.iterate_add_apply,
      Function.iterate_add_apply, h2, ih]

theorem iterate_F_odd_n (Φ₀ : L →+* L) (m : ℕ) (Y : SL(ν, L)) :
    (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2 * m + 1] Y =
      invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[2 * m + 1] Y) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_F_even_n]

theorem invTransposeSL_iterate_map_n (Φ₀ : L →+* L) (k : ℕ) (Z : SL(ν, L)) :
    invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[k] Z) =
      (⇑(SpecialLinearGroup.map Φ₀))^[k] (invTransposeSL Z) := by
  induction k generalizing Z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, invTransposeSL_map_n]

theorem invTransposeSL_map_frob_iff_n [CharP L 2] (g : ℕ) (B : SL(ν, L)) :
    invTransposeSL (SpecialLinearGroup.map (iterateFrobenius L 2 g) B) = B ↔
      (((B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g))ᵀ * (B : Matrix (Fin ν) (Fin ν) L) = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : ((SpecialLinearGroup.map (iterateFrobenius L 2 g) B : SL(ν, L)) :
      Matrix (Fin ν) (Fin ν) L) = (B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g) := by
    ext a b
    simp [SpecialLinearGroup.map_apply_coe, iterateFrobenius_def]
  have hinv : (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * (B : Matrix (Fin ν) (Fin ν) L) = 1 := by
    exact congrArg (fun C : SL(ν, L) => (C : Matrix (Fin ν) (Fin ν) L)) (inv_mul_cancel B)
  have hinv' : (B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 := by
    exact congrArg (fun C : SL(ν, L) => (C : Matrix (Fin ν) (Fin ν) L)) (mul_inv_cancel B)
  constructor
  · intro h
    have h1 := congrArg invTransposeSL h
    rw [invTransposeSL_invTransposeSL] at h1
    have h2 := congrArg (fun C : SL(ν, L) => (C : Matrix (Fin ν) (Fin ν) L)) h1
    simp only [hmap, coe_invTransposeSL] at h2
    rw [h2, Matrix.transpose_transpose]
    exact hinv
  · intro h
    have h1 : SpecialLinearGroup.map (iterateFrobenius L 2 g) B = invTransposeSL B := by
      apply Subtype.ext
      change ((SpecialLinearGroup.map (iterateFrobenius L 2 g) B : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = ((invTransposeSL B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)
      rw [hmap, coe_invTransposeSL]
      have h3 : ((B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g))ᵀ =
          (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
        calc ((B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g))ᵀ
            = ((B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g))ᵀ *
              ((B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L)) := by
              rw [hinv', Matrix.mul_one]
          _ = (((B : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ g))ᵀ *
                (B : Matrix (Fin ν) (Fin ν) L)) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
              rw [Matrix.mul_assoc]
          _ = (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) := by rw [h, Matrix.one_mul]
      rw [← h3, Matrix.transpose_transpose]
    rw [h1, invTransposeSL_invTransposeSL]

end UnitaryAux

section SUHomsN

variable {ν : ℕ} {K : Type} [Field K] [Finite K] {g : ℕ}

@[expose] def statedSU_toSL_n (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2) :
    ↥(StatedSU ν (2 ^ g) K) →* SL(ν, K) where
  toFun A := ⟨((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K),
    ((mem_statedSU_iff_n hν hK A.1).1 A.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem statedSU_toSL_n_injective (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2) :
    Function.Injective (statedSU_toSL_n hν hK) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun C : SL(ν, K) => (C : Matrix (Fin ν) (Fin ν) K)) h

theorem statedSU_toSL_n_unitary (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2)
    (A : ↥(StatedSU ν (2 ^ g) K)) :
    (((statedSU_toSL_n hν hK A : SL(ν, K)) : Matrix (Fin ν) (Fin ν) K).map (· ^ 2 ^ g))ᵀ *
      ((statedSU_toSL_n hν hK A : SL(ν, K)) : Matrix (Fin ν) (Fin ν) K) = 1 :=
  ((mem_statedSU_iff_n hν hK A.1).1 A.2).2

theorem toGL_mem_statedSU_n (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2) (B : SL(ν, K))
    (h : (((B : Matrix (Fin ν) (Fin ν) K)).map (· ^ 2 ^ g))ᵀ *
      (B : Matrix (Fin ν) (Fin ν) K) = 1) :
    Matrix.SpecialLinearGroup.toGL B ∈ StatedSU ν (2 ^ g) K := by
  rw [mem_statedSU_iff_n hν hK]
  exact ⟨B.2, h⟩

@[expose] noncomputable def statedSU_map_n (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2)
    (σ : K ≃+* K) : ↥(StatedSU ν (2 ^ g) K) →* ↥(StatedSU ν (2 ^ g) K) :=
  ((Matrix.GeneralLinearGroup.map σ.toRingHom).comp (StatedSU ν (2 ^ g) K).subtype).codRestrict
    (StatedSU ν (2 ^ g) K) fun A => by
      have hA := (mem_statedSU_iff_n hν hK A.1).1 A.2
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, mem_statedSU_iff_n hν hK]
      have hc : ((Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin ν) K) : GL (Fin ν) K) :
          Matrix (Fin ν) (Fin ν) K) = ((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map σ := rfl
      rw [hc]
      refine ⟨?_, ?_⟩
      · have := RingHom.map_det σ.toRingHom ((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K)
        rw [hA.1, map_one] at this
        exact this.symm
      · have e : (((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map σ).map (· ^ 2 ^ g) =
            (((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map (· ^ 2 ^ g)).map σ := by
          ext i j
          simp
        rw [e, ← Matrix.transpose_map, ← Matrix.map_mul]
        rw [hA.2]
        ext i j
        simp [Matrix.one_apply]

theorem coe_statedSU_map_n (hν : 1 ≤ ν) (hK : Nat.card K = (2 ^ g) ^ 2) (σ : K ≃+* K)
    (A : ↥(StatedSU ν (2 ^ g) K)) :
    ((((statedSU_map_n hν hK σ A : ↥(StatedSU ν (2 ^ g) K)) : GL (Fin ν) K)) :
      Matrix (Fin ν) (Fin ν) K) =
      (((A : GL (Fin ν) K)) : Matrix (Fin ν) (Fin ν) K).map σ := rfl

end SUHomsN

section Unitary

variable {ν : ℕ} {K₀ L : Type} [Field K₀] [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L] [CharP L 2]

omit [Algebra K₀ L] [IsAlgClosure K₀ L] [CharP L 2] [Field K₀] in
theorem eq_conj_of_inv_conj (H : GL (Fin ν) L) (N T : Matrix (Fin ν) (Fin ν) L)
    (h : (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L) * N * (H : Matrix (Fin ν) (Fin ν) L) = T) :
    N = (H : Matrix (Fin ν) (Fin ν) L) * T * (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
  rw [← h]
  calc N = ((H : Matrix (Fin ν) (Fin ν) L) * (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L)) * N *
        ((H : Matrix (Fin ν) (Fin ν) L) * (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L)) := by
        rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem an_unitary_model (hν : 3 ≤ ν) {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hodd : Odd p) (π : Equiv.Perm (Fin ν)) (Θ : SL(ν, L) ≃* SL(ν, L))
    (b : Fin ν → Fin ν → Lˣ)
    (hshape : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        1 + single (π j) (π i) ((b i j : L) * iterateFrobenius L 2 f₀ t)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K)
      (ψ : ↥(StatedSU ν (2 ^ (p * f₀)) K) →* SL(ν, L))
      (τ' : ↥(StatedSU ν (2 ^ (p * f₀)) K) →* ↥(StatedSU ν (2 ^ (p * f₀)) K)),
      Nat.card K = (2 ^ (p * f₀)) ^ 2 ∧ orderOf σ = p ∧
      (∀ A, (((τ' A : ↥(StatedSU ν (2 ^ (p * f₀)) K)) : GL (Fin ν) K) :
          Matrix (Fin ν) (Fin ν) K) =
        (((A : ↥(StatedSU ν (2 ^ (p * f₀)) K)) : GL (Fin ν) K) :
          Matrix (Fin ν) (Fin ν) K).map σ) ∧
      Function.Injective ψ ∧ (∀ A, Θ (ψ A) = ψ (τ' A)) ∧
      ∀ X, (⇑Θ)^[p] X = X ↔ X ∈ ψ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hp0 := hp.pos
  have hν1 : 1 ≤ ν := by omega
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  obtain ⟨⟨A, hA⟩, -⟩ := sln_root_permuting_frobenius_fixed_unitary (ℓ := 2) (f := f₀) (k := K₀)
    (Ω := L) Nat.prime_two hf₀ hK₀ hν π Θ b (fun i j hij t => by rw [hshape i j hij t, hΦ₀c])
  obtain ⟨H, hHdet, hconj, -⟩ := matrix_graph_frobenius_unitary_descent (ℓ := 2) (f := f₀)
    (K := K₀) (Ω := L) Nat.prime_two hf₀ hK₀ hν1 A
  set Hs : SL(ν, L) := ⟨H, hHdet⟩ with hHsdef
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  have hmapΦ : ∀ X : SL(ν, L), ((SpecialLinearGroup.map Φ₀ X : SL(ν, L)) :
      Matrix (Fin ν) (Fin ν) L) = (X : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ f₀) := fun X => by
    ext a b
    simp [SpecialLinearGroup.map_apply_coe, hΦ₀c]
  have hcoe : ∀ Y : SL(ν, L), ((Y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      ((Matrix.SpecialLinearGroup.toGL Y : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) :=
    fun Y => rfl
  have hΘH : ∀ Z : SL(ν, L), Θ (Hs * Z * Hs⁻¹) =
      Hs * invTransposeSL (SpecialLinearGroup.map Φ₀ Z) * Hs⁻¹ := by
    intro Z
    apply Subtype.ext
    have hY : ((Hs * Z * Hs⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        (H : Matrix (Fin ν) (Fin ν) L) * (Z : Matrix (Fin ν) (Fin ν) L) *
          (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      rw [hcoe, map_mul, map_mul, map_inv, hHs, Units.val_mul, Units.val_mul]
      rfl
    have h1 := hconj (Matrix.SpecialLinearGroup.toGL Z) Z.2
    have h2 := eq_conj_of_inv_conj H _ _ h1
    have h3 : ((Hs * invTransposeSL (SpecialLinearGroup.map Φ₀ Z) * Hs⁻¹ : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = (H : Matrix (Fin ν) (Fin ν) L) *
          ((((Z : Matrix (Fin ν) (Fin ν) L).map (· ^ 2 ^ f₀))⁻¹)ᵀ) *
            (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      rw [hcoe, map_mul, map_mul, map_inv, hHs, Units.val_mul, Units.val_mul]
      change (H : Matrix (Fin ν) (Fin ν) L) * ((invTransposeSL (SpecialLinearGroup.map Φ₀ Z) :
        SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) * (↑H⁻¹ : Matrix (Fin ν) (Fin ν) L) = _
      rw [coe_invTransposeSL, coe_inv_eq_nonsing_inv, hmapΦ]
    rw [h3, hA, hY]
    exact h2
  obtain ⟨K, _, _, _, ι, hKcard, hKfix⟩ :=
    exists_subfield_card (L := L) (n := 2 * (p * f₀)) (by positivity)
  have hK : Nat.card K = (2 ^ (p * f₀)) ^ 2 := by rw [hKcard, ← pow_mul, mul_comm]
  obtain ⟨σ, hσord, hσc⟩ := exists_sigma_unitary (K := K) hf₀ hp hodd hK
  set FQ : K →+* K := iterateFrobenius K 2 (p * f₀) with hFQdef
  set σ₁ : K →+* K := iterateFrobenius K 2 f₀ with hσ₁def
  have hFQ : ∀ a, FQ a = a ^ 2 ^ (p * f₀) := fun a => iterateFrobenius_def 2 (p * f₀) a
  have hσ₁ : ∀ a, σ₁ a = a ^ 2 ^ f₀ := fun a => iterateFrobenius_def 2 f₀ a
  have hι₁ : ∀ a : K, Φ₀ (ι a) = ι (σ₁ a) := fun a => by rw [hΦ₀c, hσ₁, map_pow]
  have hιQ : ∀ a : K, (⇑Φ₀)^[p] (ι a) = ι (FQ a) := fun a => by
    rw [iterate_frob_pow p Φ₀ hΦ₀c, hFQ, map_pow, ← pow_mul, mul_comm]
  have hσFQ : ∀ a, σ a = FQ (σ₁ a) := fun a => by
    rw [hσc, hFQ, hσ₁, ← pow_mul, ← pow_add]
    congr 2
    ring
  set toSL := statedSU_toSL_n hν1 hK with htoSL
  set ψ : ↥(StatedSU ν (2 ^ (p * f₀)) K) →* SL(ν, L) :=
    (MulAut.conj Hs).toMonoidHom.comp ((SpecialLinearGroup.map ι).comp toSL) with hψdef
  have hψ : ∀ A, ψ A = Hs * SpecialLinearGroup.map ι (toSL A) * Hs⁻¹ := fun A => rfl
  set τ' := statedSU_map_n hν1 hK σ with hτ'
  have htoSLτ : ∀ A, toSL (τ' A) = SpecialLinearGroup.map σ.toRingHom (toSL A) := fun A =>
    Subtype.ext rfl
  have hBu : ∀ A, invTransposeSL (SpecialLinearGroup.map FQ (toSL A)) = toSL A := fun A =>
    (invTransposeSL_map_frob_iff_n (p * f₀) (toSL A)).2 (statedSU_toSL_n_unitary hν1 hK A)
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ, ψ, τ', hK, hσord,
    fun A => coe_statedSU_map_n hν1 hK σ A, ?_, ?_, ?_⟩
  · intro A A' hAA
    rw [hψ, hψ] at hAA
    exact statedSU_toSL_n_injective hν1 hK (specialLinearGroup_map_injective ι.injective
      ((MulAut.conj Hs).injective hAA))
  · intro A
    have h1 : invTransposeSL (SpecialLinearGroup.map σ₁ (toSL A)) =
        SpecialLinearGroup.map σ.toRingHom (toSL A) := by
      have hc : SpecialLinearGroup.map FQ (SpecialLinearGroup.map σ₁ (toSL A)) =
          SpecialLinearGroup.map σ₁ (SpecialLinearGroup.map FQ (toSL A)) := by
        ext i j
        simp [SpecialLinearGroup.map_apply_coe, hFQ, hσ₁, ← pow_mul, mul_comm]
      have hu1 : invTransposeSL (SpecialLinearGroup.map FQ (SpecialLinearGroup.map σ₁ (toSL A))) =
          SpecialLinearGroup.map σ₁ (toSL A) := by
        rw [hc, invTransposeSL_map_n, hBu]
      have h2 := congrArg invTransposeSL hu1
      rw [invTransposeSL_invTransposeSL] at h2
      rw [← h2]
      ext i j
      simp [SpecialLinearGroup.map_apply_coe, hσFQ]
    rw [hψ A, hψ (τ' A), htoSLτ A, hΘH]
    congr 2
    have h2 : SpecialLinearGroup.map Φ₀ (SpecialLinearGroup.map ι (toSL A)) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.map σ₁ (toSL A)) := by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe, hι₁]
    rw [h2, invTransposeSL_map_n, h1]
  · intro X
    obtain ⟨m, hm⟩ := hodd
    have hiter : ∀ k Y, (⇑Θ)^[k] Y = Hs *
        (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[k] (Hs⁻¹ * Y * Hs) * Hs⁻¹ := by
      intro k
      induction k with
      | zero =>
        intro Y
        simp only [Function.iterate_zero, id_eq]
        group
      | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hΘH]
    have hF : ∀ Y : SL(ν, L), (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[p] Y =
        invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) := by
      intro Y
      rw [hm]
      exact iterate_F_odd_n Φ₀ m Y
    have hmapι : ∀ B : SL(ν, K), (⇑(SpecialLinearGroup.map Φ₀))^[p] (SpecialLinearGroup.map ι B) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.map FQ B) := by
      intro B
      ext i j
      simpa [iterate_map_sl_n, SpecialLinearGroup.map_apply_coe] using hιQ (B i j)
    have key : ∀ Y : SL(ν, L), invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) = Y ↔
        ∃ A, SpecialLinearGroup.map ι (toSL A) = Y := by
      intro Y
      constructor
      · intro hY
        have hY1 : (⇑(SpecialLinearGroup.map Φ₀))^[p] Y = invTransposeSL Y := by
          have := congrArg invTransposeSL hY
          rwa [invTransposeSL_invTransposeSL] at this
        have hY2 : (⇑(SpecialLinearGroup.map Φ₀))^[p] ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) =
            Y := by
          rw [hY1, ← invTransposeSL_iterate_map_n, hY1, invTransposeSL_invTransposeSL]
        have hent : ∀ i j, ∃ c : K, ι c = (Y : Matrix (Fin ν) (Fin ν) L) i j := by
          intro i j
          refine (hKfix _).1 ?_
          have h3 := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) i j) hY2
          simp only [iterate_map_sl_n, iterate_frob_pow p Φ₀ hΦ₀c] at h3
          rw [← pow_mul] at h3
          have e : (2 ^ f₀) ^ p * (2 ^ f₀) ^ p = 2 ^ (2 * (p * f₀)) := by
            rw [← pow_mul, ← pow_add, ← two_mul]
            congr 1
            ring
          rwa [e] at h3
        obtain ⟨B, hB⟩ := exists_map_eq_of_forall_mem_range ι.injective Y
          (fun i j => by
            obtain ⟨c, hc⟩ := hent i j
            exact ⟨c, hc⟩)
        have hu : invTransposeSL (SpecialLinearGroup.map FQ B) = B := by
          have h1 : invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p]
              (SpecialLinearGroup.map ι B)) = SpecialLinearGroup.map ι B := by
            rw [hB]
            exact hY
          rw [hmapι, invTransposeSL_map_n] at h1
          exact specialLinearGroup_map_injective ι.injective h1
        have hmem := toGL_mem_statedSU_n hν1 hK B
          ((invTransposeSL_map_frob_iff_n (p * f₀) B).1 hu)
        refine ⟨⟨_, hmem⟩, ?_⟩
        rw [← hB]
        rfl
      · rintro ⟨A, rfl⟩
        rw [hmapι, invTransposeSL_map_n, hBu]
    rw [hiter, hF]
    constructor
    · intro hX
      have hX' : invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] (Hs⁻¹ * X * Hs)) =
          Hs⁻¹ * X * Hs := by
        have := congrArg (fun Z => Hs⁻¹ * Z * Hs) hX
        simpa [mul_assoc] using this
      obtain ⟨A, hA⟩ := (key _).1 hX'
      refine ⟨A, ?_⟩
      rw [hψ, hA]
      group
    · rintro ⟨A, rfl⟩
      rw [hψ]
      have h3 : Hs⁻¹ * (Hs * SpecialLinearGroup.map ι (toSL A) * Hs⁻¹) * Hs =
          SpecialLinearGroup.map ι (toSL A) := by group
      rw [h3, (key _).2 ⟨A, rfl⟩]

end Unitary

section Embedding

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


structure AnEmbedding (τ : Tag) (ν : ℕ) (S : Set (Fin τ.rank → ℤ)) where
  ρ : ∀ (L : Type) [Field L], SL(ν, L) →* ModGL τ L
  r : Fin ν → Fin ν → (Fin τ.rank → ℤ)
  mem : ∀ x, x ∈ S ↔ ∃ i j, i ≠ j ∧ x = r i j
  isRoot : ∀ i j, i ≠ j → IsRoot τ (r i j)
  neg : ∀ i j, -(r i j) = r j i
  inj : ∀ (L : Type) [Field L], Function.Injective (ρ L)
  range : ∀ (L : Type) [Field L], (ρ L).range = rootSpan τ L S
  gen : ∀ (L : Type) [Field L] (i j : Fin ν) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ L (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (r i j) ((ε : L) * t)
  tor : ∀ (L : Type) [Field L] (b : Fin τ.rank → Lˣ), ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
    rootDiagUnit τ b * ρ L A * (rootDiagUnit τ b)⁻¹ = ρ L (conjDiagn d A)
  diag : ∀ (L : Type) [Field L] (A : SL(ν, L)),
    (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0) → ρ L A ∈ torusGroup τ L

end Embedding

section Bridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {ν : ℕ} {S : Set (Fin τ.rank → ℤ)} {L : Type} [Field L]

theorem an_bridge (E : AnEmbedding τ ν S) {n₀ : ModGL τ L} {Φ₀ Fr : L →+* L} {p : ℕ}
    (hn₀fix : Units.map (entrywiseHom Φ₀) n₀ = n₀)
    (hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u)
    (Θ₀ : SL(ν, L) ≃* SL(ν, L))
    (hΘ₀ : ∀ X, n₀ * Units.map (entrywiseHom Φ₀) (E.ρ L X) * n₀⁻¹ = E.ρ L (Θ₀ X))
    {D : Type} [Group D] (ψ : D →* SL(ν, L)) (τ' : D →* D) (hψinj : Function.Injective ψ)
    (hcompat : ∀ d, Θ₀ (ψ d) = ψ (τ' d))
    (hfix : ∀ X, (⇑Θ₀)^[p] X = X ↔ X ∈ ψ.range) :
    Function.Injective ((E.ρ L).comp ψ) ∧
      ((E.ρ L).comp ψ).range = (E.ρ L).range ⊓
        twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) ∧
      ∀ d, n₀ * Units.map (entrywiseHom Φ₀) (((E.ρ L).comp ψ) d) * n₀⁻¹ =
        ((E.ρ L).comp ψ) (τ' d) := by
  have hρiter : ∀ (k : ℕ) (X : SL(ν, L)), E.ρ L ((⇑Θ₀)^[k] X) =
      (fun v => n₀ * Units.map (entrywiseHom Φ₀) v * n₀⁻¹)^[k] (E.ρ L X) := by
    intro k
    induction k with
    | zero => intro X; rfl
    | succ k ih =>
      intro X
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hΘ₀]
  have hρp : ∀ X : SL(ν, L), E.ρ L ((⇑Θ₀)^[p] X) =
      n₀ ^ p * Units.map (entrywiseHom Fr) (E.ρ L X) * (n₀ ^ p)⁻¹ := by
    intro X
    rw [hρiter, iterate_F0 (Units.map (entrywiseHom Φ₀)) hn₀fix p, ← hΦK]
  refine ⟨(E.inj L).comp hψinj, ?_, fun d => ?_⟩
  · refine Subgroup.ext fun u => ?_
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨⟨ψ d, rfl⟩, ?_⟩
      rw [mem_twistedFixedPoints]
      show n₀ ^ p * Units.map (entrywiseHom Fr) (E.ρ L (ψ d)) * (n₀ ^ p)⁻¹ = E.ρ L (ψ d)
      rw [← hρp, (hfix _).2 ⟨d, rfl⟩]
    · rintro ⟨⟨X, rfl⟩, hX⟩
      rw [mem_twistedFixedPoints, ← hρp] at hX
      have h1 : (⇑Θ₀)^[p] X = X := (E.inj L) hX
      obtain ⟨d, hd⟩ := (hfix X).1 h1
      exact ⟨d, by simp [hd]⟩
  · change n₀ * Units.map (entrywiseHom Φ₀) (E.ρ L (ψ d)) * n₀⁻¹ = E.ρ L (ψ (τ' d))
    rw [hΘ₀, hcompat]

end Bridge

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}

theorem iterate_coe_map {D ι K : Type} [Field K] (c : D → Matrix ι ι K) (τ : D → D)
    (σ : K ≃+* K) (hτ : ∀ A, c (τ A) = (c A).map σ) (k : ℕ) (A : D) :
    c (τ^[k] A) = (c A).map (σ ^ k) := by
  induction k generalizing A with
  | zero => ext i j; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, hτ]
    ext i j
    simp [pow_succ, RingAut.mul_apply]

theorem iterate_map_sl_ringAut {ν : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (k : ℕ)
    (B : SL(ν, K)) :
    (⇑(Matrix.SpecialLinearGroup.map σ.toRingHom))^[k] B =
      Matrix.SpecialLinearGroup.map (σ ^ k).toRingHom B := by
  induction k generalizing B with
  | zero => ext i j; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    ext i j
    simp [pow_succ, RingAut.mul_apply]

theorem an_model (E : AnEmbedding τ (m + 3) S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (π : Equiv.Perm (Fin (m + 3))) {K₀ K L : Type} [Field K₀] [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L] [Algebra K L] [CharP L 2] {f₀ p : ℕ}
    (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (hσ : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c))
    (n₀ : ModGL τ L) (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hn₀m : n₀ ∈ monomialSubgroup τ L)
    (hWs : δ = 1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π i) (π j))
    (hWu : δ = -1 → ∀ i j, i ≠ j →
      weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = E.r (π j) (π i)) :
    ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D), Function.Injective ρ' ∧
      ρ'.range = (E.ρ L).range ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ∧
      (∀ d, n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ k : ℕ, ¬ p ∣ k → ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G),
        (∀ d, φ d = 1 → d ∈ Subgroup.center D) → (∀ d, α (φ d) = φ ((⇑τ')^[k] d)) →
        ∀ Q : Subgroup G, φ.range = Q → LayerClaims2 p α Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hp0 := hp.pos
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀bij : Function.Bijective Φ₀ := ⟨Φ₀.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f₀ by positivity)
    exact ⟨x, by rw [hΦ₀c, hx]⟩⟩
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  choose! ε hε using fun (i j : Fin (m + 3)) (hij : i ≠ j) => E.gen L i j hij
  rcases hδ with rfl | rfl
  ·
    have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π i) (π j)) ((b : L) * c) :=
      fun i j hij => by
        obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn₀m (E.isRoot i j hij)
        exact ⟨μ, fun c => by rw [hμ c, hWs rfl i j hij]⟩
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
      (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj
    obtain ⟨ψ, hψinj, hψcompat, hψfix⟩ := an_split_model (by omega : 3 ≤ m + 3) hf₀ hK₀ hp.one_le
      hK σ hσ π Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := an_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ
      (Matrix.SpecialLinearGroup.map σ.toRingHom) hψinj hψcompat hψfix
    refine ⟨SL(m + 3, K), inferInstance, (E.ρ L).comp ψ, Matrix.SpecialLinearGroup.map σ.toRingHom,
      hinj, hrange, hcompat, ?_⟩
    intro k hk G _ α φ hkerφ hαφ Q hQ
    have hσk : σ ^ k ≠ 1 := fun h => hk (hσord ▸ orderOf_dvd_of_pow_eq_one h)
    refine sl_claims2' (m := m + 1) hp5 hf₀ hK hσk α φ hkerφ (fun B => ?_) Q hQ
    rw [hαφ, iterate_map_sl_ringAut]
  ·
    have hconj : ∀ i j : Fin (m + 3), i ≠ j → ∃ b : Lˣ, ∀ c : L,
        n₀ * pinnedX τ L (E.r i j) c * n₀⁻¹ = pinnedX τ L (E.r (π j) (π i)) ((b : L) * c) :=
      fun i j hij => by
        obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn₀m (E.isRoot i j hij)
        exact ⟨μ, fun c => by rw [hμ c, hWu rfl i j hij]⟩
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData_n (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
      (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj
    obtain ⟨K'', _, _, _, σ'', ψ, τ', hK'', hσ''ord, hτ', hψinj, hψcompat, hψfix⟩ :=
      an_unitary_model (by omega : 3 ≤ m + 3) hf₀ hK₀ hp (hp.odd_of_ne_two (by omega)) π Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := an_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ τ' hψinj hψcompat hψfix
    refine ⟨↥(StatedSU (m + 3) (2 ^ (p * f₀)) K''), inferInstance, (E.ρ L).comp ψ, τ', hinj,
      hrange, hcompat, ?_⟩
    intro k hk G _ α φ hkerφ hαφ Q hQ
    have hσk : orderOf (σ'' ^ k) = p := by
      rw [Nat.Coprime.orderOf_pow (by rw [hσ''ord]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hk),
        hσ''ord]
    let τk : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') →* ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') :=
      { toFun := (⇑τ')^[k]
        map_one' := Function.iterate_fixed (map_one τ') k
        map_mul' := fun a b => iterate_map_mul τ' k a b }
    have hτk : ∀ A, (((τk A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'')) : GL (Fin (m + 3)) K'') :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K'') =
        (((A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'')) : GL (Fin (m + 3)) K'') :
          Matrix (Fin (m + 3)) (Fin (m + 3)) K'').map (σ'' ^ k) := fun A =>
      iterate_coe_map (fun A : ↥(StatedSU (m + 3) (2 ^ (p * f₀)) K'') =>
        ((A : GL (Fin (m + 3)) K'') : Matrix (Fin (m + 3)) (Fin (m + 3)) K'')) τ' σ'' hτ' k A
    exact su_claims2' hp hp5 hf₀ hK'' hσk α φ hkerφ τk hτk hαφ Q hQ

end Model

end CFSG.RankThree.PartOne.TCX.E

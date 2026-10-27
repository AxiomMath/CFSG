module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.RankThree.Classical2

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Field

theorem exists_isAlgClosure_powFixedSubfield {ℓ : ℕ} [Fact ℓ.Prime] {k Ω : Type} [Field k]
    [Finite k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [CharP Ω ℓ] {f : ℕ} (hf : 1 ≤ f) :
    ∃ K : Subfield Ω, IsAlgClosure K Ω ∧ Nat.card K = ℓ ^ f ∧ ∀ c : Ω, c ∈ K ↔ c ^ ℓ ^ f = c := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  let K : Subfield Ω := (iterateFrobenius Ω ℓ f).eqLocusField (RingHom.id Ω)
  have hmem : ∀ c : Ω, c ∈ K ↔ c ^ ℓ ^ f = c := fun c => by
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hcard : Nat.card K = ℓ ^ f := by
    rw [← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (e := f) (by omega)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  refine ⟨K, ?_, hcard, hmem⟩
  let _ : Algebra (ZMod ℓ) Ω := ZMod.algebra Ω ℓ
  have hΩ : Algebra.IsAlgebraic (ZMod ℓ) Ω :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := k)
  have : CharP K ℓ := RingHom.charP (algebraMap K Ω) (algebraMap K Ω).injective ℓ
  have hAlg : Algebra.IsAlgebraic K Ω := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp0, hpx⟩ := hΩ.isAlgebraic x
    let φ : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap K Ω).comp φ = algebraMap (ZMod ℓ) Ω from RingHom.ext_zmod _ _]
    rwa [Polynomial.aeval_def] at hpx
  exact ⟨inferInstance, hAlg⟩

end Field

section CharTwo

variable {Ω : Type*} [Field Ω] {n : ℕ}

theorem finite_odd_card_center_specialLinearGroup [CharP Ω 2] (hn : 1 ≤ n) :
    Finite (Subgroup.center SL(n, Ω)) ∧ Odd (Nat.card (Subgroup.center SL(n, Ω))) := by
  have : NeZero (Fintype.card (Fin n)) := ⟨by rw [Fintype.card_fin]; omega⟩
  let ε := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin n) (R := Ω)
    ⟨0, by omega⟩
  have hfin : Finite (Subgroup.center SL(n, Ω)) := Finite.of_equiv _ ε.symm.toEquiv
  refine ⟨hfin, ?_⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw : orderOf (ε z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have hw2 : (((ε z : rootsOfUnity (Fintype.card (Fin n)) Ω) : Ωˣ) : Ω) ^ 2 = 1 := by
    have h1 : ε z ^ 2 = 1 := by
      rw [← hw]
      exact pow_orderOf_eq_one (ε z)
    have h := congrArg (fun u : rootsOfUnity (Fintype.card (Fin n)) Ω => ((u : Ωˣ) : Ω)) h1
    simpa using h
  have htwo : (2 : Ω) = 0 := CharTwo.two_eq_zero
  have hsq1 : ∀ u : Ω, u ^ 2 = 1 → u = 1 := fun u hu => by
    have h : (u - 1) ^ 2 = 0 := by linear_combination hu + (1 - u) * htwo
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  have hw1 := hsq1 _ hw2
  have hone : ε z = 1 := Subtype.ext (Units.ext (by simpa using hw1))
  rw [hone, orderOf_one] at hw
  exact absurd hw (by norm_num)

theorem isPerfect_specialLinearGroup_of_infinite [Infinite Ω] (hn : 2 ≤ n) :
    Group.IsPerfect SL(n, Ω) :=
  CFSG.LinearGroups.special_linear_isPerfect hn (Or.inr (Infinite.exists_subset_card_eq Ω 4))

end CharTwo

section Split

variable {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {n : ℕ}

theorem eqLocus_conjSLn_frobenius_split (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (hn : 1 ≤ n) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    (A : GL (Fin n) Ω) :
    ∃ (H : SL(n, Ω)) (e : SL(n, k) ≃*
        ((conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr)).eqLocus (MonoidHom.id _)),
      ∀ Y, ((e Y : _) : SL(n, Ω)) = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hσ : ⇑Fr = (· ^ ℓ ^ f) := funext hFr
  set Φ : SL(n, Ω) →* SL(n, Ω) := (conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr) with hΦdef
  have hmemΦ : ∀ X, X ∈ Φ.eqLocus (MonoidHom.id _) ↔ Φ X = X := fun _ => Iff.rfl
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq hn A
  have hΦB : ∀ X : SL(n, Ω), Φ X = B * Matrix.SpecialLinearGroup.map Fr X * B⁻¹ := fun X =>
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hB]
      rfl)
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang hℓ hf hk hn (Matrix.SpecialLinearGroup.toGL B)
  obtain ⟨H, hHdet, hBH⟩ := hlang B.2
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hBHs : B = Hs⁻¹ * Matrix.SpecialLinearGroup.map Fr Hs := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, hσ, coe_inv_eq_nonsing_inv]
    change (Matrix.SpecialLinearGroup.toGL B : Matrix (Fin n) (Fin n) Ω) = _
    rw [hBH, Matrix.coe_units_inv])
  have hΦH : ∀ X, Φ X = Hs⁻¹ * Matrix.SpecialLinearGroup.map Fr (Hs * X * Hs⁻¹) * Hs := fun X => by
    rw [hΦB, hBHs, map_mul, map_mul, map_inv]
    group
  have hσfix : ∀ W : SL(n, Ω), Matrix.SpecialLinearGroup.map Fr W = W ↔
      ∃ Y : SL(n, k), Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y = W := by
    intro W
    rw [exists_map_algebraMap_eq_iff hℓ hf hk W, ← hσ]
    constructor
    · intro h
      have := congrArg (fun Z : SL(n, Ω) => (Z : Matrix (Fin n) (Fin n) Ω)) h
      simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this
    · intro h
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, h]
  have hfix : ∀ X : SL(n, Ω), X ∈ Φ.eqLocus (MonoidHom.id _) ↔
      ∃ Y : SL(n, k), X = Hs⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * Hs⁻¹⁻¹ := by
    intro X
    rw [hmemΦ, hΦH, inv_inv]
    constructor
    · intro h
      have hW : Matrix.SpecialLinearGroup.map Fr (Hs * X * Hs⁻¹) = Hs * X * Hs⁻¹ := by
        calc Matrix.SpecialLinearGroup.map Fr (Hs * X * Hs⁻¹) =
            Hs * (Hs⁻¹ * Matrix.SpecialLinearGroup.map Fr (Hs * X * Hs⁻¹) * Hs) * Hs⁻¹ := by group
          _ = Hs * X * Hs⁻¹ := by rw [h]
      obtain ⟨Y, hY⟩ := (hσfix _).mp hW
      refine ⟨Y, ?_⟩
      rw [hY]
      group
    · rintro ⟨Y, rfl⟩
      have hW : Hs * (Hs⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * Hs) * Hs⁻¹ =
          Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y := by group
      rw [hW, (hσfix _).mpr ⟨Y, rfl⟩]
  let ι : SL(n, k) →* SL(n, Ω) := Matrix.SpecialLinearGroup.map (algebraMap k Ω)
  have hι : Function.Injective ι := specialLinearGroup_map_injective (algebraMap k Ω).injective
  let θ : SL(n, k) →* SL(n, Ω) := (MulAut.conj Hs⁻¹).toMonoidHom.comp ι
  have hθmem : ∀ Y, θ Y ∈ Φ.eqLocus (MonoidHom.id _) := fun Y => (hfix _).mpr ⟨Y, rfl⟩
  let e : SL(n, k) ≃* Φ.eqLocus (MonoidHom.id _) := MulEquiv.ofBijective (θ.codRestrict _ hθmem)
    ⟨fun Y Z h => hι ((MulAut.conj Hs⁻¹).injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨Y, hY⟩ := (hfix x).mp x.2
      exact ⟨Y, Subtype.ext hY.symm⟩⟩
  exact ⟨Hs⁻¹, e, fun Y => rfl⟩

theorem isQuasisimple_eqLocus_conjSLn_frobenius_split {k' : Type} [Field k'] [Finite k']
    [Algebra k' Ω] [IsAlgClosure k' Ω] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hq : n ≠ 2 ∨ 4 ≤ ℓ ^ f) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f) (A : GL (Fin n) Ω) :
    Finite (((conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr)).eqLocus (MonoidHom.id _)) ∧
      CFSG.IsQuasisimple
        (((conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr)).eqLocus (MonoidHom.id _)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hKcl, hKcard, -⟩ := 
    exists_isAlgClosure_powFixedSubfield (ℓ := ℓ) (k := k') (Ω := Ω) hf
  have := hKcl
  obtain ⟨-, e, -⟩ := eqLocus_conjSLn_frobenius_split (k := K) hℓ hf hKcard (by omega) Fr hFr A
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; exact (pow_pos hℓ.pos f).ne')
  have hQ : CFSG.IsQuasisimple SL(n, K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple n K hn
      (hq.imp_right fun h => by omega) (hq.imp_right fun h => by omega)
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e hQ⟩

end Split

section Unitary

variable {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {n : ℕ}

theorem eqLocus_conjSLn_frobenius_unitary_canonical (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (hn : 1 ≤ n) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    (A : GL (Fin n) Ω) :
    ∃ F : Subfield Ω, Nat.card F = (ℓ ^ f) ^ 2 ∧
      (∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧ ∃ (H : SL(n, Ω)) (e : StatedSU n (ℓ ^ f) F ≃*
        ((conjSLn A).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr))).eqLocus
          (MonoidHom.id _)),
      ∀ Y, ((e Y : _) : SL(n, Ω)) = H * statedSUToSL F n (ℓ ^ f) Y * H⁻¹ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hσ : ⇑Fr = (· ^ ℓ ^ f) := funext hFr
  set Φ : SL(n, Ω) →* SL(n, Ω) :=
    (conjSLn A).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr)) with hΦdef
  have hmemΦ : ∀ X, X ∈ Φ.eqLocus (MonoidHom.id _) ↔ Φ X = X := fun _ => Iff.rfl
  have hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) := fun X => by
    change (A : Matrix (Fin n) (Fin n) Ω) *
        (↑(Matrix.SpecialLinearGroup.map Fr X)⁻¹ : Matrix (Fin n) (Fin n) Ω)ᵀ *
          (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) = _
    rw [coe_inv_eq_nonsing_inv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      hσ]
  obtain ⟨H, hHdet, -, hset⟩ :=
    matrix_graph_frobenius_unitary_descent hℓ hf hk hn A
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  have hfix : ∀ X : SL(n, Ω), X ∈ Φ.eqLocus (MonoidHom.id _) ↔ ∃ Y ∈ unitarySet (ℓ ^ f) n,
      Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL Hs * Y * (Matrix.SpecialLinearGroup.toGL Hs)⁻¹ := by
    intro X
    have hX := Set.ext_iff.mp hset (Matrix.SpecialLinearGroup.toGL X)
    rw [hmemΦ, hHs]
    constructor
    · intro h
      obtain ⟨Y, hY, hXY⟩ := hX.mp ⟨X.2, by
        show (A : Matrix (Fin n) (Fin n) Ω) *
            (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
              (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) = (X : Matrix (Fin n) (Fin n) Ω)
        rw [← hA' X, h]⟩
      exact ⟨Y, hY, hXY.symm⟩
    · rintro ⟨Y, hY, hXY⟩
      have h := (hX.mpr ⟨Y, hY, hXY.symm⟩).2
      apply Subtype.ext
      rw [hA' X]
      exact h
  set F : Subfield Ω := (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : Ω, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  let Ψ : StatedSU n (ℓ ^ f) F →* SL(n, Ω) := statedSUToSL F n (ℓ ^ f)
  let θ : StatedSU n (ℓ ^ f) F →* SL(n, Ω) := (MulAut.conj Hs).toMonoidHom.comp Ψ
  have hθ : ∀ Y, θ Y = Hs * Ψ Y * Hs⁻¹ := fun Y => rfl
  have hθmem : ∀ Y, θ Y ∈ Φ.eqLocus (MonoidHom.id _) := by
    intro Y
    rw [hfix, hθ]
    refine ⟨Matrix.SpecialLinearGroup.toGL (Ψ Y),
      (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hθsurj : ∀ X ∈ Φ.eqLocus (MonoidHom.id _), ∃ Y, θ Y = X := by
    intro X hX
    obtain ⟨Y', hY', hXY⟩ := (hfix X).mp hX
    have hW : Matrix.SpecialLinearGroup.toGL (Hs⁻¹ * X * Hs) = Y' := by
      rw [map_mul, map_mul, map_inv, hXY]
      group
    obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mpr (hW ▸ hY')
    refine ⟨Y, ?_⟩
    rw [hθ, show Ψ Y = Hs⁻¹ * X * Hs from hY]
    group
  let e : StatedSU n (ℓ ^ f) F ≃* Φ.eqLocus (MonoidHom.id _) :=
    MulEquiv.ofBijective (θ.codRestrict _ hθmem)
      ⟨fun Y Z h => statedSUToSL_injective F n (ℓ ^ f)
        ((MulAut.conj Hs).injective (congrArg Subtype.val h)), fun X => by
          obtain ⟨Y, hY⟩ := hθsurj X X.2
          exact ⟨Y, Subtype.ext hY⟩⟩
  exact ⟨F, hFcard, hF, Hs, e, fun Y => rfl⟩

theorem eqLocus_conjSLn_frobenius_unitary (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (hn : 1 ≤ n) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    (A : GL (Fin n) Ω) :
    ∃ F : Subfield Ω, Nat.card F = (ℓ ^ f) ^ 2 ∧ ∃ (H : SL(n, Ω)) (e : StatedSU n (ℓ ^ f) F ≃*
        ((conjSLn A).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr))).eqLocus
          (MonoidHom.id _)),
      ∀ Y, ((e Y : _) : SL(n, Ω)) = H * statedSUToSL F n (ℓ ^ f) Y * H⁻¹ := by
  obtain ⟨F, hFcard, -, H, e, he⟩ :=
    eqLocus_conjSLn_frobenius_unitary_canonical hℓ hf hk hn Fr hFr A
  exact ⟨F, hFcard, H, e, he⟩

theorem isQuasisimple_eqLocus_conjSLn_frobenius_unitary {k' : Type} [Field k'] [Finite k']
    [Algebra k' Ω] [IsAlgClosure k' Ω] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hnq : (n, ℓ ^ f) ≠ (3, 2)) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    (A : GL (Fin n) Ω) :
    Finite (((conjSLn A).comp
        (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr))).eqLocus (MonoidHom.id _)) ∧
      CFSG.IsQuasisimple (((conjSLn A).comp
        (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr))).eqLocus (MonoidHom.id _)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hKcl, hKcard, -⟩ := 
    exists_isAlgClosure_powFixedSubfield (ℓ := ℓ) (k := k') (Ω := Ω) hf
  have := hKcl
  obtain ⟨F, hFcard, -, e, -⟩ :=
    eqLocus_conjSLn_frobenius_unitary (k := K) hℓ hf hKcard (by omega) Fr hFr A
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  obtain ⟨hQ, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hn hnq)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ f hFcard n hn hnq)
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e hQ⟩

end Unitary

section RankOne

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

private theorem sl2Diag_inv_eq (s : Kˣ) : (sl2Diag K s)⁻¹ = sl2Diag K s⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sl2Diag_mul_apply_zero_zero (s : Kˣ) (N : SL(2, K)) :
    ((sl2Diag K s * N : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (s : K) * (N : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl2Diag_conj_coe (s : Kˣ) (M : SL(2, K)) :
    ((sl2Diag K s * M * (sl2Diag K s)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![(M : Matrix (Fin 2) (Fin 2) K) 0 0, (s : K) ^ 2 * (M : Matrix (Fin 2) (Fin 2) K) 0 1;
        ((s : K)⁻¹) ^ 2 * (M : Matrix (Fin 2) (Fin 2) K) 1 0,
        (M : Matrix (Fin 2) (Fin 2) K) 1 1] := by
  rw [sl2Diag_inv_eq]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

private theorem exists_pow_eq_primitiveRoot_seven [IsAlgClosed K] [CharP K 2] {q : ℕ}
    (hq : q ≠ 0) : ∃ (ω : Kˣ) (ζ : K), IsPrimitiveRoot ζ 7 ∧ (ω : K) ^ q = ζ := by
  have : NeZero ((7 : ℕ) : K) := ⟨by rw [CharP.cast_eq_mod K 2 7]; norm_num⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 7
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_pow_nat_eq ζ (Nat.pos_of_ne_zero hq)
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow hq] at hω
    exact hζ.ne_zero (by norm_num) hω.symm
  exact ⟨Units.mk0 ω hω0, ζ, hζ, hω⟩

private theorem exists_sl2Upper_of_sl2Diag [IsAlgClosed K] [CharP K 2] {q : ℕ}
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(2, K) →* SL(2, K))
    (hT : ∀ t : Kˣ, τ (sl2Diag K t) = sl2Diag K (t ^ q)) :
    ∃ b : K, ∀ c, τ (sl2Upper K c) = sl2Upper K (b * c ^ q) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Y : K → SL(2, K) := fun c => τ (sl2Upper K c) with hYdef
  have hYadd : ∀ c d, Y (c + d) = Y c * Y d := fun c d => by
    simp only [hYdef, sl2Upper_add, map_mul]
  have hY0 : Y 0 = 1 := by simp only [hYdef, sl2Upper_zero, map_one]
  have hYt : ∀ (t : Kˣ) (c : K), Y ((t : K) ^ 2 * c) =
      sl2Diag K (t ^ q) * Y c * (sl2Diag K (t ^ q))⁻¹ := fun t c => by
    have h' : sl2Upper K ((t : K) ^ 2 * c) = sl2Diag K t * sl2Upper K c * (sl2Diag K t)⁻¹ := by
      rw [sl2Diag_mul_upper, mul_inv_cancel_right]
    simp only [hYdef, h', map_mul, map_inv, hT]
  set M : Matrix (Fin 2) (Fin 2) K := ((Y 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) with hM
  have hYm : ∀ t : Kˣ, ((Y ((t : K) ^ 2) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![M 0 0, ((t : K) ^ q) ^ 2 * M 0 1; (((t : K) ^ q)⁻¹) ^ 2 * M 1 0, M 1 1] := fun t => by
    have h := hYt t 1
    rw [mul_one] at h
    rw [h, sl2Diag_conj_coe, Units.val_pow_eq_pow_val]
  obtain ⟨ω, ζ, hζ, hωζ⟩ := exists_pow_eq_primitiveRoot_seven (K := K) hq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hω1 : (ω : K) + 1 ≠ 0 := by
    intro h
    apply hζ1
    have hω : (ω : K) = 1 := by linear_combination h - h2
    rw [← hωζ, hω, one_pow]
  set ω₁ : Kˣ := Units.mk0 ((ω : K) + 1) hω1 with hω₁
  have hω₁q : (ω₁ : K) ^ q = ζ + 1 := by
    rw [hω₁, Units.val_mk0, ← hFr, map_add, map_one, hFr, hωζ]
  have hsq : (ω₁ : K) ^ 2 = (ω : K) ^ 2 + 1 := by
    rw [hω₁, Units.val_mk0]
    linear_combination (ω : K) * h2
  have hYω : Y ((ω₁ : K) ^ 2) = Y ((ω : K) ^ 2) * Y 1 := by rw [hsq, hYadd]
  have hYω' : Y ((ω₁ : K) ^ 2) = Y 1 * Y ((ω : K) ^ 2) := by rw [hsq, add_comm, hYadd]
  have hY11 : Y 1 * Y 1 = 1 := by rw [← hYadd, one_add_one_eq_two, h2, hY0]
  have e1 := congrArg (fun Z : SL(2, K) => (Z : Matrix (Fin 2) (Fin 2) K) 0 0) hYω
  have e2 := congrArg (fun Z : SL(2, K) => (Z : Matrix (Fin 2) (Fin 2) K) 0 0) hYω'
  have e3 := congrArg (fun Z : SL(2, K) => (Z : Matrix (Fin 2) (Fin 2) K) 1 0) hYω
  have e4 := congrArg (fun Z : SL(2, K) => (Z : Matrix (Fin 2) (Fin 2) K) 0 0) hY11
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hYm, hωζ,
    hω₁q, ← hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq] at e1 e2 e3 e4
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hM]
    exact (Y 1).2
  have hζ4 : ζ ^ 4 ≠ 1 := fun h => by
    have := hζ.dvd_of_pow_eq_one 4 h
    norm_num at this
  have hbe : M 0 1 * M 1 0 = 0 := by
    have hsub : (ζ ^ 2 - (ζ⁻¹) ^ 2) * (M 0 1 * M 1 0) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.mp hsub with h | h
    · exfalso
      apply hζ4
      have hζinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
      linear_combination ζ ^ 2 * h + (ζ * ζ⁻¹ + 1) * hζinv
    · exact h
  have ha : M 0 0 = 1 := by linear_combination e1 + e4 + (ζ ^ 2 - 1) * hbe
  have hd : M 1 1 = 1 := by linear_combination hdet + hbe - M 1 1 * ha
  have hζ3 : ζ ^ 2 + ζ + 1 ≠ 0 := fun h => by
    have h3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * h
    have := hζ.dvd_of_pow_eq_one 3 h3
    norm_num at this
  have hζ10 : ζ + 1 ≠ 0 := fun h => hζ1 (by linear_combination h - h2)
  have he : M 1 0 = 0 := by
    have hu : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
    have hu₁ : (ζ + 1) * (ζ + 1)⁻¹ = 1 := mul_inv_cancel₀ hζ10
    have e3' : ((ζ + 1)⁻¹) ^ 2 * M 1 0 = (ζ⁻¹) ^ 2 * M 1 0 + M 1 0 := by
      linear_combination e3 + (ζ⁻¹) ^ 2 * M 1 0 * ha + M 1 0 * hd
    have key : M 1 0 * (ζ ^ 2 + ζ + 1) ^ 2 = 0 := by
      linear_combination (-(ζ ^ 2 * (ζ + 1) ^ 2)) * e3' +
        ζ ^ 2 * M 1 0 * ((ζ + 1) * (ζ + 1)⁻¹ - 1 + 2) * hu₁ -
        (ζ + 1) ^ 2 * M 1 0 * (ζ * ζ⁻¹ - 1 + 2) * hu + ζ ^ 2 * M 1 0 * h2
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hζ3
  have hY1 : Y 1 = sl2Upper K (M 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hM, ha, hd, he]
  refine ⟨M 0 1, fun c => ?_⟩
  change Y c = _
  by_cases hc : c = 0
  · rw [hc, zero_pow hq, mul_zero, sl2Upper_zero, hY0]
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c (by norm_num : 0 < 2)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at ht
      exact hc ht.symm
    have h := hYt (Units.mk0 t ht0) 1
    rw [Units.val_mk0, ht, mul_one] at h
    rw [h, hY1, sl2Diag_mul_upper, mul_inv_cancel_right, Units.val_pow_eq_pow_val, Units.val_mk0,
      ← ht]
    congr 1
    ring

private theorem sl2_root_params_of_sl2Diag [IsAlgClosed K] [CharP K 2] {q : ℕ}
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(2, K) →* SL(2, K))
    (hT : ∀ t : Kˣ, τ (sl2Diag K t) = sl2Diag K (t ^ q)) :
    ∃ b : K, b ≠ 0 ∧ (∀ c, τ (sl2Upper K c) = sl2Upper K (b * c ^ q)) ∧
      ∀ c, τ (sl2Lower K c) = sl2Lower K (b⁻¹ * c ^ q) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set W : SL(2, K) := sl2Weyl K 1 with hWdef
  have hWW : W * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hWdef, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  have hWinv : W⁻¹ = W := inv_eq_of_mul_eq_one_right hWW
  have hWD : ∀ t : Kˣ, W * sl2Diag K t * W = sl2Diag K t⁻¹ := fun t => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hWdef, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  have hWU : ∀ c : K, W * sl2Upper K c * W = sl2Lower K c := fun c => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hWdef, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  obtain ⟨b, hb⟩ := exists_sl2Upper_of_sl2Diag Fr hFr τ hT
  let τ' : SL(2, K) →* SL(2, K) :=
    (MulAut.conj W).toMonoidHom.comp (τ.comp (MulAut.conj W).toMonoidHom)
  have hτ' : ∀ A, τ' A = W * τ (W * A * W⁻¹) * W⁻¹ := fun A => rfl
  have hT' : ∀ t : Kˣ, τ' (sl2Diag K t) = sl2Diag K (t ^ q) := fun t => by
    rw [hτ', hWinv, hWD, hT, hWD, inv_pow, inv_inv]
  obtain ⟨b', hb'⟩ := exists_sl2Upper_of_sl2Diag Fr hFr τ' hT'
  have hWWx : ∀ x : SL(2, K), W * (W * x * W) * W = x := fun x => by
    rw [show W * (W * x * W) * W = (W * W) * x * (W * W) by group, hWW, one_mul, mul_one]
  have hlow : ∀ c, τ (sl2Lower K c) = sl2Lower K (b' * c ^ q) := fun c => by
    have h := hb' c
    rw [hτ', hWinv, hWU] at h
    rw [← hWWx (τ (sl2Lower K c)), h, hWU]
  obtain ⟨ω, ζ, hζ, hωζ⟩ := exists_pow_eq_primitiveRoot_seven (K := K) hq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hrel : sl2Upper K ω * sl2Lower K (-((ω⁻¹ : Kˣ) : K)) * sl2Upper K ω =
      sl2Diag K ω * W := by
    rw [← sl2Weyl_eq, hWdef, sl2Weyl_eq_diag_mul ω 1, inv_one, mul_one]
  have hW1 : W = sl2Upper K 1 * sl2Lower K (-1) * sl2Upper K 1 := by
    rw [hWdef, sl2Weyl_eq, inv_one, Units.val_one]
  have hτrel := congrArg τ hrel
  simp only [map_mul] at hτrel
  rw [hb, hlow, hT, hW1] at hτrel
  simp only [map_mul] at hτrel
  rw [hb, hlow] at hτrel
  have h00 := congrArg (fun Z : SL(2, K) => (Z : Matrix (Fin 2) (Fin 2) K) 0 0) hτrel
  rw [coe_upper_lower_upper_zero_zero, sl2Diag_mul_apply_zero_zero,
    coe_upper_lower_upper_zero_zero] at h00
  have hneg1 : (-1 : K) ^ q = -1 := by rw [← hFr, map_neg, map_one]
  have hinvq : (-((ω⁻¹ : Kˣ) : K)) ^ q = -ζ⁻¹ := by
    rw [← hFr, map_neg, Units.val_inv_eq_inv_val, map_inv₀, hFr, hωζ]
  rw [Units.val_pow_eq_pow_val, hωζ, hneg1, hinvq, one_pow] at h00
  have hζinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hbb : b * b' = 1 := by
    have h' : (1 - b * b') * (1 - ζ) = 0 := by linear_combination h00 + b * b' * hζinv
    rcases mul_eq_zero.mp h' with h | h
    · linear_combination -h
    · exact absurd (by linear_combination -h) hζ1
  have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbb
  have hb' : b' = b⁻¹ := eq_inv_of_mul_eq_one_right hbb
  exact ⟨b, hb0, hb, fun c => by rw [hlow, hb']⟩

private theorem eq_conjSLn_comp_map_of_sl2Diag_pow [IsAlgClosed K] [CharP K 2] {q : ℕ}
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(2, K) →* SL(2, K))
    (hT : ∀ t : Kˣ, τ (sl2Diag K t) = sl2Diag K (t ^ q)) :
    ∃ X : GL (Fin 2) K, τ = (conjSLn X).comp (Matrix.SpecialLinearGroup.map Fr) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  obtain ⟨b, hb0, hb, hlow⟩ := sl2_root_params_of_sl2Diag Fr hFr τ hT
  let X : GL (Fin 2) K := ⟨!![b, 0; 0, 1], !![b⁻¹, 0; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp [hb0],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp [hb0]⟩
  refine ⟨X, MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := K)) ?_⟩
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · rw [hb c]
    apply Subtype.ext
    have hmap : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map Fr = !![1, c ^ q; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hFr, hq]
    change !![1, b * c ^ q; 0, 1] =
      !![b, 0; 0, 1] * (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map Fr * !![b⁻¹, 0; 0, 1]
    rw [hmap, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0]
  · rw [hlow c]
    apply Subtype.ext
    have hmap : (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K).map Fr = !![1, 0; c ^ q, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hFr, hq]
    change !![1, 0; b⁻¹ * c ^ q, 1] =
      !![b, 0; 0, 1] * (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K).map Fr * !![b⁻¹, 0; 0, 1]
    rw [hmap, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0, mul_comm]

theorem eq_conjSLn_comp_map_of_sl2Diag [IsAlgClosed K] [CharP K 2] {q : ℕ} (Fr : K →+* K)
    (hFr : ∀ c, Fr c = c ^ q) (τ : SL(2, K) →* SL(2, K))
    (hT : (∀ t : Kˣ, τ (sl2Diag K t) = sl2Diag K (t ^ q)) ∨
      ∀ t : Kˣ, τ (sl2Diag K t) = (sl2Diag K (t ^ q))⁻¹) :
    ∃ X : GL (Fin 2) K, τ = (conjSLn X).comp (Matrix.SpecialLinearGroup.map Fr) := by
  rcases hT with hT | hT
  · exact eq_conjSLn_comp_map_of_sl2Diag_pow Fr hFr τ hT
  · set W : SL(2, K) := sl2Weyl K 1 with hWdef
    have hWW : W * W = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hWdef, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
    have hWinv : W⁻¹ = W := inv_eq_of_mul_eq_one_right hWW
    have hWD : ∀ t : Kˣ, W * sl2Diag K t * W = sl2Diag K t⁻¹ := fun t => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hWdef, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
    obtain ⟨X, hX⟩ := eq_conjSLn_comp_map_of_sl2Diag_pow Fr hFr
      ((MulAut.conj W).toMonoidHom.comp τ) (fun t => by
        change W * τ (sl2Diag K t) * W⁻¹ = _
        rw [hT, hWinv, sl2Diag_inv_eq, hWD, inv_inv])
    refine ⟨Matrix.SpecialLinearGroup.toGL W * X, MonoidHom.ext fun A => ?_⟩
    have h := congrArg (fun φ : SL(2, K) →* SL(2, K) => φ A) hX
    change W * τ A * W⁻¹ = conjSLn X (Matrix.SpecialLinearGroup.map Fr A) at h
    have hA : τ A = W * conjSLn X (Matrix.SpecialLinearGroup.map Fr A) * W := by
      rw [← h, hWinv, show W * (W * τ A * W) * W = (W * W) * τ A * (W * W) by group, hWW,
        one_mul, mul_one]
    rw [hA]
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_mul, coe_conjSLn,
      Units.val_mul, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
      hWinv, Matrix.mul_assoc]

end RankOne

section RankN

open CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction.LinearPilot

variable {K : Type} [Field K] {n : ℕ}

private theorem sl2Upper_eq_transvection (c : K) :
    sl2Upper K c = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

private theorem sl2Lower_eq_transvection (c : K) :
    sl2Lower K c = Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

private def diagSLn (d : Fin n → Kˣ) (hd : ∏ i, d i = 1) : SL(n, K) :=
  ⟨Matrix.diagonal fun i => (d i : K), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hd, Units.val_one]⟩

private theorem coe_diagSLn (d : Fin n → Kˣ) (hd : ∏ i, d i = 1) :
    ((diagSLn d hd : SL(n, K)) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (d i : K) :=
  rfl

private theorem transvection_mem_blockSpecialLinear_of_isDiag [IsAlgClosed K] [CharP K 2]
    {q : ℕ} (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(n, K) →* SL(n, K))
    (hT : ∀ D : SL(n, K), (D : Matrix (Fin n) (Fin n) K).IsDiag →
      τ D = Matrix.SpecialLinearGroup.map Fr D)
    {k l : Fin n} (hkl : k ≠ l) (c : K) :
    τ (Matrix.SpecialLinearGroup.transvection hkl c) ∈ blockSpecialLinear {k, l} := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ω, ζ, hζ, hωζ⟩ := exists_pow_eq_primitiveRoot_seven (K := K) hq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt two_ne_zero (by norm_num)
  have hζ3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt three_ne_zero (by norm_num)
  have hωinv : (((ω⁻¹ : Kˣ) : K)) ^ q = ζ⁻¹ := by
    rw [← hFr, Units.val_inv_eq_inv_val, map_inv₀, hFr, hωζ]
  set Y := τ (Matrix.SpecialLinearGroup.transvection hkl c) with hYdef
  have hYY : Y * Y = 1 := by
    rw [hYdef, ← map_mul, ← Matrix.SpecialLinearGroup.transvection_add, ← two_mul, h2, zero_mul]
    rw [show Matrix.SpecialLinearGroup.transvection hkl (0 : K) = 1 by
      ext i j
      simp]
    exact map_one τ
  have hoff : ∀ m, m ≠ k → m ≠ l → ∀ j, j ≠ m →
      (Y : Matrix (Fin n) (Fin n) K) m j = 0 ∧ (Y : Matrix (Fin n) (Fin n) K) j m = 0 := by
    intro m hmk hml j hjm
    set d : Fin n → Kˣ := Pi.mulSingle k ω * Pi.mulSingle l ω * Pi.mulSingle m (ω⁻¹ ^ 2)
      with hd
    have hdprod : ∏ i, d i = 1 := by
      simp only [hd, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
        Finset.mem_univ, if_true]
      group
    have hdk : d k = ω := by simp [hd, hkl, hmk.symm]
    have hdl : d l = ω := by simp [hd, hkl.symm, hml.symm]
    have hdm : d m = ω⁻¹ ^ 2 := by simp [hd, hmk, hml]
    have hdj : (d j : K) ^ q = ζ ∨ (d j : K) ^ q = 1 := by
      by_cases hjk : j = k
      · left; rw [hjk, hdk, hωζ]
      · by_cases hjl : j = l
        · left; rw [hjl, hdl, hωζ]
        · right
          have : d j = 1 := by simp [hd, hjk, hjl, hjm]
          rw [this, Units.val_one, one_pow]
    have hdmq : (d m : K) ^ q = (ζ⁻¹) ^ 2 := by
      rw [hdm, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hωinv]
    have hne : (d m : K) ^ q ≠ (d j : K) ^ q := by
      rw [hdmq]
      intro h
      rcases hdj with h' | h'
      · rw [h'] at h
        apply hζ3
        field_simp at h
        linear_combination -h
      · rw [h'] at h
        apply hζ2
        field_simp at h
        linear_combination -h
    set D := diagSLn d hdprod with hD
    have hcomm : D * Matrix.SpecialLinearGroup.transvection hkl c =
        Matrix.SpecialLinearGroup.transvection hkl c * D := by
      ext r s
      simp only [Matrix.SpecialLinearGroup.coe_mul, hD, coe_diagSLn,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases hrs : r = s
      · subst hrs
        have : ¬ (k = r ∧ l = r) := fun h => hkl (h.1.trans h.2.symm)
        simp [this]
      · by_cases h : k = r ∧ l = s
        · obtain ⟨rfl, rfl⟩ := h
          simp [hrs, hdk, hdl, mul_comm]
        · simp [hrs, h]
    have hτD : τ D = Matrix.SpecialLinearGroup.map Fr D := hT D (Matrix.isDiag_diagonal _)
    have hcommY : Matrix.SpecialLinearGroup.map Fr D * Y = Y * Matrix.SpecialLinearGroup.map Fr D := by
      rw [← hτD, hYdef, ← map_mul, hcomm, map_mul]
    have hcoe : ((Matrix.SpecialLinearGroup.map Fr D : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        Matrix.diagonal fun i => (d i : K) ^ q := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hD, coe_diagSLn]
      ext r s
      simp only [Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [hFr, hq]
    have hent : ∀ r s, ((d r : K) ^ q - (d s : K) ^ q) * (Y : Matrix (Fin n) (Fin n) K) r s = 0 := by
      intro r s
      have h := congrArg (fun Z : SL(n, K) => (Z : Matrix (Fin n) (Fin n) K) r s) hcommY
      simp only [Matrix.SpecialLinearGroup.coe_mul, hcoe, Matrix.diagonal_mul,
        Matrix.mul_diagonal] at h
      linear_combination h
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp (hent m j) with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    · rcases mul_eq_zero.mp (hent j m) with h | h
      · exact absurd (sub_eq_zero.mp h).symm hne
      · exact h
  have hdiag : ∀ m, m ≠ k → m ≠ l → (Y : Matrix (Fin n) (Fin n) K) m m = 1 := by
    intro m hmk hml
    have h := congrArg (fun Z : SL(n, K) => (Z : Matrix (Fin n) (Fin n) K) m m) hYY
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, Matrix.mul_apply] at h
    rw [Finset.sum_eq_single m (fun j _ hjm => by rw [(hoff m hmk hml j hjm).1, zero_mul])
      (fun h' => absurd (Finset.mem_univ m) h')] at h
    have hsq : ((Y : Matrix (Fin n) (Fin n) K) m m - 1) ^ 2 = 0 := by
      linear_combination h + (1 - (Y : Matrix (Fin n) (Fin n) K) m m) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  intro i j hij
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hij
  by_cases hij' : i = j
  · subst hij'
    have hi : i ≠ k ∧ i ≠ l := hij.elim id id
    rw [hdiag i hi.1 hi.2, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hij']
    rcases hij with ⟨hik, hil⟩ | ⟨hjk, hjl⟩
    · exact (hoff i hik hil j (Ne.symm hij')).1
    · exact (hoff j hjk hjl i hij').2

private theorem transvection_params_of_isDiag [IsAlgClosed K] [CharP K 2] {q : ℕ}
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(n, K) →* SL(n, K))
    (hT : ∀ D : SL(n, K), (D : Matrix (Fin n) (Fin n) K).IsDiag →
      τ D = Matrix.SpecialLinearGroup.map Fr D)
    {k l : Fin n} (hkl : k ≠ l) :
    ∃ b : K, b ≠ 0 ∧ ∀ c, τ (Matrix.SpecialLinearGroup.transvection hkl c) =
      Matrix.SpecialLinearGroup.transvection hkl (b * c ^ q) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  set φ : SL(2, K) →* SL(n, K) := pairEmbed hkl with hφ
  have hφU : ∀ c, φ (sl2Upper K c) = Matrix.SpecialLinearGroup.transvection hkl c := fun c => by
    rw [hφ, sl2Upper_eq_transvection, pairEmbed_transvection_zero_one]
  have hφL : ∀ c, φ (sl2Lower K c) = Matrix.SpecialLinearGroup.transvection hkl.symm c :=
    fun c => by rw [hφ, sl2Lower_eq_transvection, pairEmbed_transvection_one_zero]
  have hrange : ∀ A, τ (φ A) ∈ φ.range := by
    intro A
    rw [hφ, range_pairEmbed]
    have hA : A ∈ Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top A
    induction hA using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [hφU]
        exact transvection_mem_blockSpecialLinear_of_isDiag Fr hFr τ hT hkl c
      · rw [hφL, Finset.pair_comm]
        exact transvection_mem_blockSpecialLinear_of_isDiag Fr hFr τ hT hkl.symm c
    | one => rw [map_one, map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv, map_inv]; exact Subgroup.inv_mem _ hx
  have hφinj : Function.Injective φ := pairEmbed_injective hkl
  let e₀ : SL(2, K) ≃* φ.range := MonoidHom.ofInjective hφinj
  let τ' : SL(2, K) →* SL(2, K) := e₀.symm.toMonoidHom.comp ((τ.comp φ).codRestrict φ.range hrange)
  have hφτ : ∀ A, φ (τ' A) = τ (φ A) := fun A =>
    (MonoidHom.ofInjective_apply hφinj (x := e₀.symm ⟨τ (φ A), hrange A⟩)).symm.trans
      (congrArg Subtype.val (e₀.apply_symm_apply ⟨τ (φ A), hrange A⟩))
  have hT' : ∀ t : Kˣ, τ' (sl2Diag K t) = sl2Diag K (t ^ q) := by
    intro t
    apply hφinj
    rw [hφτ]
    have hdiag : (φ (sl2Diag K t) : Matrix (Fin n) (Fin n) K).IsDiag := by
      intro i j hij
      rw [hφ, pairEmbed_apply]
      split_ifs <;> simp_all
    rw [hT _ hdiag]
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hφ,
      pairEmbed_apply, pairEmbed_apply]
    split_ifs <;> simp_all [Matrix.one_apply]
  obtain ⟨b, hb0, hb, -⟩ := sl2_root_params_of_sl2Diag Fr hFr τ' hT'
  refine ⟨b, hb0, fun c => ?_⟩
  rw [← hφU, ← hφτ, hb, hφU]

theorem eq_conjSLn_comp_map_of_isDiag [IsAlgClosed K] [CharP K 2] {q : ℕ} (hn : 3 ≤ n)
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(n, K) →* SL(n, K))
    (hT : ∀ D : SL(n, K), (D : Matrix (Fin n) (Fin n) K).IsDiag →
      τ D = Matrix.SpecialLinearGroup.map Fr D) :
    ∃ A : GL (Fin n) K, τ = (conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr) := by
  classical
  have hpar : ∀ i j : Fin n, ∃ b : Kˣ, ∀ (hij : i ≠ j) (t : K),
      ((τ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, K)) :
        Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j ((b : K) * Fr t) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨1, fun h => absurd hij h⟩
    · obtain ⟨b, hb0, hb⟩ := transvection_params_of_isDiag Fr hFr τ hT hij
      refine ⟨Units.mk0 b hb0, fun hij' t => ?_⟩
      rw [hb, Matrix.SpecialLinearGroup.transvection_coe, Units.val_mk0, hFr]
  choose b hb using hpar
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting hn Fr (1 : Equiv.Perm (Fin n)) τ b
    (fun i j hij t => by simpa using hb i j hij t)
  refine ⟨A, MonoidHom.ext fun X => Subtype.ext ?_⟩
  rw [hA X]
  rfl

private theorem conjSLn_inv_conjSLn (A : GL (Fin n) K) (X : SL(n, K)) :
    conjSLn A⁻¹ (conjSLn A X) = X := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

private theorem conjSLn_conjSLn (A B : GL (Fin n) K) (X : SL(n, K)) :
    conjSLn A (conjSLn B X) = conjSLn (A * B) X := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, coe_conjSLn, Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
  simp only [Matrix.mul_assoc]

private def invTransposeGL (A : GL (Fin n) K) : GL (Fin n) K :=
  ⟨(↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, (A : Matrix (Fin n) (Fin n) K)ᵀ,
    by rw [← Matrix.transpose_mul, A.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, A.inv_mul, Matrix.transpose_one]⟩

private theorem invTransposeSL_conjSLn (A : GL (Fin n) K) (X : SL(n, K)) :
    invTransposeSL (conjSLn A X) = conjSLn (invTransposeGL A) (invTransposeSL X) := by
  apply Subtype.ext
  rw [coe_invTransposeSL, ← map_inv, coe_conjSLn, coe_conjSLn, coe_invTransposeSL,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rfl

theorem eq_conjSLn_comp_map_of_torus [IsAlgClosed K] [CharP K 2] {q : ℕ} (hn : 3 ≤ n)
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(n, K) →* SL(n, K)) (A₀ : GL (Fin n) K)
    (hT : ∀ D : SL(n, K), (D : Matrix (Fin n) (Fin n) K).IsDiag →
      τ D = conjSLn A₀ (Matrix.SpecialLinearGroup.map Fr D)) :
    ∃ A : GL (Fin n) K, τ = (conjSLn A).comp (Matrix.SpecialLinearGroup.map Fr) := by
  obtain ⟨A₁, hA₁⟩ := eq_conjSLn_comp_map_of_isDiag hn Fr hFr ((conjSLn A₀⁻¹).comp τ)
    (fun D hD => by rw [MonoidHom.comp_apply, hT D hD, conjSLn_inv_conjSLn])
  refine ⟨A₀ * A₁, MonoidHom.ext fun X => ?_⟩
  have h := congrArg (fun φ : SL(n, K) →* SL(n, K) => φ X) hA₁
  simp only [MonoidHom.comp_apply] at h
  rw [MonoidHom.comp_apply, ← conjSLn_conjSLn, ← h, conjSLn_conjSLn, mul_inv_cancel]
  apply Subtype.ext
  rw [coe_conjSLn, Units.val_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_conjSLn_comp_invTranspose_of_torus [IsAlgClosed K] [CharP K 2] {q : ℕ} (hn : 3 ≤ n)
    (Fr : K →+* K) (hFr : ∀ c, Fr c = c ^ q) (τ : SL(n, K) →* SL(n, K)) (A₀ : GL (Fin n) K)
    (hT : ∀ D : SL(n, K), (D : Matrix (Fin n) (Fin n) K).IsDiag →
      τ D = conjSLn A₀ (invTransposeSL (Matrix.SpecialLinearGroup.map Fr D))) :
    ∃ A : GL (Fin n) K,
      τ = (conjSLn A).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr)) := by
  obtain ⟨A₁, hA₁⟩ := eq_conjSLn_comp_map_of_isDiag hn Fr hFr
    (invTransposeSL.comp ((conjSLn A₀⁻¹).comp τ))
    (fun D hD => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hT D hD, conjSLn_inv_conjSLn,
        invTransposeSL_invTransposeSL])
  refine ⟨A₀ * invTransposeGL A₁, MonoidHom.ext fun X => ?_⟩
  have h := congrArg (fun φ : SL(n, K) →* SL(n, K) => φ X) hA₁
  simp only [MonoidHom.comp_apply] at h
  have hX : τ X = conjSLn A₀ (invTransposeSL (invTransposeSL (conjSLn A₀⁻¹ (τ X)))) := by
    rw [invTransposeSL_invTransposeSL, conjSLn_conjSLn, mul_inv_cancel]
    apply Subtype.ext
    rw [coe_conjSLn, Units.val_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rw [hX, h, invTransposeSL_conjSLn, conjSLn_conjSLn]
  rfl

end RankN

end CFSG.RankThree.Classical2

end

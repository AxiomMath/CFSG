module

public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.RankThree.Classical2.GraphFrobeniusUnitaryDescent
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.Classical2

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section General

@[expose] def fixSubgroup {G : Type*} [Group G] (Φ : G ≃* G) : Subgroup G where
  carrier := {x | Φ x = x}
  mul_mem' {x y} hx hy := by
    change Φ (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one Φ
  inv_mem' {x} hx := by
    change Φ x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_fixSubgroup {G : Type*} [Group G] (Φ : G ≃* G) {x : G} :
    x ∈ fixSubgroup Φ ↔ Φ x = x :=
  Iff.rfl

theorem natCard_rootsOfUnity_eq_gcd {K : Type*} [Field K] [Finite K] (n : ℕ) :
    Nat.card (rootsOfUnity n K) = Nat.gcd (Nat.card K - 1) n := by
  have : rootsOfUnity n K = (powMonoidHom n : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [this, IsCyclic.card_powMonoidHom_ker, Nat.card_units]

theorem natCard_center_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv e,
    Subgroup.card_map_of_injective e.injective]

theorem symm_mem_center_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : H}
    (hx : x ∈ Subgroup.center H) : e.symm x ∈ Subgroup.center G := by
  rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv e.symm]
  exact ⟨x, hx, rfl⟩

theorem isSimpleGroup_of_center_eq_bot {G : Type*} [Group G]
    [IsSimpleGroup (G ⧸ Subgroup.center G)] (h : Subgroup.center G = ⊥) : IsSimpleGroup G :=
  ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm.isSimpleGroup

variable {n : ℕ}

theorem mem_center_of_coe_eq_scalar {R : Type*} [CommRing R] {S : Subgroup SL(n, R)} (x : S)
    {c : R} (hx : ((x : SL(n, R)) : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c) :
    x ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Subtype.ext
  change ((y : SL(n, R)) : Matrix (Fin n) (Fin n) R) * ((x : SL(n, R)) : Matrix (Fin n) (Fin n) R) =
    ((x : SL(n, R)) : Matrix (Fin n) (Fin n) R) * ((y : SL(n, R)) : Matrix (Fin n) (Fin n) R)
  rw [hx]
  exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq.symm

theorem coe_conj_eq_scalar {R : Type*} [CommRing R] (g Y : SL(n, R)) {c : R}
    (hY : (Y : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c) :
    ((g * Y * g⁻¹ : SL(n, R)) : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hY,
    ← (Matrix.scalar_commute c (fun r => Commute.all c r) (g : Matrix (Fin n) (Fin n) R)).eq,
    Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

theorem scalar_map {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) (c : R) :
    (scalar (Fin n) c).map ψ = scalar (Fin n) (ψ c) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero ψ)]

theorem isQuasisimple_specialLinearGroup {K : Type*} [Field K] (hn : 3 ≤ n) :
    CFSG.IsQuasisimple SL(n, K) := by
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hn
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega) (Or.inl hn)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(n, K) ⧸ Subgroup.center SL(n, K)) := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(n, K) ⧸ Subgroup.center SL(n, K)) this

end General

section Map

variable {n : ℕ}

theorem specialLinearGroup_map_injective {R S : Type*} [CommRing R] [CommRing S] {ψ : R →+* S}
    (hψ : Function.Injective ψ) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin n) ψ) := by
  intro X Y h
  ext i j
  have := congrArg (fun Z : SL(n, S) => (Z : Matrix (Fin n) (Fin n) S) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact hψ this

theorem exists_map_eq_of_forall_mem_range {R S : Type*} [CommRing R] [CommRing S] {ψ : R →+* S}
    (hψ : Function.Injective ψ) (X : SL(n, S))
    (hX : ∀ i j, (X : Matrix (Fin n) (Fin n) S) i j ∈ Set.range ψ) :
    ∃ Y : SL(n, R), Matrix.SpecialLinearGroup.map ψ Y = X := by
  choose Y hY using hX
  have hdet : (Matrix.of Y).det = 1 := by
    apply hψ
    rw [RingHom.map_det, map_one]
    have : ψ.mapMatrix (Matrix.of Y) = (X : Matrix (Fin n) (Fin n) S) := by
      ext i j
      exact hY i j
    rw [this, X.2]
  refine ⟨⟨Matrix.of Y, hdet⟩, ?_⟩
  ext i j
  exact hY i j

theorem exists_specialLinear_conj_eq {K : Type} [Field K] [IsAlgClosed K] (hn : 1 ≤ n)
    (A : GL (Fin n) K) : ∃ B : SL(n, K), ∀ Y : Matrix (Fin n) (Fin n) K,
      (B : Matrix (Fin n) (Fin n) K) * Y * (↑B⁻¹ : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * Y * (↑A⁻¹ : Matrix (Fin n) (Fin n) K) := by
  have hdet : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)).ne_zero
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq ((A : Matrix (Fin n) (Fin n) K).det)⁻¹
    (by omega : 0 < n)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hμ
    exact inv_ne_zero hdet hμ.symm
  have hBdet : (μ • (A : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hμ, inv_mul_cancel₀ hdet]
  set B : SL(n, K) := ⟨μ • (A : Matrix (Fin n) (Fin n) K), hBdet⟩ with hBdef
  have hBinv : (↑B⁻¹ : Matrix (Fin n) (Fin n) K) = μ⁻¹ • (↑A⁻¹ : Matrix (Fin n) (Fin n) K) := by
    rw [coe_inv_eq_nonsing_inv]
    refine Matrix.inv_eq_left_inv ?_
    change μ⁻¹ • (↑A⁻¹ : Matrix (Fin n) (Fin n) K) * (μ • (A : Matrix (Fin n) (Fin n) K)) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul, A.inv_mul]
  refine ⟨B, fun Y => ?_⟩
  rw [hBinv]
  change μ • (A : Matrix (Fin n) (Fin n) K) * Y * (μ⁻¹ • (↑A⁻¹ : Matrix (Fin n) (Fin n) K)) = _
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ0,
    one_smul]

end Map

section Split

variable {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {n : ℕ}

theorem mem_range_algebraMap_iff (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] [CharP k ℓ] (c : Ω) :
    c ∈ Set.range (algebraMap k Ω) ↔ c ^ ℓ ^ f = c := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hsub : Set.range (algebraMap k Ω) ⊆ {c : Ω | c ^ ℓ ^ f = c} := by
    rintro _ ⟨a, rfl⟩
    change (algebraMap k Ω a) ^ ℓ ^ f = algebraMap k Ω a
    rw [← map_pow, show ℓ ^ f = Fintype.card k by rw [← Nat.card_eq_fintype_card, hk],
      FiniteField.pow_card]
  have hcard : Nat.card {c : Ω | c ^ ℓ ^ f = c} = ℓ ^ f :=
    natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega)
  have hfin : Finite {c : Ω | c ^ ℓ ^ f = c} := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (pow_pos hℓ.pos f).ne')
  have hrange : Nat.card (Set.range (algebraMap k Ω)) = ℓ ^ f := by
    rw [Nat.card_range_of_injective (algebraMap k Ω).injective, hk]
  have heq : Set.range (algebraMap k Ω) = {c : Ω | c ^ ℓ ^ f = c} := by
    have := Fintype.ofFinite {c : Ω | c ^ ℓ ^ f = c}
    have : Fintype (Set.range (algebraMap k Ω)) :=
      Set.Finite.fintype ((Set.toFinite _).subset hsub)
    refine Set.eq_of_subset_of_card_le hsub ?_
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hrange]
  rw [heq]
  rfl

theorem exists_map_algebraMap_eq_iff (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] [CharP k ℓ] (X : SL(n, Ω)) :
    (∃ Y : SL(n, k), Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y = X) ↔
      (X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f) = X := by
  constructor
  · rintro ⟨Y, rfl⟩
    ext i j
    rw [Matrix.map_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (mem_range_algebraMap_iff hℓ hf hk _).mp ⟨_, rfl⟩
  · intro hX
    refine exists_map_eq_of_forall_mem_range (algebraMap k Ω).injective X fun i j => ?_
    rw [mem_range_algebraMap_iff hℓ hf hk]
    exact congrFun (congrFun hX i) j

theorem sln_root_permuting_frobenius_fixed_split (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (hn : 3 ≤ n) (π : Equiv.Perm (Fin n))
    (Φ : SL(n, Ω) ≃* SL(n, Ω)) (b : Fin n → Fin n → Ωˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
        1 + single (π i) (π j) ((b i j : Ω) * t ^ ℓ ^ f)) :
    (∃ A : GL (Fin n) Ω, ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f) *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω)) ∧
    (∃ H : SL(n, Ω), ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(n, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹) ∧
    Finite (fixSubgroup Φ) ∧ CFSG.IsQuasisimple (fixSubgroup Φ) ∧
    (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
      ∃ c : Ω, ((x : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c) ∧
    Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd n (ℓ ^ f - 1) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  have hσ' : ∀ c, σ c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hσ : ⇑σ = (· ^ ℓ ^ f) := funext hσ'
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting hn σ π Φ.toMonoidHom b
    (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσ'])
  have hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f) *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) := fun X => by
    have := hA X
    rwa [MulEquiv.coe_toMonoidHom, hσ] at this
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (by omega : 1 ≤ n) A
  have hΦB : ∀ X : SL(n, Ω), Φ X = B * Matrix.SpecialLinearGroup.map σ X * B⁻¹ := fun X =>
    Subtype.ext (by
      rw [hA' X, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hB, hσ])
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang hℓ hf hk (by omega : 1 ≤ n)
    (Matrix.SpecialLinearGroup.toGL B)
  obtain ⟨H, hHdet, hBH⟩ := hlang B.2
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hBHs : B = Hs⁻¹ * Matrix.SpecialLinearGroup.map σ Hs := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, hσ, coe_inv_eq_nonsing_inv]
    change (Matrix.SpecialLinearGroup.toGL B : Matrix (Fin n) (Fin n) Ω) = _
    rw [hBH, Matrix.coe_units_inv])
  have hΦH : ∀ X, Φ X = Hs⁻¹ * Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) * Hs := fun X => by
    rw [hΦB, hBHs, map_mul, map_mul, map_inv]
    group
  have hσfix : ∀ W : SL(n, Ω), Matrix.SpecialLinearGroup.map σ W = W ↔
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
  have hfix : ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(n, k), X = Hs⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * Hs⁻¹⁻¹ := by
    intro X
    rw [mem_fixSubgroup, hΦH, inv_inv]
    constructor
    · intro h
      have hW : Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) = Hs * X * Hs⁻¹ := by
        calc Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) =
            Hs * (Hs⁻¹ * Matrix.SpecialLinearGroup.map σ (Hs * X * Hs⁻¹) * Hs) * Hs⁻¹ := by group
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
  have hθmem : ∀ Y, θ Y ∈ fixSubgroup Φ := fun Y => (hfix _).mpr ⟨Y, rfl⟩
  let e : SL(n, k) ≃* fixSubgroup Φ := MulEquiv.ofBijective (θ.codRestrict _ hθmem)
    ⟨fun Y Z h => hι ((MulAut.conj Hs⁻¹).injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨Y, hY⟩ := (hfix x).mp x.2
      exact ⟨Y, Subtype.ext hY.symm⟩⟩
  have he : ∀ Y, ((e Y : fixSubgroup Φ) : SL(n, Ω)) = Hs⁻¹ * ι Y * Hs⁻¹⁻¹ := fun Y => rfl
  have hQ : CFSG.IsQuasisimple (fixSubgroup Φ) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e
      (isQuasisimple_specialLinearGroup hn)
  refine ⟨⟨A, hA'⟩, ⟨Hs⁻¹, hfix⟩, Finite.of_equiv _ e.toEquiv, hQ,
    fun x => ⟨fun hx => ?_, fun ⟨c, hc⟩ => mem_center_of_coe_eq_scalar x hc⟩, ?_⟩
  ·
    obtain ⟨r, -, hr⟩ :=
      Matrix.SpecialLinearGroup.mem_center_iff.mp (symm_mem_center_of_mulEquiv e hx)
    refine ⟨algebraMap k Ω r, ?_⟩
    rw [← e.apply_symm_apply x, he]
    refine coe_conj_eq_scalar _ _ ?_
    change ((Matrix.SpecialLinearGroup.map (algebraMap k Ω) (e.symm x) : SL(n, Ω)) :
      Matrix (Fin n) (Fin n) Ω) = _
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← hr, scalar_map]
  ·
    rw [← natCard_center_eq_of_mulEquiv e, Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by omega⟩ : Fin n)).toEquiv,
      Fintype.card_fin, natCard_rootsOfUnity_eq_gcd, hk, Nat.gcd_comm]

end Split

section Unitary

variable {Ω : Type} [Field Ω] {n : ℕ}

theorem statedSU_le_ker_det (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K ≤ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  (CFSG.Open.StatedAPI.statedSU_le_statedSL n q K).trans
    (CFSG.Open.StatedAPI.statedSL_eq_ker_det n K).le

@[expose] noncomputable def statedSUToSL (F : Subfield Ω) (n q : ℕ) :
    StatedSU n q F →* SL(n, Ω) :=
  (Matrix.SpecialLinearGroup.map F.subtype).comp
    (Matrix.SpecialLinearGroup.toGLKerEquiv.symm.toMonoidHom.comp
      (Subgroup.inclusion (statedSU_le_ker_det n q F)))

theorem coe_statedSUToSL (F : Subfield Ω) (n q : ℕ) (Y : StatedSU n q F) :
    ((statedSUToSL F n q Y : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map F.subtype :=
  rfl

theorem statedSUToSL_injective (F : Subfield Ω) (n q : ℕ) :
    Function.Injective (statedSUToSL F n q) := by
  intro Y Z h
  have h1 := congrArg (fun W : SL(n, Ω) => (W : Matrix (Fin n) (Fin n) Ω)) h
  simp only [coe_statedSUToSL] at h1
  exact Subtype.ext (Units.ext (Matrix.map_injective F.subtype.injective h1))

variable {ℓ f : ℕ}

theorem mem_range_statedSUToSL_iff (hℓ : ℓ.Prime) (F : Subfield Ω)
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) (hFcard : Nat.card F = (ℓ ^ f) ^ 2)
    (hn : 1 ≤ n) (Y : SL(n, Ω)) :
    Y ∈ (statedSUToSL F n (ℓ ^ f)).range ↔
      Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (ℓ ^ f) n := by
  obtain ⟨hset, -, -⟩ := CFSG.LinearGroups.unitary_scalar_kernel (K := F) hℓ hFcard hn
  have hmem : ∀ A : GL (Fin n) F, A ∈ StatedSU n (ℓ ^ f) F ↔
      (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
        ((A : Matrix (Fin n) (Fin n) F).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) F) = 1 :=
    fun A => Set.ext_iff.mp hset A
  have hcomm : ∀ M : Matrix (Fin n) (Fin n) F,
      (M.map F.subtype).map (· ^ ℓ ^ f) = (M.map (· ^ ℓ ^ f)).map F.subtype := by
    intro M
    ext i j
    simp only [Matrix.map_apply, map_pow]
  constructor
  · rintro ⟨Z, rfl⟩
    obtain ⟨-, hZu⟩ := (hmem Z).mp Z.2
    refine ⟨fun i j => (hF _).mp (SetLike.coe_mem _), (statedSUToSL F n (ℓ ^ f) Z).2, ?_⟩
    change (((((Z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).map F.subtype).map
      (· ^ ℓ ^ f))ᵀ * ((Z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map F.subtype = 1
    rw [hcomm, ← Matrix.transpose_map, ← Matrix.map_mul, hZu,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rintro ⟨hent, -, hu⟩
    set M : Matrix (Fin n) (Fin n) F := Matrix.of fun i j =>
      ⟨(Y : Matrix (Fin n) (Fin n) Ω) i j, (hF _).mpr (hent i j)⟩ with hMdef
    have hMY : M.map F.subtype = (Y : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      rfl
    have hMdet : M.det = 1 := by
      apply F.subtype.injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hMY, map_one]
      exact Y.2
    have hMu : (M.map (· ^ ℓ ^ f))ᵀ * M = 1 := by
      apply Matrix.map_injective F.subtype.injective
      change ((M.map (· ^ ℓ ^ f))ᵀ * M).map F.subtype = (1 : Matrix (Fin n) (Fin n) F).map F.subtype
      rw [Matrix.map_mul, Matrix.transpose_map, ← hcomm, hMY,
        Matrix.map_one _ (map_zero _) (map_one _)]
      exact hu
    have hMg : GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero) ∈
        StatedSU n (ℓ ^ f) F := (hmem _).mpr ⟨hMdet, hMu⟩
    exact ⟨⟨_, hMg⟩, Subtype.ext hMY⟩

theorem sln_root_permuting_frobenius_fixed_unitary {k : Type} [Field k] [Algebra k Ω]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (hn : 3 ≤ n)
    (π : Equiv.Perm (Fin n)) (Φ : SL(n, Ω) ≃* SL(n, Ω)) (b : Fin n → Fin n → Ωˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
        1 + single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f)) :
    (∃ A : GL (Fin n) Ω, ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω)) ∧
    (∃ H : SL(n, Ω), ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) n, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
    Finite (fixSubgroup Φ) ∧
    ((n, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple (fixSubgroup Φ) ∧
      (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
        ∃ c : Ω, ((x : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c) ∧
      Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd n (ℓ ^ f + 1)) ∧
    ((n, ℓ ^ f) = (4, 2) → Group.IsPerfect (fixSubgroup Φ) ∧ IsSimpleGroup (fixSubgroup Φ) ∧
      ∃ a b : fixSubgroup Φ, a * b ≠ b * a) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  have hσ' : ∀ c, σ c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hσ : ⇑σ = (· ^ ℓ ^ f) := funext hσ'
  obtain ⟨A, hA⟩ := exists_conj_map_inv_transpose_of_root_permuting hn σ π Φ.toMonoidHom b
    (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσ'])
  have hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) := fun X => by
    have := hA X
    rwa [MulEquiv.coe_toMonoidHom, hσ] at this
  obtain ⟨H, hHdet, -, hset⟩ :=
    matrix_graph_frobenius_unitary_descent hℓ hf hk (by omega : 1 ≤ n) A
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  have hfix : ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) n,
      Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL Hs * Y * (Matrix.SpecialLinearGroup.toGL Hs)⁻¹ := by
    intro X
    have hX := Set.ext_iff.mp hset (Matrix.SpecialLinearGroup.toGL X)
    rw [mem_fixSubgroup, hHs]
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
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  let Ψ : StatedSU n (ℓ ^ f) F →* SL(n, Ω) := statedSUToSL F n (ℓ ^ f)
  let θ : StatedSU n (ℓ ^ f) F →* SL(n, Ω) := (MulAut.conj Hs).toMonoidHom.comp Ψ
  have hθ : ∀ Y, θ Y = Hs * Ψ Y * Hs⁻¹ := fun Y => rfl
  have hθmem : ∀ Y, θ Y ∈ fixSubgroup Φ := by
    intro Y
    rw [hfix, hθ]
    refine ⟨Matrix.SpecialLinearGroup.toGL (Ψ Y),
      (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hθsurj : ∀ X ∈ fixSubgroup Φ, ∃ Y, θ Y = X := by
    intro X hX
    obtain ⟨Y', hY', hXY⟩ := (hfix X).mp hX
    have hW : Matrix.SpecialLinearGroup.toGL (Hs⁻¹ * X * Hs) = Y' := by
      rw [map_mul, map_mul, map_inv, hXY]
      group
    obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mpr (hW ▸ hY')
    refine ⟨Y, ?_⟩
    rw [hθ, show Ψ Y = Hs⁻¹ * X * Hs from hY]
    group
  let e : StatedSU n (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (θ.codRestrict _ hθmem)
    ⟨fun Y Z h => statedSUToSL_injective F n (ℓ ^ f)
      ((MulAut.conj Hs).injective (congrArg Subtype.val h)), fun X => by
        obtain ⟨Y, hY⟩ := hθsurj X X.2
        exact ⟨Y, Subtype.ext hY⟩⟩
  have he : ∀ Y, ((e Y : fixSubgroup Φ) : SL(n, Ω)) = Hs * Ψ Y * Hs⁻¹ := fun Y => rfl
  have hmain : (n, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple (fixSubgroup Φ) ∧
      (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
        ∃ c : Ω, ((x : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c) ∧
      Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd n (ℓ ^ f + 1) := by
    intro hnq
    obtain ⟨hQ, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
      (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hn hnq)
      (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ f hFcard n hn hnq)
    refine ⟨CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e hQ,
      fun x => ⟨fun hx => ?_, fun ⟨c, hc⟩ => mem_center_of_coe_eq_scalar x hc⟩, ?_⟩
    · have h1 := symm_mem_center_of_mulEquiv e hx
      rw [hZ, Subgroup.mem_subgroupOf] at h1
      obtain ⟨c, hc⟩ := h1
      refine ⟨((c : F) : Ω), ?_⟩
      rw [← e.apply_symm_apply x, he]
      refine coe_conj_eq_scalar _ _ ?_
      rw [coe_statedSUToSL, ← hc, GeneralLinearGroup.coe_scalar, scalar_map]
      rfl
    · rw [← natCard_center_eq_of_mulEquiv e, hZ]
      exact (CFSG.LinearGroups.unitary_scalar_kernel hℓ hFcard (by omega)).2.2
  refine ⟨⟨A, hA'⟩, ⟨Hs, hfix⟩, Finite.of_equiv _ e.toEquiv, hmain, fun h42 => ?_⟩
  have hnq : (n, ℓ ^ f) ≠ (3, 2) := by
    rw [h42]
    decide
  obtain ⟨⟨hperf, hsimple, hnab⟩, -, hcard⟩ := hmain hnq
  have hgcd : Nat.gcd n (ℓ ^ f + 1) = 1 := by
    rw [show n = 4 from congrArg Prod.fst h42, show ℓ ^ f = 2 from congrArg Prod.snd h42]
    rfl
  have hZ : Subgroup.center (fixSubgroup Φ) = ⊥ := Subgroup.card_eq_one.mp (hcard.trans hgcd)
  refine ⟨hperf, isSimpleGroup_of_center_eq_bot hZ, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  exact ⟨a', b', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩

end Unitary

end CFSG.RankThree.Classical2

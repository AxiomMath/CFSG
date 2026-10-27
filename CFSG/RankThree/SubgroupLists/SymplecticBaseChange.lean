module

public import CFSG.RankThree.SubgroupLists.SymplecticPartThreeBase
public import Certificates.Certificate113

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module Polynomial

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K K' : Type} [Field K] [Field K']

@[expose] noncomputable def mapGL (φ : K →+* K') : GL V₄ K →* GL V₄ K' :=
  Matrix.GeneralLinearGroup.map φ

theorem coe_mapGL (φ : K →+* K') (x : GL V₄ K) :
    ((mapGL φ x : GL V₄ K') : Matrix V₄ V₄ K') = (x : Matrix V₄ V₄ K).map φ := rfl

theorem mapGL_injective (φ : K →+* K') : Function.Injective (mapGL φ) := by
  intro x y h
  apply Units.ext
  have := congrArg (fun z : GL V₄ K' => (z : Matrix V₄ V₄ K')) h
  simp only [coe_mapGL] at this
  ext i j
  have := congrFun (congrFun this i) j
  simpa using φ.injective this

theorem spGram_map (φ : K →+* K') : (spGram 2 K).map φ = spGram 2 K' := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spGram, Matrix.fromBlocks, Matrix.one_apply]

theorem map_mem_statedSp (φ : K →+* K') {x : GL V₄ K} (hx : x ∈ StatedSp 2 K) :
    mapGL φ x ∈ StatedSp 2 K' := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_mapGL]
  have h := transpose_mul_spGram_mul hx
  have := congrArg (fun M : Matrix V₄ V₄ K => M.map φ) h
  simp only [Matrix.map_mul, Matrix.transpose_map, spGram_map] at this
  exact this

theorem isSqZero_map_iff (φ : K →+* K') {x : GL V₄ K} :
    IsSqZero (mapGL φ x) ↔ IsSqZero x := by
  rw [IsSqZero, IsSqZero, coe_mapGL]
  have : ((x : Matrix V₄ V₄ K).map φ - 1) * ((x : Matrix V₄ V₄ K).map φ - 1) =
      (((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1)).map φ := by
    rw [Matrix.map_mul, Matrix.map_sub (⇑φ) (map_sub φ),
      Matrix.map_one (⇑φ) φ.map_zero φ.map_one]
  rw [this]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa using φ.injective (by simpa using this)
  · intro h
    rw [h]
    simp

theorem map_mem_cliffSpace (φ : K →+* K') {Z : Matrix V₄ V₄ K}
    (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    Z.map φ ∈ (cliffSpace : Submodule K' _) := by
  obtain ⟨hJ, ht⟩ := hZ
  refine ⟨?_, ?_⟩
  · have := congrArg (fun M : Matrix V₄ V₄ K => M.map φ) hJ
    simp only [Matrix.map_mul, Matrix.transpose_map, spGram_map] at this
    exact this
  · have ht' : (Z.map φ).trace = φ Z.trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rw [ht', ht, map_zero]

theorem cliffB_map (φ : K →+* K') (Z Y : Matrix V₄ V₄ K) :
    cliffB (Z.map φ) (Y.map φ) = φ (cliffB Z Y) := by
  simp only [cliffB, ← Matrix.map_mul, Matrix.add_apply, Matrix.map_apply, map_add, map_mul,
    map_inv₀, map_ofNat]

theorem isNCInv_of_mem_cliffSpace (h2 : (2 : K) ≠ 0) {u : GL V₄ K}
    (hu : (u : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _))
    (huu : (u : Matrix V₄ V₄ K) * u = 1) : IsNCInv u := by
  have hu2 : u * u = 1 := Units.ext (by rw [Units.val_mul, huu, Units.val_one])
  refine ⟨?_, hu2, ?_, ?_⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    have hJ := hu.1
    calc (u : Matrix V₄ V₄ K)ᵀ * fromBlocks 0 1 (-1) 0 * (u : Matrix V₄ V₄ K)
        = (u : Matrix V₄ V₄ K)ᵀ * spGram 2 K * (u : Matrix V₄ V₄ K) := rfl
      _ = spGram 2 K * (u : Matrix V₄ V₄ K) * (u : Matrix V₄ V₄ K) := by rw [hJ]
      _ = fromBlocks 0 1 (-1) 0 := by rw [Matrix.mul_assoc, huu, Matrix.mul_one]
  · intro h
    have ht := hu.2
    rw [h, Units.val_one, Matrix.trace_one] at ht
    simp at ht
    apply h2
    have : ((4 : ℕ) : K) = 0 := by simpa using ht
    have h4 : (4 : K) = 2 * 2 := by norm_num
    have : (2 : K) * 2 = 0 := by rw [← h4]; exact_mod_cast this
    exact (mul_self_eq_zero.mp this)
  · intro h
    have ht := hu.2
    rw [h, Units.val_neg, Units.val_one, Matrix.trace_neg, Matrix.trace_one] at ht
    simp at ht
    apply h2
    have : ((4 : ℕ) : K) = 0 := by simpa using ht
    have h4 : (4 : K) = 2 * 2 := by norm_num
    have : (2 : K) * 2 = 0 := by rw [← h4]; exact_mod_cast this
    exact (mul_self_eq_zero.mp this)

theorem exists_isNCInv_smul_map [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {u : Matrix V₄ V₄ K} (hu : u ∈ (cliffSpace : Submodule K _)) (hQ : cliffB u u ≠ 0) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' p) (φ : K →+* K')
      (u' : GL V₄ K'), IsNCInv u' ∧ ∃ s : K', s ≠ 0 ∧ (u' : Matrix V₄ V₄ K') = s • u.map φ := by
  classical
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have huu : u * u = cliffB u u • (1 : Matrix V₄ V₄ K) := by
    rw [mul_self_of_mem h2 hu, cliffB_self h2]
  by_cases hsq : IsSquare (cliffB u u)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hQ (by rw [hr, mul_zero])
    set v : Matrix V₄ V₄ K := r⁻¹ • u
    have hrr : r⁻¹ * (r⁻¹ * (r * r)) = 1 := by
      rw [← mul_assoc, ← mul_inv, inv_mul_cancel₀ (mul_ne_zero hr0 hr0)]
    have hvv : v * v = 1 := by
      simp only [v, Matrix.smul_mul, Matrix.mul_smul, smul_smul, huu, hr]
      rw [hrr, one_smul]
    let v' : GL V₄ K := ⟨v, v, hvv, hvv⟩
    refine ⟨K, inferInstance, inferInstance, inferInstance, RingHom.id K, v', ?_, r⁻¹,
      inv_ne_zero hr0, ?_⟩
    · exact isNCInv_of_mem_cliffSpace h2 (Submodule.smul_mem _ _ hu) hvv
    · show v = r⁻¹ • u.map (RingHom.id K)
      simp [v]
  ·
    set c := cliffB u u
    set f : K[X] := X ^ 2 - C c
    have hfmon : f.Monic := by simp only [f]; monicity!
    have hfdeg : f.natDegree = 2 := by simp only [f]; compute_degree!
    have hfirr : Irreducible f := by
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [hfdeg]
        decide
      · intro x hx
        apply hsq
        refine ⟨x, ?_⟩
        simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx
        rw [← hx, pow_two]
    haveI : Fact (Irreducible f) := ⟨hfirr⟩
    set K' := AdjoinRoot f
    haveI : Module.Finite K K' := (AdjoinRoot.powerBasis hfmon.ne_zero).finite
    haveI : Finite K' := Module.finite_of_finite K
    haveI : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
    set φ : K →+* K' := AdjoinRoot.of f
    set ξ : K' := AdjoinRoot.root f
    have hξ : ξ * ξ = φ c := by
      have := AdjoinRoot.eval₂_root f
      simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
        sub_eq_zero] at this
      rw [← pow_two]
      exact this
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hξ
      exact hQ (φ.injective (by rw [← hξ, map_zero]))
    set v : Matrix V₄ V₄ K' := ξ⁻¹ • u.map φ
    have hvv : v * v = 1 := by
      simp only [v, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul, huu]
      rw [Matrix.map_smul' _ _ _ (fun a b => by simp), Matrix.map_one _ φ.map_zero φ.map_one,
        smul_smul, ← hξ, ← mul_inv, inv_mul_cancel₀ (mul_ne_zero hξ0 hξ0), one_smul]
    let v' : GL V₄ K' := ⟨v, v, hvv, hvv⟩
    have h2' : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
    refine ⟨K', inferInstance, inferInstance, inferInstance, φ, v', ?_, ξ⁻¹, inv_ne_zero hξ0, rfl⟩
    exact isNCInv_of_mem_cliffSpace h2' (Submodule.smul_mem _ _ (map_mem_cliffSpace φ hu)) hvv

end CFSG.RankThree.SubgroupLists

module

public import CFSG.RankThree.GF2n.Tim79aCitedSp62

import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSixCoverTwoKernelPairs
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadicalCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixBasisTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix Module Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SevenTransvectionE7
open CFSG.LocalAnalysis.ComponentInitial.SixCoverTwoKernel
open scoped commutatorElement

private theorem coe_statedSpCongr_apply {K L : Type} [Field K] [Field L] (σ : K ≃+* L)
    (n : ℕ) (g : StatedSp n K) (i j : Fin n ⊕ Fin n) :
    (((statedSpCongr σ n g : StatedSp n L) : GL (Fin n ⊕ Fin n) L) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) i j =
      σ (((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) i j) := by
  unfold statedSpCongr
  simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.toMulEquiv_apply,
    TauCeti.GLSymplectic.coe_map]
  rfl

private lemma vecMul_fromBlocks_inl (a : Fin 3 ⊕ Fin 3 → ZMod 2) (i : Fin 3) :
    (a ᵥ* (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)))
        (Sum.inl i) = a (Sum.inr i) := by
  simp only [vecMul, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply,
    Matrix.zero_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma vecMul_fromBlocks_inr (a : Fin 3 ⊕ Fin 3 → ZMod 2) (i : Fin 3) :
    (a ᵥ* (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)))
        (Sum.inr i) = a (Sum.inl i) := by
  simp only [vecMul, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply,
    Matrix.zero_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · simp [ZMod.neg_eq_self_mod_two]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma b0_basis_apply
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e)
    (j : Fin 3 ⊕ Fin 3) (u : Fin 6 → ZMod 2) :
    b0 (e j) u = (e.repr u ᵥ* (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) j := by
  rcases j with i | i
  · rw [bilin_inl he, vecMul_fromBlocks_inl]
  · rw [bilin_inr he, vecMul_fromBlocks_inr]

private theorem toMatrix_binarySymplecticTransvection
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)}
    (he : IsSymplecticBasis b0 e) (u : Fin 6 → ZMod 2) :
    LinearMap.toMatrix e e ((binarySymplecticTransvection b0 b0_isAlt u :
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)) :
        (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      1 + vecMulVec (e.repr u) (e.repr u ᵥ* (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) := by
  ext i j
  rw [LinearMap.toMatrix_apply, binarySymplecticTransvection_apply]
  change e.repr (e j + b0 (e j) u • u) i =
    (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) i j +
      vecMulVec (e.repr u) (e.repr u ᵥ* (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) i j
  rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_eq_pi_single, Pi.single_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    b0_basis_apply he, smul_eq_mul]
  split_ifs <;> ring

private theorem map_fromBlocks_J (σ : GaloisField 2 1 ≃+* ZMod 2) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)).map σ =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
  haveI : CharP (GaloisField 2 1) 2 := inferInstance
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fromBlocks, CharTwo.neg_eq, ZMod.neg_eq_self_mod_two]

private theorem map_vecMul_J (σ : GaloisField 2 1 ≃+* ZMod 2)
    (v : Fin 3 ⊕ Fin 3 → GaloisField 2 1) :
    (fun j => σ ((v ᵥ* (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))) j)) =
      (fun i => σ (v i)) ᵥ* (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
  funext j
  rw [← map_fromBlocks_J]
  exact RingHom.map_vecMul (σ : GaloisField 2 1 →+* ZMod 2)
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) v j

private noncomputable def coverMap {Γ : Type} [Group Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1))
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e) :
    Γ →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2) :=
  (bilinIsometryGroup b0).subtype.comp
    (((spCoord he).symm.toMonoidHom.comp (statedSpCongr σ 3).toMonoidHom).comp φ)

private theorem spMatrixOf_statedSpCongr_transvection
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    (t : StatedSp 3 (GaloisField 2 1)) (v : Fin 3 ⊕ Fin 3 → GaloisField 2 1)
    (ht : ((t : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) =
      1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)))) :
    spMatrixOf (statedSpCongr σ 3 t) =
      1 + vecMulVec (fun i => σ (v i))
        ((fun i => σ (v i)) ᵥ* (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) := by
  ext i j
  rw [spMatrixOf, coe_statedSpCongr_apply, ht]
  change σ ((1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)))) i j) =
    (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) i j +
      vecMulVec (fun i => σ (v i))
        ((fun i => σ (v i)) ᵥ* (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) i j
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, map_add, map_mul, congrFun (map_vecMul_J σ v) j]
  by_cases hij : i = j <;> simp [hij]

private theorem coverMap_apply_eq_transvection {Γ : Type} [Group Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1))
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e)
    (t : Γ) (v : Fin 3 ⊕ Fin 3 → GaloisField 2 1)
    (ht : ((φ t : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) =
      1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))))
    (u : Fin 6 → ZMod 2) (hu : e.repr u = fun i => σ (v i)) :
    coverMap φ σ he t = binarySymplecticTransvection b0 b0_isAlt u := by
  have hρmat : LinearMap.toMatrix e e ((coverMap φ σ he t :
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)) :
        (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      spMatrixOf (statedSpCongr σ 3 (φ t)) := by
    simp only [coverMap, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    rw [← spMatrixOf_spCoord he ((spCoord he).symm (statedSpCongr σ 3 (φ t)))]
    rw [MulEquiv.apply_symm_apply]
  have hSmat : spMatrixOf (statedSpCongr σ 3 (φ t)) =
      1 + vecMulVec (fun i => σ (v i))
        ((fun i => σ (v i)) ᵥ* (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) :=
    spMatrixOf_statedSpCongr_transvection σ (φ t) v ht
  have hτmat := toMatrix_binarySymplecticTransvection he u
  rw [hu] at hτmat
  have hmat : LinearMap.toMatrix e e ((coverMap φ σ he t :
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)) :
        (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      LinearMap.toMatrix e e ((binarySymplecticTransvection b0 b0_isAlt u :
        LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)) :
          (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) := by
    rw [hρmat, hSmat, ← hτmat]
  apply Units.ext
  exact (LinearMap.toMatrix e e).injective hmat

private theorem coverMap_range {Γ : Type} [Group Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1)) (hφ : Function.Surjective φ)
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e) :
    (coverMap φ σ he).range = bilinIsometryGroup b0 := by
  have hsurj : Function.Surjective
      (((spCoord he).symm.toMonoidHom.comp (statedSpCongr σ 3).toMonoidHom).comp φ) :=
    ((spCoord he).symm.surjective.comp (statedSpCongr σ 3).surjective).comp hφ
  unfold coverMap
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private theorem coverMap_ker {Γ : Type} [Group Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1))
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e) :
    (coverMap φ σ he).ker = φ.ker := by
  ext x
  simp only [coverMap, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

private theorem b0_eq_dotProduct_repr
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e)
    (x y : Fin 6 → ZMod 2) :
    b0 x y = e.repr x ⬝ᵥ ((fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ e.repr y) := by
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e b0 x y, he]

private theorem dotProduct_J_map (σ : GaloisField 2 1 ≃+* ZMod 2)
    (v w : Fin 3 ⊕ Fin 3 → GaloisField 2 1) :
    (fun i => σ (v i)) ⬝ᵥ ((fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ fun i => σ (w i)) =
      σ (v ⬝ᵥ ((fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) *ᵥ w)) := by
  have hmat : ((fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ fun i => σ (w i)) =
      fun i => σ (((fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) *ᵥ w) i) := by
    funext i
    rw [← map_fromBlocks_J]
    exact (RingHom.map_mulVec (σ : GaloisField 2 1 →+* ZMod 2)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3)
        (GaloisField 2 1)) w i).symm
  rw [hmat]
  exact (RingHom.map_dotProduct (σ : GaloisField 2 1 →+* ZMod 2) v
    ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3)
      (GaloisField 2 1)) *ᵥ w)).symm

private theorem coverMap_ker_sq {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1))
    (σ : GaloisField 2 1 ≃+* ZMod 2)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin 6 → ZMod 2)} (he : IsSymplecticBasis b0 e)
    (hcard : Nat.card φ.ker = 2) :
    ∀ c ∈ (coverMap φ σ he).ker, c ^ 2 = 1 := by
  intro c hc
  rw [coverMap_ker] at hc
  have hdvd : orderOf c ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard φ.ker hc
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · rw [orderOf_eq_one_iff.mp h]; exact one_pow 2
  · rw [← h]
    exact orderOf_dvd_iff_pow_eq_one.mp dvd_rfl

private theorem coverLift_order
    {Γ : Type} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (ρ : Γ →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2))
    (hρrange : ρ.range = bilinIsometryGroup b0) (hρC : ρ.ker ≤ center Γ)
    (hρ2 : ∀ c ∈ ρ.ker, c ^ 2 = 1) (hρcard : Nat.card ρ.ker = 2)
    (t : Γ) (u : Fin 6 → ZMod 2) (hu_ne : u ≠ 0)
    (hρt : ρ t = binarySymplecticTransvection b0 b0_isAlt u) :
    orderOf t = 4 := by
  have htsq : t ^ 2 = liftT hρrange u ^ 2 :=
    sq_eq_of_map_eq ρ hρC hρ2 (by rw [map_liftT, hρt])
  have hlam : t ^ 2 = liftT hρrange (bitVec 2) ^ 2 := by
    rw [htsq]
    exact liftT_sq_eq hρrange hρC hρ2 hu_ne (by decide)
  have hlamne : liftT hρrange (bitVec 2) ^ 2 ≠ 1 :=
    liftT_sq_ne_one_of_card_ker_eq_two hρrange hρC hρ2 hρcard
  have hlam2 : (t ^ 2) ^ 2 = 1 := by
    rw [hlam]
    exact hρ2 _ (liftT_sq_mem hρrange (bitVec 2))
  have h4 : t ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hlam2]
  have h2ne : t ^ 2 ≠ 1 := by rw [hlam]; exact hlamne
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa only [pow_one] using h2ne) h4
  simpa using this

private theorem coverLift_noncommute
    {Γ : Type} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (ρ : Γ →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2))
    (hρrange : ρ.range = bilinIsometryGroup b0) (hρC : ρ.ker ≤ center Γ)
    (hρ2 : ∀ c ∈ ρ.ker, c ^ 2 = 1) (hρcard : Nat.card ρ.ker = 2)
    {t s : Γ} {u u' : Fin 6 → ZMod 2}
    (hρt : ρ t = binarySymplecticTransvection b0 b0_isAlt u)
    (hρs : ρ s = binarySymplecticTransvection b0 b0_isAlt u')
    (hu_ne : u ≠ 0) (hu'_ne : u' ≠ 0) (hune : u ≠ u') (hb0 : b0 u u' = 0) :
    t * s ≠ s * t := by
  have hcomm : ⁅t, s⁆ = liftT hρrange (bitVec 2) ^ 2 := by
    have hmap_t : ρ t = ρ (liftT hρrange u) := by rw [hρt, map_liftT]
    have hmap_s : ρ s = ρ (liftT hρrange u') := by rw [hρs, map_liftT]
    calc
      ⁅t, s⁆ = ⁅liftT hρrange u, liftT hρrange u'⁆ :=
        (commutatorElement_eq_of_map_eq ρ hρC hmap_t hmap_s).symm
      _ = ⁅liftT hρrange (bitVec 2), liftT hρrange (bitVec 8)⁆ :=
        commutatorElement_liftT_eq_of_orth hρrange hρC hu_ne hu'_ne hune hb0
      _ = liftT hρrange (bitVec 2) ^ 2 :=
        (liftT_sq_eq_commutatorElement hρrange hρC hρ2).symm
  intro hts
  have h1 : ⁅t, s⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).mpr hts
  rw [hcomm] at h1
  exact liftT_sq_ne_one_of_card_ker_eq_two hρrange hρC hρ2 hρcard h1

theorem sp62CoverLiftStatement_holds :
    Sp62CoverLiftStatement := by
  intro Γ _ _ φ hφ hcen hcard hperf t s v w hv hw ht hs
  classical
  haveI : Group.IsPerfect Γ := ⟨hperf⟩
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hGal : Fintype.card (GaloisField 2 1) = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [GaloisField.card 2 1 one_ne_zero, Nat.card_zmod]
    norm_num
  let σ : GaloisField 2 1 ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hGal
  obtain ⟨e, he⟩ := BinarySymplecticSix.exists_isSymplecticBasis b0_isAlt b0_nondegenerate
    (n := 3) (by rw [Module.finrank_fin_fun])
  let ρ := coverMap φ σ he
  have hρrange : ρ.range = bilinIsometryGroup b0 := coverMap_range φ hφ σ he
  have hρker : ρ.ker = φ.ker := coverMap_ker φ σ he
  have hρC : ρ.ker ≤ center Γ := by rw [hρker]; exact hcen
  have hρ2 : ∀ c ∈ ρ.ker, c ^ 2 = 1 := coverMap_ker_sq φ σ he hcard
  have hρcard : Nat.card ρ.ker = 2 := by rw [hρker, hcard]
  let u : Fin 6 → ZMod 2 := e.equivFun.symm (fun i => σ (v i))
  have hu : e.repr u = fun i => σ (v i) := by
    rw [show e.repr u = e.equivFun u from (Basis.equivFun_apply e u).symm]
    dsimp only [u]
    exact e.equivFun.apply_symm_apply _
  have hρt : ρ t = binarySymplecticTransvection b0 b0_isAlt u :=
    coverMap_apply_eq_transvection φ σ he t v ht u hu
  have hu_ne : u ≠ 0 := by
    intro h
    apply hv
    have h1 : (fun i => σ (v i)) = 0 := by
      rw [← hu]
      rw [h]
      simp
    funext i
    exact σ.injective (by simpa using congrFun h1 i)
  refine ⟨coverLift_order ρ hρrange hρC hρ2 hρcard t u hu_ne hρt, ?_⟩
  intro hvw hdot
  let u' : Fin 6 → ZMod 2 := e.equivFun.symm (fun i => σ (w i))
  have hu' : e.repr u' = fun i => σ (w i) := by
    rw [show e.repr u' = e.equivFun u' from (Basis.equivFun_apply e u').symm]
    dsimp only [u']
    exact e.equivFun.apply_symm_apply _
  have hρs : ρ s = binarySymplecticTransvection b0 b0_isAlt u' :=
    coverMap_apply_eq_transvection φ σ he s w hs u' hu'
  have hu'_ne : u' ≠ 0 := by
    intro h
    apply hw
    have h1 : (fun i => σ (w i)) = 0 := by
      rw [← hu']
      rw [h]
      simp
    funext i
    exact σ.injective (by simpa using congrFun h1 i)
  have hune : u ≠ u' := by
    intro h
    apply hvw
    funext i
    have h1 : (fun i => σ (v i)) = (fun i => σ (w i)) := by
      rw [← hu, ← hu', h]
    exact σ.injective (by simpa using congrFun h1 i)
  have hb0 : b0 u u' = 0 := by
    rw [b0_eq_dotProduct_repr he, hu, hu', dotProduct_J_map, hdot, map_zero]
  exact coverLift_noncommute ρ hρrange hρC hρ2 hρcard hρt hρs hu_ne hu'_ne hune hb0

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4Diag
import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
import CFSG.RankThree.PartOne.Q1327C.BU5Diag
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.LieType.Universal.Unitary (SUid mem_SUid conjTr SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open Matrix

section SU

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem u4_conjTr_l4Blk3_mul (X Y : Matrix (Fin 3) (Fin 3) K) :
    conjTr σ (l4Blk3 X) * l4Blk3 Y = l4Blk3 (conjTr σ X * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Blk3, conjTr, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four,
      Matrix.transpose_apply]

theorem u4_l4BlkGL3_mem {B : GL (Fin 3) K} (hB : B ∈ SUid σ 3) : l4BlkGL3 B ∈ SUid σ 4 := by
  obtain ⟨h1, h2⟩ := mem_SUid.mp hB
  refine mem_SUid.mpr ⟨?_, ?_⟩
  · rw [coe_l4BlkGL3, det_l4Blk3]
    exact h1
  · rw [coe_l4BlkGL3, u4_conjTr_l4Blk3_mul, h2, l4Blk3_one]

theorem u4_mem_SUid_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (g : GL (Fin n) K) :
    g ∈ SUid σ n ↔ Sec21.Tables.reindexGL e g ∈ SUid σ n := by
  have hdet : ((Sec21.Tables.reindexGL e g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (g : Matrix (Fin n) (Fin n) K).det := by
    rw [Sec21.Tables.coe_reindexGL, det_submatrix_equiv_self]
  have hu : conjTr σ ((Sec21.Tables.reindexGL e g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((Sec21.Tables.reindexGL e g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (conjTr σ (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)).submatrix e e := by
    rw [Sec21.Tables.coe_reindexGL, ← Matrix.submatrix_mul_equiv _ _ _ e]
    congr 1
  rw [mem_SUid, mem_SUid, hdet, hu]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, submatrix_one_equiv]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.submatrix e.symm e.symm) h2
    simpa using h3

theorem u4_mem_SUid_three_of_block {M : GL (Fin 4) K} (hM : M ∈ SUid σ 4) {B : GL (Fin 3) K}
    (hB : (B : Matrix (Fin 3) (Fin 3) K) =
      (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc)
    (hz : ∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
      (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0)
    (hdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1) : B ∈ SUid σ 3 := by
  refine mem_SUid.mpr ⟨hdet, ?_⟩
  have hcs : ∀ k : Fin 4, (∀ l : Fin 3, (Fin.castSucc l : Fin 4) ≠ k) → k = 3 := by decide
  have h1 := (mem_SUid.mp hM).2
  have hv : ∀ i k, (∀ l : Fin 3, (Fin.castSucc l : Fin 4) ≠ k) →
      conjTr σ (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) k = 0 := by
    intro i k hk
    rw [hcs k hk]
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
    rw [(hz i).2, map_zero]
  have h2 : (conjTr σ (M : Matrix (Fin 4) (Fin 4) K) *
      (M : Matrix (Fin 4) (Fin 4) K)).submatrix Fin.castSucc Fin.castSucc =
      conjTr σ (B : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) := by
    rw [l4_submatrix_mul Fin.castSucc (Fin.castSucc_injective 3) hv, hB]
    congr 1
  rw [← h2, h1, submatrix_one _ (Fin.castSucc_injective 3)]

theorem u4_mem_SUid_iff {p f : ℕ} (h : UnitaryFieldData p f K) (hσ : ∀ c, σ c = h.bar c) {n : ℕ}
    (g : GL (Fin n) K) :
    g ∈ SUid σ n ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 ∧
      g ∈ primeFormUnitary h (idGram K n) := by
  have hmap : (g : Matrix (Fin n) (Fin n) K).map σ = (g : Matrix (Fin n) (Fin n) K).map h.bar := by
    ext i j
    simp [hσ]
  rw [mem_SUid, mem_primeFormUnitary, conjTr, hmap]
  simp [idGram]

theorem u4_exists_diag {p f : ℕ} (h : UnitaryFieldData p f K) {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (hmq : 3 ∣ p ^ f + 1) {A : GL (Fin 4) K}
    (hAU : A ∈ primeFormUnitary h (idGram K 4)) (hA3 : A ^ 3 = 1) :
    ∃ g ∈ primeFormUnitary h (idGram K 4), ∃ a : Fin 4 → ZMod 3,
      ((g * A * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal (fun i => ω ^ (a i).val) := by
  have hω := RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  set U := primeFormUnitary h (idGram K 4) with hU
  set X : U := ⟨A, hAU⟩ with hX
  have hX3 : X ^ 3 = 1 := Subtype.ext (by simpa [X] using hA3)
  have hcomm : ∀ y ∈ Subgroup.zpowers X, ∀ z ∈ Subgroup.zpowers X, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl X).zpow_zpow i j).eq
  have hpow : ∀ y ∈ Subgroup.zpowers X, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hX3,
      _root_.one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hω hmq
    (Subgroup.zpowers X) hcomm hpow
  have hdiag := hP X (Subgroup.mem_zpowers X)
  refine ⟨(P : GL (Fin 4) K)⁻¹, U.inv_mem P.2, ?_⟩
  set D : GL (Fin 4) K := (P : GL (Fin 4) K)⁻¹ * A * (P : GL (Fin 4) K)⁻¹⁻¹ with hDdef
  have hDeq : ((P⁻¹ * X * P : U) : GL (Fin 4) K) = D := by
    rw [hDdef, inv_inv]
    rfl
  rw [hDeq] at hdiag
  obtain ⟨d, hd⟩ : ∃ d : Fin 4 → K, (D : Matrix (Fin 4) (Fin 4) K) = diagonal d :=
    ⟨fun l => (D : Matrix (Fin 4) (Fin 4) K) l l, hdiag.diagonal_diag.symm⟩
  have hD3 : D ^ 3 = 1 := by rw [hDdef, conj_pow, hA3, mul_one, mul_inv_cancel]
  have hd3 : ∀ l, d l ^ 3 = 1 := by
    intro l
    have hm : (D : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hD3, Units.val_one]
    rw [hd, diagonal_pow] at hm
    have := congrFun (congrFun hm l) l
    simpa [diagonal_apply_eq] using this
  choose a ha using fun l => RonanK432.exists_zmod_three_pow_eq hω2 (hd3 l)
  refine ⟨a, ?_⟩
  rw [hd]
  congr 1
  funext l
  exact (ha l).symm

end SU

theorem u4_exists_cube_root {F : Type} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  have hdvdU : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g3, hg3⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvdU
  have hω3 : (g3 : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg3, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (g3 : F) ≠ 1 := by
    intro h1
    have hg1 : g3 = 1 := Units.ext h1
    rw [hg1, orderOf_one] at hg3
    exact absurd hg3 (by norm_num)
  refine ⟨g3, ?_⟩
  have h1 : ((g3 : F) - 1) * ((g3 : F) ^ 2 + (g3 : F) + 1) = 0 := by
    linear_combination hω3
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hω1
  · exact h2

theorem u4_card_galoisField (p : ℕ) [Fact p.Prime] :
    Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
  rw [GaloisField.card p (2 * 1) (by norm_num)]
  ring


theorem u4_good429_SUid {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ}
    (h : UnitaryFieldData p f K) (hσ : ∀ c, σ c = h.bar c) {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (hmq : 3 ∣ p ^ f + 1) (hQ : IsQuasisimple (SUid σ 3))
    (A : SUid σ 4) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    Good429 (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓ SUid σ 4) := by
  have hω := RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 4) K) ≠ 1 := fun h' => hA1 (Subtype.ext h')
  have hAU := ((u4_mem_SUid_iff σ h hσ _).mp A.2).2
  obtain ⟨g, hgU, a, hD⟩ := u4_exists_diag h hω2 h3 hmq hAU hA3'
  refine l4_good429_of_conj h3 hω hQ (fun g hg => (mem_SUid.mp hg).1)
    (fun e g => u4_mem_SUid_reindex σ e g) (fun B hB => u4_l4BlkGL3_mem σ hB)
    (fun M hM B hB hz hdet => u4_mem_SUid_three_of_block σ hM hB hz hdet) ?_ A.2 hA3' hA1' ?_ hD
  · intro u hu hu3
    have h4 : u ^ 4 = 1 := by
      have hd := (mem_SUid.mp hu).1
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin] at hd
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd)
    calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hu3, inv_one, one_mul]
  · intro M
    rw [u4_mem_SUid_iff σ h hσ, u4_mem_SUid_iff σ h hσ]
    have hdet : ((g * M * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
        (M : Matrix (Fin 4) (Fin 4) K).det := by
      have e : GeneralLinearGroup.det (g * M * g⁻¹) = GeneralLinearGroup.det M := by
        rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      have e' := congrArg Units.val e
      simpa only [GeneralLinearGroup.val_det_apply] using e'
    rw [hdet]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU h2) (Subgroup.inv_mem _ hgU)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h5 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgU) h2) hgU
      rwa [show g⁻¹ * (g * M * g⁻¹) * g = M by group] at h5

theorem u4_good429_SU4 {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp2 : p % 3 = 2)
    (A : SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    Good429 (Subgroup.centralizer ({(A : GL (Fin 4) (GaloisField p (2 * 1)))} :
      Set (GL (Fin 4) (GaloisField p (2 * 1)))) ⊓
        SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
  have hpp : p.Prime := Fact.out
  have hK := u4_card_galoisField p
  have h := Sec4.unitaryFieldData_galoisField p 1 le_rfl
  have hσ : ∀ c, unitaryInvolution (GaloisField p (2 * 1)) p 1 c = h.bar c := fun c => by
    rw [unitaryInvolution_apply, h.bar_apply]
  have h3 : (3 : GaloisField p (2 * 1)) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : GaloisField p (2 * 1)) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p (2 * 1)) p 3).mp h0'
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp hdvd
    omega
  have hp21 : p ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hp2]
  have hpos : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpp.pos
  obtain ⟨ω, hω2⟩ := u4_exists_cube_root (F := GaloisField p (2 * 1)) (by
    rw [hK, pow_one]
    omega)
  have hmq : 3 ∣ p ^ 1 + 1 := by
    rw [pow_one]
    omega
  have hnq : ((3 : ℕ), p ^ 1) ≠ (3, 2) := by
    intro he
    have : p ^ 1 = 2 := (Prod.mk.inj he).2
    rw [pow_one] at this
    omega
  have hQ : IsQuasisimple (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 3) := by
    rw [SUid_eq_statedSU hK 3]
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl hnq).1
  exact u4_good429_SUid _ h hσ hω2 h3 hmq hQ A hA3 hA1

theorem u4_good429_projSU {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp2 : p % 3 = 2)
    (x : projSU 4 p 1) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set (projSU 4 p 1))) := by
  have hK := u4_card_galoisField p
  have hproj : projSU 4 p 1 =
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.PGLModel.projImage_statedSU]
  let e₀ : projSU 4 p 1 ≃*
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) :=
    MulEquiv.subgroupCongr hproj
  refine Good429.of_mulEquiv_centralizer e₀ ?_
  refine l4_good429_proj (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) ?_
    (fun A hA3 hA1 => u4_good429_SU4 hp hp2 A hA3 hA1) (e₀ x)
    (by rw [MulEquiv.orderOf_eq]; exact hx)
  intro u hu
  have hd := (mem_SUid.mp hu).1
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hd
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd)

theorem rowSOf429_four_SU_mod_two : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    RowSOf429 (projSU 4 p 1) := by
  intro p _ hp hp2
  refine rowSOf429_of_noCfg fun S _ _ _ hna ⟨e⟩ => ?_
  exact noCfgS429_of_model e (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e RonanK432.not_three_dvd_card_outer_projSU_four_prime)
    (fun x hx => u4_good429_projSU hp hp2 x hx)

end CFSG.RankThree.PartTwo.Sec4.RonanK429H

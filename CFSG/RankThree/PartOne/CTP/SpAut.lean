module

public import CFSG.RankThree.PartOne.CTP.Spectrum4
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Semilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_spSemilinearAutGroup_of_odd_pow {α : MulAut (StatedProj (StatedSp 2 K))} {p : ℕ}
    (hp : Odd p) (hα : α ^ p = 1) : α ∈ spSemilinearAutGroup 2 K := by
  have hidx := CFSG.RankThree.PartOne.KCSpComm.index_spSemilinearAutGroup_two (K := K)
  by_contra hne
  obtain ⟨m, rfl⟩ := hp
  have h2 : α * α ∈ spSemilinearAutGroup 2 K :=
    (Subgroup.mul_mem_iff_of_index_two hidx).mpr Iff.rfl
  have h3 : α ^ (2 * m) ∈ spSemilinearAutGroup 2 K := by
    rw [pow_mul, sq]
    exact pow_mem h2 m
  have h5 : α ^ (2 * m) * α ∈ spSemilinearAutGroup 2 K := by
    rw [← pow_succ, hα]
    exact one_mem _
  exact hne (((Subgroup.mul_mem_iff_of_index_two hidx).mp h5).mp h3)

omit [Finite K] [CharP K 2] in
theorem spInner_mul_fieldAut_pow (g : StatedSp 2 K) (φ : K ≃+* K) (k : ℕ) :
    ∃ N : StatedSp 2 K, (spInner 2 K g * fieldAut 2 K φ) ^ k =
      spInner 2 K N * fieldAut 2 K (φ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N * fieldSp 2 K (φ ^ k) g, ?_⟩
    rw [pow_succ, hN, spInner_mul_fieldAut_mul, pow_succ]

omit [Finite K] in
theorem fieldAut_pow_eq_one_of_pow_eq_one {g : StatedSp 2 K} {φ : K ≃+* K} {p : ℕ}
    (h : (spInner 2 K g * fieldAut 2 K φ) ^ p = 1) : φ ^ p = 1 := by
  obtain ⟨N, hN⟩ := spInner_mul_fieldAut_pow g φ p
  have h1 : spInner 2 K N * fieldAut 2 K (φ ^ p) = spInner 2 K 1 * fieldAut 2 K 1 := by
    rw [← hN, h, map_one, map_one, mul_one]
  exact (spInner_mul_fieldAut_inj h1).2

end Semilinear

section Spectrum

variable {r : ℕ} {K : Type} [Field K]

theorem formJ_mul_formJ' : formJ r K * formJ r K = -1 := by
  rw [formJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, one_apply, Matrix.neg_apply]

theorem formJ_mul_neg_formJ : formJ r K * -formJ r K = 1 := by
  rw [Matrix.mul_neg, formJ_mul_formJ', neg_neg]

theorem isRoot_charpoly_inv_of_statedSp (g : StatedSp r K) {a : K}
    (ha : (mat r K g).charpoly.IsRoot a) : (mat r K g).charpoly.IsRoot a⁻¹ := by
  classical
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := mat r K g with hM
  have hJ : Mᵀ * formJ r K * M = formJ r K :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have hJJ : formJ r K * formJ r K = -1 := formJ_mul_formJ'
  have hleft : (-formJ r K * Mᵀ * formJ r K) * M = 1 := by
    calc (-formJ r K * Mᵀ * formJ r K) * M = -formJ r K * (Mᵀ * formJ r K * M) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.neg_mul, hJJ, neg_neg]
  have hginv : mat r K g⁻¹ = -formJ r K * Mᵀ * formJ r K := by
    have h1 : mat r K g⁻¹ * M = 1 := by rw [hM, ← map_mul, inv_mul_cancel, map_one]
    have h2 : M * mat r K g⁻¹ = 1 := by rw [hM, ← map_mul, mul_inv_cancel, map_one]
    calc mat r K g⁻¹ = 1 * mat r K g⁻¹ := (Matrix.one_mul _).symm
      _ = ((-formJ r K * Mᵀ * formJ r K) * M) * mat r K g⁻¹ := by rw [hleft]
      _ = (-formJ r K * Mᵀ * formJ r K) * (M * mat r K g⁻¹) := by rw [Matrix.mul_assoc]
      _ = -formJ r K * Mᵀ * formJ r K := by rw [h2, Matrix.mul_one]
  have hcp : (mat r K g⁻¹).charpoly = M.charpoly := by
    rw [hginv, Matrix.charpoly_mul_comm]
    have : formJ r K * (-formJ r K * Mᵀ) = Mᵀ := by
      rw [← Matrix.mul_assoc, formJ_mul_neg_formJ, Matrix.one_mul]
    rw [this, Matrix.charpoly_transpose]
  have hspec : a ∈ spectrum K M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ha
  have ha0 : a ≠ 0 := spectrum.ne_zero_of_mem_of_unit (a := (g : GL (Fin r ⊕ Fin r) K)) hspec
  have hspec' : a ∈ spectrum K (mat r K g⁻¹) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hcp]
    exact ha
  have h2 := (spectrum.inv_mem_iff (R := K) (r := Units.mk0 a ha0)
    (a := ((g : GL (Fin r ⊕ Fin r) K)⁻¹))).mp hspec'
  rw [inv_inv] at h2
  exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp h2

end Spectrum

section Torus

theorem exists_sl2_orderOf_eq {L : Type} [Field L] [Finite L] :
    ∃ t : SL(2, L), orderOf t = Nat.card L - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  refine ⟨CFSG.ClassicalInvolution.WeakCT.torusHom L g, ?_⟩
  rw [orderOf_injective (CFSG.ClassicalInvolution.WeakCT.torusHom L)
    (CFSG.ClassicalInvolution.WeakCT.torusHom_injective (K := L)) g,
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]

end Torus

section Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sp_aut_odd {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : Odd p)
    {ε : MulAut (StatedSp 2 K)} (hε : ε ^ p = 1) {x : StatedSp 2 K}
    (hx : orderOf x = Nat.card K - 1) (hεx : ε x = x) :
    ∃ g : StatedSp 2 K, ∀ s, ε s = g * s * g⁻¹ := by
  classical
  have hπ := UnitaryHigher.proj_bijective_of_charTwo (r := 2) (K := K)
  set α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr (projSpEquiv K) ε with hαdef
  have hα : ∀ s : StatedSp 2 K, α (proj 2 K s) = proj 2 K (ε s) := by
    intro s
    change projSpEquiv K (ε ((projSpEquiv K).symm (projSpEquiv K s))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hαp : α ^ p = 1 := by rw [hαdef, ← map_pow, hε, map_one]
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut
    (mem_spSemilinearAutGroup_of_odd_pow hp hαp)
  have hφp : φ ^ p = 1 := fieldAut_pow_eq_one_of_pow_eq_one (by rw [← hgφ]; exact hαp)
  have hfix : g * fieldSp 2 K φ x * g⁻¹ = x := by
    apply hπ.1
    have h1 := hα x
    rw [hεx, hgφ, spInner_mul_fieldAut_proj] at h1
    exact h1
  have hconj : ∃ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, IsUnit M ∧
      M * (mat 2 K x).map φ = mat 2 K x * M := by
    refine ⟨mat 2 K g, (g : GL (Fin 2 ⊕ Fin 2) K).isUnit, ?_⟩
    have hfix' : g * fieldSp 2 K φ x = x * g := by
      have h0 := hfix
      rwa [mul_inv_eq_iff_eq_mul] at h0
    have h1 := congrArg (mat 2 K) hfix'
    rw [map_mul, map_mul] at h1
    exact h1
  have hodd : Odd (Nat.card K - 1) := by
    have h1 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    refine ⟨2 ^ (f - 1) - 1, ?_⟩
    have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hK, h2]
    omega
  have hord : orderOf (mat 2 K x) = Nat.card K - 1 := by
    rw [orderOf_injective (mat 2 K) mat_injective x, hx]
  have hrec : ∀ r : K, (mat 2 K x).charpoly.IsRoot r → (mat 2 K x).charpoly.IsRoot r⁻¹ :=
    fun r hr => isRoot_charpoly_inv_of_statedSp x hr
  have hfixroots := fixes_rootsOfUnity_of_conj (by simp) φ hp hφp hodd (dvd_refl _) hord hrec
    hconj
  have hφ1 : φ = 1 := by
    refine RingEquiv.ext fun r => ?_
    change φ r = r
    by_cases hr : r = 0
    · rw [hr, map_zero]
    · refine hfixroots r ?_
      have : Fintype K := Fintype.ofFinite K
      have h1 := FiniteField.pow_card_sub_one_eq_one r hr
      rwa [Nat.card_eq_fintype_card]
  subst hφ1
  refine ⟨g, fun s => ?_⟩
  apply hπ.1
  have h1 := hα s
  rw [hgφ, spInner_mul_fieldAut_proj, map_one, MulAut.one_apply] at h1
  exact h1.symm

end Inner

end CFSG.RankThree.PartOne.CTP

module

public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

@[expose] def GGExcFive (t : StatedLieTag) : Prop :=
  t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6

@[expose] def absTag : StatedLieTag → StatedLieTag
  | .twistedE6 => .E6
  | t => t

theorem det_cartan_F4 : (Tag.cartan .F4).det = 1 :=
  CFSG.LieType.Chevalley.det_cartan_F4

theorem det_cartan_E6 : (Tag.cartan .E6).det = 3 :=
  CFSG.LieType.Chevalley.det_cartan_E6

theorem det_cartan_E7 : (Tag.cartan .E7).det = 2 :=
  CFSG.LieType.Chevalley.det_cartan_E7

theorem det_cartan_E8 : (Tag.cartan .E8).det = 1 :=
  CFSG.LieType.Chevalley.det_cartan_E8

section Bridge

theorem ggU_cartan_F4 (n f : ℕ) : (ggU .F4 n f).D.cartan = Tag.cartan .F4 := rfl

theorem ggU_cartan_E6 (n f : ℕ) : (ggU .E6 n f).D.cartan = Tag.cartan .E6 := rfl

theorem ggU_cartan_E7 (n f : ℕ) : (ggU .E7 n f).D.cartan = Tag.cartan .E7 := rfl

theorem ggU_cartan_E8 (n f : ℕ) : (ggU .E8 n f).D.cartan = Tag.cartan .E8 := rfl

theorem ggU_divisible_F4 (n f : ℕ) : (ggU .F4 n f).D.divisible = ∅ := rfl

theorem ggU_divisible_E6 (n f : ℕ) : (ggU .E6 n f).D.divisible = ∅ := rfl

theorem ggU_divisible_E7 (n f : ℕ) : (ggU .E7 n f).D.divisible = ∅ := rfl

theorem ggU_divisible_E8 (n f : ℕ) : (ggU .E8 n f).D.divisible = ∅ := rfl

theorem ggU_divisible_twistedE6 (n f : ℕ) : (ggU .twistedE6 n f).D.divisible = ∅ := rfl

theorem mem_roots_F4 (n f : ℕ) (v : Fin Tag.F4.rank → ℤ) :
    v ∈ (ggU .F4 n f).D.roots ↔ v ∈ rootFinset Tag.F4 := by
  rw [mem_rootFinset, CFSG.LieType.Chevalley.isRoot_iff_mem_roots]
  rfl

theorem mem_roots_E6 (n f : ℕ) (v : Fin Tag.E6.rank → ℤ) :
    v ∈ (ggU .E6 n f).D.roots ↔ v ∈ rootFinset Tag.E6 := by
  rw [mem_rootFinset, CFSG.LieType.Chevalley.isRoot_iff_mem_roots]
  rfl

theorem mem_roots_E7 (n f : ℕ) (v : Fin Tag.E7.rank → ℤ) :
    v ∈ (ggU .E7 n f).D.roots ↔ v ∈ rootFinset Tag.E7 := by
  rw [mem_rootFinset, CFSG.LieType.Chevalley.isRoot_iff_mem_roots]
  rfl

theorem mem_roots_E8 (n f : ℕ) (v : Fin Tag.E8.rank → ℤ) :
    v ∈ (ggU .E8 n f).D.roots ↔ v ∈ rootFinset Tag.E8 := by
  rw [mem_rootFinset, CFSG.LieType.Chevalley.isRoot_iff_mem_roots]
  rfl

theorem mem_roots_twistedE6 (n f : ℕ) (v : Fin Tag.F4.rank → ℤ) :
    v ∈ (ggU .twistedE6 n f).D.roots ↔ v ∈ rootFinset Tag.F4 := by
  rw [mem_rootFinset, CFSG.LieType.Chevalley.isRoot_iff_mem_roots]
  rfl

private theorem isRootGram_cartan_F4 (S : Matrix (Fin 4) (Fin 4) ℤ)
    (hsym : ∀ i j, S i j = S j i)
    (hdiag : ∀ i j, 2 * S i j = Tag.cartan .F4 i j * S i i)
    (hpos : ∀ i, 0 < S i i) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • (Tag.symmetrizedCartan .F4 : Matrix (Fin 4) (Fin 4) ℤ) := by
  have c01 : Tag.cartan .F4 (0 : Fin 4) (1 : Fin 4) = -1 := by decide +kernel
  have c10 : Tag.cartan .F4 (1 : Fin 4) (0 : Fin 4) = -1 := by decide +kernel
  have c12 : Tag.cartan .F4 (1 : Fin 4) (2 : Fin 4) = -1 := by decide +kernel
  have c21 : Tag.cartan .F4 (2 : Fin 4) (1 : Fin 4) = -2 := by decide +kernel
  have c23 : Tag.cartan .F4 (2 : Fin 4) (3 : Fin 4) = -1 := by decide +kernel
  have c32 : Tag.cartan .F4 (3 : Fin 4) (2 : Fin 4) = -1 := by decide +kernel
  have c02 : Tag.cartan .F4 (0 : Fin 4) (2 : Fin 4) = 0 := by decide +kernel
  have c03 : Tag.cartan .F4 (0 : Fin 4) (3 : Fin 4) = 0 := by decide +kernel
  have c13 : Tag.cartan .F4 (1 : Fin 4) (3 : Fin 4) = 0 := by decide +kernel
  have d01 : 2 * S 0 1 = -S 0 0 := by have h := hdiag 0 1; rw [c01] at h; omega
  have d10 : 2 * S 1 0 = -S 1 1 := by have h := hdiag 1 0; rw [c10] at h; omega
  have d12 : 2 * S 1 2 = -S 1 1 := by have h := hdiag 1 2; rw [c12] at h; omega
  have d21 : 2 * S 2 1 = -2 * S 2 2 := by have h := hdiag 2 1; rw [c21] at h; omega
  have d23 : 2 * S 2 3 = -S 2 2 := by have h := hdiag 2 3; rw [c23] at h; omega
  have d32 : 2 * S 3 2 = -S 3 3 := by have h := hdiag 3 2; rw [c32] at h; omega
  have d02 : 2 * S 0 2 = 0 := by have h := hdiag 0 2; rw [c02] at h; omega
  have d03 : 2 * S 0 3 = 0 := by have h := hdiag 0 3; rw [c03] at h; omega
  have d13 : 2 * S 1 3 = 0 := by have h := hdiag 1 3; rw [c13] at h; omega
  have s01 : S 0 1 = S 1 0 := hsym 0 1
  have s12 : S 1 2 = S 2 1 := hsym 1 2
  have s23 : S 2 3 = S 3 2 := hsym 2 3
  have s02 : S 0 2 = S 2 0 := hsym 0 2
  have s03 : S 0 3 = S 3 0 := hsym 0 3
  have s13 : S 1 3 = S 3 1 := hsym 1 3
  have hp : 0 < S 2 2 := hpos 2
  have e01 : S 0 0 = S 1 1 := by omega
  have e12 : S 1 1 = 2 * S 2 2 := by omega
  have e23 : S 2 2 = S 3 3 := by omega
  have hneg : S 2 3 < 0 := by omega
  let k : ℕ := (-S 2 3).toNat
  have hk : (k : ℤ) = -S 2 3 := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
  have hkpos : 0 < k := by
    have : (0 : ℤ) < (k : ℤ) := by rw [hk]; linarith
    exact_mod_cast this
  have hS22 : S 2 2 = 2 * k := by omega
  have hS00 : S 0 0 = 4 * k := by omega
  have hS11 : S 1 1 = 4 * k := by omega
  have hS33 : S 3 3 = 2 * k := by omega
  have hS01 : S 0 1 = -2 * k := by omega
  have hS10 : S 1 0 = -2 * k := by omega
  have hS12 : S 1 2 = -2 * k := by omega
  have hS21 : S 2 1 = -2 * k := by omega
  have hS23 : S 2 3 = -k := by omega
  have hS32 : S 3 2 = -k := by omega
  have hS02 : S 0 2 = 0 := by omega
  have hS20 : S 2 0 = 0 := by omega
  have hS03 : S 0 3 = 0 := by omega
  have hS30 : S 3 0 = 0 := by omega
  have hS13 : S 1 3 = 0 := by omega
  have hS31 : S 3 1 = 0 := by omega
  let M4 : Matrix (Fin 4) (Fin 4) ℤ := Tag.symmetrizedCartan .F4
  have hM00 : M4 (0 : Fin 4) (0 : Fin 4) = 4 := by decide +kernel
  have hM01 : M4 (0 : Fin 4) (1 : Fin 4) = -2 := by decide +kernel
  have hM02 : M4 (0 : Fin 4) (2 : Fin 4) = 0 := by decide +kernel
  have hM03 : M4 (0 : Fin 4) (3 : Fin 4) = 0 := by decide +kernel
  have hM10 : M4 (1 : Fin 4) (0 : Fin 4) = -2 := by decide +kernel
  have hM11 : M4 (1 : Fin 4) (1 : Fin 4) = 4 := by decide +kernel
  have hM12 : M4 (1 : Fin 4) (2 : Fin 4) = -2 := by decide +kernel
  have hM13 : M4 (1 : Fin 4) (3 : Fin 4) = 0 := by decide +kernel
  have hM20 : M4 (2 : Fin 4) (0 : Fin 4) = 0 := by decide +kernel
  have hM21 : M4 (2 : Fin 4) (1 : Fin 4) = -2 := by decide +kernel
  have hM22 : M4 (2 : Fin 4) (2 : Fin 4) = 2 := by decide +kernel
  have hM23 : M4 (2 : Fin 4) (3 : Fin 4) = -1 := by decide +kernel
  have hM30 : M4 (3 : Fin 4) (0 : Fin 4) = 0 := by decide +kernel
  have hM31 : M4 (3 : Fin 4) (1 : Fin 4) = 0 := by decide +kernel
  have hM32 : M4 (3 : Fin 4) (2 : Fin 4) = -1 := by decide +kernel
  have hM33 : M4 (3 : Fin 4) (3 : Fin 4) = 2 := by decide +kernel
  refine ⟨k, hkpos, ?_⟩
  change S = (k : ℤ) • M4
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
    (first | rw [hS00] | rw [hS01] | rw [hS02] | rw [hS03] | rw [hS10] | rw [hS11] |
      rw [hS12] | rw [hS13] | rw [hS20] | rw [hS21] | rw [hS22] | rw [hS23] |
      rw [hS30] | rw [hS31] | rw [hS32] | rw [hS33]) <;>
    rw [Matrix.smul_apply, smul_eq_mul] <;>
    (first | rw [hM00] | rw [hM01] | rw [hM02] | rw [hM03] | rw [hM10] | rw [hM11] |
      rw [hM12] | rw [hM13] | rw [hM20] | rw [hM21] | rw [hM22] | rw [hM23] |
      rw [hM30] | rw [hM31] | rw [hM32] | rw [hM33]) <;>
    ring

private theorem isRootGram_cartan_E6 (S : Matrix (Fin 6) (Fin 6) ℤ)
    (hsym : ∀ i j, S i j = S j i)
    (hdiag : ∀ i j, 2 * S i j = Tag.cartan .E6 i j * S i i)
    (hpos : ∀ i, 0 < S i i) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E6 := by
  let M : Matrix (Fin 6) (Fin 6) ℤ := Tag.symmetrizedCartan .E6
  have hMEq : M = (Tag.cartan .E6 : Matrix (Fin 6) (Fin 6) ℤ) := by
    show Tag.symmetrizedCartan .E6 = (Tag.cartan .E6 : Matrix (Fin 6) (Fin 6) ℤ)
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  have hME : ∀ i j : Fin 6, M i j = Tag.cartan .E6 i j :=
    fun i j => congrFun (congrFun hMEq i) j
  have hMdiag : ∀ i : Fin 6, M i i = 2 := by
    intro i; rw [hME i i]; simp [Tag.cartan, Tag.cartanE]
  have hMsym : ∀ i j : Fin 6, M i j = M j i := by
    intro i j; rw [hME i j, hME j i]; fin_cases i <;> fin_cases j <;> decide +kernel
  have hMoff : ∀ i j : Fin 6, i ≠ j → M i j = 0 ∨ M i j = -1 := by
    intro i j hij
    rw [hME i j]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide +kernel
  have hadj : ∀ i j : Fin 6, M i j ≠ 0 → S i i = S j j := by
    intro i j hij
    by_cases hne : i = j
    · subst hne; rfl
    · have h1 := hdiag i j; have h2 := hdiag j i; have h3 := hsym i j
      rw [← hME i j] at h1
      rw [← hME j i] at h2
      rcases hMoff i j hne with h0 | hm1
      · exact absurd h0 hij
      · have hji : M j i = -1 := by rw [hMsym j i, hm1]
        rw [hm1] at h1
        rw [hji] at h2
        omega
  have e02 : S 0 0 = S 2 2 := hadj 0 2 (by decide +kernel)
  have e13 : S 1 1 = S 3 3 := hadj 1 3 (by decide +kernel)
  have e23 : S 2 2 = S 3 3 := hadj 2 3 (by decide +kernel)
  have e34 : S 3 3 = S 4 4 := hadj 3 4 (by decide +kernel)
  have e45 : S 4 4 = S 5 5 := hadj 4 5 (by decide +kernel)
  have hdiagall : ∀ i : Fin 6, S i i = S 0 0 := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hM23 : M (2 : Fin 6) (3 : Fin 6) = -1 := by rw [hME]; decide +kernel
  have h23 : 2 * S 2 3 = -S 2 2 := by
    have h := hdiag 2 3; rw [← hME 2 3, hM23] at h; omega
  have hneg : S 2 3 < 0 := by have := hdiagall 2; have := hpos 2; omega
  let k : ℕ := (-S 2 3).toNat
  have hk : (k : ℤ) = -S 2 3 := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
  have hkpos : 0 < k := by
    have : (0 : ℤ) < (k : ℤ) := by rw [hk]; linarith
    exact_mod_cast this
  have hS22 : S 2 2 = 2 * k := by omega
  have hentry : ∀ i j : Fin 6, S i j = (k : ℤ) * M i j := by
    intro i j
    have h := hdiag i j
    rw [← hME i j] at h
    have hii := hdiagall i
    by_cases hij : i = j
    · subst hij
      rw [hMdiag i] at h ⊢
      omega
    · rcases hMoff i j hij with h0 | hm1
      · rw [h0] at h; rw [h0]; omega
      · rw [hm1] at h; rw [hm1]; omega
  refine ⟨k, hkpos, ?_⟩
  change S = (k : ℤ) • M
  ext i j
  rw [hentry i j, Matrix.smul_apply, smul_eq_mul]

private theorem isRootGram_cartan_E7 (S : Matrix (Fin 7) (Fin 7) ℤ)
    (hsym : ∀ i j, S i j = S j i)
    (hdiag : ∀ i j, 2 * S i j = Tag.cartan .E7 i j * S i i)
    (hpos : ∀ i, 0 < S i i) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E7 := by
  let M : Matrix (Fin 7) (Fin 7) ℤ := Tag.symmetrizedCartan .E7
  have hMEq : M = (Tag.cartan .E7 : Matrix (Fin 7) (Fin 7) ℤ) := by
    show Tag.symmetrizedCartan .E7 = (Tag.cartan .E7 : Matrix (Fin 7) (Fin 7) ℤ)
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  have hME : ∀ i j : Fin 7, M i j = Tag.cartan .E7 i j :=
    fun i j => congrFun (congrFun hMEq i) j
  have hMdiag : ∀ i : Fin 7, M i i = 2 := by
    intro i; rw [hME i i]; simp [Tag.cartan, Tag.cartanE]
  have hMsym : ∀ i j : Fin 7, M i j = M j i := by
    intro i j; rw [hME i j, hME j i]; fin_cases i <;> fin_cases j <;> decide +kernel
  have hMoff : ∀ i j : Fin 7, i ≠ j → M i j = 0 ∨ M i j = -1 := by
    intro i j hij
    rw [hME i j]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide +kernel
  have hadj : ∀ i j : Fin 7, M i j ≠ 0 → S i i = S j j := by
    intro i j hij
    by_cases hne : i = j
    · subst hne; rfl
    · have h1 := hdiag i j; have h2 := hdiag j i; have h3 := hsym i j
      rw [← hME i j] at h1
      rw [← hME j i] at h2
      rcases hMoff i j hne with h0 | hm1
      · exact absurd h0 hij
      · have hji : M j i = -1 := by rw [hMsym j i, hm1]
        rw [hm1] at h1
        rw [hji] at h2
        omega
  have e02 : S 0 0 = S 2 2 := hadj 0 2 (by decide +kernel)
  have e13 : S 1 1 = S 3 3 := hadj 1 3 (by decide +kernel)
  have e23 : S 2 2 = S 3 3 := hadj 2 3 (by decide +kernel)
  have e34 : S 3 3 = S 4 4 := hadj 3 4 (by decide +kernel)
  have e45 : S 4 4 = S 5 5 := hadj 4 5 (by decide +kernel)
  have e56 : S 5 5 = S 6 6 := hadj 5 6 (by decide +kernel)
  have hdiagall : ∀ i : Fin 7, S i i = S 0 0 := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hM23 : M (2 : Fin 7) (3 : Fin 7) = -1 := by rw [hME]; decide +kernel
  have h23 : 2 * S 2 3 = -S 2 2 := by
    have h := hdiag 2 3; rw [← hME 2 3, hM23] at h; omega
  have hneg : S 2 3 < 0 := by have := hdiagall 2; have := hpos 2; omega
  let k : ℕ := (-S 2 3).toNat
  have hk : (k : ℤ) = -S 2 3 := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
  have hkpos : 0 < k := by
    have : (0 : ℤ) < (k : ℤ) := by rw [hk]; linarith
    exact_mod_cast this
  have hS22 : S 2 2 = 2 * k := by omega
  have hentry : ∀ i j : Fin 7, S i j = (k : ℤ) * M i j := by
    intro i j
    have h := hdiag i j
    rw [← hME i j] at h
    have hii := hdiagall i
    by_cases hij : i = j
    · subst hij
      rw [hMdiag i] at h ⊢
      omega
    · rcases hMoff i j hij with h0 | hm1
      · rw [h0] at h; rw [h0]; omega
      · rw [hm1] at h; rw [hm1]; omega
  refine ⟨k, hkpos, ?_⟩
  change S = (k : ℤ) • M
  ext i j
  rw [hentry i j, Matrix.smul_apply, smul_eq_mul]

private theorem isRootGram_cartan_E8 (S : Matrix (Fin 8) (Fin 8) ℤ)
    (hsym : ∀ i j, S i j = S j i)
    (hdiag : ∀ i j, 2 * S i j = Tag.cartan .E8 i j * S i i)
    (hpos : ∀ i, 0 < S i i) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E8 := by
  let M : Matrix (Fin 8) (Fin 8) ℤ := Tag.symmetrizedCartan .E8
  have hMEq : M = (Tag.cartan .E8 : Matrix (Fin 8) (Fin 8) ℤ) := by
    show Tag.symmetrizedCartan .E8 = (Tag.cartan .E8 : Matrix (Fin 8) (Fin 8) ℤ)
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  have hME : ∀ i j : Fin 8, M i j = Tag.cartan .E8 i j :=
    fun i j => congrFun (congrFun hMEq i) j
  have hMdiag : ∀ i : Fin 8, M i i = 2 := by
    intro i; rw [hME i i]; simp [Tag.cartan, Tag.cartanE]
  have hMsym : ∀ i j : Fin 8, M i j = M j i := by
    intro i j; rw [hME i j, hME j i]; fin_cases i <;> fin_cases j <;> decide +kernel
  have hMoff : ∀ i j : Fin 8, i ≠ j → M i j = 0 ∨ M i j = -1 := by
    intro i j hij
    rw [hME i j]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide +kernel
  have hadj : ∀ i j : Fin 8, M i j ≠ 0 → S i i = S j j := by
    intro i j hij
    by_cases hne : i = j
    · subst hne; rfl
    · have h1 := hdiag i j; have h2 := hdiag j i; have h3 := hsym i j
      rw [← hME i j] at h1
      rw [← hME j i] at h2
      rcases hMoff i j hne with h0 | hm1
      · exact absurd h0 hij
      · have hji : M j i = -1 := by rw [hMsym j i, hm1]
        rw [hm1] at h1
        rw [hji] at h2
        omega
  have e02 : S 0 0 = S 2 2 := hadj 0 2 (by decide +kernel)
  have e13 : S 1 1 = S 3 3 := hadj 1 3 (by decide +kernel)
  have e23 : S 2 2 = S 3 3 := hadj 2 3 (by decide +kernel)
  have e34 : S 3 3 = S 4 4 := hadj 3 4 (by decide +kernel)
  have e45 : S 4 4 = S 5 5 := hadj 4 5 (by decide +kernel)
  have e56 : S 5 5 = S 6 6 := hadj 5 6 (by decide +kernel)
  have e67 : S 6 6 = S 7 7 := hadj 6 7 (by decide +kernel)
  have hdiagall : ∀ i : Fin 8, S i i = S 0 0 := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hM23 : M (2 : Fin 8) (3 : Fin 8) = -1 := by rw [hME]; decide +kernel
  have h23 : 2 * S 2 3 = -S 2 2 := by
    have h := hdiag 2 3; rw [← hME 2 3, hM23] at h; omega
  have hneg : S 2 3 < 0 := by have := hdiagall 2; have := hpos 2; omega
  let k : ℕ := (-S 2 3).toNat
  have hk : (k : ℤ) = -S 2 3 := Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
  have hkpos : 0 < k := by
    have : (0 : ℤ) < (k : ℤ) := by rw [hk]; linarith
    exact_mod_cast this
  have hS22 : S 2 2 = 2 * k := by omega
  have hentry : ∀ i j : Fin 8, S i j = (k : ℤ) * M i j := by
    intro i j
    have h := hdiag i j
    rw [← hME i j] at h
    have hii := hdiagall i
    by_cases hij : i = j
    · subst hij
      rw [hMdiag i] at h ⊢
      omega
    · rcases hMoff i j hij with h0 | hm1
      · rw [h0] at h; rw [h0]; omega
      · rw [hm1] at h; rw [hm1]; omega
  refine ⟨k, hkpos, ?_⟩
  change S = (k : ℤ) • M
  ext i j
  rw [hentry i j, Matrix.smul_apply, smul_eq_mul]

theorem isRootGram_F4 (n f : ℕ)
    (S : Matrix (Fin (ggU .F4 n f).D.rank) (Fin (ggU .F4 n f).D.rank) ℤ)
    (hS : IsRootGram (ggU .F4 n f).D S) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .F4 := by
  have hd : ∀ i j : Fin 4, 2 * S i j = Tag.cartan .F4 i j * S i i := by
    intro i j
    have h := hS.2.1 i j
    rwa [ggU_cartan_F4 n f] at h
  exact isRootGram_cartan_F4 S (fun i j => hS.1 i j) hd (fun i => hS.2.2 i)

theorem isRootGram_E6 (n f : ℕ)
    (S : Matrix (Fin (ggU .E6 n f).D.rank) (Fin (ggU .E6 n f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 n f).D S) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E6 := by
  have hd : ∀ i j : Fin 6, 2 * S i j = Tag.cartan .E6 i j * S i i := by
    intro i j
    have h := hS.2.1 i j
    rwa [ggU_cartan_E6 n f] at h
  exact isRootGram_cartan_E6 S (fun i j => hS.1 i j) hd (fun i => hS.2.2 i)

theorem isRootGram_E7 (n f : ℕ)
    (S : Matrix (Fin (ggU .E7 n f).D.rank) (Fin (ggU .E7 n f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E7 n f).D S) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E7 := by
  have hd : ∀ i j : Fin 7, 2 * S i j = Tag.cartan .E7 i j * S i i := by
    intro i j
    have h := hS.2.1 i j
    rwa [ggU_cartan_E7 n f] at h
  exact isRootGram_cartan_E7 S (fun i j => hS.1 i j) hd (fun i => hS.2.2 i)

theorem isRootGram_E8 (n f : ℕ)
    (S : Matrix (Fin (ggU .E8 n f).D.rank) (Fin (ggU .E8 n f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E8 n f).D S) :
    ∃ k : ℕ, 0 < k ∧ S = (k : ℤ) • Tag.symmetrizedCartan .E8 := by
  have hd : ∀ i j : Fin 8, 2 * S i j = Tag.cartan .E8 i j * S i i := by
    intro i j
    have h := hS.2.1 i j
    rwa [ggU_cartan_E8 n f] at h
  exact isRootGram_cartan_E8 S (fun i j => hS.1 i j) hd (fun i => hS.2.2 i)

@[expose] def GGLatAdmPlaneExc : Prop :=
  ∀ (τ : StatedLieTag) (f : ℕ), GGExcFive τ →
    ∀ (S : Matrix (Fin (ggU (absTag τ) 6 f).D.rank) (Fin (ggU (absTag τ) 6 f).D.rank) ℤ)
      (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank)),
      IsRootGram (ggU (absTag τ) 6 f).D S → IsDiagAut (ggU (absTag τ) 6 f).D π →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ q2 : Prop, LatAdmPlane (ggU (absTag τ) 6 f).D S p q2 π

end Bridge

end CFSG.StandardType

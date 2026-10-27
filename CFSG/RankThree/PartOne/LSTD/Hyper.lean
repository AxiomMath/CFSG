module

public import CFSG.RankThree.PartOne.LSTD.Lines

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

theorem zeta_ne_one {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) : ζ ≠ 1 := fun h => by
  apply hζ.pow_ne_one_of_pos_of_lt (by norm_num : (1 : ℕ) ≠ 0) (by norm_num : 1 < 5)
  rw [pow_one, h]

theorem zeta_ne_inv {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) : ζ ≠ ζ⁻¹ := fun h => by
  apply hζ.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 < 5)
  rw [pow_two, mul_eq_one_iff_eq_inv]
  exact h

section Hyper

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

theorem mem_centralizer_Jfun_iff {a b : Fin 5} (hab : a ≠ b) {v : Fin 5 → Kˣ}
    (hv : v ∈ torusVec 5 5 K) :
    projU K f (tSU hU h5 v hv) ∈ Subgroup.centralizer (Jfun hU a b : Set _) ↔ v a = v b := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    obtain ⟨k₀, hk₀, hswap⟩ := exists_swap (h := hU) hab
    have hk₀S : k₀ ∈ unitarySU 2 f K 5 := blk_le_unitarySU hab hk₀
    have hmem : projU K f ⟨k₀, hk₀S⟩ ∈ Jfun hU a b := by
      rw [Jfun_of_ne hU hab]
      exact ⟨⟨k₀, hk₀S⟩, hk₀, rfl⟩
    have h1 := hc _ hmem
    rw [← map_mul, ← map_mul] at h1
    obtain ⟨z, hz, hz1⟩ := projU_eq_iff.mp h1
    obtain ⟨c, hc'⟩ := exists_of_mem_scalarsU hz
    have h2 : k₀ * diagU v = diagU v * k₀ * diagU (fun _ => c) := by
      have := congrArg (fun g : ↥(unitarySU 2 f K 5) => (g : GL (Fin 5) K)) hz1
      simpa [Subgroup.coe_mul, hc'] using this
    rw [hswap v] at h2
    have h3 : k₀ * diagU (fun _ => c) = diagU (fun _ => c) * k₀ := by
      apply Units.ext
      simp only [Units.val_mul, diagU_val]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
    rw [mul_assoc (diagU v), h3, ← mul_assoc, diagU_mul] at h2
    have h4 := mul_right_cancel h2
    have h5' : (v ∘ Equiv.swap a b) = v * fun _ => c := diagU_injective h4
    have hthird : ∀ a b : Fin 5, ∃ k : Fin 5, k ≠ a ∧ k ≠ b := by decide
    obtain ⟨k, hka, hkb⟩ := hthird a b
    have h6 := congrFun h5' k
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.swap_apply_of_ne_of_ne hka hkb] at h6
    have hc1 : c = 1 := by
      have : v k * c = v k * 1 := by rw [mul_one]; exact h6.symm
      exact mul_left_cancel this
    have h7 := congrFun h5' a
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.swap_apply_left, hc1, mul_one] at h7
    exact h7.symm
  · intro hvab x hx
    rw [Jfun_of_ne hU hab] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tSU]
    exact blk_comm_diagU hab hvab (show (k : GL (Fin 5) K) ∈ blk hU hab from hk)

include h5 in
theorem hyper_ne_model {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) {a b d e : Fin 5}
    (hab : a ≠ b) (hde : d ≠ e) (hne : ¬ ((a = d ∧ b = e) ∨ (a = e ∧ b = d))) :
    torusBar K f ⊓ Subgroup.centralizer (Jfun hU a b : Set _) ≠
      torusBar K f ⊓ Subgroup.centralizer (Jfun hU d e : Set _) := by
  obtain ⟨n, c, hnc, h1, h2⟩ := exists_witness_pair a b d e hab hde hne
  intro heq
  have hvm : torusElt n c ζ ∈ torusVec 5 5 K := torusElt_mem hnc hζ.pow_eq_one
  have hT : projU K f (tSU hU h5 (torusElt n c ζ) hvm) ∈ torusBar K f :=
    (mem_torusBar_iff hU h5).mpr ⟨_, hvm, rfl⟩
  have hin : projU K f (tSU hU h5 (torusElt n c ζ) hvm) ∈
      torusBar K f ⊓ Subgroup.centralizer (Jfun hU a b : Set _) :=
    ⟨hT, (mem_centralizer_Jfun_iff hU h5 hab hvm).mpr
      ((torusElt_apply_eq_iff (zeta_ne_one hζ) (zeta_ne_inv hζ) hnc a b).mpr h1)⟩
  rw [heq] at hin
  exact h2 ((torusElt_apply_eq_iff (zeta_ne_one hζ) (zeta_ne_inv hζ) hnc d e).mp
    ((mem_centralizer_Jfun_iff hU h5 hde hvm).mp hin.2))

end Hyper

theorem torusVec_chain {v : Fin 5 → Kˣ} (hv : v ∈ torusVec 5 5 K) :
    v = torusElt 0 1 (v 0) * torusElt 1 2 (v 0 * v 1) * torusElt 2 3 (v 0 * v 1 * v 2) *
      torusElt 3 4 (v 0 * v 1 * v 2 * v 3) := by
  have hprod : v 0 * v 1 * v 2 * v 3 * v 4 = 1 := by
    have := hv.2
    rwa [Fin.prod_univ_five] at this
  have h4 : v 4 = (v 0 * v 1 * v 2 * v 3)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  funext i
  fin_cases i <;> simp [torusElt, h4] <;> group

section Gen

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

include h5 in
theorem torusBar_le_lines :
    torusBar K f ≤ (torusBar K f ⊓ Jfun hU 0 1) ⊔ (torusBar K f ⊓ Jfun hU 1 2) ⊔
      (torusBar K f ⊓ Jfun hU 2 3) ⊔ (torusBar K f ⊓ Jfun hU 3 4) := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hx
  have hv5 : ∀ i, v i ^ 5 = 1 := hv.1
  have u1 : (v 0 * v 1) ^ 5 = 1 := by rw [mul_pow, hv5, hv5, one_mul]
  have u2 : (v 0 * v 1 * v 2) ^ 5 = 1 := by rw [mul_pow, u1, hv5, one_mul]
  have u3 : (v 0 * v 1 * v 2 * v 3) ^ 5 = 1 := by rw [mul_pow, u2, hv5, one_mul]
  have e1 : (0 : Fin 5) ≠ 1 := by decide
  have e2 : (1 : Fin 5) ≠ 2 := by decide
  have e3 : (2 : Fin 5) ≠ 3 := by decide
  have e4 : (3 : Fin 5) ≠ 4 := by decide
  have hx : tSU hU h5 v hv = tSU hU h5 _ (torusElt_mem e1 (hv5 0)) *
      tSU hU h5 _ (torusElt_mem e2 u1) * tSU hU h5 _ (torusElt_mem e3 u2) *
      tSU hU h5 _ (torusElt_mem e4 u3) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_tSU, diagU_mul]
    exact congrArg diagU (torusVec_chain hv)
  have mem : ∀ {a b : Fin 5} (hab : a ≠ b) {u : Kˣ} (hu : u ^ 5 = 1),
      projU K f (tSU hU h5 (torusElt a b u) (torusElt_mem hab hu)) ∈
        torusBar K f ⊓ Jfun hU a b := by
    intro a b hab u hu
    refine ⟨(mem_torusBar_iff hU h5).mpr ⟨_, _, rfl⟩, ?_⟩
    rw [Jfun_of_ne hU hab]
    exact ⟨_, lineElt_mem_Bk hU h5 hab hu, rfl⟩
  rw [hx, map_mul, map_mul, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem e1 (hv5 0)))))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem e2 u1)))))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem e3 u2))))
    (Subgroup.mem_sup_right (mem e4 u3))

theorem Jfun_le_centralizer_of_disjoint {a b d e : Fin 5} (hab : a ≠ b) (hde : d ≠ e)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) :
    Jfun hU a b ≤ Subgroup.centralizer (Jfun hU d e : Set (StatedProj (unitarySU 2 f K 5))) := by
  intro x hx
  rw [Jfun_of_ne hU hab] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Jfun_of_ne hU hde] at hy
  obtain ⟨l, hl, rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (blk_comm_of_disjoint hab hde had hae hbd hbe
    (show (k : GL (Fin 5) K) ∈ blk hU hab from hk)
    (show (l : GL (Fin 5) K) ∈ blk hU hde from hl)).symm

end Gen

end CFSG.RankThree.PartOne.LSTD

module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessBlock
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessStep1
import Mathlib.Tactic.NormNum.Prime
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessRot
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessStep2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {F : Type} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

@[expose] noncomputable def primeMap (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    GL (Fin 3) (ZMod p) →* GL (Fin 3) F :=
  Units.map (ZMod.castHom (dvd_refl p) F).mapMatrix.toMonoidHom

theorem coe_primeMap (g : GL (Fin 3) (ZMod p)) :
    ((primeMap F p g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)).map (ZMod.castHom (dvd_refl p) F) :=
  rfl

theorem primeMap_hessT (i : Fin 3) : primeMap F p (hessT i) = hessT i := by
  apply Units.ext
  rw [coe_primeMap, coe_hessT, coe_hessT]
  ext a b
  simp only [Matrix.map_apply, hessTMat, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem primeMap_hessS0 (hp3 : p ≠ 3) :
    primeMap F p (hessS0 (three_ne_zero_of (K := ZMod p) hp3)) =
      hessS0 (three_ne_zero_of (K := F) hp3) := by
  apply Units.ext
  rw [coe_primeMap, coe_hessS0, coe_hessS0]
  ext a b
  simp only [Matrix.map_apply, hessS0Mat]
  split_ifs <;> simp only [map_sub, map_div₀, map_ofNat, map_one, map_zero]

theorem primeMap_hessC : primeMap F p hessC = hessC := by
  apply Units.ext
  rw [coe_primeMap, coe_hessC, coe_hessC]
  ext a b
  simp only [Matrix.map_apply, hessCMat]
  split_ifs <;> simp

theorem primeMap_hessR_le {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hp3 : p ≠ 3) :
    (hessR hp3).map (primeMap F p) ≤ hessH hω (three_ne_zero_of hp3) := by
  rw [hessR, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with ⟨i, rfl⟩ | hy
  · rw [primeMap_hessT]
    exact hessT_mem_hessH hω _ i
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [primeMap_hessS0 hp3, hessS0_eq ω hω]
    exact hessS_mem_hessH hω _ 0

theorem primeMap_mem_hessH {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    {g : GL (Fin 3) (ZMod p)} (hg : g ∈ omegaGL (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) :
    primeMap F p g ∈ hessH hω (three_ne_zero_of hp3) :=
  primeMap_hessR_le hω hp3 ⟨g, omegaGL_le_hessR hp2 hp3 hp5 hp7 hp11 hg, rfl⟩

section Block

variable {k₀ : Type} [Field k₀] (ψ : k₀ →+* F)

theorem coe_blockHom_rot2 {c s : k₀} (h : c ^ 2 + s ^ 2 = 1) :
    ((blockHom ψ (rot2 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      hessRotMat (ψ c) (ψ s) := by
  rw [coe_blockHom, coe_rot2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, hessRotMat]

theorem coe_blockHom_delta2 {ω₀ : k₀} (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) :
    ((blockHom ψ (delta2 hω₀) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      hessDeltaMat (ψ ω₀) := by
  rw [coe_blockHom, coe_delta2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, hessDeltaMat, Matrix.diagonal]

theorem blockHom_neg_one : blockHom ψ (-1) = hessT 0 := by
  apply Units.ext
  rw [coe_blockHom, coe_hessT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, hessTMat, Matrix.diagonal]

theorem coe_blockHom_z2 {ω₀ : k₀} (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) (h2₀ : (2 : k₀) ≠ 0) :
    ((blockHom ψ (z2 hω₀ h2₀) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      hessZMat (ψ ω₀) := by
  rw [coe_blockHom, coe_z2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, hessZMat, map_div₀, map_ofNat]

end Block

theorem hessPhi_mem_hessH_of_z {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {k₀ : Type} [Field k₀] (ψ : k₀ →+* F) {ω₀ : k₀}
    (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) (hψ : ψ ω₀ = ω) (h2₀ : (2 : k₀) ≠ 0) {r : SL(2, k₀)}
    (hr : blockHom ψ r ∈ hessH hω h3) (hC : (hessC : GL (Fin 3) F) ∈ hessH hω h3)
    (hz : z2 hω₀ h2₀ ∈ Subgroup.closure ({r, delta2 hω₀, -1} : Set SL(2, k₀))) :
    hessPhi hω h3 ∈ hessH hω h3 := by
  have hδ : blockHom ψ (delta2 hω₀) ∈ hessH hω h3 := by
    have he : blockHom ψ (delta2 hω₀) = hessPhi hω h3 * hessC * (hessPhi hω h3)⁻¹ := by
      apply Units.ext
      rw [coe_blockHom_delta2, hψ, hessPhi_conj_hessC]
    rw [he]
    exact hessPhi_conj_mem_hessH hω h3 hC
  have hle : (Subgroup.closure ({r, delta2 hω₀, -1} : Set SL(2, k₀))).map (blockHom ψ) ≤
      hessH hω h3 := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl | rfl
    · exact hr
    · exact hδ
    · rw [blockHom_neg_one]
      exact hessT_mem_hessH hω h3 0
  have hz' : hessZ hω h2 ∈ hessH hω h3 := by
    have he : blockHom ψ (z2 hω₀ h2₀) = hessZ hω h2 := by
      apply Units.ext
      rw [coe_blockHom_z2, hψ, coe_hessZ]
    rw [← he]
    exact hle ⟨_, hz, rfl⟩
  rw [hessPhi_eq hω h2 h3]
  exact mul_mem (mul_mem hz' (hessPhi_conj_mem_hessH hω h3 hz')) hz'

theorem map_hessRotMat {K L : Type*} [Field K] [Field L] (f : K →+* L) (a b : K) :
    (hessRotMat a b).map f = hessRotMat (f a) (f b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessRotMat]

theorem blockHom_rotA_mem {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) (hp11 : p ≠ 11)
    {k₀ : Type} [Field k₀] (ψ : k₀ →+* F) (h5₀ : (5 : k₀) ≠ 0) :
    blockHom ψ (rotA h5₀) ∈ hessH hω (three_ne_zero_of hp3) := by
  have h5Z : (5 : ZMod p) ≠ 0 := by
    have := prime_ne_zero_of (k := ZMod p) Nat.prime_five hp5
    exact_mod_cast this
  have h5F : (5 : F) ≠ 0 := by
    have := prime_ne_zero_of (k := F) Nat.prime_five hp5
    exact_mod_cast this
  have hab : (3 / 5 : ZMod p) ^ 2 + (4 / 5) ^ 2 = 1 := by
    have h25 : (25 : ZMod p) ≠ 0 := twentyfive_ne_zero h5Z
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by
      rw [show (5 : ZMod p) ^ 2 = 25 by norm_num]; exact h25)]
    norm_num
  have hmem := primeMap_mem_hessH (F := F) hω hp2 hp3 hp5 hp7 hp11 (hessRot_sq_mem_omegaGL hab)
  have h25F := twentyfive_ne_zero h5F
  convert hmem using 1
  apply Units.ext
  rw [rotA, coe_blockHom_rot2, coe_primeMap, Units.val_mul, coe_hessRot,
    hessRotMat_mul, map_hessRotMat]
  congr 1
  · simp only [map_div₀, map_neg, map_ofNat, map_sub, map_mul]
    field_simp
    norm_num
  · simp only [map_div₀, map_neg, map_ofNat, map_add, map_mul]
    field_simp
    norm_num

theorem blockHom_rotB_mem {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) (hp11 : p ≠ 11) (hp13 : p ≠ 13)
    {k₀ : Type} [Field k₀] (ψ : k₀ →+* F) (h13₀ : (13 : k₀) ≠ 0) :
    blockHom ψ (rotB h13₀) ∈ hessH hω (three_ne_zero_of hp3) := by
  have h13Z : (13 : ZMod p) ≠ 0 := by
    have := prime_ne_zero_of (k := ZMod p) (by norm_num : Nat.Prime 13) hp13
    exact_mod_cast this
  have h13F : (13 : F) ≠ 0 := by
    have := prime_ne_zero_of (k := F) (by norm_num : Nat.Prime 13) hp13
    exact_mod_cast this
  have hab : (5 / 13 : ZMod p) ^ 2 + (12 / 13) ^ 2 = 1 := by
    have h169 : (169 : ZMod p) ≠ 0 := oneSixtyNine_ne_zero h13Z
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by
      rw [show (13 : ZMod p) ^ 2 = 169 by norm_num]; exact h169)]
    norm_num
  have hmem := primeMap_mem_hessH (F := F) hω hp2 hp3 hp5 hp7 hp11 (hessRot_sq_mem_omegaGL hab)
  have h169F := oneSixtyNine_ne_zero h13F
  convert hmem using 1
  apply Units.ext
  rw [rotB, coe_blockHom_rot2, coe_primeMap, Units.val_mul, coe_hessRot,
    hessRotMat_mul, map_hessRotMat]
  congr 1
  · simp only [map_div₀, map_neg, map_ofNat, map_sub, map_mul]
    field_simp
    norm_num
  · simp only [map_div₀, map_neg, map_ofNat, map_add, map_mul]
    field_simp
    norm_num

theorem hessC_mem_hessH {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) (hp11 : p ≠ 11) :
    (hessC : GL (Fin 3) F) ∈ hessH hω (three_ne_zero_of hp3) := by
  have := primeMap_mem_hessH (F := F) hω hp2 hp3 hp5 hp7 hp11 hessC_mem_omegaGL
  rwa [primeMap_hessC] at this

section Step2

variable {k₀ : Type} [Field k₀] [Finite k₀] {f : ℕ} [CharP k₀ p]

theorem z2_mem_closure_rotA (hk : Nat.card k₀ = p ^ f)
    (hp23 : 23 ≤ p) (hbad : p ∉ ([31, 41, 79, 193] : List ℕ)) {ω₀ : k₀}
    (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) (h2₀ : (2 : k₀) ≠ 0) (h3₀ : (3 : k₀) ≠ 0) (h5₀ : (5 : k₀) ≠ 0)
    (G : Subgroup SL(2, k₀)) (hG : Nat.card G ≤ p * (p ^ 2 - 1)) (hrG : rotA h5₀ ∈ G)
    (hδG : delta2 hω₀ ∈ G) (hnG : (-1 : SL(2, k₀)) ∈ G) (hzG : z2 hω₀ h2₀ ∈ G) :
    z2 hω₀ h2₀ ∈ Subgroup.closure ({rotA h5₀, delta2 hω₀, -1} : Set SL(2, k₀)) := by
  have hpA : p ∉ ([2, 3, 7, 11, 13, 17, 19, 31, 41, 79] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad ⊢
    omega
  have hpT : p ∉ ([2, 3, 193] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad ⊢
    omega
  rw [closure_eq_of_dickson (by omega) hk G hG hrG hδG hnG (delta2_pow_three hω₀)
    (delta2_ne_one hω₀ h3₀) (fun j hj1 hj5 => rotA_pow_ne h5₀ hpA hj1 hj5)
    (rotA_trace_ne hω₀ h5₀ hpT).1 (rotA_trace_ne hω₀ h5₀ hpT).2]
  exact hzG

theorem z2_mem_closure_rotB (hk : Nat.card k₀ = p ^ f)
    (hbad : p ∈ ([31, 41, 79, 193] : List ℕ)) {ω₀ : k₀}
    (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) (h2₀ : (2 : k₀) ≠ 0) (h3₀ : (3 : k₀) ≠ 0)
    (h13₀ : (13 : k₀) ≠ 0)
    (G : Subgroup SL(2, k₀)) (hG : Nat.card G ≤ p * (p ^ 2 - 1)) (hrG : rotB h13₀ ∈ G)
    (hδG : delta2 hω₀ ∈ G) (hnG : (-1 : SL(2, k₀)) ∈ G) (hzG : z2 hω₀ h2₀ ∈ G) :
    z2 hω₀ h2₀ ∈ Subgroup.closure ({rotB h13₀, delta2 hω₀, -1} : Set SL(2, k₀)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad
  have hpB : p ∉ ([2, 3, 5, 7, 11, 17, 19, 23, 37, 61, 199, 239, 719] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hpT : p ∉ ([2, 3, 5, 17761] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [closure_eq_of_dickson (by omega) hk G hG hrG hδG hnG (delta2_pow_three hω₀)
    (delta2_ne_one hω₀ h3₀) (fun j hj1 hj5 => rotB_pow_ne h13₀ hpB hj1 hj5)
    (rotB_trace_ne hω₀ h13₀ hpT).1 (rotB_trace_ne hω₀ h13₀ hpT).2]
  exact hzG

theorem exists_rot_z2_mem_closure {F : Type} [Field F] [CharP F p]
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hk : Nat.card k₀ = p ^ f) (hp23 : 23 ≤ p) (ψ : k₀ →+* F)
    {ω₀ : k₀} (hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0) (h2₀ : (2 : k₀) ≠ 0) (h3₀ : (3 : k₀) ≠ 0)
    (h5₀ : (5 : k₀) ≠ 0) (h13₀ : (13 : k₀) ≠ 0)
    (G : Subgroup SL(2, k₀)) (hG : Nat.card G ≤ p * (p ^ 2 - 1)) (hAG : rotA h5₀ ∈ G)
    (hBG : rotB h13₀ ∈ G) (hδG : delta2 hω₀ ∈ G) (hnG : (-1 : SL(2, k₀)) ∈ G)
    (hzG : z2 hω₀ h2₀ ∈ G) :
    ∃ r : SL(2, k₀), blockHom ψ r ∈ hessH hω (three_ne_zero_of (p := p) (by omega)) ∧
      z2 hω₀ h2₀ ∈ Subgroup.closure ({r, delta2 hω₀, -1} : Set SL(2, k₀)) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hp5 : p ≠ 5 := by omega
  have hp7 : p ≠ 7 := by omega
  have hp11 : p ≠ 11 := by omega
  have hp13 : p ≠ 13 := by omega
  by_cases hbad : p ∈ ([31, 41, 79, 193] : List ℕ)
  · exact ⟨rotB h13₀, blockHom_rotB_mem hω hp2 hp3 hp5 hp7 hp11 hp13 ψ h13₀,
      z2_mem_closure_rotB hk hbad hω₀ h2₀ h3₀ h13₀ G hG hBG hδG hnG hzG⟩
  · exact ⟨rotA h5₀, blockHom_rotA_mem hω hp2 hp3 hp5 hp7 hp11 ψ h5₀,
      z2_mem_closure_rotA hk hp23 hbad hω₀ h2₀ h3₀ h5₀ G hG hAG hδG hnG hzG⟩

end Step2

end CFSG.RankThree.PartTwo.Sec4.Ronan148B

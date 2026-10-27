module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA7
public import CFSG.ClassicalInvolution.AschTight.S19MInv
public import CFSG.Quasithin.Vol2.Ch3E213MOLA2
public import CFSG.Quasithin.Vol2.Ch3E213MOLA4

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  {E : Type} [Group E]

theorem uni_commute_two (hF : Nat.card F = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (θ : Phan.Su F p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su F p f 3)) :
    ∀ y ∈ Subgroup.centralizer ({θ (Models.rootInvSU F p f (n := 3) (by norm_num))} : Set E),
      ∀ a ∈ (rootU F p f).map θ, ∀ b ∈ (rootU F p f).map θ, a * b ≠ b * a →
      y * a = a * y → y * b = b * y →
      y ∈ Subgroup.centralizer (((rootU F p f).map θ : Subgroup E) : Set E) := by
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  have hst := Models.isLongRootSU2_standard (K := F) (p := p) (f := f) (by norm_num : 2 ≤ 3)
  intro y hy
  rw [centralizer_map_eq_of_isLongRootSU2 hF hp hq (le_refl 3) hθ hker (Or.inl (by norm_num))
    hst] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩ hab hxa hxb
  set X := (((x : Phan.Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hX
  have hXB : IsBlockDiag X := by
    refine isBlockDiag_of_commute_negBlock h2 X ?_
    have h1 := congrArg (fun g : Phan.Su F p f 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    simp only [Subgroup.coe_mul, Units.val_mul, coe_rootInvSU_three] at h1
    exact h1
  obtain ⟨g02, g12, g20, g21⟩ := hXB
  have hR : ∀ C : Phan.Su F p f 2, θ x * θ (Phan.blockEmb F p f 3 2 0 (by norm_num) C) =
      θ (Phan.blockEmb F p f 3 2 0 (by norm_num) C) * θ x →
      x * Phan.blockEmb F p f 3 2 0 (by norm_num) C =
        Phan.blockEmb F p f 3 2 0 (by norm_num) C * x := by
    intro C hc
    set r := Phan.blockEmb F p f 3 2 0 (by norm_num) C
    have hr : r ∈ rootU F p f := ⟨C, rfl⟩
    have hcl := Models.isClassicalSL2_rootSU2 (K := F) (p := p) (f := f) hF hp
      (by norm_num : 2 ≤ 3)
    have hN := hcl.centralizer_le_normalizer hx
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ rootU F p f :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN r).mp hr) (Subgroup.inv_mem _ hr)
    have h3 : x * r * x⁻¹ * r⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h4 := eq_one_of_mem_ker_of_isLongRootSU2 hF hp hq (le_refl 3) hst hker _ h1 h3
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [h4, one_mul]
  set Y : Matrix (Fin 2) (Fin 2) F := !![X 0 0, X 0 1; X 1 0, X 1 1] with hY
  have hmat : ∀ C : Phan.Su F p f 2,
      x * Phan.blockEmb F p f 3 2 0 (by norm_num) C =
        Phan.blockEmb F p f 3 2 0 (by norm_num) C * x →
      Y * ((C : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((C : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Y := by
    intro C hC
    have h1 := congrArg (fun g : Phan.Su F p f 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hC
    simp only [Subgroup.coe_mul, Units.val_mul, coe_blockEmb3] at h1
    have e00 := congrFun (congrFun h1 0) 0
    have e01 := congrFun (congrFun h1 0) 1
    have e10 := congrFun (congrFun h1 1) 0
    have e11 := congrFun (congrFun h1 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, ← hX, g02, g12, g20, g21] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hY, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination e00
        | linear_combination e01
        | linear_combination e10
        | linear_combination e11
  have hAB : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((B : GL (Fin 2) F) : Matrix _ _ F) ≠
      ((B : GL (Fin 2) F) : Matrix _ _ F) * ((A : GL (Fin 2) F) : Matrix _ _ F) := fun h => hab (by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul, h])))
  obtain ⟨y01, y10, y0011⟩ := isScalar_of_commute_two (hmat A (hR A hxa)) (hmat B (hR B hxb)) hAB
  simp only [hY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at y01 y10 y0011
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨_, ⟨C, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_blockEmb3, ← hX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, g02, g12, g20, g21, y01, y10, ← y0011] <;> ring

theorem uni_conj_inv (hF : Nat.card F = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (θ : Phan.Su F p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su F p f 3)) :
    ∀ t : E, orderOf t = 2 →
      ∃ g : E, t = g * θ (Models.rootInvSU F p f (n := 3) (by norm_num)) * g⁻¹ := by
  intro t ht
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  obtain ⟨y₀, rfl⟩ := hθ t
  have ht2 : θ y₀ * θ y₀ = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hy₀ : y₀ * y₀ ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, ht2]
  have hy2 : y₀ ^ 3 * y₀ ^ 3 = 1 := by
    rw [← pow_add, show 3 + 3 = 2 * 3 from rfl, pow_mul, pow_two]
    exact center_pow_three_su3 hF hq _ (hker hy₀)
  have hθy : θ (y₀ ^ 3) = θ y₀ := by
    rw [map_pow, pow_succ, pow_two, ht2, one_mul]
  have hy1 : y₀ ^ 3 ≠ 1 := fun h => by
    have h1 : θ y₀ = 1 := by rw [← hθy, h, map_one]
    rw [h1, orderOf_one] at ht
    omega
  have hcl := Models.isClassicalSL2_rootSU2 (K := F) (p := p) (f := f) hF hp
    (by norm_num : 2 ≤ 3)
  have hz2 : Models.rootInvSU F p f (n := 3) (by norm_num) *
      Models.rootInvSU F p f (n := 3) (by norm_num) = 1 := by
    have h1 := pow_orderOf_eq_one (Models.rootInvSU F p f (n := 3) (by norm_num))
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hz1 : Models.rootInvSU F p f (n := 3) (by norm_num) ≠ 1 := fun h => by
    have h1 := hcl.orderOf_eq_two
    rw [h, orderOf_one] at h1
    omega
  obtain ⟨g, hg⟩ := Disconnected.AschTight.S19M.involutionsConj_su3 hF h2 _ _ hz2 hy2 hz1 hy1
  refine ⟨θ g, ?_⟩
  rw [← hθy, ← hg, map_mul, map_mul, map_inv]

variable [Finite E]

theorem uni_kfact (hF : Nat.card F = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) (θ : Phan.Su F p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su F p f 3)) (S : Sylow 2 E) :
    ∃ z' : E, orderOf z' = 2 ∧ E2P.zOf (S : Subgroup E) = Subgroup.zpowers z' ∧
      (∀ Q : Subgroup E, Q ≤ Subgroup.centralizer ({z'} : Set E) → IsPGroup 2 Q →
        Subgroup.centralizer ({z'} : Set E) ≤ Subgroup.normalizer (Q : Set E) →
        Q ≤ Subgroup.zpowers z') ∧
      ∀ v : MulAut E, orderOf v = 2 →
        (∀ x ∈ Subgroup.centralizer ({z'} : Set E), v x * x⁻¹ ∈ Subgroup.zpowers z') →
        v ∈ (MulAut.conj : E →* MulAut E).range := by
  have hodd := Models.odd_natCard_fixedSubfield hF hp
  have h4 : 4 ≤ Nat.card (fixedSubfield F p f) := by rw [card_fixedSubfield hF]; omega
  have hL : IsClassicalSL2 (fixedSubfield F p f) ((rootU F p f).map θ)
      (θ (Models.rootInvSU F p f (n := 3) (by norm_num))) :=
    IsLongRootSU2Image.isClassicalSL2 hF hp hq (le_refl 3) hθ hker (Or.inl (by norm_num))
      ⟨_, _, Models.isLongRootSU2_standard (K := F) (p := p) (f := f) (by norm_num : 2 ≤ 3),
        rfl, rfl⟩
  refine kfact_of_classical hodd h4 hL (uni_centralizer_two hF hp hq hq4 θ hθ hker)
    (uni_commute_two hF hp hq θ hθ hker) (fun v hv2 hfix => ?_)
    (uni_conj_inv hF hp hq θ hθ hker) S
  obtain ⟨y, hy⟩ := inner_of_fix_rootU hF hp hq θ hθ hker hv2 fun A =>
    hfix _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact ⟨y, hy.symm⟩

end CFSG.Quasithin.Ch3E213M.OLA

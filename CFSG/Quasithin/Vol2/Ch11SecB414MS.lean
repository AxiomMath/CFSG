module

public import CFSG.Quasithin.Vol2.Ch11SecB414MQ

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {F : Type} [Field F]

theorem twAdj_one (k : ℕ) (M : Matrix (Fin 3) (Fin 3) F) : twAdj k 1 M = M := by
  simp [twAdj]

theorem twAdj_mul (k : ℕ) (g h : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdj k (g * h) M = twAdj k g (twAdj k h M) := by
  rw [twAdj, twAdj, twAdj, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.det_mul,
    mul_pow, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    mul_comm ((g : Matrix (Fin 3) (Fin 3) F).det ^ k)]
  congr 1
  simp only [Matrix.mul_assoc]

@[expose] def stabTw (k : ℕ) (M : Matrix (Fin 3) (Fin 3) F) : Subgroup (GL (Fin 3) F) where
  carrier := {g | twAdj k g M = M}
  one_mem' := twAdj_one k M
  mul_mem' := fun {g h} hg hh => by
    show twAdj k (g * h) M = M
    rw [twAdj_mul, show twAdj k h M = M from hh, show twAdj k g M = M from hg]
  inv_mem' := fun {g} hg => by
    show twAdj k g⁻¹ M = M
    conv_lhs => rw [← show twAdj k g M = M from hg]
    rw [← twAdj_mul, inv_mul_cancel, twAdj_one]

@[expose] def facE (k : ℕ) (i j : Fin 3) : ℕ :=
  k + (if i = 0 then 1 else 0) + (if j = 0 then 2 else 0)

theorem entry_eq_zero_of_fixed {k : ℕ} {c : Fˣ} {M : Matrix (Fin 3) (Fin 3) F}
    (h : twAdj k (dgHom c) M = M) (i j : Fin 3)
    (hf : (c : F) ^ k * dgv (c : F) i * dgv ((c⁻¹ : Fˣ) : F) j ≠ 1) : M i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [twAdj_dg_apply] at e
  have : ((c : F) ^ k * dgv (c : F) i * dgv ((c⁻¹ : Fˣ) : F) j - 1) * M i j = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hf)

theorem twAdj_dg_eq_self {k : ℕ} {c : Fˣ} {M : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ i j, M i j ≠ 0 → (c : F) ^ k * dgv (c : F) i * dgv ((c⁻¹ : Fˣ) : F) j = 1) :
    twAdj k (dgHom c) M = M := by
  ext i j
  rw [twAdj_dg_apply]
  by_cases hM : M i j = 0
  · rw [hM]
    ring
  · linear_combination M i j * h i j hM

variable (hF : Nat.card F = 4)
include hF

theorem inv_eq_sq (c : Fˣ) : ((c⁻¹ : Fˣ) : F) = (c : F) ^ 2 := by
  rw [Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact pow_three_eq_one hF c.ne_zero)

theorem fac_eq_pow (c : Fˣ) (k : ℕ) (i j : Fin 3) :
    (c : F) ^ k * dgv (c : F) i * dgv ((c⁻¹ : Fˣ) : F) j = (c : F) ^ (facE k i j % 3) := by
  have h3 : (c : F) ^ 3 = 1 := pow_three_eq_one hF c.ne_zero
  have hmod : ∀ n : ℕ, (c : F) ^ n = (c : F) ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [← hmod, inv_eq_sq hF, facE]
  fin_cases i <;> fin_cases j <;> simp [pow_succ] <;> ring

theorem fixed_iff {ν : Fˣ} (hν : ν ≠ 1) (k : ℕ) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdj k (dgHom ν) M = M ↔ ∀ i j, facE k i j % 3 ≠ 0 → M i j = 0 := by
  have h3 := pow_three_eq_one hF ν.ne_zero
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  constructor
  · intro h i j hij
    refine entry_eq_zero_of_fixed h i j ?_
    rw [fac_eq_pow hF]
    exact pow_ne_one_of_lt_three h3 hν1 (Nat.mod_lt _ (by norm_num)) hij
  · intro h
    refine twAdj_dg_eq_self fun i j hM => ?_
    rw [fac_eq_pow hF]
    by_cases hij : facE k i j % 3 = 0
    · rw [hij, pow_zero]
    · exact absurd (h i j hij) hM

omit hF

abbrev IsBlock (A : Matrix (Fin 3) (Fin 3) F) : Prop :=
  A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 0 = 0 ∧ A 2 0 = 0

theorem block_comm_dg {A : SpecialLinearGroup (Fin 3) F}
    (hA : IsBlock (A : Matrix (Fin 3) (Fin 3) F)) (c : Fˣ) :
    SpecialLinearGroup.toGL A * dgHom c = dgHom c * SpecialLinearGroup.toGL A := by
  obtain ⟨h01, h02, h10, h20⟩ := hA
  apply Units.ext
  simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_dgHom]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, mul_comm]

theorem mk_mem_Ptheta_zero {A : SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ Ptheta F 0 := by
  refine CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.mk_mem_Ptheta (j := 0)
    (mem_stabilizer_of_map_le ?_)
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ flagSpace 3 F 1 := hw
  rw [mem_flagSpace] at hw'
  show _ ∈ flagSpace 3 F 1
  rw [mem_flagSpace]
  have h1 := hw' 1 (by simp)
  have h2 := hw' 2 (by simp)
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h10, h20]

variable {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F}
  (m : Model Γ V Z F k α)

theorem Model.comm_mem_iff {γ : ↥Γ} {g : GL (Fin 3) F} (hg : ProjGenLinGroup.mk g = α γ)
    {v : G} (hv : v ∈ V) :
    (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z ↔
      twAdj k g (Multiplicative.toAdd (m.β ⟨v, hv⟩)) = Multiplicative.toAdd (m.β ⟨v, hv⟩) := by
  have hmem : (γ : G) * v * (γ : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (m.normV γ.2) v).mp hv
  have hmem' : (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ V := V.mul_mem hmem (V.inv_mem hv)
  have e : (⟨_, hmem'⟩ : ↥V) = ⟨_, hmem⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := rfl
  refine (m.toAdd_eq_zero ⟨_, hmem'⟩).symm.trans ?_
  rw [e, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_inv, m.act γ ⟨v, hv⟩ ⟨_, hmem⟩ rfl g hg,
    ← sub_eq_add_neg, sub_eq_zero]

omit m in
theorem exists_gen {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν))) :
    ∃ x₁ : ↥Γ, (x₁ : G) ∈ X ∧ α x₁ = ProjGenLinGroup.mk (dgHom ν) := by
  have h : ProjGenLinGroup.mk (dgHom ν) ∈ (X.subgroupOf Γ).map α := by
    rw [hX]
    exact Subgroup.mem_zpowers _
  obtain ⟨x₁, hx₁, h1⟩ := h
  exact ⟨x₁, Subgroup.mem_subgroupOf.mp hx₁, h1⟩

theorem Model.isFixedMod_iff (hXΓ : X ≤ Γ) {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {v : G} (hv : v ∈ V) :
    IsFixedMod X Z v ↔ twAdj k (dgHom ν) (Multiplicative.toAdd (m.β ⟨v, hv⟩)) =
      Multiplicative.toAdd (m.β ⟨v, hv⟩) := by
  constructor
  · intro h
    obtain ⟨x₁, hx₁X, hx₁⟩ := exists_gen hX
    exact (m.comm_mem_iff hx₁.symm hv).mp (h _ hx₁X)
  · intro h x hx
    have hα : α ⟨x, hXΓ hx⟩ ∈ Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)) := by
      rw [← hX]
      exact ⟨⟨x, hXΓ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hα
    have hg : ProjGenLinGroup.mk (dgHom ν ^ z) = α ⟨x, hXΓ hx⟩ := by rw [map_zpow, hz]
    exact (m.comm_mem_iff (γ := ⟨x, hXΓ hx⟩) hg hv).mpr
      (Subgroup.zpow_mem (stabTw k _) (show dgHom ν ∈ stabTw k _ from h) z)

omit m in
theorem exists_block_of_isCentMod (hLΓ : L ≤ Γ)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ} (hν : ν ≠ 1)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {l : G} (hl : l ∈ L) (hc : IsCentMod X (α.ker.map Γ.subtype) l) :
    ∃ A : SpecialLinearGroup (Fin 3) F, IsBlock (A : Matrix (Fin 3) (Fin 3) F) ∧
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) = α ⟨l, hLΓ hl⟩ := by
  obtain ⟨A, h10, h20, hA⟩ := exists_rep_of_mem_L hLΓ hL hl
  obtain ⟨x₁, hx₁X, hx₁⟩ := exists_gen hX
  obtain ⟨δ, hδ, hδe⟩ := hc _ hx₁X
  have hδ' : δ = ⟨l, hLΓ hl⟩ * x₁ * (⟨l, hLΓ hl⟩ : ↥Γ)⁻¹ * x₁⁻¹ := Subtype.ext hδe
  have hαδ : α δ = ProjGenLinGroup.mk (SpecialLinearGroup.toGL A * dgHom ν *
      (SpecialLinearGroup.toGL A)⁻¹ * (dgHom ν)⁻¹) := by
    rw [hδ', map_mul, map_mul, map_mul, map_inv, map_inv, ← hA, hx₁]
    simp only [map_mul, map_inv]
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hαδ, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hδ
  obtain ⟨u, hu⟩ := hδ
  have hu' : SpecialLinearGroup.toGL A * dgHom ν =
      GeneralLinearGroup.scalar (Fin 3) u * (dgHom ν * SpecialLinearGroup.toGL A) := by
    rw [hu]
    group
  have hm := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hu'
  simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_dgHom,
    GeneralLinearGroup.coe_scalar] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.scalar_apply] at e00 e01 e02
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.prop
  rw [det_of_par h10 h20] at hdet
  have hA0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have hν0 : (ν : F) ≠ 0 := ν.ne_zero
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  have hu1 : (u : F) = 1 := by
    have : ((u : F) - 1) * ((ν : F) * (A : Matrix (Fin 3) (Fin 3) F) 0 0) = 0 := by
      linear_combination -e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero hν0 hA0))
  rw [hu1] at e01 e02
  refine ⟨A, ⟨?_, ?_, h10, h20⟩, hA⟩
  · have : ((ν : F) - 1) * (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν1)
  · have : ((ν : F) - 1) * (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination -e02
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν1)

omit m in
theorem exists_isCentMod_of_block (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {A : SpecialLinearGroup (Fin 3) F} (hA : IsBlock (A : Matrix (Fin 3) (Fin 3) F)) :
    ∃ l : G, ∃ hl : l ∈ L, IsCentMod X (α.ker.map Γ.subtype) l ∧
      α ⟨l, hLΓ hl⟩ = ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) := by
  have h := mk_mem_Ptheta_zero hA.2.2.1 hA.2.2.2
  rw [← hL] at h
  obtain ⟨γ, hγ, hγA⟩ := h
  have hγL : (γ : G) ∈ L := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨γ, hγL, fun x hx => ?_, hγA⟩
  obtain ⟨c, hc⟩ := exists_dg_of_mem hXΓ hX hx
  refine ⟨γ * ⟨x, hXΓ hx⟩ * γ⁻¹ * (⟨x, hXΓ hx⟩ : ↥Γ)⁻¹, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc, hγA]
  have e : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) * ProjGenLinGroup.mk (dgHom c) =
      ProjGenLinGroup.mk (dgHom c) * ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) := by
    rw [← map_mul, ← map_mul, block_comm_dg hA c]
  rw [e]
  group

end CFSG.Quasithin.H13.Ch4.B414.M

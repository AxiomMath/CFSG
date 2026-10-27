module

public import CFSG.Monster.B.TwoA.Amalgam.Flag4Stab

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

@[expose] def flag4Obj
    (j : Fin 3) (c : P4 ⧸ flag4H j) : Submodule (ZMod 2) V8 :=
  Quotient.liftOn' c (fun g : P4 => (flag4W j).map (p4Proj g : V8 →ₗ[ZMod 2] V8))
    fun a b hab => by
      have h := (mem_flag4H_iff j _).1 (QuotientGroup.leftRel_apply.1 hab)
      change (flag4W j).map (p4Proj a : V8 →ₗ[ZMod 2] V8) =
        (flag4W j).map (p4Proj b : V8 →ₗ[ZMod 2] V8)
      rw [show b = a * (a⁻¹ * b) by group, map_p4Proj_mul, h]

theorem flag4Obj_mk
    (j : Fin 3) (g : P4) :
    flag4Obj j (g : P4 ⧸ flag4H j) = (flag4W j).map (p4Proj g : V8 →ₗ[ZMod 2] V8) :=
  rfl

theorem flag4Obj_mem
    (j : Fin 3) (c : P4 ⧸ flag4H j) :
    flag4Obj j c ∈ singularSubspaces qForm ((j : ℕ) + 1) := by
  induction c using QuotientGroup.induction_on with
  | H g => exact map_p4Proj_mem g (flag4W_mem j)

theorem flag4Obj_injective
    (j : Fin 3) : Function.Injective (flag4Obj j) := by
  intro c d h
  induction c using QuotientGroup.induction_on with
  | H a =>
  induction d using QuotientGroup.induction_on with
  | H b =>
  rw [flag4Obj_mk, flag4Obj_mk] at h
  rw [QuotientGroup.eq, mem_flag4H_iff, map_p4Proj_mul, ← h, ← map_p4Proj_mul, inv_mul_cancel,
    map_p4Proj_one]

theorem flag4Obj_smul
    (j : Fin 3) (g : P4) (c : P4 ⧸ flag4H j) :
    flag4Obj j (g • c) = (flag4Obj j c).map (p4Proj g : V8 →ₗ[ZMod 2] V8) := by
  induction c using QuotientGroup.induction_on with
  | H a =>
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, flag4Obj_mk, flag4Obj_mk, map_p4Proj_mul]

@[expose] def flag4Equiv
    (j : Fin 3) :
    P4 ⧸ flag4H j ≃ singularSubspaces qForm ((j : ℕ) + 1) :=
  Equiv.ofBijective (fun c => ⟨flag4Obj j c, flag4Obj_mem j c⟩)
    ⟨fun _ _ h => flag4Obj_injective j (congrArg Subtype.val h), fun X => by
      obtain ⟨g, hg⟩ := exists_p4_map_eq j X.2
      exact ⟨g, Subtype.ext hg⟩⟩

theorem coe_flag4Equiv
    (j : Fin 3) (c : P4 ⧸ flag4H j) :
    (flag4Equiv j c : Submodule (ZMod 2) V8) = flag4Obj j c :=
  rfl

theorem index_flag4H
    (j : Fin 3) :
    (flag4H j).index = Nat.card (singularSubspaces qForm ((j : ℕ) + 1)) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (flag4Equiv j)

theorem coset_inter_iff
    {j k : Fin 3} (hjk : j < k) (a b : P4) :
    (∃ x : P4, (x : P4 ⧸ flag4H j) = a ∧ (x : P4 ⧸ flag4H k) = b) ↔
      (flag4W j).map (p4Proj a : V8 →ₗ[ZMod 2] V8) ≤
        (flag4W k).map (p4Proj b : V8 →ₗ[ZMod 2] V8) := by
  constructor
  · rintro ⟨x, hxa, hxb⟩
    rw [← flag4Obj_mk, ← flag4Obj_mk, ← hxa, ← hxb, flag4Obj_mk, flag4Obj_mk]
    exact Submodule.map_mono (flag4W_mono hjk.le)
  · intro hle
    have hU : (flag4W j).map (p4Proj (b⁻¹ * a) : V8 →ₗ[ZMod 2] V8) ≤ flag4W k := by
      have h := Submodule.map_mono (f := (p4Proj b⁻¹ : V8 →ₗ[ZMod 2] V8)) hle
      rwa [← map_p4Proj_mul, ← map_p4Proj_mul, inv_mul_cancel, map_p4Proj_one] at h
    have hjk' : (j : ℕ) < k := hjk
    have hk3 := k.isLt
    obtain ⟨M, hM, hMU, hMX⟩ := qForm_pair_transitive (j := (j : ℕ) + 1) (k := (k : ℕ) + 1)
      (by omega) (by omega) (by omega) (flag4W_mono hjk.le) hU (flag4W_mem j).1
      (by rw [LinearEquiv.finrank_map_eq]; exact (flag4W_mem j).1) (flag4W_mem k) (flag4W_mem k)
    obtain ⟨y, hy⟩ := p4Proj_surjective ⟨M, hM⟩
    have hyM : (p4Proj y : V8 ≃ₗ[ZMod 2] V8) = M := congrArg Subtype.val hy
    refine ⟨b * y, flag4Obj_injective j ?_, flag4Obj_injective k ?_⟩
    · rw [flag4Obj_mk, flag4Obj_mk, map_p4Proj_mul, hyM, hMU, ← map_p4Proj_mul,
        mul_inv_cancel_left]
    · rw [flag4Obj_mk, flag4Obj_mk, map_p4Proj_mul, hyM, hMX]

theorem p4_flag_transitive
    {F F' : Fin 3 → Submodule (ZMod 2) V8}
    (hF : F ∈ singularFlags qForm 3) (hF' : F' ∈ singularFlags qForm 3) :
    ∃ g : P4, ∀ i, (F i).map (p4Proj g : V8 →ₗ[ZMod 2] V8) = F' i := by
  obtain ⟨M, hM, hMF⟩ := qForm_flag_transitive le_rfl hF hF'
  obtain ⟨g, hg⟩ := p4Proj_surjective ⟨M, hM⟩
  refine ⟨g, fun i => ?_⟩
  rw [hg]
  exact hMF i

theorem flag4_coset_transitive
    (c : (j : Fin 3) → P4 ⧸ flag4H j)
    (hc : ∀ j k, ∃ x : P4, (x : P4 ⧸ flag4H j) = c j ∧ (x : P4 ⧸ flag4H k) = c k) :
    ∃ g : P4, ∀ j, (g : P4 ⧸ flag4H j) = c j := by
  have hO : (fun j => flag4Obj j (c j)) ∈ singularFlags qForm 3 := by
    refine ⟨fun j => (flag4Obj_mem j (c j)).1, fun j k hjk => ?_,
      fun j => (flag4Obj_mem j (c j)).2⟩
    obtain ⟨x, hxj, hxk⟩ := hc j k
    change flag4Obj j (c j) ≤ flag4Obj k (c k)
    rw [← hxj, ← hxk, flag4Obj_mk, flag4Obj_mk]
    exact Submodule.map_mono (flag4W_mono hjk)
  obtain ⟨g, hg⟩ := p4_flag_transitive flag4W_mem_singularFlags hO
  exact ⟨g, fun j => flag4Obj_injective j (hg j)⟩

theorem short_fourth_centralizer_orthogonal_flag :
    Pc 3 = P4 ∧ Function.Surjective p4Proj ∧ p4Proj.ker = Lgrp.subgroupOf P4 ∧
    QuadraticMap.Equivalent qForm (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1) ∧
    Nonempty (TauCeti.QuadraticMap.orthogonalGroup qForm ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)) ∧
    (a8Vec (Echain 1) = span (ZMod 2) {bvec 8 1} ∧
      a8Vec (Echain 2) = span (ZMod 2) {bvec 8 1, bvec 8 2} ∧
      a8Vec (Echain 3) = span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4}) ∧
    (∀ j : Fin 3, a8Vec (Echain ((j : ℕ) + 1)) ∈ singularSubspaces qForm ((j : ℕ) + 1)) ∧
    a8Vec (Echain 1) < a8Vec (Echain 2) ∧ a8Vec (Echain 2) < a8Vec (Echain 3) ∧
    (∀ X : Submodule (ZMod 2) V8, (∀ v ∈ X, qForm v = 0) → finrank (ZMod 2) X ≤ 3) ∧
    (∀ j : Fin 3, (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4 =
      (MulAction.stabilizer (TauCeti.QuadraticMap.orthogonalGroup qForm)
        (a8Vec (Echain ((j : ℕ) + 1)))).comap p4Proj) ∧
    (⨅ (j : Fin 4) (_ : j ≠ 3) (g : P4), conjSub (g : Dfull) (Pc 3 ⊓ Pc j)) = Nc 3 ∧
    Nc 3 = Lgrp ∧
    (∀ j : Fin 3, ∃ Φ : P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4 ≃
        singularSubspaces qForm ((j : ℕ) + 1),
      (∀ g : P4, (Φ g : Submodule (ZMod 2) V8) =
        (a8Vec (Echain ((j : ℕ) + 1))).map (p4Proj g : V8 →ₗ[ZMod 2] V8)) ∧
      ∀ (g : P4) (c : P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4),
        (Φ (g • c) : Submodule (ZMod 2) V8) =
          (Φ c : Submodule (ZMod 2) V8).map (p4Proj g : V8 →ₗ[ZMod 2] V8)) ∧
    Nat.card (singularSubspaces qForm 1) = 119 ∧ Nat.card (singularSubspaces qForm 2) = 1071 ∧
    Nat.card (singularSubspaces qForm 3) = 765 ∧
    ((Pc 3 ⊓ Pc 0).subgroupOf P4).index = 119 ∧ ((Pc 3 ⊓ Pc 1).subgroupOf P4).index = 1071 ∧
    ((Pc 3 ⊓ Pc 2).subgroupOf P4).index = 765 ∧
    (∀ j k : Fin 3, j < k → ∀ a b : P4,
      (∃ x : P4, (x : P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4) = a ∧
          (x : P4 ⧸ (Pc 3 ⊓ Pc k.castSucc).subgroupOf P4) = b) ↔
        (a8Vec (Echain ((j : ℕ) + 1))).map (p4Proj a : V8 →ₗ[ZMod 2] V8) ≤
          (a8Vec (Echain ((k : ℕ) + 1))).map (p4Proj b : V8 →ₗ[ZMod 2] V8)) ∧
    (∀ F ∈ singularFlags qForm 3, ∀ F' ∈ singularFlags qForm 3,
      ∃ g : P4, ∀ i, (F i).map (p4Proj g : V8 →ₗ[ZMod 2] V8) = F' i) ∧
    (∀ c : (j : Fin 3) → P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4,
      (∀ j k, ∃ x : P4, (x : P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4) = c j ∧
        (x : P4 ⧸ (Pc 3 ⊓ Pc k.castSucc).subgroupOf P4) = c k) →
      ∃ g : P4, ∀ j, (g : P4 ⧸ (Pc 3 ⊓ Pc j.castSucc).subgroupOf P4) = c j) := by
  obtain ⟨h1, h2, h3⟩ := natCard_singularSubspaces_qForm
  have hlt : ∀ i j : Fin 3, i < j → flag4W i < flag4W j := fun i j hij =>
    lt_of_le_of_ne (flag4W_mono hij.le) fun h => (ne_of_lt hij) (Fin.ext (by
      have := congrArg (fun W : Submodule (ZMod 2) V8 => finrank (ZMod 2) W) h
      simp only [(flag4W_mem i).1, (flag4W_mem j).1] at this
      omega))
  refine ⟨rfl, p4Proj_surjective, ker_p4Proj, equivalent_quadMinus, ⟨orthMinusEquiv⟩,
    ⟨a8Vec_Echain (i := 1) le_rfl (by norm_num), a8Vec_Echain (i := 2) (by norm_num)
      (by norm_num), a8Vec_Echain (i := 3) (by norm_num) (by norm_num)⟩,
    flag4W_mem, hlt 0 1 (by decide), hlt 1 2 (by decide),
    fun _ hX => finrank_le_three_of_singular hX, flag4H_eq, iInf_conjSub_eq_Nc, Nc_three,
    fun j => ⟨flag4Equiv j, fun _ => rfl, fun g c => flag4Obj_smul j g c⟩, h1, h2, h3,
    (index_flag4H 0).trans h1, (index_flag4H 1).trans h2, (index_flag4H 2).trans h3,
    fun _ _ hjk a b => coset_inter_iff hjk a b, fun _ hF _ hF' => p4_flag_transitive hF hF',
    flag4_coset_transitive⟩

end CFSG.Monster.B.TwoA.Amalgam

module

public import CFSG.Quasithin.Recognition.St84.G24ModelChev
public import Certificates.Certificate733007
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import Certificates.Data.ExceptionalSL3

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Quasithin.G2U
open scoped Pointwise


private theorem exists_conj_H0 (hM : Facts) (σ : MulAut ↥(M1 ⊓ M2)) :
    ∃ x₀ : ↥(M1 ⊓ M2), ∀ y : ↥(M1 ⊓ M2),
      ((MulAut.conj x₀ * σ⁻¹) y : Y) ∈ H0 ↔ (y : Y) ∈ H0 := by
  classical
  let H0B : Subgroup ↥(M1 ⊓ M2) := H0.subgroupOf (M1 ⊓ M2)
  have hcardH0B : Nat.card ↥H0B = 9 := by
    change Nat.card ↥(H0.subgroupOf (M1 ⊓ M2)) = 9
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (by rw [hM.inf_M1_M2]; exact hM.H0_le_B0)).toEquiv]
    exact hM.card_H0
  have hcardB : Nat.card ↥(M1 ⊓ M2) = 36864 := by
    rw [hM.inf_M1_M2]
    exact hM.card_B0
  have hfac3 : (36864 : Nat).factorization 3 = 2 := by
    have h : (36864 : Nat) = 3 ^ 2 * 2 ^ 12 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfac : (9 : Nat) = (3 : Nat) ^ (Nat.card ↥(M1 ⊓ M2)).factorization 3 := by
    rw [hcardB, hfac3]
    norm_num
  let P : Sylow 3 ↥(M1 ⊓ M2) := Sylow.ofCard H0B (by rw [hcardH0B]; exact hfac)
  let τ : MulAut ↥(M1 ⊓ M2) := σ⁻¹
  let Q : Sylow 3 ↥(M1 ⊓ M2) := Sylow.ofCard (H0B.map τ.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective τ.injective, hcardH0B]
    exact hfac)
  have hP : (P : Subgroup ↥(M1 ⊓ M2)) = H0B := Sylow.coe_ofCard H0B _
  have hQ : (Q : Subgroup ↥(M1 ⊓ M2)) = H0B.map τ.toMonoidHom := Sylow.coe_ofCard _ _
  obtain ⟨x₀, hx₀⟩ := MulAction.exists_smul_eq ↥(M1 ⊓ M2) Q P
  have hconj : MulAut.conj x₀ • (H0B.map τ.toMonoidHom) = H0B := by
    rw [← hQ, ← Sylow.coe_subgroup_smul, hx₀, hP]
  have hconj' : MulAut.conj x₀ • ((H0.subgroupOf (M1 ⊓ M2)).map τ.toMonoidHom) =
      H0.subgroupOf (M1 ⊓ M2) := hconj
  refine ⟨x₀, fun y => ?_⟩
  rw [MulAut.mul_apply, ← Subgroup.mem_subgroupOf (H := H0) (K := M1 ⊓ M2)]
  rw [show H0.subgroupOf (M1 ⊓ M2) =
    MulAut.conj x₀ • ((H0.subgroupOf (M1 ⊓ M2)).map τ.toMonoidHom) from hconj'.symm]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.inv_apply,
    MulEquiv.symm_apply_apply, Subgroup.mem_map_equiv]
  have hsymm : (MulEquiv.symm τ) (σ⁻¹ y) = y := by
    change σ (σ⁻¹ y) = y
    exact MulEquiv.apply_symm_apply σ y
  rw [hsymm, Subgroup.mem_subgroupOf]

private theorem exists_decomp (hM : Facts) (W : Witnesses) (n : MulAut ↥(M1 ⊓ M2))
    (hn : ∀ x : ↥(M1 ⊓ M2), (x : Y) ∈ H0 → ((n x : ↥(M1 ⊓ M2)) : Y) ∈ H0) :
    ∃ (a : MulAut ↥M1) (j : Fin 8) (h : Y), h ∈ H0 ∧
      (∀ m : ↥M1, (m : Y) ∈ M2 ↔ ((a m : ↥M1) : Y) ∈ M2) ∧
      ∀ (x : ↥(M1 ⊓ M2)) (m₁ : ↥M1) (m₂ : ↥M2), (m₁ : Y) = ((n x : ↥(M1 ⊓ M2)) : Y) →
        (m₂ : Y) = h * (x : Y) * h⁻¹ → ((a m₁ : ↥M1) : Y) = ((W.W2 j m₂ : ↥M2) : Y) :=
  (Certificates.certificate733007 chevFacts hM W).decomp n hn

theorem dcProp_g24 (hM : Facts) (W : Witnesses) :
    CFSG.GH74.QTGen4.DSGen4.L34.DCProp M1 M2 := by
  intro σ _
  obtain ⟨x₀, hx₀⟩ := exists_conj_H0 hM σ
  let n : MulAut ↥(M1 ⊓ M2) := MulAut.conj x₀ * σ⁻¹
  have hn : ∀ x : ↥(M1 ⊓ M2), (x : Y) ∈ H0 → ((n x : ↥(M1 ⊓ M2)) : Y) ∈ H0 :=
    fun x hx => (hx₀ x).mpr hx
  obtain ⟨a, j, h, hhH0, ha_mem, ha_eq⟩ := exists_decomp hM W n hn
  have hx0M1 : (x₀ : Y) ∈ M1 := (Subgroup.mem_inf.mp x₀.2).1
  have hx0M2 : (x₀ : Y) ∈ M2 := (Subgroup.mem_inf.mp x₀.2).2
  have hhB : h ∈ M1 ⊓ M2 := hM.inf_M1_M2 ▸ hM.H0_le_B0 hhH0
  have hhM1 : h ∈ M1 := (Subgroup.mem_inf.mp hhB).1
  have hhM2 : h ∈ M2 := (Subgroup.mem_inf.mp hhB).2
  let x0 : ↥M1 := ⟨x₀, hx0M1⟩
  let hM2' : ↥M2 := ⟨h, hhM2⟩
  let a₁ : MulAut ↥M1 := a * MulAut.conj x0
  let a₂ : MulAut ↥M2 := MulAut.conj hM2'⁻¹ * (W.W2 j)⁻¹
  have ha₁ : ∀ m : ↥M1, (m : Y) ∈ M2 ↔ ((a₁ m : ↥M1) : Y) ∈ M2 := by
    intro m
    have hcoe : ((MulAut.conj x0 m : ↥M1) : Y) = (x₀ : Y) * (m : Y) * (x₀ : Y)⁻¹ := by
      rw [MulAut.conj_apply]
      rfl
    have hconj : (m : Y) ∈ M2 ↔ ((MulAut.conj x0 m : ↥M1) : Y) ∈ M2 := by
      rw [hcoe, mul_mem_cancel_right (M2.inv_mem hx0M2), mul_mem_cancel_left hx0M2]
    exact hconj.trans (ha_mem (MulAut.conj x0 m))
  have ha₂ : ∀ m : ↥M2, (m : Y) ∈ M1 ↔ ((a₂ m : ↥M2) : Y) ∈ M1 := by
    intro m
    have hW : (m : Y) ∈ M1 ↔ (((W.W2 j)⁻¹ m : ↥M2) : Y) ∈ M1 := by
      have h := W.W2_mem j ((W.W2 j)⁻¹ m)
      rw [show ((W.W2 j) ((W.W2 j)⁻¹ m) : ↥M2) = m from MulAut.apply_inv_self ↥M2 (W.W2 j) m] at h
      exact h.symm
    have hcoe : ((MulAut.conj hM2'⁻¹ ((W.W2 j)⁻¹ m) : ↥M2) : Y) =
        (h : Y)⁻¹ * (((W.W2 j)⁻¹ m : ↥M2) : Y) * (h : Y) := by
      rw [MulAut.conj_apply]
      rfl
    have hconj : (((W.W2 j)⁻¹ m : ↥M2) : Y) ∈ M1 ↔
        ((MulAut.conj hM2'⁻¹ ((W.W2 j)⁻¹ m) : ↥M2) : Y) ∈ M1 := by
      rw [hcoe, mul_mem_cancel_right hhM1, mul_mem_cancel_left (M1.inv_mem hhM1)]
    have hcomp : ((a₂ m : ↥M2) : Y) =
        ((MulAut.conj hM2'⁻¹ ((W.W2 j)⁻¹ m) : ↥M2) : Y) := by
      simp only [a₂, MulAut.mul_apply]
    rw [hcomp]
    exact hW.trans hconj
  refine ⟨a₁, a₂, ha₁, ha₂, ?_⟩
  intro b m₁ m₂ hm₁ hm₂
  let z1 : ↥M1 := ⟨((n (σ b) : ↥(M1 ⊓ M2)) : Y),
    (Subgroup.mem_inf.mp (n (σ b)).2).1⟩
  have hz1 : (z1 : Y) = (x₀ : Y) * (b : Y) * (x₀ : Y)⁻¹ := by
    change ((n (σ b) : ↥(M1 ⊓ M2)) : Y) = _
    have hs : (σ⁻¹ (σ b) : ↥(M1 ⊓ M2)) = b := MulEquiv.symm_apply_apply σ b
    simp only [n, MulAut.mul_apply, MulAut.conj_apply, hs]
    rfl
  have hcz : MulAut.conj x0 m₁ = z1 := by
    refine Subtype.ext ?_
    change (x₀ : Y) * (m₁ : Y) * (x₀ : Y)⁻¹ = (z1 : Y)
    rw [hz1, hm₁]
  let m2' : ↥M2 := ⟨h * ((σ b : ↥(M1 ⊓ M2)) : Y) * h⁻¹,
    M2.mul_mem (M2.mul_mem hhM2 (Subgroup.mem_inf.mp (σ b).2).2)
      (M2.inv_mem hhM2)⟩
  have haeq : ((a z1 : ↥M1) : Y) = ((W.W2 j m2' : ↥M2) : Y) :=
    ha_eq (σ b) z1 m2' rfl rfl
  have ha₁m₁ : ((a₁ m₁ : ↥M1) : Y) = ((a z1 : ↥M1) : Y) := by
    simp only [a₁, MulAut.mul_apply, hcz]
  have hW2eq : W.W2 j m2' = m₂ := by
    refine Subtype.ext ?_
    rw [← haeq, ← ha₁m₁]
    exact hm₂
  have ha₂m : ((a₂ m₂ : ↥M2) : Y) = ((σ b : ↥(M1 ⊓ M2)) : Y) := by
    rw [← hW2eq]
    have hinv : ((W.W2 j)⁻¹ (W.W2 j m2') : ↥M2) = m2' := by
      rw [MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply (W.W2 j) m2'
    change (((MulAut.conj hM2'⁻¹ * (W.W2 j)⁻¹) (W.W2 j m2') : ↥M2) : Y) = _
    rw [MulAut.mul_apply, hinv, MulAut.conj_apply]
    change (h : Y)⁻¹ * ((h : Y) * ((σ b : ↥(M1 ⊓ M2)) : Y) * (h : Y)⁻¹) * (h : Y) = _
    group
  exact ha₂m

end CFSG.Quasithin.F112R.St84.G24M

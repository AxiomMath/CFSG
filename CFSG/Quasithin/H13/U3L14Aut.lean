module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup

theorem perm5_comm_support : ∀ σ τ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 → τ ^ 2 = 1 →
    τ ≠ 1 → σ * τ = τ * σ → τ.support.card = 2 := by
  decide +kernel

theorem mulAut_alt5_eq_one {α : MulAut (alternatingGroup (Fin 5))} (hα : α ^ 3 = 1)
    {τ : alternatingGroup (Fin 5)} (hτ1 : τ ≠ 1) (hτ2 : τ ^ 2 = 1) (hfix : α τ = τ) : α = 1 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨σ, rfl⟩ := hbij.2 α
  have hσ3 : σ ^ 3 = 1 := hbij.1 (by rw [map_pow, hα, map_one])
  by_cases hσ1 : σ = 1
  · rw [hσ1, map_one]
  exfalso
  have hcomm : σ * (τ : Equiv.Perm (Fin 5)) = τ * σ := by
    have h1 := congrArg Subtype.val hfix
    rw [MulAut.conjNormal_apply] at h1
    calc σ * (τ : Equiv.Perm (Fin 5)) = σ * τ * σ⁻¹ * σ := by group
      _ = τ * σ := by rw [h1]
  have hτ1' : (τ : Equiv.Perm (Fin 5)) ≠ 1 := fun h => hτ1 (Subtype.ext h)
  have hτ2' : (τ : Equiv.Perm (Fin 5)) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hτ2
  have hswap : (τ : Equiv.Perm (Fin 5)).IsSwap :=
    Equiv.Perm.card_support_eq_two.mp (perm5_comm_support σ τ hσ3 hσ1 hτ2' hτ1' hcomm)
  have hsign := hswap.sign_eq
  rw [Equiv.Perm.mem_alternatingGroup.mp τ.2] at hsign
  exact absurd hsign (by decide)

theorem gl32_norm_U : ∀ a b c d e f g h i : ZMod 2,
    Matrix.det !![a, b, c; d, e, f; g, h, i] = 1 →
    (∃ x y z : ZMod 2, !![a, b, c; d, e, f; g, h, i] * !![1, 1, 0; 0, 1, 0; 0, 0, 1] =
        !![1, x, y; 0, 1, z; 0, 0, 1] * !![a, b, c; d, e, f; g, h, i]) →
    (∃ x y z : ZMod 2, !![a, b, c; d, e, f; g, h, i] * !![1, 0, 0; 0, 1, 1; 0, 0, 1] =
        !![1, x, y; 0, 1, z; 0, 0, 1] * !![a, b, c; d, e, f; g, h, i]) →
    !![a, b, c; d, e, f; g, h, i] * !![a, b, c; d, e, f; g, h, i] *
      !![a, b, c; d, e, f; g, h, i] = 1 →
    !![a, b, c; d, e, f; g, h, i] = 1 := by
  decide +kernel

theorem upper_det_eq_one : ∀ a b c d e f : ZMod 2,
    Matrix.det !![a, b, c; 0, d, e; 0, 0, f] = 1 → a = 1 ∧ d = 1 ∧ f = 1 := by
  decide

theorem det_gl32 (A : GL (Fin 3) (ZMod 2)) : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

@[expose] def U32 : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0}
  mul_mem' {A B} hA hB := by
    obtain ⟨a10, a20, a21⟩ := hA
    obtain ⟨b10, b20, b21⟩ := hB
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  inv_mem' {A} hA := by
    obtain ⟨a10, a20, a21⟩ := hA
    show ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ _
    rw [Matrix.coe_units_inv, Matrix.inv_def, det_gl32, Ring.inverse_one, one_smul]
    refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.adjugate_fin_three, a10, a20, a21]

theorem eq_of_mem_U32 {A : GL (Fin 3) (ZMod 2)} (hA : A ∈ U32) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      !![1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2;
        0, 1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2; 0, 0, 1] := by
  obtain ⟨a10, a20, a21⟩ := hA
  have hdet := det_gl32 A
  have e := Matrix.eta_fin_three (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [a10, a20, a21] at e
  rw [e] at hdet
  obtain ⟨h0, h1, h2⟩ := upper_det_eq_one _ _ _ _ _ _ hdet
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

theorem card_U32 : Nat.card U32 = 8 := by
  have hinv : ∀ x y z : ZMod 2,
      !![1, x, y; 0, 1, z; 0, 0, 1] * !![1, x, x * z + y; 0, 1, z; 0, 0, 1] = 1 := by decide
  have hinv' : ∀ x y z : ZMod 2,
      !![1, x, x * z + y; 0, 1, z; 0, 0, 1] * !![1, x, y; 0, 1, z; 0, 0, 1] = 1 := by decide
  let f : ZMod 2 × ZMod 2 × ZMod 2 → U32 := fun v =>
    ⟨⟨!![1, v.1, v.2.1; 0, 1, v.2.2; 0, 0, 1],
      !![1, v.1, v.1 * v.2.2 + v.2.1; 0, 1, v.2.2; 0, 0, 1], hinv _ _ _, hinv' _ _ _⟩,
      by refine ⟨?_, ?_, ?_⟩ <;> rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h1 := congrArg
        (fun A : U32 => ((A : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
      have e01 := congrFun (congrFun h1 0) 1
      have e02 := congrFun (congrFun h1 0) 2
      have e12 := congrFun (congrFun h1 1) 2
      simp [f] at e01 e02 e12
      rw [e01, e02, e12]
    · rintro ⟨A, hA⟩
      refine ⟨⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2,
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact (eq_of_mem_U32 hA).symm
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card]
  simp

@[expose] def uA : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def uB : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

theorem uA_mem : uA ∈ U32 := ⟨rfl, rfl, rfl⟩

theorem uB_mem : uB ∈ U32 := ⟨rfl, rfl, rfl⟩

theorem mulAut_gl32_eq_one {α : MulAut (GL (Fin 3) (ZMod 2))} (hα : α ^ 3 = 1)
    {P : Subgroup (GL (Fin 3) (ZMod 2))} (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (hαP : P.map α.toMonoidHom = P) : α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := Subgroup.sq_mem_of_index_two CFSG.LieType.SteinbergBR.AutGL32.index_inner α
  obtain ⟨s, hs⟩ : α ∈ (MulAut.conj : GL (Fin 3) (ZMod 2) →* MulAut _).range := by
    have : α = α ^ 3 * (α ^ 2)⁻¹ := by group
    rw [this, hα, one_mul]
    exact inv_mem hsq
  subst hs
  have hs3 : s ^ 3 = 1 := CFSG.LieType.SteinbergBR.AutGL32.conj_injective
    (by rw [map_pow, hα, map_one])
  have hU2 : IsPGroup 2 U32 := IsPGroup.of_card (n := 3) (by rw [card_U32]; norm_num)
  have hUi : ¬ 2 ∣ U32.index := by
    have h := U32.card_mul_index
    rw [card_U32, CFSG.LieType.SteinbergBR.AutGL32.card_GL32] at h
    have : U32.index = 21 := by omega
    rw [this]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) (hU2.toSylow hUi)
    (hP2.toSylow hPi)
  have hPg : P = U32.map (MulAut.conj g).toMonoidHom := by
    have := congrArg
      (fun Q : Sylow 2 (GL (Fin 3) (ZMod 2)) => (Q : Subgroup (GL (Fin 3) (ZMod 2)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at this
    rw [← this]
    rfl
  set t := g⁻¹ * s * g with ht
  have hnorm : ∀ u ∈ U32, t * u * t⁻¹ ∈ U32 := by
    intro u hu
    have h1 : g * u * g⁻¹ ∈ P := by rw [hPg]; exact ⟨u, hu, rfl⟩
    have h2 : s * (g * u * g⁻¹) * s⁻¹ ∈ P := by
      rw [← hαP]
      exact ⟨_, h1, rfl⟩
    rw [hPg] at h2
    obtain ⟨v, hv, hve⟩ := h2
    have : t * u * t⁻¹ = v := by
      have hve' : g * v * g⁻¹ = s * (g * u * g⁻¹) * s⁻¹ := hve
      rw [ht]
      calc g⁻¹ * s * g * u * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * (g * u * g⁻¹) * s⁻¹) * g := by group
        _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hve']
        _ = v := by group
    rw [this]
    exact hv
  have hs3' : s * s * s = 1 := by rw [← pow_three', hs3]
  have ht3 : t * t * t = 1 := by
    rw [ht]
    have : g⁻¹ * s * g * (g⁻¹ * s * g) * (g⁻¹ * s * g) = g⁻¹ * (s * s * s) * g := by group
    rw [this, hs3']
    group
  have hE : ∀ (E : GL (Fin 3) (ZMod 2)), E ∈ U32 → ∃ x y z : ZMod 2,
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) * E = !![1, x, y; 0, 1, z; 0, 0, 1] * t := by
    intro E hE
    have h1 := hnorm E hE
    set u := t * E * t⁻¹ with hu
    refine ⟨(u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2,
      (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2, ?_⟩
    rw [← eq_of_mem_U32 h1]
    have : t * E = u * t := by rw [hu]; group
    exact congrArg (fun A : GL (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) this
  have e := Matrix.eta_fin_three (t : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hdet := det_gl32 t
  have h1 := hE _ uA_mem
  have h2 := hE _ uB_mem
  have ht3' : (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) * t * t = 1 := by
    have := congrArg (fun A : GL (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) ht3
    simpa using this
  rw [e] at hdet h1 h2 ht3'
  have htm := gl32_norm_U _ _ _ _ _ _ _ _ _ hdet h1 h2 ht3'
  have ht1 : t = 1 := by
    apply Units.ext
    rw [e, htm]
    rfl
  have hs1 : s = 1 := by
    have : s = g * t * g⁻¹ := by rw [ht]; group
    rw [this, ht1]
    group
  rw [hs1, map_one]

end CFSG.Quasithin.H13.U3

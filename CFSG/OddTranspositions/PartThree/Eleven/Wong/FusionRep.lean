module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionSylow

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup Matrix

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

private theorem vecE_smul (c : ZMod 2) (b : Fin 4 → ZMod 2) :
    D.vecE b ^ c.val = D.vecE (c • b) := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, zero_smul, D.vecE_zero]
  · rw [ZMod.val_one, pow_one, one_smul]

private theorem vecE_row (i : Fin 4) :
    D.vecE (fun j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) = D.eb i := by
  fin_cases i <;>
    simp [SwapData.vecE, SwapData.eb, Matrix.one_eq_pi_single, ZMod.val_one]

private theorem eb_mem_E (i : Fin 4) : D.eb i ∈ D.E := by
  fin_cases i
  · change D.t ∈ D.E
    exact Subgroup.subset_closure (by simp)
  · change D.u ∈ D.E
    exact Subgroup.subset_closure (by simp)
  · change D.v ∈ D.E
    exact Subgroup.subset_closure (by simp)
  · change D.w ∈ D.E
    exact Subgroup.subset_closure (by simp)

private theorem vecE_add_four (a b c d : Fin 4 → ZMod 2) :
    D.vecE (a + b + c + d) = D.vecE a * D.vecE b * D.vecE c * D.vecE d := by
  rw [D.vecE_add, D.vecE_add, D.vecE_add]

private theorem conj_vecE_eq_four (g : G) (a : Fin 4 → ZMod 2) :
    g⁻¹ * D.vecE a * g =
      (g⁻¹ * D.eb 0 * g) ^ (a 0).val * (g⁻¹ * D.eb 1 * g) ^ (a 1).val *
        (g⁻¹ * D.eb 2 * g) ^ (a 2).val * (g⁻¹ * D.eb 3 * g) ^ (a 3).val := by
  have h : D.vecE a = D.eb 0 ^ (a 0).val * D.eb 1 ^ (a 1).val *
      D.eb 2 ^ (a 2).val * D.eb 3 ^ (a 3).val := by
    simp [SwapData.vecE, SwapData.eb]
  have e0 : g⁻¹ * D.eb 0 ^ (a 0).val * g = (g⁻¹ * D.eb 0 * g) ^ (a 0).val := by
    simpa [MulAut.conj_apply] using map_pow (MulAut.conj g⁻¹) (D.eb 0) (a 0).val
  have e1 : g⁻¹ * D.eb 1 ^ (a 1).val * g = (g⁻¹ * D.eb 1 * g) ^ (a 1).val := by
    simpa [MulAut.conj_apply] using map_pow (MulAut.conj g⁻¹) (D.eb 1) (a 1).val
  have e2 : g⁻¹ * D.eb 2 ^ (a 2).val * g = (g⁻¹ * D.eb 2 * g) ^ (a 2).val := by
    simpa [MulAut.conj_apply] using map_pow (MulAut.conj g⁻¹) (D.eb 2) (a 2).val
  have e3 : g⁻¹ * D.eb 3 ^ (a 3).val * g = (g⁻¹ * D.eb 3 * g) ^ (a 3).val := by
    simpa [MulAut.conj_apply] using map_pow (MulAut.conj g⁻¹) (D.eb 3) (a 3).val
  rw [h]
  calc g⁻¹ * (D.eb 0 ^ (a 0).val * D.eb 1 ^ (a 1).val * D.eb 2 ^ (a 2).val *
        D.eb 3 ^ (a 3).val) * g
      = (g⁻¹ * D.eb 0 ^ (a 0).val * g) * (g⁻¹ * D.eb 1 ^ (a 1).val * g) *
          (g⁻¹ * D.eb 2 ^ (a 2).val * g) * (g⁻¹ * D.eb 3 ^ (a 3).val * g) := by group
    _ = (g⁻¹ * D.eb 0 * g) ^ (a 0).val * (g⁻¹ * D.eb 1 * g) ^ (a 1).val *
          (g⁻¹ * D.eb 2 * g) ^ (a 2).val * (g⁻¹ * D.eb 3 * g) ^ (a 3).val := by
        rw [e0, e1, e2, e3]

private theorem conj_vecE_of_rows {g : G} {m : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ i, g⁻¹ * D.eb i * g = D.vecE (m i)) (a : Fin 4 → ZMod 2) :
    g⁻¹ * D.vecE a * g = D.vecE (a ᵥ* m) := by
  have hv : ((a 0) • m 0 + (a 1) • m 1 + (a 2) • m 2 + (a 3) • m 3) = a ᵥ* m := by
    funext j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  calc g⁻¹ * D.vecE a * g
      = (g⁻¹ * D.eb 0 * g) ^ (a 0).val * (g⁻¹ * D.eb 1 * g) ^ (a 1).val *
          (g⁻¹ * D.eb 2 * g) ^ (a 2).val * (g⁻¹ * D.eb 3 * g) ^ (a 3).val :=
        D.conj_vecE_eq_four g a
    _ = D.vecE ((a 0) • m 0) * D.vecE ((a 1) • m 1) *
          D.vecE ((a 2) • m 2) * D.vecE ((a 3) • m 3) := by
        rw [h 0, h 1, h 2, h 3, D.vecE_smul, D.vecE_smul, D.vecE_smul, D.vecE_smul]
    _ = D.vecE ((a 0) • m 0 + (a 1) • m 1 + (a 2) • m 2 + (a 3) • m 3) :=
        (D.vecE_add_four _ _ _ _).symm
    _ = D.vecE (a ᵥ* m) := by rw [hv]

private theorem commute_of_mem_E {x y : G} (hx : x ∈ D.E) (hy : y ∈ D.E) :
    Commute x y := by
  have hx2 : x ^ 2 = 1 := D.sq_eq_one_of_mem_E hx
  have hy2 : y ^ 2 = 1 := D.sq_eq_one_of_mem_E hy
  have hxy : (x * y) ^ 2 = 1 := D.sq_eq_one_of_mem_E (mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx2)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy2)
  have hxyi : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hxy)
  rw [Commute]
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

theorem exists_isBasisRep [Finite G] :
    ∃ ρ : normalizer (D.E : Set G) →* GL (Fin 4) (ZMod 2), D.IsBasisRep ρ := by
  classical
  let e : ∀ (g : normalizer (D.E : Set G)) (i : Fin 4), ∃ a : Fin 4 → ZMod 2,
      D.vecE a = (g : G)⁻¹ * D.eb i * g := fun g i => by
    refine D.mem_E_iff.mp ?_
    exact (Subgroup.mem_normalizer_iff''.mp g.2 (D.eb i)).mp (D.eb_mem_E i)
  let m : normalizer (D.E : Set G) → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    fun g => fun i => Classical.choose (e g i)
  have hm : ∀ g i, D.vecE (m g i) = (g : G)⁻¹ * D.eb i * g := fun g i =>
    Classical.choose_spec (e g i)
  have hm_one : m 1 = 1 := by
    refine funext fun i => ?_
    apply D.vecE_injective
    rw [hm]
    simp [D.vecE_row]
  have hm_mul : ∀ g h : normalizer (D.E : Set G), m (g * h) = m g * m h := by
    intro g h
    refine funext fun i => ?_
    apply D.vecE_injective
    rw [hm]
    rw [Subgroup.coe_mul]
    calc ((g : G) * (h : G))⁻¹ * D.eb i * ((g : G) * (h : G))
        = (h : G)⁻¹ * ((g : G)⁻¹ * D.eb i * (g : G)) * (h : G) := by group
      _ = (h : G)⁻¹ * D.vecE (m g i) * (h : G) := by rw [hm]
      _ = D.vecE (m g i ᵥ* m h) :=
            D.conj_vecE_of_rows (m := m h) (fun j => (hm h j).symm) (m g i)
      _ = D.vecE ((m g * m h) i) := by rw [Matrix.mul_apply_eq_vecMul]
  let φ : normalizer (D.E : Set G) →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    { toFun := m
      map_one' := hm_one
      map_mul' := hm_mul }
  refine ⟨φ.toHomUnits, fun g i => ?_⟩
  rw [← hm g i, MonoidHom.coe_toHomUnits]
  rfl

section Rep

variable {D} {ρ : normalizer (D.E : Set G) →* GL (Fin 4) (ZMod 2)}

theorem IsBasisRep.conj_vecE (hρ : D.IsBasisRep ρ) (g : normalizer (D.E : Set G))
    (a : Fin 4 → ZMod 2) :
    (g : G)⁻¹ * D.vecE a * g = D.vecE (a ᵥ* (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
  exact D.conj_vecE_of_rows (m := (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2))) (hρ g) a

theorem IsBasisRep.ker_eq [Finite G] (hρ : D.IsBasisRep ρ) :
    ρ.ker = D.E.subgroupOf (normalizer (D.E : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have h1 : ((ρ g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
      rw [hg]; rfl
    have hcomm : ∀ i : Fin 4, (g : G)⁻¹ * D.eb i * g = D.eb i := fun i => by
      have := hρ g i
      rw [h1] at this
      simpa [D.vecE_row i] using this
    have hmem : (g : G) ∈ centralizer ({D.t, D.u, D.v} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · have h := hcomm 0
        simp [SwapData.eb] at h
        calc D.t * (g : G) = (g : G) * ((g : G)⁻¹ * D.t * (g : G)) := by group
          _ = (g : G) * D.t := by rw [h]
      · have h := hcomm 1
        simp [SwapData.eb] at h
        calc D.u * (g : G) = (g : G) * ((g : G)⁻¹ * D.u * (g : G)) := by group
          _ = (g : G) * D.u := by rw [h]
      · have h := hcomm 2
        simp [SwapData.eb] at h
        calc D.v * (g : G) = (g : G) * ((g : G)⁻¹ * D.v * (g : G)) := by group
          _ = (g : G) * D.v := by rw [h]
    rwa [D.centralizer_t_u_v] at hmem
  · intro hgE
    have hrow : ∀ i : Fin 4, (g : G)⁻¹ * D.eb i * g = D.eb i := fun i => by
      have hc : Commute (D.eb i) (g : G) :=
        D.commute_of_mem_E (D.eb_mem_E i) hgE
      calc (g : G)⁻¹ * D.eb i * g = (g : G)⁻¹ * (D.eb i * g) := by group
        _ = (g : G)⁻¹ * (g * D.eb i) := by rw [hc]
        _ = D.eb i := by group
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hvec : (fun j => ((ρ g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) =
        fun j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j := by
      apply D.vecE_injective
      rw [← hρ g i, hrow i]
      simp [D.vecE_row i]
    exact congrFun hvec j

theorem IsBasisRep.apply_h1 (hρ : D.IsBasisRep ρ) :
    ρ ⟨D.h1, D.h1_mem_normalizer_E⟩ = fusionUnitA := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hvec : (fun j => ((ρ ⟨D.h1, D.h1_mem_normalizer_E⟩ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) = fusionA i := by
    apply D.vecE_injective
    rw [← hρ ⟨D.h1, D.h1_mem_normalizer_E⟩ i]
    fin_cases i <;>
      simp [SwapData.vecE, SwapData.eb, fusionA, D.conj_h1_eb, ZMod.val_one, ZMod.val_zero]
  simpa using congrFun hvec j

theorem IsBasisRep.apply_c1 (hρ : D.IsBasisRep ρ) :
    ρ ⟨D.c1, D.c1_mem_normalizer_E⟩ = fusionUnitB := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hvec : (fun j => ((ρ ⟨D.c1, D.c1_mem_normalizer_E⟩ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) = fusionB i := by
    apply D.vecE_injective
    rw [← hρ ⟨D.c1, D.c1_mem_normalizer_E⟩ i]
    fin_cases i <;>
      simp [SwapData.vecE, SwapData.eb, fusionB, D.conj_c1_eb, ZMod.val_one, ZMod.val_zero]
  simpa using congrFun hvec j

theorem IsBasisRep.apply_f12 (hρ : D.IsBasisRep ρ) :
    ρ ⟨D.f12, D.f12_mem_normalizer_E⟩ = fusionUnitF := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hvec : (fun j => ((ρ ⟨D.f12, D.f12_mem_normalizer_E⟩ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) = fusionF i := by
    apply D.vecE_injective
    rw [← hρ ⟨D.f12, D.f12_mem_normalizer_E⟩ i]
    fin_cases i <;>
      simp [SwapData.vecE, SwapData.eb, fusionF, D.conj_f12_eb, ZMod.val_one, ZMod.val_zero]
  simpa using congrFun hvec j

theorem IsBasisRep.not_eight_dvd [Finite G] (hρ : D.IsBasisRep ρ) : ¬ 8 ∣ Nat.card ρ.range := by
  intro h8
  have hker : Nat.card ρ.ker = 16 := by
    rw [hρ.ker_eq]
    calc Nat.card (D.E.subgroupOf (normalizer (D.E : Set G)))
        = Nat.card D.E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
      _ = 16 := D.card_E
  have hcardN := Subgroup.card_ker_mul_card_range ρ
  rw [hker] at hcardN
  have h128 : 2 ^ 7 ∣ Nat.card (normalizer (D.E : Set G)) := by
    obtain ⟨k, hk⟩ := h8
    refine ⟨k, ?_⟩
    rw [← hcardN, hk]
    ring
  have h27 : 2 ^ 7 ∣ Nat.card G :=
    h128.trans (Subgroup.card_subgroup_dvd_card (normalizer (D.E : Set G)))
  have hle : 7 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.ne_of_gt Nat.card_pos)).mp h27
  rw [D.factorization_card_two] at hle
  omega

end Rep

end SwapData

end CFSG.OddTranspositions.PartThree.Wong

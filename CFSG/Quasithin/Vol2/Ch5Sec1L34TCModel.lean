module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34IrrPar
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.TorusComm

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.KGL34P CFSG.Quasithin.H13.SecFix

@[expose] def ConjPm {X : Type*} [Group X] (y x : X) : Prop :=
  ∃ t : X, x = t * y * t⁻¹ ∨ x = t * y ^ 2 * t⁻¹

theorem conjPm_conj {X : Type*} [Group X] {y x : X} (h : ConjPm y x) (s : X) :
    ConjPm y (s * x * s⁻¹) := by
  obtain ⟨t, rfl | rfl⟩ := h
  · exact ⟨s * t, Or.inl (by group)⟩
  · exact ⟨s * t, Or.inr (by group)⟩

theorem card_of_lieModel {X : Type} [Group X] (hX : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (hX.statedClassicalModel (by decide))

variable {k : Type} [Field k] [CharP k 2] {ω : k}

theorem proj_torusDiag_ne_one (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    proj 3 k (torusDiag ω hω3) ≠ 1 := by
  rw [Ne, proj_eq_one_iff]
  rintro ⟨c, -, hc⟩
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  rw [coe_torusDiag] at h0 h1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h0 h1
  have hω : ω = 1 := h1.trans h0.symm
  rw [hω] at hω2
  have h3 : (1 : k) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have : (1 : k) = 0 := by linear_combination hω2 - h3
  exact one_ne_zero this

theorem pair01 : ((0, 1) : ZMod 3 × ZMod 3) ≠ (0, 0) := by decide
theorem pair11 : ((1, 1) : ZMod 3 × ZMod 3) ≠ (0, 0) := by decide
theorem pair21 : ((2, 1) : ZMod 3 × ZMod 3) ≠ (0, 0) := by decide
theorem pair12 : ((1, 2) : ZMod 3 × ZMod 3) ≠ (0, 0) := by decide
theorem pair22 : ((2, 2) : ZMod 3 × ZMod 3) ≠ (0, 0) := by decide

theorem exists_partner {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 3 2 2) {y : X}
    (hy : orderOf y = 3) :
    ∃ b : X, b ^ 3 = 1 ∧ y * b = b * y ∧ ConjPm y b ∧ ConjPm y (y * b) ∧
      ConjPm y (y * b * b) := by
  classical
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨ω, hω3, hω2⟩ := exists_primitive_cube_root hk
  have hy03 : proj 3 k (torusDiag ω hω3) ^ 3 = 1 := by
    rw [← map_pow, torusDiag_pow_three, map_one]
  have hc03 : proj 3 k (cycSL (k := k)) ^ 3 = 1 := by
    rw [← map_pow, cycSL_pow_three, map_one]
  have hyc : Commute (proj 3 k (torusDiag ω hω3)) (proj 3 k cycSL) :=
    (proj_cycSL_commute hω3 hω2).symm
  set y₀ := proj 3 k (torusDiag ω hω3) with hy₀
  set c₀ := proj 3 k (cycSL (k := k)) with hc₀
  set φ := hom33 y₀ c₀ hy03 hc03 hyc with hφ
  have hconj : ∀ g, g ≠ 1 → ConjPm y₀ (φ g) := by
    intro g hg
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = g := ⟨Multiplicative.toAdd g, rfl⟩
    rw [hφ, hom33_apply]
    refine exists_conj_torusDiag_cycSL hω3 hω2 (ZMod.val_lt i) (ZMod.val_lt j) fun hij => hg ?_
    rw [(ZMod.val_eq_zero i).mp hij.1, (ZMod.val_eq_zero j).mp hij.2]
    rfl
  have hy0 : y₀ ≠ 1 := proj_torusDiag_ne_one hω3 hω2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hg1
    obtain ⟨t, h | h⟩ := hconj g hg1
    · rw [hg, eq_comm, conj_eq_one_iff] at h
      exact hy0 h
    · rw [hg, eq_comm, conj_eq_one_iff] at h
      apply hy0
      calc y₀ = y₀ ^ 3 * (y₀ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hy03, h, inv_one, one_mul]
  set ψ : Multiplicative (ZMod 3 × ZMod 3) →* X := e.symm.toMonoidHom.comp φ with hψ
  have hψinj : Function.Injective ψ := e.symm.injective.comp hinj
  have hEcard : Nat.card ψ.range = 9 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  have hE3 : IsPGroup 3 ψ.range := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hEi : ¬ 3 ∣ ψ.range.index := by
    have h := Subgroup.card_mul_index ψ.range
    rw [hEcard, card_of_lieModel hX] at h
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let SE : Sylow 3 X := hE3.toSylow hEi
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := hy3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P SE
  have hgy : g * y * g⁻¹ ∈ ψ.range := by
    have h1 : g * y * g⁻¹ ∈ ((g • P : Sylow 3 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨y, hP (Subgroup.mem_zpowers y), rfl⟩
    rw [hg] at h1
    exact h1
  obtain ⟨m, hm⟩ := hgy
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [map_one, eq_comm, conj_eq_one_iff] at hm
    rw [hm, orderOf_one] at hy
    exact absurd hy (by norm_num)
  set y₀' := e.symm y₀ with hy₀'
  set c₀' := e.symm c₀ with hc₀'
  have hconj' : ∀ g, g ≠ 1 → ConjPm y₀' (ψ g) := by
    intro g hg
    obtain ⟨t, h | h⟩ := hconj g hg
    · refine ⟨e.symm t, Or.inl ?_⟩
      show e.symm (φ g) = _
      rw [h, map_mul, map_mul, map_inv]
    · refine ⟨e.symm t, Or.inr ?_⟩
      show e.symm (φ g) = _
      rw [h, map_mul, map_mul, map_inv, map_pow]
  have hy₀3 : y₀' ^ 3 = 1 := by rw [hy₀', ← map_pow, hy03, map_one]
  have hc₀3 : c₀' ^ 3 = 1 := by rw [hc₀', ← map_pow, hc03, map_one]
  have hyc' : Commute y₀' c₀' := by
    show e.symm y₀ * e.symm c₀ = e.symm c₀ * e.symm y₀
    rw [← map_mul e.symm y₀ c₀, hyc.eq, map_mul]
  have h4 : y₀' = (y₀' ^ 2) ^ 2 := by
    calc y₀' = y₀' ^ 3 * y₀' := by rw [hy₀3, one_mul]
      _ = (y₀' ^ 2) ^ 2 := by group
  have hψapp : ∀ a b : ZMod 3, ψ (Multiplicative.ofAdd (a, b)) = y₀' ^ a.val * c₀' ^ b.val := by
    intro a b
    rw [hψ, MonoidHom.comp_apply, hφ, hom33_apply]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_pow]
    rfl
  obtain ⟨s, z, hz, hzs⟩ : ∃ s z : X, (z = y₀' ∨ z = y₀' ^ 2) ∧ y = s * z * s⁻¹ := by
    obtain ⟨t, h | h⟩ := hconj' m hm1
    · rw [hm] at h
      refine ⟨g⁻¹ * t, y₀', Or.inl rfl, ?_⟩
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = _ := by rw [h]; group
    · rw [hm] at h
      refine ⟨g⁻¹ * t, y₀' ^ 2, Or.inr rfl, ?_⟩
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = _ := by rw [h]; group
  have hy2 : y ^ 2 = s * z ^ 2 * s⁻¹ := by rw [hzs, conj_pow]
  have hkey : ConjPm y y₀' ∧ ConjPm y (y₀' ^ 2) := by
    rcases hz with rfl | rfl
    · refine ⟨⟨s⁻¹, Or.inl ?_⟩, ⟨s⁻¹, Or.inr ?_⟩⟩
      · rw [hzs]; group
      · rw [hy2]; group
    · refine ⟨⟨s⁻¹, Or.inr ?_⟩, ⟨s⁻¹, Or.inl ?_⟩⟩
      · rw [hy2, ← h4]; group
      · rw [hzs]; group
  have hC : ∀ x : X, ConjPm y₀' x → ConjPm y x := by
    rintro x ⟨t, rfl | rfl⟩
    · exact conjPm_conj hkey.1 t
    · exact conjPm_conj hkey.2 t
  have hCψ : ∀ a b : ZMod 3, (a, b) ≠ (0, 0) →
      ConjPm y (s * (y₀' ^ a.val * c₀' ^ b.val) * s⁻¹) := by
    intro a b hab
    rw [← hψapp]
    refine conjPm_conj (hC _ (hconj' _ fun h => hab ?_)) s
    exact congrArg Multiplicative.toAdd h
  have hzc : Commute z c₀' := by
    rcases hz with rfl | rfl
    · exact hyc'
    · exact hyc'.pow_left 2
  have v0 : (0 : ZMod 3).val = 0 := rfl
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  refine ⟨s * c₀' * s⁻¹, by rw [conj_pow, hc₀3, mul_one, mul_inv_cancel], ?_, ?_, ?_, ?_⟩
  · rw [hzs]
    calc s * z * s⁻¹ * (s * c₀' * s⁻¹) = s * (z * c₀') * s⁻¹ := by group
      _ = s * (c₀' * z) * s⁻¹ := by rw [hzc.eq]
      _ = _ := by group
  · have h := hCψ 0 1 pair01
    rwa [v0, v1, pow_zero, pow_one, one_mul] at h
  · have e1 : y * (s * c₀' * s⁻¹) = s * (z * c₀') * s⁻¹ := by rw [hzs]; group
    rw [e1]
    rcases hz with rfl | rfl
    · have h := hCψ 1 1 pair11
      rwa [v1, pow_one, pow_one] at h
    · have h := hCψ 2 1 pair21
      rwa [v2, v1, pow_one] at h
  · have e1 : y * (s * c₀' * s⁻¹) * (s * c₀' * s⁻¹) = s * (z * c₀' ^ 2) * s⁻¹ := by
      calc y * (s * c₀' * s⁻¹) * (s * c₀' * s⁻¹)
          = s * z * s⁻¹ * (s * c₀' * s⁻¹) * (s * c₀' * s⁻¹) := by rw [hzs]
        _ = s * (z * (c₀' * c₀')) * s⁻¹ := by group
        _ = s * (z * c₀' ^ 2) * s⁻¹ := by rw [sq]
    rw [e1]
    rcases hz with rfl | rfl
    · have h := hCψ 1 2 pair12
      rwa [v1, v2, pow_one] at h
    · have h := hCψ 2 2 pair22
      rwa [v2] at h

end CFSG.Quasithin.H13.TorusComm

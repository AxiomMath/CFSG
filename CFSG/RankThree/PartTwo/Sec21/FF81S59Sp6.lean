module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RSevSp
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec8.Hering418
open CFSG.RankThree.PartTwo.Sec4.Res417Four (sm6 mk6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 mat6 mat6_apply mat6_injective card_H6 ε6)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Matrix

local instance decEqH6 : DecidableEq H6 := inferInstance

theorem exists_poly_of_commute_z7M (C : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hC : C * z7M = z7M * C) : ∃ a : Fin 6 → ZMod 2, C = ∑ i : Fin 6, a i • z7M ^ (i : ℕ) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 6 → ZMod 2, a = kryMi *ᵥ (C *ᵥ z7Vec) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 6) (Fin 6) (ZMod 2),
      P = ∑ i : Fin 6, a i • z7M ^ (i : ℕ) := ⟨_, rfl⟩
  have hCc : Commute C z7M := hC
  have hPz : Commute P z7M := by
    rw [hP]
    exact Commute.sum_left _ _ _ fun i _ => ((Commute.refl z7M).pow_left (i : ℕ)).smul_left (a i)
  have hPv : P *ᵥ z7Vec = C *ᵥ z7Vec := by
    rw [hP, sum_smul_pow_mulVec, ha, Matrix.mulVec_mulVec, kryM_mul_kryMi, Matrix.one_mulVec]
  have hcore : ∀ j : ℕ, C *ᵥ ((z7M ^ j) *ᵥ z7Vec) = P *ᵥ ((z7M ^ j) *ᵥ z7Vec) := by
    intro j
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hCc.pow_right j).eq,
      (hPz.pow_right j).eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hPv]
  have hcolK : ∀ (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (r c : Fin 6),
      (M * kryM) r c = (M *ᵥ ((z7M ^ (c : ℕ)) *ᵥ z7Vec)) r := by
    intro M r c
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, kryM_apply]
  have hCK : C * kryM = P * kryM := by
    ext r c
    rw [hcolK, hcolK, hcore]
  have hCP : C = P := by
    calc C = C * (kryM * kryMi) := by rw [kryM_mul_kryMi, mul_one]
      _ = (C * kryM) * kryMi := (Matrix.mul_assoc _ _ _).symm
      _ = (P * kryM) * kryMi := by rw [hCK]
      _ = P * (kryM * kryMi) := Matrix.mul_assoc _ _ _
      _ = P := by rw [kryM_mul_kryMi, mul_one]
  exact ⟨a, by rw [hCP, hP]⟩

set_option maxRecDepth 100000 in
theorem poly_symp_check : ∀ a : Fin 6 → ZMod 2,
    (sm6 (∑ i : Fin 6, a i • z7M ^ (i : ℕ)))ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        sm6 (∑ i : Fin 6, a i • z7M ^ (i : ℕ)) = Matrix.fromBlocks 0 1 (-1) 0 →
      ∃ k : Fin 7, (∑ i : Fin 6, a i • z7M ^ (i : ℕ)) = z7M ^ (k : ℕ) := by
  decide +kernel

theorem symp_mat6 (C : H6) :
    (sm6 (mat6 C))ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 (mat6 C) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  have h1 : sm6 (mat6 C) = ((C : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
    rw [mat6_apply]
    exact CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.submatrix_ε6_symm _
  rw [h1]
  exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp C.2

theorem eq_pow_z7_of_commute (C : H6) (hC : C * z7 = z7 * C) : C ∈ Subgroup.zpowers z7 := by
  have hM : mat6 C * z7M = z7M * mat6 C := by
    rw [← mat6_z7, ← map_mul, ← map_mul, hC]
  obtain ⟨a, ha⟩ := exists_poly_of_commute_z7M _ hM
  have hs := symp_mat6 C
  rw [ha] at hs
  obtain ⟨k, hk⟩ := poly_symp_check a hs
  rw [← ha] at hk
  refine ⟨((k : ℕ) : ℤ), ?_⟩
  apply mat6_injective
  simp only [zpow_natCast, map_pow, mat6_z7]
  exact hk.symm

@[expose] def h0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0]

@[expose] def h0Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0]

theorem h0_check : sm6 h0M * sm6 h0Mi = 1 ∧ sm6 h0Mi * sm6 h0M = 1 ∧
    (sm6 h0M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 h0M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def h0 : H6 := mk6 h0M h0Mi h0_check

theorem mat6_h0 : mat6 h0 = h0M :=
  mat6_mk6 h0M h0Mi h0_check

theorem h0M_twist : h0M * z7M = z7M ^ 3 * h0M := by
  decide +kernel

theorem h0_twist : h0 * z7 * h0⁻¹ = z7 ^ 3 := by
  have h : h0 * z7 = z7 ^ 3 * h0 := by
    apply mat6_injective
    simp only [map_mul, map_pow, mat6_h0, mat6_z7]
    exact h0M_twist
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem exists_conj_generator (γ : H6) (hγ : orderOf γ = 7) :
    ∃ (g w : H6), g * w * g⁻¹ = z7 ∧ Subgroup.zpowers w = Subgroup.zpowers γ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hzc : Nat.card (Subgroup.zpowers γ) = 7 := by rw [Nat.card_zpowers, hγ]
  have hz7c : Nat.card (Subgroup.zpowers z7) = 7 := by rw [Nat.card_zpowers, orderOf_z7]
  have hzP : IsPGroup 7 (Subgroup.zpowers γ) :=
    IsPGroup.of_card (n := 1) (by rw [hzc, pow_one])
  have hz7P : IsPGroup 7 (Subgroup.zpowers z7) :=
    IsPGroup.of_card (n := 1) (by rw [hz7c, pow_one])
  have hzi : ¬ 7 ∣ (Subgroup.zpowers γ).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers γ)
    rw [hzc, card_H6] at h
    have h' : (Subgroup.zpowers γ).index = 207360 := by omega
    rw [h']
    norm_num
  have hz7i : ¬ 7 ∣ (Subgroup.zpowers z7).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers z7)
    rw [hz7c, card_H6] at h
    have h' : (Subgroup.zpowers z7).index = 207360 := by omega
    rw [h']
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H6 (hzP.toSylow hzi) (hz7P.toSylow hz7i)
  have hmap : (Subgroup.zpowers γ).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z7 := by
    have h1 : ((g • hzP.toSylow hzi : Sylow 7 H6) : Subgroup H6) =
        ((hz7P.toSylow hz7i : Sylow 7 H6) : Subgroup H6) := by
      rw [hg]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1
  have hz7mem : z7 ∈ (Subgroup.zpowers γ).map (MulAut.conj g).toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_zpowers z7
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz7mem
  have hgw : g * w * g⁻¹ = z7 := hwz
  refine ⟨g, w, hgw, ?_⟩
  have hwo : orderOf w = 7 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
    have h' : (MulAut.conj g).toMonoidHom w = z7 := hgw
    rw [h', orderOf_z7] at h
    exact h.symm
  have hle : Subgroup.zpowers w ≤ Subgroup.zpowers γ := (Subgroup.zpowers_le).mpr hw
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hzc, Nat.card_zpowers, hwo]

theorem H6_seven (γ : H6) (hγ : orderOf γ = 7) :
    (∀ c : H6, c * γ = γ * c → c ∈ Subgroup.zpowers γ) ∧ ∃ h : H6, h * γ * h⁻¹ = γ ^ 3 := by
  obtain ⟨g, w, hgw, hzw⟩ := exists_conj_generator γ hγ
  have hwγ : w ∈ Subgroup.zpowers γ := hzw ▸ Subgroup.mem_zpowers w
  have hγw : γ ∈ Subgroup.zpowers w := hzw ▸ Subgroup.mem_zpowers γ
  refine ⟨fun c hc => ?_, g⁻¹ * h0 * g, ?_⟩
  ·
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwγ
    have hcw : c * w = w * c := by
      rw [← hm]
      exact ((show Commute c γ from hc).zpow_right m).eq
    have hcz : g * c * g⁻¹ * z7 = z7 * (g * c * g⁻¹) := by
      rw [← hgw]
      calc g * c * g⁻¹ * (g * w * g⁻¹) = g * (c * w) * g⁻¹ := by group
        _ = g * (w * c) * g⁻¹ := by rw [hcw]
        _ = g * w * g⁻¹ * (g * c * g⁻¹) := by group
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (eq_pow_z7_of_commute (g * c * g⁻¹) hcz)
    have hcn : c = w ^ n := by
      have h1 : g * c * g⁻¹ = g * w ^ n * g⁻¹ := by
        rw [← hn, ← hgw]
        exact conj_zpow (a := g) (b := w) (i := n)
      have h2 := mul_right_cancel h1
      exact mul_left_cancel h2
    rw [hcn]
    exact Subgroup.zpow_mem _ hwγ n
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hγw
    have hhw : g⁻¹ * h0 * g * w * (g⁻¹ * h0 * g)⁻¹ = w ^ 3 := by
      have h1 : g⁻¹ * h0 * g * w * (g⁻¹ * h0 * g)⁻¹ = g⁻¹ * (h0 * (g * w * g⁻¹) * h0⁻¹) * g := by
        group
      rw [h1, hgw, h0_twist, ← hgw]
      calc g⁻¹ * (g * w * g⁻¹) ^ 3 * g = g⁻¹ * (g * w ^ 3 * g⁻¹) * g := by rw [conj_pow]
        _ = w ^ 3 := by group
    have hpow : (w ^ 3) ^ k = (w ^ k) ^ 3 := by
      rw [← zpow_natCast w 3, ← zpow_mul, ← zpow_natCast (w ^ k) 3, ← zpow_mul, mul_comm]
    rw [← hk, ← conj_zpow, hhw, hpow]

theorem sp6_seven {G : Type} [Group G] {L : Subgroup G}
    (hL : StatedClassicalModel L .PSp 3 2 1) {γ : G} (hγL : γ ∈ L) (hγ : orderOf γ = 7) :
    (∀ x ∈ L, x * γ = γ * x → x ∈ Subgroup.zpowers γ) ∧
      ∃ h ∈ L, h * γ * h⁻¹ = γ ^ 3 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated hL
  have hγ' : orderOf (e ⟨γ, hγL⟩) = 7 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hγ
  obtain ⟨hc, h', hh'⟩ := H6_seven (e ⟨γ, hγL⟩) hγ'
  refine ⟨fun x hx hxγ => ?_, (e.symm h' : L), (e.symm h').2, ?_⟩
  · have hcomm : e ⟨x, hx⟩ * e ⟨γ, hγL⟩ = e ⟨γ, hγL⟩ * e ⟨x, hx⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxγ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc _ hcomm)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : e ((⟨γ, hγL⟩ : L) ^ k) = e ⟨x, hx⟩ := by rw [map_zpow]; exact hk
    exact congrArg Subtype.val (e.injective h1)
  · have h1 : e.symm h' * ⟨γ, hγL⟩ * (e.symm h')⁻¹ = (⟨γ, hγL⟩ : L) ^ 3 := by
      apply e.injective
      simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
      exact hh'
    exact congrArg Subtype.val h1

end CFSG.RankThree.PartTwo.Sec21.FF81.S59

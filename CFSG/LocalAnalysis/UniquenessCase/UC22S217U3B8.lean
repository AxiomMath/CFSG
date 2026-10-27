module

public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTorus
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

private def uc22s217u3b8_e : Fin 3 → ℕ := ![1, 7, 55]

private theorem uc22s217u3b8_e_rev :
    ∀ s : Fin 3, 63 ∣ uc22s217u3b8_e s * 2 ^ 3 + uc22s217u3b8_e (Fin.rev s) := by
  decide

private theorem uc22s217u3b8_e_sum :
    63 ∣ uc22s217u3b8_e 0 + uc22s217u3b8_e 1 + uc22s217u3b8_e 2 := by
  decide

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem uc22s217u3b8_pow_of_dvd {w : K} (hw : w ^ 63 = 1) {m : ℕ} (h : 63 ∣ m) :
    w ^ m = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, hw, one_pow]

private def uc22s217u3b8_d (w : K) (s : Fin 3) : K := w ^ uc22s217u3b8_e s

private theorem uc22s217u3b8_d_unitary {w : K} (hw : w ^ 63 = 1) (s : Fin 3) :
    unitaryInvolution K 2 3 (uc22s217u3b8_d w s) * uc22s217u3b8_d w (Fin.rev s) = 1 := by
  rw [unitaryInvolution_apply, uc22s217u3b8_d, uc22s217u3b8_d, ← pow_mul, ← pow_add]
  exact uc22s217u3b8_pow_of_dvd hw (uc22s217u3b8_e_rev s)

private theorem uc22s217u3b8_d_det {w : K} (hw : w ^ 63 = 1) :
    (diagonal (uc22s217u3b8_d w)).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three, uc22s217u3b8_d, uc22s217u3b8_d, uc22s217u3b8_d,
    ← pow_add, ← pow_add]
  exact uc22s217u3b8_pow_of_dvd hw uc22s217u3b8_e_sum

private noncomputable def uc22s217u3b8_g {w : K} (hw : w ^ 63 = 1) :
    SU (unitaryInvolution K 2 3) 3 :=
  ⟨CFSG.StandardType.InnerDiagSU.diagJ (uc22s217u3b8_d w) (uc22s217u3b8_d_unitary hw),
    mem_SU.2 ⟨uc22s217u3b8_d_det hw,
      CFSG.StandardType.InnerDiagSU.isJUnitary_diagJ _ (uc22s217u3b8_d_unitary hw)⟩⟩

private theorem uc22s217u3b8_g_mat {w : K} (hw : w ^ 63 = 1) :
    SUExtras.mat (unitaryInvolution K 2 3) 3 (uc22s217u3b8_g hw) = diagonal (uc22s217u3b8_d w) :=
  rfl

private theorem uc22s217u3b8_g_pow_mat {w : K} (hw : w ^ 63 = 1) (m : ℕ) :
    SUExtras.mat (unitaryInvolution K 2 3) 3 (uc22s217u3b8_g hw ^ m) =
      diagonal (fun s => w ^ (uc22s217u3b8_e s * m)) := by
  rw [map_pow, uc22s217u3b8_g_mat, Matrix.diagonal_pow]
  congr 1
  funext s
  rw [Pi.pow_apply, uc22s217u3b8_d, ← pow_mul]

private theorem uc22s217u3b8_eq_of_mem_center (hK : Nat.card K = (2 ^ 3) ^ 2) {w : K}
    (hw : w ^ 63 = 1) {m : ℕ}
    (hm : uc22s217u3b8_g hw ^ m ∈ center (SU (unitaryInvolution K 2 3) 3)) :
    w ^ m = w ^ (7 * m) := by
  obtain ⟨c, hc⟩ := CFSG.StandardType.InnerDiagSU.exists_scalar_of_mem_center hK (n := 3)
    (by norm_num) (by decide) hm
  rw [uc22s217u3b8_g_pow_mat] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  rw [Matrix.diagonal_apply_eq, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e00 e11
  have h0 : uc22s217u3b8_e 0 * m = m := by rw [show uc22s217u3b8_e 0 = 1 from rfl, one_mul]
  have h1 : uc22s217u3b8_e 1 * m = 7 * m := by rw [show uc22s217u3b8_e 1 = 7 from rfl]
  rw [h0] at e00
  rw [h1] at e11
  exact e00.trans e11.symm

theorem uc22s217u3b8_exists_torus (hK : Nat.card K = (2 ^ 3) ^ 2) :
    ∃ g : SU (unitaryInvolution K 2 3) 3, g ^ 63 = 1 ∧
      g ^ 9 ∉ center (SU (unitaryInvolution K 2 3) 3) ∧
      ∀ k : ℕ, g ^ (7 * k) ∈ center (SU (unitaryInvolution K 2 3) 3) → 3 ∣ k := by
  obtain ⟨w₀, hw₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hwo : orderOf (w₀ : K) = 63 := by
    rw [orderOf_units, hw₀, Nat.card_units, hK]
    norm_num
  have hw : (w₀ : K) ^ 63 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one _
  have hw0 : (w₀ : K) ≠ 0 := w₀.ne_zero
  refine ⟨uc22s217u3b8_g hw, ?_, fun h => ?_, fun k hk => ?_⟩
  · apply SUExtras.mat_injective
    rw [uc22s217u3b8_g_pow_mat, map_one, ← Matrix.diagonal_one]
    congr 1
    funext s
    exact uc22s217u3b8_pow_of_dvd hw (dvd_mul_left 63 _)
  ·
    have h1 := uc22s217u3b8_eq_of_mem_center hK hw h
    rw [show 7 * 9 = 63 from rfl, hw] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hwo] at h2
    norm_num at h2
  ·
    have h1 := uc22s217u3b8_eq_of_mem_center hK hw hk
    have h2 : (w₀ : K) ^ (42 * k) = 1 := by
      have h3 : (w₀ : K) ^ (42 * k) * (w₀ : K) ^ (7 * k) = 1 * (w₀ : K) ^ (7 * k) := by
        rw [← pow_add, one_mul, show 42 * k + 7 * k = 7 * (7 * k) by ring, ← h1]
      exact mul_right_cancel₀ (pow_ne_zero _ hw0) h3
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hwo] at h3
    omega

end Torus

variable {X : Type} [Group X] [Finite X]

private theorem uc22s217u3b8_factorization_seven {m : ℕ} (hm : ¬ 7 ∣ m) :
    (7 * m).factorization 7 = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 7)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd hm]

theorem uc22s217u3b8_exists_fix
    (hX : IsSU3 X 3) (hZ : Nat.card (center X) ∣ 3)
    {α : MulAut X} (hα7 : α ^ 7 = 1) (hα : α ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ u : X, α u = u ∧ u ^ 9 = 1 ∧ ∀ k : ℕ, u ^ k ∈ center X → 3 ∣ k := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hq, hU3⟩ := hX
  have hXZ : Nat.card (X ⧸ center X) = 5515776 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide))
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two (n := 6) (hK.trans (by norm_num))
  obtain ⟨β, hβ, hβc, -⟩ := uc22pwsu3_exists_cover (by norm_num) hK hq e₁
  have hSp : Group.IsPerfect (SU (unitaryInvolution K 2 3) 3) :=
    Group.isPerfect_def.2 (uc22pwsu3_commutator_eq_top (by norm_num) hK)
  have hcen : ∀ s, β s ∈ center X → s ∈ center (SU (unitaryInvolution K 2 3) 3) := fun s hs => by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hSp β hβ hβc]
    exact hs
  obtain ⟨g, hg63, hg9, hg7⟩ := uc22s217u3b8_exists_torus hK
  have hd7 : (β g ^ 9) ^ 7 = 1 := by rw [← pow_mul, ← map_pow, hg63, map_one]
  have hd1 : β g ^ 9 ≠ 1 := fun h => hg9 (hβc (by rw [MonoidHom.mem_ker, map_pow, h]))
  have hdo : orderOf (β g ^ 9) = 7 := orderOf_eq_prime hd7 hd1
  have hu9 : (β g ^ 7) ^ 9 = 1 := by rw [← pow_mul, ← map_pow, hg63, map_one]
  have huZ : ∀ k : ℕ, (β g ^ 7) ^ k ∈ center X → 3 ∣ k := fun k hk =>
    hg7 k (hcen _ (by rw [map_pow, pow_mul]; exact hk))
  have hZ3 : ∀ z ∈ center X, z ^ 3 = 1 := fun z hz => UCK.pow_three_eq_one_of_mem_center hZ hz
  obtain ⟨b, hb, hb7⟩ := UCK.exists_inner_gen_pow_eq_one hZ3 (by norm_num) (by norm_num) hα7 hα
  by_cases hb1 : b = 1
  · refine ⟨β g ^ 7, ?_, hu9, huZ⟩
    rw [← hb, hb1, map_one]
    rfl
  have hbo : orderOf b = 7 := orderOf_eq_prime hb7 hb1
  have hfac : (Nat.card X).factorization 7 = 1 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hXZ]
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h | h
    · rw [h, show 5515776 * 1 = 7 * 787968 by norm_num]
      exact uc22s217u3b8_factorization_seven (by norm_num)
    · rw [h, show 5515776 * 3 = 7 * 2363904 by norm_num]
      exact uc22s217u3b8_factorization_seven (by norm_num)
  have hdc : Nat.card (zpowers (β g ^ 9)) = 7 ^ (Nat.card X).factorization 7 := by
    rw [Nat.card_zpowers, hdo, hfac, pow_one]
  have hbc : Nat.card (zpowers b) = 7 ^ (Nat.card X).factorization 7 := by
    rw [Nat.card_zpowers, hbo, hfac, pow_one]
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (Sylow.ofCard _ hdc) (Sylow.ofCard _ hbc)
  have hbQ : b ∈ ((x • Sylow.ofCard _ hdc : Sylow 7 X) : Set X) := by
    rw [hx]
    exact Subgroup.mem_zpowers b
  rw [Sylow.coe_smul] at hbQ
  obtain ⟨p, hp, hpb⟩ := Set.mem_smul_set.1 hbQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hpb
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (show p ∈ zpowers (β g ^ 9) from hp)
  have hcomm : Commute b (x * β g ^ 7 * x⁻¹) := by
    rw [← hpb, ← hj]
    have h1 : Commute ((β g ^ 9) ^ j) (β g ^ 7) := ((Commute.refl (β g)).pow_pow 9 7).zpow_left j
    simpa only [MulAut.conj_apply] using h1.map (MulAut.conj x)
  refine ⟨x * β g ^ 7 * x⁻¹, ?_, ?_, fun k hk => huZ k ?_⟩
  · rw [← hb, MulAut.conj_apply, hcomm.eq, mul_inv_cancel_right]
  · rw [conj_pow, hu9, mul_one, mul_inv_cancel]
  · rw [conj_pow] at hk
    have h2 := Subgroup.mem_center_iff.1 hk x
    have h1 : (β g ^ 7) ^ k = x * (β g ^ 7) ^ k * x⁻¹ := by
      calc (β g ^ 7) ^ k = x⁻¹ * ((x * (β g ^ 7) ^ k * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * (β g ^ 7) ^ k * x⁻¹)) := by rw [h2]
        _ = x * (β g ^ 7) ^ k * x⁻¹ := by group
    rw [h1]
    exact hk

theorem uc22s217u3b8_fix_three
    (hCen : UCK.U3Center) (hX : IsSU3 X 3) {α : MulAut X}
    (hα7 : α ^ 7 = 1) (hα : α ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ z : X, orderOf z = 3 ∧ α z = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu, hu9, huZ⟩ := uc22s217u3b8_exists_fix hX (hCen X 3 hX) hα7 hα
  have hu1 : u ≠ 1 := fun h => by
    have := huZ 1 (by rw [pow_one, h]; exact (center X).one_mem)
    omega
  by_cases h3 : u ^ 3 = 1
  · exact ⟨u, orderOf_eq_prime h3 hu1, hu⟩
  · refine ⟨u ^ 3, orderOf_eq_prime (by rw [← pow_mul]; exact hu9) h3, ?_⟩
    rw [map_pow, hu]

end CFSG.LocalAnalysis.UniquenessCase.UC22

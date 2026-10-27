module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.H13.A5W1622b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

noncomputable def kbarEquivOfSurj {G : Type} [Group G] {K : Subgroup G} {X : Type} [Group X]
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem sl2_card_ne {n c : ℕ} (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 2520 * c := by
  intro h
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n <;> omega
  · have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have h1 : 255 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h2 : 16 * 255 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h16 h1
    have hdvd : 2 ^ n ∣ 2520 * c := ⟨_, h.symm⟩
    have h32 : 32 ∣ 2 ^ n ∨ 2 ^ n = 16 := by
      rcases Nat.lt_or_ge n 5 with h5 | h5
      · right; interval_cases n; rfl
      · left
        calc 32 = 2 ^ 5 := by norm_num
          _ ∣ 2 ^ n := pow_dvd_pow 2 h5
    rcases h32 with h32 | h32
    · have := dvd_trans h32 hdvd
      interval_cases c <;> omega
    · rw [h32] at h
      omega

theorem center_eq_bot_of_isSimple_of_isQuasisimple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hq : CFSG.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [(QuotientGroup.eq_one_iff a).mpr (h ▸ Subgroup.mem_top a),
      (QuotientGroup.eq_one_iff b).mpr (h ▸ Subgroup.mem_top b)]

theorem eq_seven_of_factorial {m : ℕ} (h : Nat.factorial m = 5040) : m = 7 := by
  have h1 : m ≤ 7 := by
    by_contra hm
    have : Nat.factorial 8 ≤ Nat.factorial m := Nat.factorial_le (by omega)
    rw [h] at this
    norm_num [Nat.factorial] at this
  interval_cases m
  all_goals first | rfl | (norm_num [Nat.factorial] at h)

theorem two_mul_card_alt {m : ℕ} (hm : 2 ≤ m) :
    2 * Nat.card (alternatingGroup (Fin m)) = Nat.factorial m := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin m)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin m)), Fintype.card_perm,
    Fintype.card_fin] at h2
  exact h2

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem z_eq_v12_mul_e2 : S.z = S.v12 * S.e2 := by
  have h : S.frame.ψ ⟨S.z, S.z_mem_V⟩ =
      S.frame.ψ ⟨S.v12 * S.e2, V.mul_mem S.v12_mem_V S.e2_mem_V⟩ := by
    have e : (⟨S.v12 * S.e2, V.mul_mem S.v12_mem_V S.e2_mem_V⟩ : ↥V) =
        ⟨S.v12, S.v12_mem_V⟩ * ⟨S.e2, S.e2_mem_V⟩ := rfl
    rw [e, map_mul, S.psi_z, S.psi_v12, S.psi_e2]
    exact e23_props.2.2.2.2.symm
  exact congrArg Subtype.val (S.frame.ψ.injective h)

theorem not_Lv_le_centralizer_z : ¬ S.Lv ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro h
  obtain ⟨y, hy, hyN, hτ⟩ := S.exists_Lv_line
  obtain ⟨hyp, -⟩ := conj_q_line hyN hτ
  apply hyp
  have hyz : y * S.z * y⁻¹ = S.z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (h hy), mul_inv_cancel_right]
  have hyv : y * S.v12 * y⁻¹ = S.v12 := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (S.Lv_le_Gv hy), mul_inv_cancel_right]
  rw [S.z_eq_v12_mul_e2] at hyz
  calc y * S.e2 * y⁻¹ = (y * S.v12 * y⁻¹)⁻¹ * (y * (S.v12 * S.e2) * y⁻¹) := by group
    _ = S.e2 := by rw [hyv, hyz]; group

theorem sqtkGroup_sup_Tv {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) : SQTKGroup ↥(K₀ ⊔ S.Tv) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := K₀ ⊔ S.Tv with hHdef
  have hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hO : pCoreOf 2 H ≠ ⊥ := by
    have hle : Subgroup.zpowers S.v12 ≤ H := (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    intro h
    have hvO := le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
    rw [h, Subgroup.mem_bot] at hvO
    exact S.v12_ne_one hvO
  exact sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO

end Setting

end CFSG.Quasithin.H13.A5

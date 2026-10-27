module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Str
public import CFSG.Quasithin.EmptyFaithful.S152Z2A

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.N204
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

namespace YCtx

variable {T Mc M : Subgroup G} (c : YCtx T Mc M)

include c

theorem exists_pow_of_five {y : G} (hyY : y ∈ yOf152 T Mc M) (hy5 : orderOf y = 5) :
    ∀ x ∈ yOf152 T Mc M, ∃ n : ℕ, (y ^ n)⁻¹ * x ∈ pCoreOf 2 (yOf152 T Mc M) := by
  set Y := yOf152 T Mc M with hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : (pCoreOf 2 Y).relIndex Y = 5 := c.relIndex_five
  let y₀ : ↥Y := ⟨y, hyY⟩
  have hy₀ : orderOf y₀ = 5 := by rw [← Subgroup.orderOf_coe]; exact hy5
  have hy₀Q : y ∉ pCoreOf 2 Y := by
    intro hmem
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨y, hmem⟩
    have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h5d : 5 ∣ 2 ^ k := hy5 ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5d
    omega
  let N : Subgroup ↥Y := (pCoreOf 2 Y).subgroupOf Y
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 Y)
  have hcard : Nat.card (↥Y ⧸ N) = 5 := h5
  have hne : (QuotientGroup.mk y₀ : ↥Y ⧸ N) ≠ 1 := fun h =>
    hy₀Q (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y₀).mp h))
  have htop := zpowers_eq_top_of_prime_card hcard hne
  intro x hx
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥Y ⧸ N) ∈ Subgroup.zpowers (QuotientGroup.mk y₀) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  have hk' := Subgroup.mem_subgroupOf.mp hk
  have hyk : y ^ k = y ^ (k % 5).toNat := by
    have h1 : y ^ (k % (orderOf y : ℤ)) = y ^ k := zpow_mod_orderOf y k
    rw [hy5] at h1
    rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    norm_num
  refine ⟨(k % 5).toNat, ?_⟩
  rw [← hyk]
  exact hk'

end YCtx

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem pCoreY_le_pCoreG₁ :
    pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g1Of T Mc M K₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (pCoreOf_isPGroup 2 _)
  · exact (pCoreOf_le 2 _).trans (Y_le_l1.trans (le_sup_left.trans le_sup_left))
  · exact c.G₁_le_M.trans (c.y.normal.trans (normalizer_le_normalizer_pCoreOf 2 _))

theorem commutator_pow_mem {y : G} (hyG : y ∈ g0Of T Mc M K₁)
    (hy : ∀ p ∈ pCoreOf 2 (g1Of T Mc M K₁), ⁅y, p⁆ ∈ pCoreOf 2 (g0Of T Mc M K₁)) (n : ℕ)
    {p : G} (hp : p ∈ pCoreOf 2 (g1Of T Mc M K₁)) : ⁅y ^ n, p⁆ ∈ pCoreOf 2 (g0Of T Mc M K₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : y ∈ Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G) :=
    le_normalizer_pCoreOf 2 _ hyG
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ⁅y ^ (n + 1), p⁆ = y * ⁅y ^ n, p⁆ * y⁻¹ * ⁅y, p⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 (g0Of T Mc M K₁)).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hnorm _).mp ih) (hy p hp)

theorem charTwo_G₀_of_five (hJ : thompsonJ T ≤ sOf T K₁) (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M)
    (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥) {y : G} (hyY : y ∈ yOf152 T Mc M)
    (hy5 : orderOf y = 5)
    (hy : ∀ p ∈ pCoreOf 2 (g1Of T Mc M K₁), ⁅y, p⁆ ∈ pCoreOf 2 (g0Of T Mc M K₁)) :
    CharTwo (g0Of T Mc M K₁) := by
  have hq := c.hs.qtfe
  set V := V154 T Mc M with hV
  set Y := yOf152 T Mc M with hY
  set Q₀ := pCoreOf 2 (g0Of T Mc M K₁) with hQ₀
  have h1 : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp c.y.hYV
  have hV₀P : ⁅V, Y⁆ ≤ pCoreOf 2 (g1Of T Mc M K₁) := c.commV_le_pCoreY.trans c.pCoreY_le_pCoreG₁
  have hV₀S : ⁅V, Y⁆ ≤ sOf T K₁ := c.commV_le_pCoreY.trans c.pCoreY_le_S
  have hV₀G : ⁅V, Y⁆ ≤ g0Of T Mc M K₁ := hV₀S.trans S_le_G₀
  have hV₀T : ⁅V, Y⁆ ≤ T := hV₀S.trans S_le_T
  have hTV₀ : T ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) :=
    Z2.le_normalizer_commutator c.T_le_normalizer_V c.T_le_normalizer_Y
  have hyG : y ∈ g0Of T Mc M K₁ := Y_le_G₀ hyY
  have hcomm : ⁅⁅V, Y⁆, Y⁆ ≤ Q₀ := by
    refine Subgroup.commutator_le.mpr fun v hv x hx => ?_
    obtain ⟨n, hn⟩ := c.y.exists_pow_of_five hyY hy5 x hx
    obtain ⟨o, ho⟩ : ∃ o, o = (y ^ n)⁻¹ * x := ⟨_, rfl⟩
    rw [← ho] at hn
    have hxo : x = y ^ n * o := by rw [ho]; group
    have hoV := Subgroup.mem_centralizer_iff.mp (by
      rw [c.y.pCoreY_eq] at hn
      exact hn.2)
    have hvV : v ∈ V := h1 hv
    have hc : o * v⁻¹ = v⁻¹ * o := (hoV v⁻¹ (V.inv_mem hvV)).symm
    have h2 : ⁅v, x⁆ = ⁅v, y ^ n⁆ := by
      rw [hxo, commutatorElement_def, commutatorElement_def]
      calc v * (y ^ n * o) * v⁻¹ * (y ^ n * o)⁻¹
          = v * y ^ n * (o * v⁻¹ * o⁻¹) * (y ^ n)⁻¹ := by group
        _ = v * y ^ n * v⁻¹ * (y ^ n)⁻¹ := by rw [hc]; group
    rw [h2, ← commutatorElement_inv]
    exact Q₀.inv_mem (c.commutator_pow_mem hyG hy n (hV₀P hv))
  have hV₀Q : ⁅V, Y⁆ ≤ Q₀ := by
    have := c.commV_idem
    rw [this] at hcomm
    exact hcomm
  obtain ⟨z, hzV₀, hz1, hzZ⟩ :=
    exists_ne_one_mem_omegaOneCenter_of_normalized hq.sylow.1 hV₀T c.commV_ne_bot hTV₀
  have hzm := mem_quasithinOmegaOneCenter_iff.mp hzZ
  refine c.charTwo_G₀_of_inf_center hJ hU hne ?_
  intro hbot
  have hzmem : z ∈ Q₀ ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
    ⟨hV₀Q hzV₀, hzm.1, hzm.2.1⟩
  rw [hbot] at hzmem
  exact hz1 (Subgroup.mem_bot.mp hzmem)

end Ctx15204

end CFSG.Quasithin.He9

module

public import CFSG.Quasithin.Recognition.RuTypeJ210d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace Sigma

theorem exists_conj_sq_five : ∀ g : SigmaL2F4, (g ^ 5 = 1 ∧ g ≠ 1) →
    ∃ x : SigmaL2F4, x * g * x⁻¹ = g ^ 2 := by
  decide +kernel

end Sigma

variable {G : Type} [Group G]

omit [Group G] in
theorem centralizer_zpowers_eq [Group G] (b : G) :
    Subgroup.centralizer (Subgroup.zpowers b : Set G) = G5 b := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem conj_mem_G5_of_normalizes [Finite G] {b c g : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) (hg : g ∈ G5 b) :
    c * g * c⁻¹ ∈ G5 b := by
  rw [← centralizer_zpowers_eq] at hg ⊢
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro y hy
  have hy' : c⁻¹ * y * c ∈ Subgroup.zpowers b := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hc) y).mp hy
    simpa using this
  have h1 := hg _ hy'
  calc y * (c * g * c⁻¹) = c * ((c⁻¹ * y * c) * g) * c⁻¹ := by group
    _ = c * (g * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = c * g * c⁻¹ * y := by group

theorem conj_mem_P5_of_normalizes [Finite G] {b c x : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) (hx : x ∈ P5 b) :
    c * x * c⁻¹ ∈ P5 b := by
  let α : G5 b ≃* G5 b :=
    { toFun := fun g => ⟨c * g * c⁻¹, conj_mem_G5_of_normalizes hc g.2⟩
      invFun := fun g => ⟨c⁻¹ * g * c, by
        have := conj_mem_G5_of_normalizes (inv_mem hc) g.2
        simpa using this⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨_, oddCore_map α hy, rfl⟩

theorem conj_pow_sq {b h : G} (hh : h * b * h⁻¹ = b ^ 2) (n : ℕ) :
    h ^ n * b * (h ^ n)⁻¹ = b ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc h ^ (n + 1) * b * (h ^ (n + 1))⁻¹ = h * (h ^ n * b * (h ^ n)⁻¹) * h⁻¹ := by
          rw [pow_succ']; group
      _ = h * b ^ (2 ^ n) * h⁻¹ := by rw [ih]
      _ = (h * b * h⁻¹) ^ (2 ^ n) := by rw [conj_pow]
      _ = b ^ (2 ^ (n + 1)) := by rw [hh, ← pow_mul, pow_succ, mul_comm]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem exists_conj_sq : ∃ h ∈ ruH M.T, h * b * h⁻¹ = b ^ 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set β : ruH M.T := ⟨b, hbH⟩ with hβ
  obtain ⟨hφ5, hφ1⟩ := φ_b_props hbH hb5
  have hφo : orderOf (M.φ β) = 5 := orderOf_eq_prime hφ5 hφ1
  obtain ⟨x, hx⟩ := Sigma.exists_conj_sq_five (M.φ β) ⟨hφ5, hφ1⟩
  obtain ⟨h0, rfl⟩ := M.φ_surj x
  set X : Subgroup (ruH M.T) := (Subgroup.zpowers (M.φ β)).comap M.φ with hXdef
  have hXidx : X.index = 24 := by
    rw [hXdef, Subgroup.index_comap_of_surjective _ M.φ_surj]
    have h := (Subgroup.zpowers (M.φ β)).card_mul_index
    rw [Nat.card_zpowers, hφo, Sigma.card_Sigma'] at h
    omega
  have hXcard : Nat.card X = 5 * 2048 := by
    have h := X.card_mul_index
    rw [hXidx, M.toRuData.card_H] at h
    omega
  have hβX : β ∈ X := Subgroup.mem_zpowers _
  have hcX : h0 * β * h0⁻¹ ∈ X := by
    show M.φ (h0 * β * h0⁻¹) ∈ Subgroup.zpowers (M.φ β)
    rw [map_mul, map_mul, map_inv, hx]
    exact Subgroup.npow_mem_zpowers _ 2
  have hβo : orderOf β = 5 := by rw [Subgroup.orderOf_mk, hb5]
  have hco : orderOf (h0 * β * h0⁻¹) = 5 := by
    rw [orderOf_conj_eq, hβo]
  have hsyl : ∀ y : X, orderOf y = 5 → ∀ P : Sylow 5 X, Subgroup.zpowers y ≤ P →
      (P : Subgroup X) = Subgroup.zpowers y := by
    intro y hy P hP
    have hPc := Sz8Sylow.card_sylow_of_prime P 2048 hXcard (by norm_num)
    exact (Subgroup.eq_of_le_of_card_ge hP (by rw [hPc, Nat.card_zpowers, hy])).symm
  have hp : ∀ y : X, orderOf y = 5 → IsPGroup 5 (Subgroup.zpowers y) := by
    intro y hy
    rw [IsPGroup.iff_card, Nat.card_zpowers, hy]
    exact ⟨1, by norm_num⟩
  set βX : X := ⟨β, hβX⟩
  set cX : X := ⟨h0 * β * h0⁻¹, hcX⟩
  have hβXo : orderOf βX = 5 := by rw [Subgroup.orderOf_mk, hβo]
  have hcXo : orderOf cX = 5 := by rw [Subgroup.orderOf_mk, hco]
  obtain ⟨PB, hPB⟩ := (hp βX hβXo).exists_le_sylow
  obtain ⟨PC, hPC⟩ := (hp cX hcXo).exists_le_sylow
  have hPBe := hsyl βX hβXo PB hPB
  have hPCe := hsyl cX hcXo PC hPC
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X PC PB
  have hmem : y * cX * y⁻¹ ∈ (PB : Subgroup X) := by
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨cX, by rw [hPCe]; exact Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
  rw [hPBe, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk' : ((y : ruH M.T) * (h0 * β * h0⁻¹) * (y : ruH M.T)⁻¹ : ruH M.T) = β ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  have hyφ : M.φ (y : ruH M.T) ∈ Subgroup.zpowers (M.φ β) := y.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyφ
  have hφk : M.φ β ^ k = M.φ β ^ (2 : ℤ) := by
    have h := congrArg M.φ hk'
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hx, map_zpow, ← hm] at h
    rw [← h]
    have hc : Commute (M.φ β ^ m) (M.φ β ^ 2) := (Commute.refl (M.φ β)).zpow_left m |>.pow_right 2
    rw [hc.eq, mul_inv_cancel_right]
    simp
  have h5 : (5 : ℤ) ∣ k - 2 := by
    have h1 : M.φ β ^ (k - 2) = 1 := by rw [zpow_sub, hφk, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hφo] at this
    exact_mod_cast this
  have hbk : β ^ k = β ^ (2 : ℤ) := by
    have h1 : β ^ (k - 2) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hβo]
      exact_mod_cast h5
    calc β ^ k = β ^ (k - 2) * β ^ (2 : ℤ) := by rw [← zpow_add]; ring_nf
      _ = β ^ (2 : ℤ) := by rw [h1, one_mul]
  refine ⟨(y : ruH M.T) * h0, ((y : ruH M.T) * h0).2, ?_⟩
  have := congrArg Subtype.val (hk'.trans hbk)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow] at this
  rw [show ((y : ruH M.T) : G) * h0 * b * (((y : ruH M.T) : G) * h0)⁻¹ =
    (y : G) * (h0 * b * (h0 : G)⁻¹) * ((y : ruH M.T) : G)⁻¹ by group]
  rw [this, zpow_two, pow_two]

theorem card_normalizer_B5 :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set G)) = 4000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, hhH, hh⟩ := exists_conj_sq hbH hb5
  have hcard := card_normalizer_eq_mul (Subgroup.zpowers b)
  rw [centralizer_zpowers_eq, (lemma_J27_5 hbH hb5).2.2.2.1] at hcard
  have hhN : h ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hh]
    exact Subgroup.zpow_mem _ (Subgroup.npow_mem_zpowers b 2) k
  have hBc : Nat.card (Subgroup.zpowers b) = 5 := by rw [Nat.card_zpowers, hb5]
  have hcyc : IsCyclic (Subgroup.zpowers b) := isCyclic_of_prime_card hBc
  have hAut : Nat.card (MulAut (Subgroup.zpowers b)) = 4 := by
    rw [IsCyclic.card_mulAut, hBc, Nat.totient_prime (by norm_num)]
  set α := autNHom (Subgroup.zpowers b) ⟨h, hhN⟩
  have hαk : ∀ n : ℕ, ((α ^ n) ⟨b, Subgroup.mem_zpowers b⟩ : G) = b ^ (2 ^ n) := by
    intro n
    rw [← map_pow, autNHom_apply]
    have e : (((⟨h, hhN⟩ : Subgroup.normalizer (Subgroup.zpowers b : Set G)) ^ n :
      Subgroup.normalizer (Subgroup.zpowers b : Set G)) : G) = h ^ n := by simp
    rw [e]
    exact conj_pow_sq hh n
  have hb4 : b ^ 4 ≠ b := by
    intro h4
    have : b ^ 3 = 1 := by
      have := congrArg (· * b⁻¹) h4
      simp only [mul_inv_cancel] at this
      rw [← this]
      group
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [hb5] at hd
    norm_num at hd
  have hαo : orderOf α = 4 := by
    have h16 : α ^ 4 = 1 := by
      have hb16 : b ^ (2 ^ 4) = b := by
        rw [show 2 ^ 4 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul, pow_five_of_orderOf hb5,
          one_pow, one_mul]
      apply MulEquiv.ext
      intro y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      have hy : y = ⟨b, Subgroup.mem_zpowers b⟩ ^ k := Subtype.ext (by simpa using hk.symm)
      rw [hy, map_zpow]
      congr 1
      exact Subtype.ext (by rw [hαk, hb16])
    have hd : orderOf α ∣ 4 := orderOf_dvd_of_pow_eq_one h16
    have hn2 : ¬ orderOf α ∣ 2 := by
      intro h2
      have h2' : α ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
      have := congrArg (fun f : MulAut (Subgroup.zpowers b) =>
        ((f ⟨b, Subgroup.mem_zpowers b⟩ : Subgroup.zpowers b) : G)) h2'
      simp only [hαk, MulAut.one_apply] at this
      exact hb4 this
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf α ∣ 2 ^ 2 from hd)
    interval_cases i
    · rw [hi'] at hn2; norm_num at hn2
    · rw [hi'] at hn2; norm_num at hn2
    · rw [hi']; norm_num
  have hR : Nat.card (autNHom (Subgroup.zpowers b)).range = 4 := by
    have h1 : Nat.card (autNHom (Subgroup.zpowers b)).range ∣ 4 :=
      hAut ▸ Subgroup.card_subgroup_dvd_card _
    have h2 : 4 ∣ Nat.card (autNHom (Subgroup.zpowers b)).range :=
      hαo ▸ Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    exact Nat.dvd_antisymm h1 h2
  rw [hcard, hR]
  norm_num

end Five

end RuDataM

end CFSG.Quasithin.RuType

module

public import CFSG.Walter.ReeOrder.JT.Section4A

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section General

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem relIndex_inf_centralizer_dvd_six {V : Subgroup X} (hV : IsKleinFour V)
    (H : Subgroup X) :
    (H ⊓ Subgroup.centralizer (V : Set X)).relIndex (H ⊓ Subgroup.normalizer (V : Set X)) ∣ 6 := by
  set N₀ := H ⊓ Subgroup.normalizer (V : Set X)
  let := conjAct N₀ V inf_le_right
  let φ : N₀ →* MulAut V := MulDistribMulAction.toMulAut N₀ V
  have hker : φ.ker = (H ⊓ Subgroup.centralizer (V : Set X)).subgroupOf N₀ := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      refine ⟨n.2.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨v, hv⟩)
      change (n : X) * v * (n : X)⁻¹ = v at this
      calc v * n = ((n : X) * v * (n : X)⁻¹) * n := by rw [this]
        _ = n * v := by group
    · intro hn
      ext v
      change (n : X) * v * (n : X)⁻¹ = v
      rw [(Subgroup.mem_centralizer_iff.mp hn.2 v v.2).symm, mul_inv_cancel_right]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, ← PSL2Facts.card_mulAut_of_isKleinFour V]
  exact Subgroup.card_subgroup_dvd_card _

omit [Finite X] in
theorem centralizer_subgroupOf_normalizer_normal (H : Subgroup X) :
    ((Subgroup.centralizer (H : Set X)).subgroupOf (Subgroup.normalizer (H : Set X))).Normal := by
  rw [← Subgroup.normalizerMonoidHom_ker]
  exact MonoidHom.normal_ker _

end General

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

omit hp in
theorem centralizer_T_le_normalizer_T :
    Subgroup.centralizer (s.T : Set G) ≤ Subgroup.normalizer (s.T : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem exists_mem_normalizer_T_orderOf_three :
    ∃ μ₀ ∈ Subgroup.normalizer (s.T : Set G), orderOf μ₀ = 3 ∧
      μ₀ ∉ Subgroup.centralizer (s.T : Set G) := by
  have hV := h.isKleinFour_inf_F hp s.S s.t_mem_S
  obtain ⟨z, hzF, hz3, hzN, hzfix⟩ := (h.facts hp).exists_orderOf_eq_three (h.mod_eight hp)
    inf_le_right hV
  obtain ⟨g, hg⟩ := (lemma_2_1 h hp).2.2.2.2.2 _ s.T hV s.four
  refine ⟨g * z * g⁻¹, ?_, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz3], ?_⟩
  · refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [← hg] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨z * y * z⁻¹, (Subgroup.mem_normalizer_iff.mp hzN y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro hC
    have : Nontrivial ((s.S : Subgroup G) ⊓ h.F : Subgroup G) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hV.card_four]
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ((s.S : Subgroup G) ⊓ h.F : Subgroup G))
    have hy1' : y ≠ 1 := fun h0 => hy1 (Subtype.ext h0)
    have hgy : g * y * g⁻¹ ∈ s.T := by
      rw [← hg]
      exact ⟨y, hy, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hC) _ hgy
    apply hy1'
    apply hzfix y hy
    have h2 : g * y * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * y * g⁻¹) := this
    have h3 : y * z = z * y := by
      have := congrArg (fun w => g⁻¹ * w * g) h2
      simp only [mul_assoc, inv_mul_cancel_left] at this
      simpa [mul_assoc] using this
    rw [← h3, mul_inv_cancel_right]

theorem relIndex_centralizer_T_normalizer_T :
    (Subgroup.centralizer (s.T : Set G)).relIndex (Subgroup.normalizer (s.T : Set G)) = 3 := by
  obtain ⟨μ₀, hμ₀N, hμ₀3, hμ₀C⟩ := s.exists_mem_normalizer_T_orderOf_three hp
  have h6 := relIndex_inf_centralizer_dvd_six s.four ⊤
  simp only [top_inf_eq] at h6
  have hodd : ¬ 2 ∣ (Subgroup.centralizer (s.T : Set G)).relIndex
      (Subgroup.normalizer (s.T : Set G)) := by
    intro h2
    have h1 := Subgroup.relIndex_dvd_of_le_left (Subgroup.normalizer (s.T : Set G))
      s.S_le_centralizer_T
    have h3 := Subgroup.relIndex_dvd_index_of_le
      (s.S_le_centralizer_T.trans s.centralizer_T_le_normalizer_T)
    exact s.S.not_dvd_index (h2.trans (h1.trans h3))
  have hne1 : (Subgroup.centralizer (s.T : Set G)).relIndex
      (Subgroup.normalizer (s.T : Set G)) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun hle => hμ₀C (hle hμ₀N)
  have hle := Nat.le_of_dvd (by norm_num) h6
  interval_cases hk : (Subgroup.centralizer (s.T : Set G)).relIndex
      (Subgroup.normalizer (s.T : Set G)) <;> simp_all

theorem S_inf_Q :
    (s.S : Subgroup G) ⊓ s.Q = ⊥ := by
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  rw [h.card_sylow hp s.S s.t_mem_S, show (8 : ℕ) = 2 ^ 3 by norm_num]
  exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr (s.odd_card_Q hp))

theorem normalizer_S_inf_centralizer_T :
    Subgroup.normalizer ((s.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (s.T : Set G) =
      s.S := by
  set H := Subgroup.normalizer ((s.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (s.T : Set G)
  have hSH : (s.S : Subgroup G) ≤ H := le_inf Subgroup.le_normalizer s.S_le_centralizer_T
  have hno : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 := by
    intro r hr hrH
    by_contra hr2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) r hrH
    have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe, hx]
    have hxodd : Odd (orderOf (x : G)) := hxo ▸ hr.odd_of_ne_two hr2
    have hxQ : (x : G) ∈ s.Q := (s.mem_Q_iff hp).mpr ⟨x.2.2, hxodd⟩
    have hxS : (x : G) ∈ Subgroup.centralizer ((s.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ (s.S : Subgroup G) :=
        (s.S : Subgroup G).mul_mem ((Subgroup.mem_normalizer_iff.mp x.2.1 y).mp hy)
          ((s.S : Subgroup G).inv_mem hy)
      have hyN : y ∈ Subgroup.normalizer (s.Q : Set G) :=
        s.normalizer_T_le_normalizer_Q hp (s.centralizer_T_le_normalizer_T
          (s.S_le_centralizer_T hy))
      have h2 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ s.Q := by
        rw [mul_assoc, mul_assoc]
        refine s.Q.mul_mem hxQ ?_
        have := (Subgroup.mem_normalizer_iff.mp hyN _).mp (s.Q.inv_mem hxQ)
        rwa [← mul_assoc]
      have h3 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ (s.S : Subgroup G) ⊓ s.Q := ⟨h1, h2⟩
      rw [s.S_inf_Q hp, Subgroup.mem_bot] at h3
      have := mul_inv_eq_one.mp h3
      calc y * x = (x : G) * y * (x : G)⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [h.centralizer_sylow hp s.S s.t_mem_S] at hxS
    have h4 : (x : G) ∈ (s.S : Subgroup G) ⊓ s.Q := ⟨hxS, hxQ⟩
    rw [s.S_inf_Q hp, Subgroup.mem_bot] at h4
    rw [h4, orderOf_one] at hxo
    exact hr.one_lt.ne hxo
  have h2 : IsPGroup 2 H := IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
    Nat.card_pos.ne' (fun hd hdH => hno _ hd hdH))
  exact (s.S.is_maximal' h2 hSH)

theorem exists_mu :
    ∃ μ ∈ Subgroup.normalizer ((s.S : Subgroup G) : Set G) ⊓ Subgroup.normalizer (s.T : Set G),
      orderOf μ = 3 ∧ μ ∉ Subgroup.centralizer (s.T : Set G) := by
  obtain ⟨μ₀, hμ₀N, -, hμ₀C⟩ := s.exists_mem_normalizer_T_orderOf_three hp
  have hconjC : ∀ g ∈ Subgroup.normalizer (s.T : Set G), ∀ y ∈ Subgroup.centralizer
      (s.T : Set G), g * y * g⁻¹ ∈ Subgroup.centralizer (s.T : Set G) := by
    intro g hg y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    have hz' : g⁻¹ * z * g ∈ s.T := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp hz
      simpa using this
    have := hy _ hz'
    calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * z := by group
  have hS'C : ((μ₀ • s.S : Sylow 2 G) : Subgroup G) ≤ Subgroup.centralizer (s.T : Set G) := by
    change MulAut.conj μ₀ • (s.S : Subgroup G) ≤ _
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
      MulAut.smul_def, MulAut.conj_apply]
    exact hconjC _ hμ₀N _ (s.S_le_centralizer_T hy)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (Subgroup.centralizer (s.T : Set G))
    ((μ₀ • s.S).subtype hS'C) (s.S.subtype s.S_le_centralizer_T)
  set μ₁ := (x : G) * μ₀
  have hxN : (x : G) ∈ Subgroup.normalizer (s.T : Set G) := s.centralizer_T_le_normalizer_T x.2
  have hμ₁T : μ₁ ∈ Subgroup.normalizer (s.T : Set G) := Subgroup.mul_mem _ hxN hμ₀N
  have hμ₁S : μ₁ ∈ Subgroup.normalizer ((s.S : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hz : (⟨μ₀ * y * μ₀⁻¹, hconjC _ hμ₀N _ (s.S_le_centralizer_T hy)⟩ :
        Subgroup.centralizer (s.T : Set G)) ∈ ((μ₀ • s.S).subtype hS'C : Subgroup _) := by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      change μ₀ * y * μ₀⁻¹ ∈ MulAut.conj μ₀ • (s.S : Subgroup G)
      exact ⟨y, hy, rfl⟩
    have hxz := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj x) _ hz
    rw [← Sylow.coe_subgroup_smul, hx, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hxz
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hxz
    rw [show μ₁ * y * μ₁⁻¹ = (x : G) * (μ₀ * y * μ₀⁻¹) * (x : G)⁻¹ by simp only [μ₁]; group]
    exact hxz
  have hμ₁C : μ₁ ∉ Subgroup.centralizer (s.T : Set G) := fun h1 => hμ₀C (by
    have : μ₀ = (x : G)⁻¹ * μ₁ := by simp only [μ₁]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) h1)
  have hnorm := centralizer_subgroupOf_normalizer_normal s.T
  have h3 : μ₁ ^ 3 ∈ Subgroup.centralizer (s.T : Set G) := by
    have := Subgroup.pow_index_mem ((Subgroup.centralizer (s.T : Set G)).subgroupOf
      (Subgroup.normalizer (s.T : Set G))) (⟨μ₁, hμ₁T⟩ : Subgroup.normalizer (s.T : Set G))
    rw [← Subgroup.relIndex, s.relIndex_centralizer_T_normalizer_T hp,
      Subgroup.mem_subgroupOf] at this
    exact this
  have h3S : μ₁ ^ 3 ∈ (s.S : Subgroup G) := by
    rw [← s.normalizer_S_inf_centralizer_T hp]
    exact ⟨Subgroup.pow_mem _ hμ₁S 3, h3⟩
  have h6 : μ₁ ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul, pow_two]
    exact h.mul_self_of_mem_sylow hp s.S s.t_mem_S h3S
  refine ⟨μ₁ ^ 4, ⟨Subgroup.pow_mem _ hμ₁S 4, Subgroup.pow_mem _ hμ₁T 4⟩, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, h6, one_pow]
    · intro h1
      apply hμ₁C
      have : μ₁ = (μ₁ ^ 3)⁻¹ * μ₁ ^ 4 := by group
      rw [this, h1, mul_one]
      exact Subgroup.inv_mem _ h3
  · intro h1
    apply hμ₁C
    have : μ₁ = μ₁ ^ 4 * (μ₁ ^ 3)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h3)

theorem normalizer_T_eq_sup
    {μ : G} (hμT : μ ∈ Subgroup.normalizer (s.T : Set G))
    (hμC : μ ∉ Subgroup.centralizer (s.T : Set G)) :
    Subgroup.normalizer (s.T : Set G) =
      Subgroup.zpowers μ ⊔ Subgroup.centralizer (s.T : Set G) := by
  set C := Subgroup.centralizer (s.T : Set G)
  set N := Subgroup.normalizer (s.T : Set G)
  set H := Subgroup.zpowers μ ⊔ C
  have hCH : C ≤ H := le_sup_right
  have hHN : H ≤ N := sup_le ((Subgroup.zpowers_le).mpr hμT) s.centralizer_T_le_normalizer_T
  have hmul := Subgroup.relIndex_mul_relIndex C H N hCH hHN
  rw [s.relIndex_centralizer_T_normalizer_T hp] at hmul
  have h1 : C.relIndex H ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun hle => hμC (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers μ)))
  have h2 : H.relIndex N = 1 := by
    have h3 : C.relIndex H ∣ 3 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h4 | h4
    · exact absurd h4 h1
    · rw [h4] at hmul
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hHN

theorem lemma_4_2_c :
    ∃ μ t₁ : G, μ ∈ Subgroup.normalizer ((s.S : Subgroup G) : Set G) ∧
      μ ∈ Subgroup.normalizer (s.T : Set G) ∧ orderOf μ = 3 ∧ t₁ ∈ s.S ∧ orderOf t₁ = 2 ∧
      μ * t₁ = t₁ * μ ∧ (∀ x ∈ s.T, μ * x * μ⁻¹ = x → x = 1) ∧
      Subgroup.normalizer (s.T : Set G) =
        Subgroup.zpowers μ ⊔ Subgroup.centralizer (s.T : Set G) ∧
      (∀ x ∈ s.Q, t₁ * x * t₁⁻¹ = x → x = 1) ∧
      Subgroup.normalizer (s.T : Set G) ≤ Subgroup.normalizer (s.Q : Set G) := by
  classical
  obtain ⟨μ, ⟨hμS, hμT⟩, hμ3, hμC⟩ := s.exists_mu hp
  have hfixT : ∀ x ∈ s.T, μ * x * μ⁻¹ = x → x = 1 := fun x hx hμx =>
    eq_one_of_conj_eq_of_orderOf_eq_three s.four hμ3 hμT hμC hx hμx
  have hμS' : Subgroup.zpowers μ ≤ Subgroup.normalizer ((s.S : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr hμS
  let := conjAct (Subgroup.zpowers μ) s.S hμS'
  have h3 : IsPGroup 3 (Subgroup.zpowers μ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hμ3, pow_one])
  have hmod := h3.card_modEq_card_fixedPoints (s.S : Subgroup G)
  rw [h.card_sylow hp s.S s.t_mem_S] at hmod
  obtain ⟨t₁, ht₁fix, ht₁1⟩ : ∃ t₁ ∈ MulAction.fixedPoints (Subgroup.zpowers μ)
      (s.S : Subgroup G), t₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : Nat.card (MulAction.fixedPoints (Subgroup.zpowers μ) (s.S : Subgroup G)) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    have : Nat.card (MulAction.fixedPoints (Subgroup.zpowers μ) (s.S : Subgroup G)) % 3 = 2 :=
      hmod.symm
    omega
  have hμt₁ : μ * t₁ * μ⁻¹ = t₁ := by
    have := congrArg Subtype.val (ht₁fix ⟨μ, Subgroup.mem_zpowers μ⟩)
    exact this
  have ht₁1' : (t₁ : G) ≠ 1 := fun h0 => ht₁1 (Subtype.ext h0)
  have ht₁T : (t₁ : G) ∉ s.T := fun hT => ht₁1' (hfixT _ hT hμt₁)
  refine ⟨μ, t₁, hμS, hμT, hμ3, t₁.2, orderOf_eq_prime (by
      rw [pow_two]; exact h.mul_self_of_mem_sylow hp s.S s.t_mem_S t₁.2) ht₁1', ?_, hfixT,
    s.normalizer_T_eq_sup hp hμT hμC, fun x hx hx' => ?_, s.normalizer_T_le_normalizer_Q hp⟩
  · calc μ * t₁ = (μ * t₁ * μ⁻¹) * μ := by group
      _ = t₁ * μ := by rw [hμt₁]
  · have hinv := s.conj_eq_inv_of_mem_S hp t₁.2 ht₁T hx
    rw [hx'] at hinv
    have hxx : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← hinv]
        _ = 1 := mul_inv_cancel x
    have hodd := ((s.mem_Q_iff hp).mp hx).2
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)

end Setup

end CFSG.Walter.JT

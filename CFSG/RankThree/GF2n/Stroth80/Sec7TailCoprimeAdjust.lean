module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem inf_eq_bot_of_coprime_three {Γ : Type*} [Group Γ] [Finite Γ] {O X : Subgroup Γ}
    (hO : Nat.Coprime 3 (Nat.card O)) (hX : IsPGroup 3 X) : X ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgX, hgO⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨k, hk⟩ := hX ⟨g, hgX⟩
  have h1 : orderOf g ∣ 3 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf g ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : O)
    simpa [Subgroup.orderOf_mk] using this
  have h3 : orderOf g ∣ Nat.gcd (3 ^ k) (Nat.card O) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd (3 ^ k) (Nat.card O) = 1 := Nat.Coprime.pow_left k hO
  rw [h4] at h3
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))

theorem card_sup_of_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {O X : Subgroup Γ} [O.Normal]
    (hXO : X ⊓ O = ⊥) : Nat.card ↥(X ⊔ O) = Nat.card X * Nat.card O := by
  have h1 := Subgroup.card_mul_index (O.subgroupOf (X ⊔ O))
  have h2 : Nat.card ↥(O.subgroupOf (X ⊔ O)) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h3 : (O.subgroupOf (X ⊔ O)).index = (O.subgroupOf X).index :=
    Subgroup.relIndex_sup_right (H := X) (K := O)
  have h4 : O.subgroupOf X = ⊥ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hx
      have hm : (x : Γ) ∈ X ⊓ O := ⟨x.2, hx⟩
      rw [hXO, Subgroup.mem_bot] at hm
      exact Subtype.ext hm
    · intro hx
      rw [hx]
      exact O.one_mem
  have h5 : (O.subgroupOf X).index = Nat.card X := by
    rw [h4, Subgroup.index_bot]
  rw [h2, h3, h5] at h1
  rw [← h1, mul_comm]

theorem exists_conj_mem_sup_zpowers {Γ : Type*} [Group Γ] [Finite Γ] (Q : Subgroup Γ) [Q.Normal]
    (hQ : ¬ 3 ∣ Nat.card Q) {y w : Γ} (hy : orderOf y = 3) (hw : orderOf w = 3)
    (hyw : y⁻¹ * w ∈ Q) : ∃ h ∈ Q ⊔ Subgroup.zpowers y, h * w * h⁻¹ = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card Q) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ
  set W : Subgroup Γ := Q ⊔ Subgroup.zpowers y with hW
  have hyW : y ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hwW : w ∈ W := by
    have : w = y * (y⁻¹ * w) := by group
    rw [this]
    exact W.mul_mem hyW (Subgroup.mem_sup_left hyw)
  have hY3 : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy]
  have hZ3 : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hw]
  have hYp : IsPGroup 3 (Subgroup.zpowers y) := IsPGroup.of_card (n := 1) (by rw [hY3]; rfl)
  have hZp : IsPGroup 3 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by rw [hZ3]; rfl)
  have hYleW : Subgroup.zpowers y ≤ W := le_sup_right
  have hZleW : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.2 hwW
  have hbot : Subgroup.zpowers y ⊓ Q = ⊥ := inf_eq_bot_of_coprime_three hcop hYp
  have hWcard : Nat.card W = Nat.card (Subgroup.zpowers y) * Nat.card Q := by
    rw [hW, sup_comm]
    exact card_sup_of_inf_eq_bot hbot
  have hidx : ∀ H : Subgroup W, Nat.card H = 3 → ¬ 3 ∣ H.index := by
    intro H hH
    have h1 := Subgroup.card_mul_index H
    rw [hH, hWcard, hY3] at h1
    have h2 : H.index = Nat.card Q := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h1
    rw [h2]
    exact hQ
  have hYc : Nat.card ((Subgroup.zpowers y).subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleW).toEquiv, hY3]
  have hZc : Nat.card ((Subgroup.zpowers w).subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleW).toEquiv, hZ3]
  have hYp' : IsPGroup 3 ((Subgroup.zpowers y).subgroupOf W) :=
    hYp.comap_of_injective W.subtype Subtype.val_injective
  have hZp' : IsPGroup 3 ((Subgroup.zpowers w).subgroupOf W) :=
    hZp.comap_of_injective W.subtype Subtype.val_injective
  let S₁ : Sylow 3 ↥W := IsPGroup.toSylow hZp' (hidx _ hZc)
  let S₂ : Sylow 3 ↥W := IsPGroup.toSylow hYp' (hidx _ hYc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) S₁ S₂
  have hS₁coe : (S₁ : Subgroup ↥W) = (Subgroup.zpowers w).subgroupOf W := rfl
  have hS₂coe : (S₂ : Subgroup ↥W) = (Subgroup.zpowers y).subgroupOf W := rfl
  obtain ⟨j, hj⟩ : ∃ j : ℤ, g.1 * w ^ j * g.1⁻¹ = y := by
    have h1 : (⟨y, hyW⟩ : ↥W) ∈ (S₂ : Subgroup ↥W) := by
      rw [hS₂coe]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)
    rw [← hg, Sylow.coe_subgroup_smul] at h1
    obtain ⟨t, ht, hgt⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [hS₁coe] at ht
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ht)
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hgt
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [hj]
    exact this
  obtain ⟨q₀, hq₀, s, hs, hqs⟩ := Subgroup.mem_sup_of_normal_left.1 g.2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  set π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπq₀ : π q₀ = 1 := (QuotientGroup.eq_one_iff _).2 hq₀
  have hπg : π g.1 = π y ^ i := by
    rw [← hqs, map_mul, hπq₀, one_mul, map_zpow]
  have hπw : π w = π y := by
    have h1 : π (y⁻¹ * w) = 1 := (QuotientGroup.eq_one_iff _).2 hyw
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.1 h1).symm
  have hy1 : π y ≠ 1 := by
    intro h1
    have hyQ : y ∈ Q := (QuotientGroup.eq_one_iff y).1 h1
    have h2 : orderOf y ∣ Nat.card Q := by
      have := Subgroup.orderOf_dvd_natCard Q hyQ
      simpa using this
    rw [hy] at h2
    exact hQ h2
  have hπy3 : orderOf (π y) = 3 := by
    refine orderOf_eq_prime ?_ hy1
    rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hkey : π y = π y ^ j := by
    have h1 : π (g.1 * w ^ j * g.1⁻¹) = π y := by rw [hj]
    rw [map_mul, map_mul, map_inv, hπg, map_zpow, hπw] at h1
    have h2 : π y ^ i * π y ^ j * (π y ^ i)⁻¹ = π y ^ j := by
      rw [← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      ring
    exact h1.symm.trans h2
  have hdvd : (3 : ℤ) ∣ j - 1 := by
    have h1 : π y ^ (j - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← hkey, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hπy3] at this
  have hwj : w ^ j = w := by
    have h1 : w ^ (j - 1) = 1 := by
      refine orderOf_dvd_iff_zpow_eq_one.1 ?_
      rw [hw]
      exact hdvd
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
    exact h1
  refine ⟨g.1, g.2, ?_⟩
  rw [← hj, hwj]

theorem hom_trivial_of_centralizer {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : IsPGroup 2 N) {y : X} (hy : orderOf y = 3) (hyN : y ∈ Subgroup.normalizer (N : Set X))
    {V : Subgroup X} (hV : ∀ x ∈ N, y * x = x * y → x ∈ V) {A : Type*} [Group A] (φ : N →* A)
    (hφy : ∀ x x' : N, (x' : X) = y * x * y⁻¹ → φ x' = φ x)
    (hφV : ∀ x : N, (x : X) ∈ V → φ x = 1) : ∀ x : N, φ x = 1 := by
  classical
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set X) :=
    Subgroup.zpowers_le.2 hyN
  have hmem : ∀ (a : Subgroup.zpowers y) (n : N), (a : X) * (n : X) * (a : X)⁻¹ ∈ N :=
    fun a n => (Subgroup.mem_normalizer_iff.1 (hnorm a.2) (n : X)).1 n.2
  letI act : MulDistribMulAction (Subgroup.zpowers y) N :=
    { smul := fun a n => ⟨(a : X) * (n : X) * (a : X)⁻¹, hmem a n⟩
      one_smul := fun n => Subtype.ext (by show (1 : X) * (n : X) * (1 : X)⁻¹ = n; group)
      mul_smul := fun a b n => Subtype.ext (by
        show (a : X) * (b : X) * (n : X) * ((a : X) * (b : X))⁻¹
          = (a : X) * ((b : X) * (n : X) * (b : X)⁻¹) * (a : X)⁻¹
        group)
      smul_mul := fun a m n => Subtype.ext (by
        show (a : X) * ((m : X) * (n : X)) * (a : X)⁻¹
          = (a : X) * (m : X) * (a : X)⁻¹ * ((a : X) * (n : X) * (a : X)⁻¹)
        group)
      smul_one := fun a => Subtype.ext (by show (a : X) * 1 * (a : X)⁻¹ = 1; group) }
  have hsy_mem : ∀ m : N, y * (m : X) * y⁻¹ ∈ N := fun m =>
    (Subgroup.mem_normalizer_iff.1 hyN (m : X)).1 m.2
  have hsy : ∀ m : N, φ ⟨y * (m : X) * y⁻¹, hsy_mem m⟩ = φ m := fun m => hφy m _ rfl
  have hinv : ∀ (a : Subgroup.zpowers y) (n : N), φ (a • n) = φ n := by
    intro a n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have hr : y ^ (k % 3) = (a : X) := by
      rw [← hk]
      have := zpow_mod_orderOf y k
      rw [hy] at this
      exact_mod_cast this
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0, zpow_zero] at hr
      have e : a • n = n := Subtype.ext (by
        show (a : X) * (n : X) * (a : X)⁻¹ = n
        rw [← hr]
        group)
      rw [e]
    · rw [h1, zpow_one] at hr
      have e : a • n = ⟨y * (n : X) * y⁻¹, hsy_mem n⟩ := Subtype.ext (by
        show (a : X) * (n : X) * (a : X)⁻¹ = y * (n : X) * y⁻¹
        rw [← hr])
      rw [e]
      exact hsy n
    · rw [h2, zpow_two] at hr
      have e : a • n = ⟨y * (y * (n : X) * y⁻¹) * y⁻¹, hsy_mem ⟨y * (n : X) * y⁻¹, hsy_mem n⟩⟩ :=
        Subtype.ext (by
          show (a : X) * (n : X) * (a : X)⁻¹ = y * (y * (n : X) * y⁻¹) * y⁻¹
          rw [← hr]
          group)
      rw [e]
      exact (hsy ⟨y * (n : X) * y⁻¹, hsy_mem n⟩).trans (hsy n)
  have hA : ¬ 2 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, hy]
    norm_num
  have hfac := (CFSG.LocalAnalysis.ComponentInitial.coprime_pgroup_commutator_factorization
    (A := Subgroup.zpowers y) (Q := N) Nat.prime_two hN hA).1
  have hsub : CFSG.LocalAnalysis.ComponentInitial.actionCommutator (Subgroup.zpowers y)
      (⊤ : Subgroup N) ≤ φ.ker := by
    unfold CFSG.LocalAnalysis.ComponentInitial.actionCommutator
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨h, -, a, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hinv a h, inv_mul_cancel]
  intro x
  obtain ⟨d, hd, c, hc, hxdc⟩ := hfac x
  have hcV : (c : X) ∈ V := by
    apply hV (c : X) c.2
    have h1 : (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • c = c := hc _
    have h2 : y * (c : X) * y⁻¹ = (c : X) := congrArg Subtype.val h1
    calc y * (c : X) = y * (c : X) * y⁻¹ * y := by group
      _ = (c : X) * y := by rw [h2]
  rw [hxdc, map_mul, MonoidHom.mem_ker.1 (hsub hd), hφV c hcV, one_mul]

end CFSG.RankThree.GF2n.Stroth80

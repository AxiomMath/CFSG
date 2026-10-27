module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3WChar

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Open CFSG.Quasithin

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem zpow_mem_nbrStab_iff {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) (t : ℤ) : x ^ t ∈ nbrStab Γ G v ↔ x ^ t = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ one_mem _⟩
  by_contra hne
  have hp := F.valence_isPrime v
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  have hpow : (x ^ t) ^ Fan86.valence Γ v = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  exact F.not_mem_nbrStab_of_orderOf (zpow_mem hx t) (orderOf_eq_prime hpow hne) h

theorem exists_normalizing_two (h65 : Fan65 F) {α β : V} (hα : Fan86.valence Γ α = 5)
    (hαβ : Γ.Adj α β) {x : G} (hx : x ∈ MulAction.stabilizer G α) (hxo : orderOf x = 5) :
    ∃ w ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β, w⁻¹ * x * w = x ^ 2 := by
  have hxo' : orderOf x = Fan86.valence Γ α := by rw [hxo, hα]
  obtain ⟨ψ, h1, h2, h3, e, heβ, hev⟩ := F.exists_edge_conj_two h65 hα hαβ hx hxo'
  have : Finite ↥(MulAction.stabilizer G α) := F.loc_finite α
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let xt : ↥(MulAction.stabilizer G α) := ⟨x, hx⟩
  obtain ⟨k, hk⟩ := F.exists_card_stabilizer α
  have hcardP : Nat.card ↥(Subgroup.zpowers xt) = 5 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxo]
  have hpg : IsPGroup 5 ↥(Subgroup.zpowers xt) := IsPGroup.of_card (n := 1) (by rw [hcardP]; simp)
  have hidx : ¬ 5 ∣ (Subgroup.zpowers xt).index := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers xt)
    rw [hcardP, hk, hα] at h
    have : (Subgroup.zpowers xt).index = 2 ^ k := by omega
    rw [this]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow hd)
    omega
  let P : Sylow 5 ↥(MulAction.stabilizer G α) := hpg.toSylow hidx
  have hPle : (P : Subgroup ↥(MulAction.stabilizer G α)) ≤ ψ.ker := by
    show Subgroup.zpowers xt ≤ ψ.ker
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.2 h2
  have htop := Sylow.normalizer_sup_eq_top' P hPle
  obtain ⟨n, hn, ν, hν, hnν⟩ := Subgroup.mem_sup_of_normal_right.1 (htop ▸ Subgroup.mem_top e)
  have hψn : ψ n = ψ e := by
    have : ψ e = ψ n * ψ ν := by rw [← hnν, map_mul]
    rw [this, MonoidHom.mem_ker.1 hν, mul_one]
  have hnβ : Γ.Adj α ((n : G) • β) := F.adj_smul_of_mem_stabilizer n.2 hαβ
  obtain ⟨a, ha⟩ := F.exists_pow_smul_eq hx hxo' hnβ hαβ
  let w₁ : ↥(MulAction.stabilizer G α) := xt ^ a * n
  have hw₁β : (w₁ : G) • β = β := by
    show (x ^ a * (n : G)) • β = β
    rw [mul_smul]
    exact ha
  have hxP : xt ∈ (P : Subgroup ↥(MulAction.stabilizer G α)) := Subgroup.mem_zpowers xt
  have hw₁N : w₁ ∈ Subgroup.normalizer ((P : Subgroup ↥(MulAction.stabilizer G α)) : Set _) :=
    mul_mem (pow_mem (Subgroup.le_normalizer hxP) a) hn
  have hψw₁ : ψ w₁ = ψ e := by rw [map_mul, map_pow, h2, one_pow, one_mul, hψn]
  obtain ⟨j, hj⟩ : ∃ j : ℤ, x ^ j = (w₁ : G) * x * (w₁ : G)⁻¹ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_normalizer_iff.1 hw₁N xt).1 hxP)
    exact ⟨j, congrArg Subtype.val hj⟩
  have hm : ((ψ w₁ : (ZMod (Fan86.valence Γ α))ˣ) : ZMod (Fan86.valence Γ α)).val = 2 := by
    rw [hψw₁]
    exact hev
  have h3' := h3 w₁
  rw [hm, ← hj] at h3'
  have h4 : x ^ (j - 2) ∈ nbrStab Γ G α := by
    have : x ^ (j - 2) = x ^ j * (x ^ 2)⁻¹ := by rw [zpow_sub, zpow_two, sq]
    rw [this]
    exact h3'
  have h5 : x ^ (j - 2) = 1 := (F.zpow_mem_nbrStab_iff hx hxo' (j - 2)).1 h4
  have h6 : x ^ j = x ^ 2 := by
    have : x ^ j = x ^ (j - 2) * x ^ 2 := by rw [zpow_sub, zpow_two, sq]; group
    rw [this, h5, one_mul]
  refine ⟨((w₁⁻¹ : ↥(MulAction.stabilizer G α)) : G), ⟨(w₁⁻¹).2, ?_⟩, ?_⟩
  · show ((w₁⁻¹ : ↥(MulAction.stabilizer G α)) : G) ∈ MulAction.stabilizer G β
    rw [MulAction.mem_stabilizer_iff]
    show (w₁ : G)⁻¹ • β = β
    rw [inv_smul_eq_iff]
    exact hw₁β.symm
  · rw [← h6, hj]
    simp

end FanTree

end CFSG.Quasithin.Fan86

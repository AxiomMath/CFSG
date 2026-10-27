module

public import CFSG.Quasithin.Recognition.RuTypeJ44d
public import CFSG.Quasithin.Recognition.RuTypeSz2

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

theorem x0_zP0_not_mem_R0 : x0 * zP0 * x0⁻¹ ∉ R0 := by decide

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem φ_mem_zpowers_of_comm {g : G} (hg : g ∈ ruH M.T)
    (hc : M.φ ⟨g, hg⟩ * M.φ ⟨M.b5el, M.b5el_mem_H⟩ = M.φ ⟨M.b5el, M.b5el_mem_H⟩ * M.φ ⟨g, hg⟩) :
    M.φ ⟨g, hg⟩ ∈ Subgroup.zpowers (M.φ ⟨M.b5el, M.b5el_mem_H⟩) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hprops := φ_b_props M.b5el_mem_H M.orderOf_b5el
  have ht5 : orderOf (M.φ ⟨M.b5el, M.b5el_mem_H⟩) = 5 := orderOf_eq_prime hprops.1 hprops.2
  have hcard : Nat.card (Subgroup.centralizer
      ({M.φ ⟨M.b5el, M.b5el_mem_H⟩} : Set SigmaL2F4)) = 5 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => Subgroup.mem_centralizer_singleton_iff)]
    exact (Nat.card_eq_fintype_card).trans (Sigma.card_centralizer_five _ hprops)
  have hle : Subgroup.zpowers (M.φ ⟨M.b5el, M.b5el_mem_H⟩) ≤
      Subgroup.centralizer ({M.φ ⟨M.b5el, M.b5el_mem_H⟩} : Set SigmaL2F4) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, ht5])
  rw [heq]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hc

theorem mem_Q_of_comm_b5el {g : G} (hg : g ∈ ruH M.T) {m : ℕ}
    (hg2 : g ^ 2 ^ m = 1) (hc : g * M.b5el * g⁻¹ * M.b5el⁻¹ ∈ ruQ M.T) : g ∈ ruQ M.T := by
  have hmem : g * M.b5el * g⁻¹ * M.b5el⁻¹ ∈ ruH M.T :=
    mul_mem (mul_mem (mul_mem hg M.b5el_mem_H) (inv_mem hg)) (inv_mem M.b5el_mem_H)
  have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
    rw [M.φ_ker, Subgroup.mem_subgroupOf]
    exact hc
  have e : (⟨_, hmem⟩ : ruH M.T) = ⟨g, hg⟩ * ⟨M.b5el, M.b5el_mem_H⟩ * (⟨g, hg⟩ : ruH M.T)⁻¹ *
      (⟨M.b5el, M.b5el_mem_H⟩ : ruH M.T)⁻¹ := rfl
  rw [MonoidHom.mem_ker, e, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
  have hcomm : M.φ ⟨g, hg⟩ * M.φ ⟨M.b5el, M.b5el_mem_H⟩ =
      M.φ ⟨M.b5el, M.b5el_mem_H⟩ * M.φ ⟨g, hg⟩ := by
    calc M.φ ⟨g, hg⟩ * M.φ ⟨M.b5el, M.b5el_mem_H⟩ =
        (M.φ ⟨g, hg⟩ * M.φ ⟨M.b5el, M.b5el_mem_H⟩ * (M.φ ⟨g, hg⟩)⁻¹ *
          (M.φ ⟨M.b5el, M.b5el_mem_H⟩)⁻¹) * (M.φ ⟨M.b5el, M.b5el_mem_H⟩ * M.φ ⟨g, hg⟩) := by
          group
      _ = M.φ ⟨M.b5el, M.b5el_mem_H⟩ * M.φ ⟨g, hg⟩ := by rw [hk, one_mul]
  have hz := M.φ_mem_zpowers_of_comm hg hcomm
  have hprops := φ_b_props M.b5el_mem_H M.orderOf_b5el
  have h5 : M.φ ⟨g, hg⟩ ^ 5 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprops.1, one_zpow]
  have h2 : M.φ ⟨g, hg⟩ ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ruH M.T) ^ 2 ^ m = 1 := Subtype.ext hg2
    rw [this, map_one]
  have h1 : M.φ ⟨g, hg⟩ = 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h2)
    have : Nat.gcd 5 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have : (⟨g, hg⟩ : ruH M.T) ∈ M.φ.ker := h1
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem b5el_mem_F1 : M.b5el ∈ M.F1 :=
  Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem Y_le_F1 : M.Ygrp ≤ M.F1 := by
  rw [← M.F1_inf_Q]
  exact inf_le_left

theorem Agrp_le_F1 : M.Agrp ≤ M.F1 := le_sup_left

theorem F1_conj_Y {f x : G} (hf : f ∈ M.F1) (hx : x ∈ M.Ygrp) :
    f * x * f⁻¹ ∈ M.Ygrp := by
  rw [← M.F1_inf_Q] at hx ⊢
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hf hx1) (inv_mem hf),
    M.conj_mem_Q (M.F1_le_H hf) hx2⟩

theorem F1_conj_b5el {f : G} (hf : f ∈ M.F1) :
    ∃ k : ℕ, ∃ q ∈ ruQ M.T, f * M.b5el * f⁻¹ = M.b5el ^ k * q :=
  M.exists_conj_b5el (M.F1_le_H hf)
    (M.σ5_mem_normalizer_of_conj_Y (M.F1_le_H hf) fun _ hx => M.F1_conj_Y hf hx)

noncomputable abbrev ψF1 : ↥M.F1 →* SigmaL2F4 :=
  M.φ.comp (Subgroup.inclusion M.F1_le_H)

theorem mem_ker_ψF1 {x : ↥M.F1} :
    x ∈ M.ψF1.ker ↔ (x : G) ∈ ruQ M.T := by
  have e : x ∈ M.ψF1.ker ↔ (⟨(x : G), M.F1_le_H x.2⟩ : ruH M.T) ∈ M.φ.ker := Iff.rfl
  rw [e, M.φ_ker, Subgroup.mem_subgroupOf]

theorem ker_ψF1 : M.ψF1.ker = M.Ygrp.subgroupOf M.F1 := by
  ext x
  rw [M.mem_ker_ψF1, Subgroup.mem_subgroupOf, ← M.F1_inf_Q]
  exact ⟨fun h => Subgroup.mem_inf.mpr ⟨x.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩

theorem card_range_ψF1 : Nat.card M.ψF1.range = 20 := by
  have h := Subgroup.card_ker_mul_card_range M.ψF1
  rw [M.ker_ψF1, card_subgroupOf_of_le M.Y_le_F1, M.card_Y, M.card_F1] at h
  have h' : 2 ^ 10 * Nat.card M.ψF1.range = 2 ^ 10 * 20 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

noncomputable abbrev uF1 : ↥M.ψF1.range :=
  ⟨M.ψF1 ⟨M.b5el, M.b5el_mem_F1⟩, ⟨_, rfl⟩⟩

theorem orderOf_uF1 : orderOf M.uF1 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hprops := φ_b_props M.b5el_mem_H M.orderOf_b5el
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime hprops.1 hprops.2

theorem uF1_normal (x : ↥M.ψF1.range) :
    x * M.uF1 * x⁻¹ ∈ Subgroup.zpowers M.uF1 := by
  obtain ⟨_, f, rfl⟩ := x
  obtain ⟨k, q, hq, hk⟩ := M.F1_conj_b5el f.2
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), Subtype.ext ?_⟩
  have hqH : q ∈ ruH M.T := pCoreOf_le 2 _ hq
  have hq1 : M.φ ⟨q, hqH⟩ = 1 := by
    have : (⟨q, hqH⟩ : ruH M.T) ∈ M.φ.ker := by
      rw [M.φ_ker, Subgroup.mem_subgroupOf]
      exact hq
    exact this
  have e : (⟨(f : G) * M.b5el * (f : G)⁻¹, M.F1_le_H (mul_mem (mul_mem f.2 M.b5el_mem_F1)
      (inv_mem f.2))⟩ : ruH M.T) = ⟨M.b5el, M.b5el_mem_H⟩ ^ k * ⟨q, hqH⟩ := Subtype.ext hk
  have e2 : M.ψF1 f * M.ψF1 ⟨M.b5el, M.b5el_mem_F1⟩ * (M.ψF1 f)⁻¹ =
      M.φ ⟨(f : G) * M.b5el * (f : G)⁻¹, M.F1_le_H (mul_mem (mul_mem f.2 M.b5el_mem_F1)
        (inv_mem f.2))⟩ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  show (M.ψF1 ⟨M.b5el, M.b5el_mem_F1⟩) ^ (k : ℤ) =
    M.ψF1 f * M.ψF1 ⟨M.b5el, M.b5el_mem_F1⟩ * (M.ψF1 f)⁻¹
  rw [e2, e, map_mul, hq1, mul_one, map_pow, zpow_natCast]
  rfl

theorem uF1_selfCentralizing (x : ↥M.ψF1.range)
    (hx : x * M.uF1 = M.uF1 * x) : x ∈ Subgroup.zpowers M.uF1 := by
  obtain ⟨_, f, rfl⟩ := x
  have hc : M.φ ⟨(f : G), M.F1_le_H f.2⟩ * M.φ ⟨M.b5el, M.b5el_mem_H⟩ =
      M.φ ⟨M.b5el, M.b5el_mem_H⟩ * M.φ ⟨(f : G), M.F1_le_H f.2⟩ := congrArg Subtype.val hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (M.φ_mem_zpowers_of_comm _ hc)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  exact hk

theorem nonempty_range_ψF1_sz :
    Nonempty (↥M.ψF1.range ≃* ↥(Sz 0)) :=
  nonempty_mulEquiv_sz_zero M.card_range_ψF1 M.orderOf_uF1 M.uF1_normal M.uF1_selfCentralizing

theorem isPGroup_Y : IsPGroup 2 M.Ygrp :=
  IsPGroup.of_card M.card_Y

theorem F1_le_normalizer_Y :
    M.F1 ≤ Subgroup.normalizer (M.Ygrp : Set G) :=
  fun _ hf => mem_normalizer_of_conj_mem fun _ hx => M.F1_conj_Y hf hx

theorem pCoreOf_F1 : pCoreOf 2 M.F1 = M.Ygrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 M.Y_le_F1 M.F1_le_normalizer_Y
    M.isPGroup_Y)
  intro x hx
  have hxF := pCoreOf_le 2 M.F1 hx
  rw [← M.F1_inf_Q]
  refine Subgroup.mem_inf.mpr ⟨hxF, ?_⟩
  have hp := pCoreOf_isPGroup 2 M.F1
  obtain ⟨m, hm⟩ := hp ⟨x, hx⟩
  have hx2 : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hbN := le_normalizer_pCoreOf 2 M.F1 M.b5el_mem_F1
  have hcO : x * M.b5el * x⁻¹ * M.b5el⁻¹ ∈ pCoreOf 2 M.F1 := by
    have h1 : M.b5el * x⁻¹ * M.b5el⁻¹ ∈ pCoreOf 2 M.F1 :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp (inv_mem hx)
    have e : x * M.b5el * x⁻¹ * M.b5el⁻¹ = x * (M.b5el * x⁻¹ * M.b5el⁻¹) := by group
    rw [e]
    exact mul_mem hx h1
  obtain ⟨m', hm'⟩ := hp ⟨_, hcO⟩
  have hc2 : (x * M.b5el * x⁻¹ * M.b5el⁻¹) ^ 2 ^ m' = 1 := congrArg Subtype.val hm'
  obtain ⟨k, q, hq, hk⟩ := M.F1_conj_b5el hxF
  have hcH : x * M.b5el * x⁻¹ * M.b5el⁻¹ ∈ ruH M.T :=
    M.F1_le_H (pCoreOf_le 2 M.F1 hcO)
  have hcQ : (x * M.b5el * x⁻¹ * M.b5el⁻¹) * M.b5el ^ (-((k : ℤ) - 1)) ∈ ruQ M.T := by
    have e : (x * M.b5el * x⁻¹ * M.b5el⁻¹) * M.b5el ^ (-((k : ℤ) - 1)) =
        M.b5el ^ ((k : ℤ) - 1) * (M.b5el * q * M.b5el⁻¹) * (M.b5el ^ ((k : ℤ) - 1))⁻¹ := by
      rw [hk, ← zpow_natCast]
      group
    rw [e]
    exact M.conj_mem_Q (zpow_mem M.b5el_mem_H _) (M.conj_mem_Q M.b5el_mem_H hq)
  obtain ⟨hcQ', -⟩ := M.mem_Q_of_mul_zpow_mem_Q hcH hc2 hcQ
  exact M.mem_Q_of_comm_b5el (M.F1_le_H hxF) hx2 hcQ'

theorem pCore_F1 : CFSG.Open.pCore 2 ↥M.F1 = M.ψF1.ker := by
  rw [M.ker_ψF1, ← M.pCoreOf_F1, pCoreOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.F1.subtype_injective]

theorem nonempty_oTwoQuot_F1 :
    Nonempty (oTwoQuot ↥M.F1 ≃* ↥(Sz 0)) := by
  obtain ⟨e⟩ := M.nonempty_range_ψF1_sz
  exact ⟨((QuotientGroup.quotientMulEquivOfEq M.pCore_F1).trans
    (QuotientGroup.quotientKerEquivRange M.ψF1)).trans e⟩

theorem charTwo_F1 : CharTwo M.F1 := by
  unfold CharTwo
  rw [M.pCoreOf_F1]
  rintro c ⟨hcF, hcY⟩
  have hcH := M.F1_le_H hcF
  have hcHC : c ∈ M.HC := by
    refine Subgroup.mem_inf.mpr ⟨hcH, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp hcY u (Subgroup.mem_sup_left
      (M.U_le_Q5 M.b5el_mem_H hu))
  rw [← M.F1_inf_Q]
  exact Subgroup.mem_inf.mpr ⟨hcF, M.HC_le_Q hcHC⟩

theorem relIndex_TF_F1 : M.TF.relIndex M.F1 = 5 := by
  have h := Subgroup.relIndex_mul_card (H := M.TF) (K := M.F1)
  rw [inf_eq_left.mpr M.TF_le_F1, M.card_TF, M.card_F1] at h
  have h' : M.TF.relIndex M.F1 * 2 ^ 12 = 5 * 2 ^ 12 := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem pow_eq_one_of_mem_TF {y : G} (hy : y ∈ M.TF) :
    y ^ 2 ^ 12 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard _ hy
  rw [M.card_TF] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem b5el_not_mem_normalizer_TF :
    M.b5el ∉ Subgroup.normalizer (M.TF : Set G) := by
  intro hb
  have hAQ : ∀ y ∈ M.Agrp, y ∈ ruQ M.T := by
    intro y hy
    have hyTF : y ∈ M.TF := Subgroup.mem_sup_left hy
    have h1 : M.b5el * y⁻¹ * M.b5el⁻¹ ∈ M.TF :=
      (Subgroup.mem_normalizer_iff.mp hb _).mp (inv_mem hyTF)
    have hcTF : y * M.b5el * y⁻¹ * M.b5el⁻¹ ∈ M.TF := by
      have e : y * M.b5el * y⁻¹ * M.b5el⁻¹ = y * (M.b5el * y⁻¹ * M.b5el⁻¹) := by group
      rw [e]
      exact mul_mem hyTF h1
    obtain ⟨k, q, hq, hk⟩ := M.Agrp_conj_b5el hy
    have hcH : y * M.b5el * y⁻¹ * M.b5el⁻¹ ∈ ruH M.T := M.TF_le_H hcTF
    have hcQ : (y * M.b5el * y⁻¹ * M.b5el⁻¹) * M.b5el ^ (-((k : ℤ) - 1)) ∈ ruQ M.T := by
      have e : (y * M.b5el * y⁻¹ * M.b5el⁻¹) * M.b5el ^ (-((k : ℤ) - 1)) =
          M.b5el ^ ((k : ℤ) - 1) * (M.b5el * q * M.b5el⁻¹) * (M.b5el ^ ((k : ℤ) - 1))⁻¹ := by
        rw [hk, ← zpow_natCast]
        group
      rw [e]
      exact M.conj_mem_Q (zpow_mem M.b5el_mem_H _) (M.conj_mem_Q M.b5el_mem_H hq)
    obtain ⟨hcQ', -⟩ := M.mem_Q_of_mul_zpow_mem_Q hcH (M.pow_eq_one_of_mem_TF hcTF) hcQ
    exact M.mem_Q_of_comm_b5el (M.Agrp_le_H hy) (M.pow_eq_one_of_mem_Agrp hy) hcQ'
  have h1 := hAQ _ M.cak_mem_Agrp_one
  have hθ : M.θ ⟨M.cak 1, M.cak_mem_L 1⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨M.cak 1, M.cak_mem_L 1⟩, Subgroup.mem_subgroupOf.mpr h1, rfl⟩
  rw [M.θ_cak, pow_one] at hθ
  exact SL3.x0_zP0_not_mem_R0 hθ

theorem F1_inf_normalizer_TF :
    M.F1 ⊓ Subgroup.normalizer (M.TF : Set G) = M.TF := by
  set K := M.F1 ⊓ Subgroup.normalizer (M.TF : Set G)
  have hTK : M.TF ≤ K := le_inf M.TF_le_F1 Subgroup.le_normalizer
  have hKF : K ≤ M.F1 := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hTK hKF
  rw [M.relIndex_TF_F1] at hmul
  have hd : M.TF.relIndex K ∣ 5 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hTK
  · exfalso
    rw [h] at hmul
    have h1 : K.relIndex M.F1 = 1 := by omega
    have hFK := Subgroup.relIndex_eq_one.mp h1
    exact M.b5el_not_mem_normalizer_TF (Subgroup.mem_inf.mp (hFK M.b5el_mem_F1)).2

theorem isSylowTwoOf_TF_F1 : IsSylowTwoOf M.TF M.F1 :=
  ⟨M.TF_le_F1, IsPGroup.of_card M.card_TF, by
    show ¬ 2 ∣ M.TF.relIndex M.F1
    rw [M.relIndex_TF_F1]
    norm_num⟩

end RuDataM

end CFSG.Quasithin.RuType

module

public import CFSG.Quasithin.Background.C1PackC127Aux
public import CFSG.Quasithin.Background.C1PackC127Act
public import CFSG.Quasithin.Background.C1PackQuasi

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S14110
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_blockU_of_a4 {K : Subgroup G} {c : G} (h : A4Data K (blockU K) c) :
    pCoreOf 2 K = blockU K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWQ : blockU K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.le h.le_normalizer
      (IsPGroup.of_card (n := 2) (by rw [h.card_W]; norm_num))
  refine le_antisymm (fun x hx => ?_) hWQ
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp (CFSG.LieType.BorelTits.pCoreOf_le 2 K hx)
  have hck : c ^ k ∈ pCoreOf 2 K := by
    have := (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).inv_mem (hWQ hw)) hx
    simpa using this
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨c ^ k, hck⟩
  have hn' : (c ^ k) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have h3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast (c ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.c_pow_three,
      one_zpow]
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hdvd : orderOf (c ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 : orderOf (c ^ k) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hord : orderOf (c ^ k) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hdvd2
  have h1 : c ^ k = 1 := orderOf_eq_one_iff.1 hord
  rw [h1, mul_one]
  exact hw

theorem blockU_le_of_not_le_centralizer {U V K : Subgroup G} {c : G} (hKU : IsBlock2 U K)
    (hA4 : A4Data K (blockU K) c) (hVU : V ≤ pCoreOf 2 U)
    (hVK : K ≤ Subgroup.normalizer (V : Set G)) (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    blockU K ≤ V := by
  have hDW : ⁅V, K⁆ ≤ blockU K := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    rw [← pCoreOf_eq_blockU_of_a4 hA4]
    exact commutator_mem_pCoreOf_block hKU (hVU hv) hk
  have hD1 : ⁅V, K⁆ ≠ ⊥ := by
    intro h
    apply hKV
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  have hc : ∀ d ∈ ⁅V, K⁆, c * d * c⁻¹ ∈ ⁅V, K⁆ := by
    intro d hd
    have hN : K ≤ Subgroup.normalizer ((⁅K, V⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left K V
    rw [Subgroup.commutator_comm] at hN
    exact (Subgroup.mem_normalizer_iff.1 (hN hA4.mem_X) d).1 hd
  have hDeq := a4Data_eq_of_invariant hA4 hDW hD1 hc
  rw [← hDeq]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVK

theorem inf_centralizer_le_normalizer_block {X U V K : Subgroup G} (hX : CharTwo X)
    (hKU : IsBlock2 U K) (hUX : U ≤ X) (hVY : V ≤ pCoreOf 2 X) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hYU : pCoreOf 2 X ≤ pCoreOf 2 U)
    (hQKV : pCoreOf 2 K ≤ V) : X ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  refine le_normalizer_of_commutator_mem hKU fun g hg k hk => ?_
  refine hYU ?_
  have hkX : k ∈ X := hUX (hKU.2.1 hk)
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := hXN hg.1
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := hXN hkX
  have hP : ∀ k ∈ K, ∀ y ∈ pCoreOf 2 X, y * k * y⁻¹ * k⁻¹ ∈ V := fun k hk y hy =>
    hQKV (commutator_mem_pCoreOf_block hKU (hYU hy) hk)
  have hP' : ∀ k ∈ K, ∀ y ∈ pCoreOf 2 X, k * y * k⁻¹ * y⁻¹ ∈ V := by
    intro k hk y hy
    have h1 := V.inv_mem (hP k hk y hy)
    have : (y * k * y⁻¹ * k⁻¹)⁻¹ = k * y * k⁻¹ * y⁻¹ := by group
    rwa [this] at h1
  have hkey : ∀ y ∈ pCoreOf 2 X,
      y * (g * k * g⁻¹ * k⁻¹) * y⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ ∈ V := by
    intro y hy
    have hy₀ : g⁻¹ * y * g ∈ pCoreOf 2 X := by
      have := (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem hg.1)) y).1 hy
      simpa using this
    have hv₁ : k⁻¹ * y * k * y⁻¹ ∈ V := by
      have := hP' k⁻¹ (K.inv_mem hk) y hy
      simpa using this
    have hv₂ : k * (g⁻¹ * y * g) * k⁻¹ * (g⁻¹ * y * g)⁻¹ ∈ V := hP' k hk _ hy₀
    have hgk : g * k * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hgN hkN) ((Subgroup.normalizer (V : Set G)).inv_mem hgN)
    have h1 : (g * k * g⁻¹) * (k⁻¹ * y * k * y⁻¹) * (g * k * g⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hgk _).1 hv₁
    have h2 : g * (k * (g⁻¹ * y * g) * k⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hgN _).1 hv₂
    have h3 := V.mul_mem h1 h2
    have e : (g * k * g⁻¹ * k⁻¹) * y * (g * k * g⁻¹ * k⁻¹)⁻¹ * y⁻¹ =
        (g * k * g⁻¹) * (k⁻¹ * y * k * y⁻¹) * (g * k * g⁻¹)⁻¹ *
          (g * (k * (g⁻¹ * y * g) * k⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹) := by group
    have h4 : (g * k * g⁻¹ * k⁻¹) * y * (g * k * g⁻¹ * k⁻¹)⁻¹ * y⁻¹ ∈ V := by
      rw [e]
      exact h3
    have h5 := V.inv_mem h4
    have e2 : ((g * k * g⁻¹ * k⁻¹) * y * (g * k * g⁻¹ * k⁻¹)⁻¹ * y⁻¹)⁻¹ =
        y * (g * k * g⁻¹ * k⁻¹) * y⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ := by group
    rwa [e2] at h5
  have hmemC : g * k * g⁻¹ * k⁻¹ ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨X.mul_mem (X.mul_mem (X.mul_mem hg.1 hkX) (X.inv_mem hg.1)) (X.inv_mem hkX), ?_⟩
    have h1 : k * g⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      B6.conj_mem_centralizer_of_mem_normalizer hkN ((Subgroup.centralizer (V : Set G)).inv_mem hg.2)
    have h2 : g * k * g⁻¹ * k⁻¹ = g * (k * g⁻¹ * k⁻¹) := by group
    rw [h2]
    exact (Subgroup.centralizer (V : Set G)).mul_mem hg.2 h1
  have hmemA : g * k * g⁻¹ * k⁻¹ ∈
      centralizerSection (X ⊓ Subgroup.centralizer (V : Set G)) (pCoreOf 2 X) V :=
    (mem_centralizerSection_iff_of_le hVY).2 ⟨hmemC, hkey⟩
  exact centralizerSection_le_pCoreOf hX hV2 hXN hmemA

theorem isBlock2_of_a3Block {X T U K : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X)
    (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G)) (hUX : U ≤ X) (hTU : T ≤ U)
    (hKU : IsBlock2 U K) (hKalt : IsAltType K 3) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hKV : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G)) :
    IsBlock2 X K ∧ blockU K ≤ VZ T X := by
  obtain ⟨hVY, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hX (le_refl _)
  have hXN : X ≤ Subgroup.normalizer (VZ T X : Set G) := hred.2.1
  have hVX : VZ T X ≤ X := hred.1
  have hKX : K ≤ X := hKU.2.1.trans hUX
  have hYU : pCoreOf 2 X ≤ pCoreOf 2 U :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hT).trans hTU)
      (hUX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hVY' : VZ T X ≤ pCoreOf 2 X := fun x hx => (hVY hx).1
  have hVU : VZ T X ≤ pCoreOf 2 U := hVY'.trans hYU
  obtain ⟨c, hA4⟩ := A4Data.of_isShort2 hKU.1 hKalt
  have hKN : K ≤ Subgroup.normalizer (VZ T X : Set G) := hKX.trans hXN
  have hW : blockU K ≤ VZ T X := blockU_le_of_not_le_centralizer hKU hA4 hVU hKN hKV
  have hQKV : pCoreOf 2 K ≤ VZ T X := by
    rw [pCoreOf_eq_blockU_of_a4 hA4]
    exact hW
  have hC : X ⊓ Subgroup.centralizer (VZ T X : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    inf_centralizer_le_normalizer_block hX hKU hUX hVY' hVel.2 hXN hYU hQKV
  have hK3 := card_autI_eq_three hVel hKX hXN hA4 hW hKV
  obtain ⟨B, hB, hKB⟩ := exists_offender_of_commutator hVel hXN hT hKX hKJ hKV hK3
  have hO2 := pCoreOf_autI_eq_bot hVel hred
  have hsolvX := isSolvable_autI_of_perfectCore_le hVel hXN hsolv
  have hKF := autI_le_fittingOf hVel hVX hXN hO2 hsolvX hKX hK3 hB hKB
  have hsubn := isSubnormal_autI_of_le_fittingOf hVel (K := K) hKF
  have hP := isSubnormal_preI hVel hXN hsubn
  have hPN := preI_le_normalizer hVel hXN hKX hC
  have hKP : K ≤ preI hVel X hXN (autI hVel K) := fun k hk =>
    (mem_preI hVel).2 ⟨hKX hk, convI_mem_autI hVel hk (hKN hk)⟩
  have hKnormal : (K.subgroupOf (preI hVel X hXN (autI hVel K))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2 hPN
  exact ⟨⟨hKU.1, hKX, isSubnormal_subgroupOf_trans' hKP (preI_le hVel) hKnormal.isSubnormal hP⟩, hW⟩

end CFSG.Quasithin.C1Pack

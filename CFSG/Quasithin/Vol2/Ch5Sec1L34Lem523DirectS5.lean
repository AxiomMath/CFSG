module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN6
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.H13.Abs523

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem cover4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) [CharP K 2] {μ : K}
    (h0 : μ ≠ 0) (h1 : μ ≠ 1) (lam : K) : lam = 0 ∨ lam = 1 ∨ lam = μ ∨ lam = 1 + μ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hne1 : (1 : K) ≠ 0 := one_ne_zero
  have hA : (1 + μ : K) ≠ 0 := by
    intro h
    apply h1
    linear_combination h - h2
  have hB : (1 + μ : K) ≠ 1 := fun h => h0 (by linear_combination h)
  have e1 : μ ≠ 1 + μ := fun h => hne1 (by linear_combination -h)
  have hs3 : ({μ, 1 + μ} : Finset K).card = 2 := Finset.card_pair e1
  have n1 : (1 : K) ∉ ({μ, 1 + μ} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h1 h.symm, hB.symm⟩
  have hs2 : ({1, μ, 1 + μ} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem n1, hs3]
  have n0 : (0 : K) ∉ ({1, μ, 1 + μ} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne1.symm, h0.symm, hA.symm⟩
  have hS : ({0, 1, μ, 1 + μ} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem n0, hs2]
  have hfull : ({0, 1, μ, 1 + μ} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hS, hcard]
  have hmem : lam ∈ ({0, 1, μ, 1 + μ} : Finset K) := by
    rw [hfull]
    exact Finset.mem_univ _
  simpa using hmem

theorem coordN_one' {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) :
    coordN D (1 : G) N.one_mem = 0 := by
  unfold coordN
  have h1 : (⟨(1 : G), N.one_mem⟩ : ↥N) = 1 := rfl
  rw [h1, map_one, toAdd_one]

theorem exists_k_moves_z' (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) (h520 : Stmt5_1_20)
    (hyp : Hyp5_1_8 G T M L H n) (not59 : IsNotation5_1_9 T M L H B D) (hmod : IsCh5Module T L V)
    (hl34 : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2)
    (hnot : ¬ Concl5_1_14_four T L V B D n) (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    (hU : ¬ IsMulCommutative ↥(Ugrp Z₁ D₃))
    {N : Subgroup G} (D' : NatL2Data L N 2) {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N)
    (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hroot : D'.SylowAdapted (T ⊓ L))
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D'.K, μ ^ 4 = μ ∧
      coordN D' v hv = μ • coordN D' z hzN)
    {d : G} (hd : d ∈ D₃) (hd1 : d ≠ 1) :
    ∃ k ∈ oTwoUpper H, (d * z * d⁻¹)⁻¹ * (k * (d * z * d⁻¹) * k⁻¹) ∉ Z₁ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, hwa⟩ := coord_z_eq s D' hroot hTN hz hz1 hzN
  have hz'V2 : d * z * d⁻¹ ∈ conjClosure Z₁ D₃ := mem_conjClosure hd hz
  obtain ⟨hz'N, μ, hμ4, hμc⟩ := hV2 _ hz'V2
  have hz'Z : d * z * d⁻¹ ∉ Z₁ := conj_z_not_mem_Z₁ s h5114 hF hU hz hz1 hd hd1
  set z' : G := d * z * d⁻¹ with hz'def
  set V₂ : Subgroup G := conjClosure Z₁ D₃ with hV₂def
  have hZV₂ : Z₁ ≤ V₂ := le_conjClosure Z₁ D₃
  have hz'V₂ : z' ∈ V₂ := hz'V2
  have hVmem : ∀ x ∈ V₂, ∃ u ∈ Z₁, x = u ∨ x = u * z' := fun x hx =>
    s.mem_V₂_iff hz hz1 hd hd1 h5114 hF hx
  have hV₂N : V₂ ≤ N := fun x hx => (hV2 x hx).elim fun hxN _ => hxN
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hz'Z
    have hc0 : coordN D' z' hz'N = coordN D' (1 : G) N.one_mem := by
      rw [hμc, h0, zero_smul, coordN_one']
    have h1 : z' = 1 := coordN_injective D' hz'N N.one_mem hc0
    rw [h1]
    exact Z₁.one_mem
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply hz'Z
    have h2 : z' = z := coordN_injective D' hz'N hzN (by rw [hμc, h1, one_smul])
    rw [h2]
    exact hz
  have hΩ : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ :=
    (h5114 G T M L V H B D n hyp not59 hmod hl34).2.1.1
  have hTH : T ≤ H := hyp.hStar.1.1
  have hZcomm : ∀ x ∈ Z₁, ∀ h ∈ H, h * x = x * h := by
    intro x hx h hh
    have hxΩ : x ∈ quasithinOmegaOneCenter T := s.z1.1 hx
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hΩ hxΩ
    exact (Subgroup.mem_centralizer_iff.mp hle h hh)
  have hKZ : ∀ k ∈ oTwoUpper H, ∀ x ∈ Z₁, k * x = x * k := fun k hk x hx =>
    hZcomm x hx k (oTwoUpper_le H hk)
  have hTZ : ∀ t ∈ T, ∀ x ∈ Z₁, t * x = x * t := fun t ht x hx =>
    hZcomm x hx t (hTH ht)
  have hku : ∀ k ∈ oTwoUpper H, ∀ u ∈ Z₁, k * u * k⁻¹ = u := by
    intro k hk u hu
    rw [hKZ k hk u hu, mul_assoc, mul_inv_cancel, mul_one]
  have htu : ∀ t ∈ T, ∀ u ∈ Z₁, t * u * t⁻¹ = u := by
    intro t ht u hu
    rw [hTZ t ht u hu, mul_assoc, mul_inv_cancel, mul_one]
  have hKV : ∀ k ∈ oTwoUpper H, ∀ x ∈ V₂, k * x * k⁻¹ ∈ V₂ := by
    intro k hk x hx
    obtain ⟨u, hu, hxu⟩ := hVmem x hx
    rcases hxu with hxu | hxu
    · rw [hxu, hku k hk u hu]
      exact hZV₂ hu
    · have hc := hcon k hk
      have e : k * (u * z') * k⁻¹ = u * (z' * (z'⁻¹ * (k * z' * k⁻¹))) := by
        rw [show k * (u * z') * k⁻¹ = (k * u * k⁻¹) * (k * z' * k⁻¹) by group, hku k hk u hu]
        group
      rw [hxu, e]
      exact V₂.mul_mem (hZV₂ hu) (V₂.mul_mem hz'V₂ (hZV₂ hc))
  have hTz : ∀ t ∈ T, t * z' * t⁻¹ ∈ V₂ := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (N : Set G) := hTN ht
    have hyN : t * z' * t⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp htN z').mp hz'N
    have htL : t ∈ Subgroup.normalizer (L : Set G) :=
      (s.hyp.hyp.toHyp5_0_1.T_le.trans s.hyp.hyp.toHyp5_0_1.normal) ht
    obtain ⟨σ, hσ⟩ := D'.exists_semilinear ⟨t, htN⟩ htL
    have hcoord : coordN D' (t * z' * t⁻¹) hyN = (σ μ) • coordN D' z hzN := by
      rw [← coordN_conj D' htN hz'N, hμc, hσ, conj_fix_of_centralizes D' htN
        (Subgroup.mem_centralizer_iff.mp (T_le_centralizer_Z₁ s ht) z hz).symm]
    have hK4 : Nat.card D'.K = 4 := by rw [D'.card]; norm_num
    haveI : CharP D'.K 2 :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D'.card
    have hzzN : z * z' ∈ N := N.mul_mem hzN hz'N
    rcases cover4 hK4 hμ0 hμ1 (σ μ) with h | h | h | h
    · have : t * z' * t⁻¹ = 1 := coordN_injective D' hyN N.one_mem (by
        rw [hcoord, h, zero_smul, coordN_one'])
      rw [this]
      exact V₂.one_mem
    · have : t * z' * t⁻¹ = z := coordN_injective D' hyN hzN (by rw [hcoord, h, one_smul])
      rw [this]
      exact hZV₂ hz
    · have : t * z' * t⁻¹ = z' := coordN_injective D' hyN hz'N (by rw [hcoord, h, hμc])
      rw [this]
      exact hz'V₂
    · have : t * z' * t⁻¹ = z * z' := coordN_injective D' hyN hzzN (by
        rw [hcoord, h, coordN_mul D' hzN hz'N hzzN, hμc, add_smul, one_smul])
      rw [this]
      exact V₂.mul_mem (hZV₂ hz) hz'V₂
  have hTV : ∀ t ∈ T, ∀ x ∈ V₂, t * x * t⁻¹ ∈ V₂ := by
    intro t ht x hx
    obtain ⟨u, hu, hxu⟩ := hVmem x hx
    rcases hxu with hxu | hxu
    · rw [hxu, htu t ht u hu]
      exact hZV₂ hu
    · have e : t * (u * z') * t⁻¹ = (t * u * t⁻¹) * (t * z' * t⁻¹) := by group
      rw [hxu, e, htu t ht u hu]
      exact V₂.mul_mem (hZV₂ hu) (hTz t ht)
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (V₂ : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hKV k hk x hx, fun hx => by
      have h := hKV k⁻¹ (inv_mem hk) _ hx
      convert h using 1
      group⟩
  have hTN' : T ≤ Subgroup.normalizer (V₂ : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hTV t ht x hx, fun hx => by
      have h := hTV t⁻¹ (inv_mem ht) _ hx
      convert h using 1
      group⟩
  have hDN : D₃ ≤ Subgroup.normalizer (V₂ : Set G) := le_normalizer_conjClosure Z₁ D₃
  have hH_sup : H = oTwoUpper H ⊔ T :=
    eq_oTwoUpper_sup_of_isSylowTwoOf' (hyp.toHyp5_0_1.isSylowTwoOf hTH)
  have hHN : H ≤ Subgroup.normalizer (V₂ : Set G) := by
    rw [hH_sup]
    exact sup_le hKN hTN'
  have hHDN : H ⊔ D₃ ≤ Subgroup.normalizer (V₂ : Set G) := sup_le hHN hDN
  have hV₂HD : V₂ ≤ H ⊔ D₃ := by
    refine conjClosure_le fun h hh x hx => ?_
    have hxT : x ∈ T := (quasithinOmegaOneCenter_le_inf T (s.z1.1 hx)).1
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left (hTH hxT)))
      (inv_mem (Subgroup.mem_sup_right hh))
  have hNcard : Nat.card ↥N = 16 := by
    rw [Nat.card_congr D'.E.toEquiv]
    show Nat.card (Fin 2 → D'.K) = 16
    rw [Nat.card_fun, D'.card]
    norm_num
  have hV₂p : IsPGroup 2 ↥V₂ := by
    have h16 : Nat.card ↥V₂ ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hV₂N
    rw [hNcard] at h16
    exact IsPGroup.of_card_dvd_pow (n := 4) (by rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; exact h16)
  have hpc : V₂ ≤ pCoreOf 2 (H ⊔ D₃) :=
    CFSG.Quasithin.RonanD33.le_pCoreOf_of_le_normalizer hV₂HD hHDN hV₂p
  have hI2 : pCoreOf 2 (H ⊔ D₃) = ⊥ :=
    (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).2
  have hzV : z ∈ V₂ := hZV₂ hz
  have hz_bot : z ∈ pCoreOf 2 (H ⊔ D₃) := hpc hzV
  rw [hI2, Subgroup.mem_bot] at hz_bot
  exact hz1 hz_bot

end CFSG.Quasithin.H13

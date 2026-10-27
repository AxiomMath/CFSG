module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeTICount
public import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.GroupTheory.IndexNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeSevenTools
import CFSG.Monster.B.GSide.HInnerFusion
import CFSG.Walter.ReeOrder.JT.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

theorem exists_sylow_two_normalizer_le {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTM : T ≤ M)
    (hNM : normalizer (T : Set X) ≤ M) {v : X} (hvM : v ∈ M) (hv : orderOf v = 2) :
    ∃ S : Sylow 2 X, v ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ M ∧
      normalizer ((S : Subgroup X) : Set X) ≤ M := by
  classical
  have hdvd : ¬ 2 ∣ T.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hrel : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
  have hdvdM : ¬ 2 ∣ (T.subgroupOf M).index := by
    intro h2
    apply hdvd
    rw [← hrel]
    exact dvd_mul_of_dvd_left h2 M.index
  have hvM' : orderOf (⟨v, hvM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe, hv]
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨v, hvM⟩ : ↥M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvM', pow_one])
  obtain ⟨m, hm⟩ := CFSG.Monster.B.GSide.exists_conj_mem_of_not_dvd_index
    (T.subgroupOf M) hdvdM hP
  have hvT : (m : X) * v * (m : X)⁻¹ ∈ T := by
    have h := hm ⟨v, hvM⟩ (Subgroup.mem_zpowers _)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  let Ssub : Subgroup X := T.map (MulAut.conj (m : X)⁻¹).toMonoidHom
  have hSsubcard : Nat.card Ssub = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj (m : X)⁻¹).injective
  have hSsubP : IsPGroup 2 Ssub :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1.map (MulAut.conj (m : X)⁻¹).toMonoidHom
  have hSsubidx : ¬ 2 ∣ Ssub.index := by
    have h1 : T.index * Nat.card T = Nat.card X := Subgroup.index_mul_card T
    have h2 : Ssub.index * Nat.card Ssub = Nat.card X := Subgroup.index_mul_card Ssub
    have h3 : Ssub.index * Nat.card T = Nat.card X := by rw [hSsubcard] at h2; exact h2
    have heq : T.index * Nat.card T = Ssub.index * Nat.card T := by rw [h1, h3]
    have hidx : Ssub.index = T.index := (Nat.mul_right_cancel Nat.card_pos heq).symm
    rw [hidx]
    exact hdvd
  let S : Sylow 2 X := hSsubP.toSylow hSsubidx
  have hScoe : (S : Subgroup X) = Ssub := IsPGroup.toSylow_coe hSsubP hSsubidx
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hScoe]
    have hf : (MulAut.conj (m : X)⁻¹) ((m : X) * v * (m : X)⁻¹) = v := by
      rw [MulAut.conj_apply]
      group
    rw [← hf]
    exact Subgroup.mem_map_of_mem _ hvT
  · rw [hScoe]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj (m : X)⁻¹) y ∈ M
    rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem (M.inv_mem m.2) (hTM hy)) (M.inv_mem (M.inv_mem m.2))
  · rw [hScoe, ← Subgroup.map_equiv_normalizer_eq T (MulAut.conj (m : X)⁻¹)]
    intro n hn
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hn
    have hyM : y ∈ M := hNM hy
    have hmM : (m : X) ∈ M := m.2
    rw [← hyeq]
    change (MulAut.conj (m : X)⁻¹) y ∈ M
    rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem (M.inv_mem hmM) hyM) (M.inv_mem (M.inv_mem hmM))

theorem index_ne_two_of_fpf {X : Type} [Group X] [Finite X] {T B M : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hT8 : Nat.card T = 8)
    (hBT : B ≤ normalizer (T : Set X)) (hB7 : Nat.card B = 7)
    (hBC : ¬ B ≤ centralizer (T : Set X)) (hTM : T ≤ M) (hBM : B ≤ M) :
    ∀ N : Subgroup ↥M, N.index ≠ 2 := by
  classical
  have : Fintype X := Fintype.ofFinite X
  intro N hN
  have hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hN
  let : N.Normal := hNnormal
  let Nx : Subgroup X := N.map M.subtype
  have hNxM : Nx ≤ M := Subgroup.map_subtype_le N
  have hNxsub : Nx.subgroupOf M = N :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective N
  have hBNx : B ≤ Nx := by
    intro b hb
    have hbM : b ∈ M := hBM hb
    have hb7 : b ^ 7 = 1 := by
      have h := pow_card_eq_one (G := ↥B) (x := ⟨b, hb⟩)
      rw [← Nat.card_eq_fintype_card, hB7] at h
      simpa using congrArg Subtype.val h
    have hb8 : b ^ 8 = b := by
      rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_succ, hb7, one_mul]
    have hsq : (⟨b, hbM⟩ : ↥M) ^ 2 ∈ N := Subgroup.sq_mem_of_index_two hN ⟨b, hbM⟩
    have hpow : ((⟨b, hbM⟩ : ↥M) ^ 2) ^ 4 ∈ N := Subgroup.pow_mem N hsq 4
    have heq : ((⟨b, hbM⟩ : ↥M) ^ 2) ^ 4 = ⟨b, hbM⟩ := by
      apply Subtype.ext
      show (b ^ 2) ^ 4 = b
      rw [← pow_mul, show 2 * 4 = 8 by norm_num, hb8]
    exact Subgroup.mem_map.mpr ⟨⟨b, hbM⟩, heq ▸ hpow, rfl⟩
  have hnotTNx : ¬ T ≤ Nx := by
    intro hle
    have hle' : T.subgroupOf M ≤ N := by
      rw [← hNxsub]
      exact Subgroup.subgroupOf_mono M hle
    have h2 : 2 ∣ (T.subgroupOf M).index := by
      have h := Subgroup.index_dvd_of_le hle'
      rwa [hN] at h
    have hdvd : ¬ 2 ∣ T.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
      rwa [Subgroup.relIndex_top_right] at h
    apply hdvd
    rw [← Subgroup.relIndex_mul_index hTM]
    exact dvd_mul_of_dvd_left h2 M.index
  let T' : Subgroup ↥M := T.subgroupOf M
  let T0' : Subgroup ↥M := T' ⊓ N
  have hT'card : Nat.card T' = 8 := by
    show Nat.card (T.subgroupOf M) = 8
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT8]
  have hnotT' : ¬ T' ≤ N := by
    intro h
    apply hnotTNx
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTM hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hT0'rel : T0'.relIndex T' ≤ 2 := by
    have h1 : T0'.relIndex T' = N.relIndex T' := by
      show (T' ⊓ N).relIndex T' = N.relIndex T'
      rw [Subgroup.inf_relIndex_left]
    rw [h1, ← QuotientGroup.ker_mk' N, Subgroup.relIndex_ker]
    have hle : Nat.card ↥(T'.map (QuotientGroup.mk' N)) ≤ Nat.card (↥M ⧸ N) := by
      have h := Nat.card_le_card_of_injective
        (fun x : ↥(T'.map (QuotientGroup.mk' N)) => (x : ↥M ⧸ N)) Subtype.coe_injective
      simpa using h
    rwa [← Subgroup.index_eq_card N, hN] at hle
  have hT0'card : Nat.card T0' = 4 := by
    have hmul : T0'.relIndex T' * Nat.card T0' = 8 := by
      have h := Subgroup.relIndex_mul_card T0' T'
      rwa [hT'card, inf_eq_left.mpr (show T0' ≤ T' from inf_le_left)] at h
    have hpos : 0 < T0'.relIndex T' := by
      rcases Nat.eq_zero_or_pos (T0'.relIndex T') with h0 | h0
      · rw [h0, zero_mul] at hmul
        omega
      · exact h0
    have hne1 : T0'.relIndex T' ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hnotT' (h1.trans inf_le_right)
    have hx2 : T0'.relIndex T' = 2 := by omega
    rw [hx2] at hmul
    omega
  let T0 : Subgroup X := T ⊓ Nx
  have hT0sub : T0.subgroupOf M = T0' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxT, hxNx⟩
      refine ⟨hxT, ?_⟩
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxNx
      have hnx' : n = x := Subtype.ext hnx
      rw [← hnx']
      exact hn
    · rintro ⟨hxT, hxN⟩
      exact ⟨hxT, Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩⟩
  have hT0card : Nat.card T0 = 4 := by
    have h1 : Nat.card ↥(T0.subgroupOf M) = Nat.card T0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_right hNxM)).toEquiv
    rw [hT0sub, hT0'card] at h1
    exact h1.symm
  have hBT0 : B ≤ normalizer (T0 : Set X) := by
    intro b hb
    have hbM : b ∈ M := hBM hb
    have hbT : b ∈ normalizer (T : Set X) := hBT hb
    have hNxconj : ∀ x : X, x ∈ Nx → b * x * b⁻¹ ∈ Nx := by
      rintro x ⟨n, hn, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨b, hbM⟩ * n * ⟨b, hbM⟩⁻¹, hNnormal.conj_mem n hn ⟨b, hbM⟩, rfl⟩
    have hNxconji : ∀ x : X, x ∈ Nx → b⁻¹ * x * b ∈ Nx := by
      rintro x ⟨n, hn, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨⟨b, hbM⟩⁻¹ * n * ⟨b, hbM⟩, by simpa using hNnormal.conj_mem n hn ⟨b, hbM⟩⁻¹, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp hbT x).mp hx.1, hNxconj x hx.2⟩
    · intro hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp hbT x).mpr hx.1, ?_⟩
      have h := hNxconji (b * x * b⁻¹) hx.2
      rwa [show b⁻¹ * (b * x * b⁻¹) * b = x by group] at h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let act : MulAction ↥B ↥T0 :=
    MulAction.compHom ↥T0 ((Subgroup.normalizerMonoidHom T0).comp (Subgroup.inclusion hBT0))
  have hBpg : IsPGroup 7 ↥B := IsPGroup.of_card (p := 7) (n := 1) (by simpa using hB7)
  have hcong : Nat.card ↥T0 ≡ (MulAction.fixedPoints ↥B ↥T0).ncard [MOD 7] := by
    have h := IsPGroup.card_modEq_card_fixedPoints (p := 7) (G := ↥B) hBpg (α := ↥T0)
    rwa [Nat.card_coe_set_eq] at h
  have hfixncard : (MulAction.fixedPoints ↥B ↥T0).ncard = 4 := by
    have hle : (MulAction.fixedPoints ↥B ↥T0).ncard ≤ 4 := by
      have h := Nat.card_le_card_of_injective
        (fun x : MulAction.fixedPoints ↥B ↥T0 => (x : ↥T0)) Subtype.coe_injective
      rw [Nat.card_coe_set_eq, hT0card] at h
      exact h
    have hmod : (MulAction.fixedPoints ↥B ↥T0).ncard % 7 = 4 := by
      have h := hcong
      rw [hT0card, Nat.ModEq] at h
      omega
    omega
  have hall : MulAction.fixedPoints ↥B ↥T0 = ⊤ := by
    apply Set.eq_top_of_card_le_of_finite
    rw [hT0card, Nat.card_coe_set_eq, hfixncard]
  have hsmul : ∀ (b : ↥B) (x : ↥T0),
      ((b • x : ↥T0) : X) = (b : X) * (x : X) * (b : X)⁻¹ := by
    intro b x
    change ((Subgroup.normalizerMonoidHom T0 (Subgroup.inclusion hBT0 b)) x : X) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hcomm : ∀ (t : ↥T0) (b : ↥B), (b : X) * (t : X) = (t : X) * (b : X) := by
    intro t b
    have htfix : t ∈ MulAction.fixedPoints ↥B ↥T0 := by rw [hall]; trivial
    have h := (MulAction.mem_fixedPoints.mp htfix) b
    have hbx : (b : X) * (t : X) * (b : X)⁻¹ = (t : X) := by
      rw [← hsmul b t]
      exact congrArg Subtype.val h
    calc (b : X) * (t : X) = (b : X) * (t : X) * (b : X)⁻¹ * (b : X) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = (t : X) * (b : X) := by rw [hbx]
  have hcardT0 : Fintype.card ↥T0 = 4 := by
    rw [← Nat.card_eq_fintype_card, hT0card]
  obtain ⟨t, htne⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := ↥T0) (by rw [hcardT0]; norm_num) (1 : ↥T0)
  have ht1 : (t : X) = 1 :=
    eq_one_of_commute_of_card_eight hT8 hBT hB7 hBC t.2.1
      (fun b hb => hcomm t ⟨b, hb⟩)
  exact htne (Subtype.ext ht1)

theorem card_centralizer_subgroupOf {X : Type} [Group X] {M K : Subgroup X} (hKM : K ≤ M) :
    Nat.card (centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M)) =
      Nat.card ↥(centralizer (K : Set X) ⊓ M) := by
  have e : centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) =
      (centralizer (K : Set X) ⊓ M).subgroupOf M := by
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨?_, y.2⟩
      intro k hk
      have := congrArg Subtype.val (h ⟨k, hKM hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
      simpa using this
    · rintro ⟨h, -⟩ z hz
      apply Subtype.ext
      exact h (z : X) (Subgroup.mem_subgroupOf.mp hz)
  rw [e]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem card_centralizer_singleton_subgroup {X : Type} [Group X] (M : Subgroup X) (j : ↥M) :
    Nat.card (centralizer ({j} : Set ↥M)) =
      Nat.card ↥(centralizer ({(j : X)} : Set X) ⊓ M) := by
  have e : centralizer ({j} : Set ↥M) =
      (centralizer ({(j : X)} : Set X) ⊓ M).subgroupOf M := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, y.2⟩
    · rintro ⟨h, -⟩
      exact Subtype.ext h
  rw [e]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem tiCountHyp_subgroup {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hT8 : Nat.card T = 8)
    (hTe : ∀ x ∈ T, x * x = 1) (hTM : T ≤ M) (hN : Nat.card (normalizer (T : Set X)) = 168)
    (hNM : normalizer (T : Set X) ≤ M)
    (hC : ∀ j ∈ M, orderOf j = 2 → ∃ P : Sylow 2 X, j ∈ (P : Subgroup X) ∧
      (P : Subgroup X) ≤ M ∧ Nat.card ↥(centralizer ({j} : Set X) ⊓ M) = 24 ∧
      centralizer ({j} : Set X) ⊓ M ≤ normalizer ((P : Subgroup X) : Set X)) :
    ∃ S : Sylow 2 ↥M, (S : Subgroup ↥M) = T.subgroupOf M ∧ TICountHyp S := by
  classical
  have hTP : IsPGroup 2 T := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1
  have hdvd : ¬ 2 ∣ T.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hrel : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
  have hdvdM : ¬ 2 ∣ (T.subgroupOf M).index := by
    intro h2
    apply hdvd
    rw [← hrel]
    exact dvd_mul_of_dvd_left h2 M.index
  have hT'P : IsPGroup 2 (T.subgroupOf M) := hTP.comap_subtype
  let S : Sylow 2 ↥M := hT'P.toSylow hdvdM
  have hScoe : (S : Subgroup ↥M) = T.subgroupOf M := IsPGroup.toSylow_coe hT'P hdvdM
  refine ⟨S, hScoe, ?_⟩
  have hcardT' : Nat.card (T.subgroupOf M) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT8]
  refine ⟨by rw [hScoe, hcardT'], ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (x : X) ∈ T := hx
    apply Subtype.ext
    exact hTe (x : X) hx'
  · intro j hj
    have hj2 : orderOf (j : X) = 2 := by rwa [Subgroup.orderOf_coe]
    obtain ⟨P, hjP, hPM, hCcard, hCle⟩ := hC (j : X) j.2 hj2
    have hidxP : ¬ 2 ∣ (P.subgroupOf M).index := by
      intro h2
      apply P.not_dvd_index
      have hrel' : P.relIndex M * M.index = P.index := Subgroup.relIndex_mul_index hPM
      rw [← hrel']
      exact dvd_mul_of_dvd_left h2 M.index
    have hPP : IsPGroup 2 (P : Subgroup X) := P.isPGroup'
    have hP'P : IsPGroup 2 (P.subgroupOf M) := hPP.comap_subtype
    let P' : Sylow 2 ↥M := hP'P.toSylow hidxP
    have hP'coe : (P' : Subgroup ↥M) = P.subgroupOf M := IsPGroup.toSylow_coe hP'P hidxP
    have hcardj : Nat.card (centralizer ({j} : Set ↥M)) = 24 := by
      rw [card_centralizer_singleton_subgroup, hCcard]
    refine ⟨hcardj, P', ?_, ?_⟩
    · rw [hP'coe]
      exact Subgroup.mem_subgroupOf.mpr hjP
    · rw [hP'coe, ← Subgroup.subgroupOf_normalizer_eq hPM]
      intro c hc
      rw [Subgroup.mem_subgroupOf]
      apply hCle
      refine ⟨?_, c.2⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
  · rw [hScoe, ← Subgroup.subgroupOf_normalizer_eq hTM]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv).trans hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

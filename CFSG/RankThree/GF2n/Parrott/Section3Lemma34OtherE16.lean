module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts
public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.GroupTheory.SylowOrbitCard
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Count
public import CFSG.LocalAnalysis.OddStandard.ThmCTSub
public import CFSG.LocalAnalysis.OddStandard.ThmCTWr
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.RankThree.GF2n.Parrott

open Subgroup CFSG.OddStandard.ThmC.T CFSG.GroupTheory
open scoped Pointwise

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
private lemma card_subgroupOf_of_le {T H : Subgroup K} (hH : H ≤ T) :
    Nat.card (H.subgroupOf T) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv

omit [Finite K] in
private lemma eq_of_subgroupOf_eq {T H₁ H₂ : Subgroup K} (h₁ : H₁ ≤ T) (h₂ : H₂ ≤ T)
    (h : H₁.subgroupOf T = H₂.subgroupOf T) : H₁ = H₂ := by
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h

omit [Finite K] in
private lemma map_conj_inv_eq_self {H : Subgroup K} {a : K}
    (h : H.map (MulAut.conj a).toMonoidHom = H) :
    H.map (MulAut.conj a⁻¹).toMonoidHom = H := by
  have h1 : (H.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = H := by
    rw [Subgroup.map_conj_map_conj, mul_inv_cancel, map_one]
    exact Subgroup.map_id H
  have h2 : (H.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj a).toMonoidHom := by rw [h1, h]
  exact Subgroup.map_injective (MulAut.conj a).injective h2

omit [Finite K] in
private lemma sq_eq_one_of_mem_left {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) {x : K} (hx : x ∈ D) :
    x * x = 1 := by
  have h := hDF.sq_left (⟨x, hDT hx⟩ : ↥T) hx
  exact congrArg Subtype.val h

omit [Finite K] in
private lemma sq_eq_one_of_mem_right {T : Sylow 2 K} {D F : Subgroup K} (hFT : F ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) {x : K} (hx : x ∈ F) :
    x * x = 1 := by
  have h := hDF.sq_right (⟨x, hFT hx⟩ : ↥T) hx
  exact congrArg Subtype.val h

omit [Finite K] in
private lemma comm_of_mem_right {T : Sylow 2 K} {D F : Subgroup K} (hFT : F ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) {x y : K} (hx : x ∈ F) (hy : y ∈ F) :
    x * y = y * x := by
  have h := hDF.comm_right (⟨x, hFT hx⟩ : ↥T) hx (⟨y, hFT hy⟩ : ↥T) hy
  exact congrArg Subtype.val h

private lemma false_of_centralizes_orderOf_three {T : Sylow 2 K} (hT : IsT ↥T)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    {w τ : K} (hwT : w ∈ T) (hw1 : w ≠ 1) (hτ : orderOf τ = 3)
    (hcomm : w * τ = τ * w) : False := by
  let wT : ↥T := ⟨w, hwT⟩
  have hdiv : Nat.card (Subgroup.zpowers wT) ∣ Nat.card ↥T :=
    Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_zpowers, hT.card_eq, show (64 : ℕ) = 2 ^ 6 by norm_num] at hdiv
  have hne1 : Nat.card (Subgroup.zpowers wT) ≠ 1 := by
    intro h
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe wT] at h
    exact hw1 (orderOf_eq_one_iff.mp h)
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hk0 : k ≠ 0 := by
    intro h0
    exact hne1 (by rw [Nat.card_zpowers, hk, h0, pow_zero])
  have h2dvd : 2 ∣ Nat.card (Subgroup.zpowers wT) := by
    rw [Nat.card_zpowers, hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers wT) 2 h2dvd
  have hcomm' : ((v : ↥T) : K) * τ = τ * ((v : ↥T) : K) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp v.2
    have hc : Commute w τ := hcomm
    have h1 : ((v : ↥T) : K) = w ^ n := by rw [← hn]; rfl
    rw [h1]
    exact (hc.zpow_left n).eq
  have hτC : τ ∈ Subgroup.centralizer ({((v : ↥T) : K)} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm'.symm
  have hdvd : orderOf τ ∣ Nat.card ↥(Subgroup.centralizer ({((v : ↥T) : K)} : Set K)) :=
    Subgroup.orderOf_dvd_natCard _ hτC
  have hv2 : orderOf ((v : ↥T) : K) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hv]
  rw [hcent _ hv2, hτ] at hdvd
  omega

omit [Finite K] in
private lemma map_conj_left_eq_left_or_right {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) {n : K}
    (hn : n ∈ normalizer (T : Set K)) :
    D.map (MulAut.conj n).toMonoidHom = D ∨ D.map (MulAut.conj n).toMonoidHom = F := by
  have hTmap : (T : Subgroup K).map (MulAut.conj n).toMonoidHom = (T : Subgroup K) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hle : D.map (MulAut.conj n).toMonoidHom ≤ T :=
    (Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hDT).trans hTmap.le
  have hcardD : Nat.card D = 16 := by
    rw [← card_subgroupOf_of_le hDT]
    exact hDF.card_left
  have hEcard : Nat.card ((D.map (MulAut.conj n).toMonoidHom).subgroupOf T) = 16 := by
    rw [card_subgroupOf_of_le hle, Subgroup.card_map_of_injective (MulAut.conj n).injective,
      hcardD]
  have hEsq : ∀ x ∈ (D.map (MulAut.conj n).toMonoidHom).subgroupOf T, x * x = 1 := by
    intro x hx
    obtain ⟨d, hd, hd'⟩ := hx
    have hxd : (x : K) = MulAut.conj n d := hd'.symm
    have hval : (x : K) * (x : K) = 1 := by
      rw [hxd, ← map_mul, sq_eq_one_of_mem_left hDT hDF hd, map_one]
    exact Subtype.ext hval
  rcases hDF.eq_or ((D.map (MulAut.conj n).toMonoidHom).subgroupOf T) hEsq hEcard with h | h
  · left
    exact eq_of_subgroupOf_eq hle hDT h
  · right
    exact eq_of_subgroupOf_eq hle hFT h

omit [Finite K] in
private lemma map_conj_right_eq_right_or_left {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) {n : K}
    (hn : n ∈ normalizer (T : Set K)) :
    F.map (MulAut.conj n).toMonoidHom = F ∨ F.map (MulAut.conj n).toMonoidHom = D := by
  have hTmap : (T : Subgroup K).map (MulAut.conj n).toMonoidHom = (T : Subgroup K) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hle : F.map (MulAut.conj n).toMonoidHom ≤ T :=
    (Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hFT).trans hTmap.le
  have hcardF : Nat.card F = 16 := by
    rw [← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hEcard : Nat.card ((F.map (MulAut.conj n).toMonoidHom).subgroupOf T) = 16 := by
    rw [card_subgroupOf_of_le hle, Subgroup.card_map_of_injective (MulAut.conj n).injective,
      hcardF]
  have hEsq : ∀ x ∈ (F.map (MulAut.conj n).toMonoidHom).subgroupOf T, x * x = 1 := by
    intro x hx
    obtain ⟨d, hd, hd'⟩ := hx
    have hxd : (x : K) = MulAut.conj n d := hd'.symm
    have hval : (x : K) * (x : K) = 1 := by
      rw [hxd, ← map_mul, sq_eq_one_of_mem_right hFT hDF hd, map_one]
    exact Subtype.ext hval
  rcases hDF.eq_or ((F.map (MulAut.conj n).toMonoidHom).subgroupOf T) hEsq hEcard with h | h
  · right
    exact eq_of_subgroupOf_eq hle hDT h
  · left
    exact eq_of_subgroupOf_eq hle hFT h

private lemma odd_index_normalizer {T : Sylow 2 K} :
    Odd (T.subgroupOf (normalizer (T : Set K))).index := by
  have hdvd : (T.subgroupOf (normalizer (T : Set K))).index ∣ T.index :=
    ⟨(normalizer (T : Set K)).index,
      (Subgroup.relIndex_mul_index (H := (T : Subgroup K)) le_normalizer).symm⟩
  exact Nat.not_even_iff_odd.mp fun he => T.not_dvd_index (even_iff_two_dvd.mp he |>.trans hdvd)

omit [Finite K] in
private lemma pow_index_mem_normalizer {T : Sylow 2 K} {n : K}
    (hn : n ∈ normalizer (T : Set K)) :
    n ^ (T.subgroupOf (normalizer (T : Set K))).index ∈ (T : Subgroup K) := by
  have hN : (T.subgroupOf (normalizer (T : Set K))).Normal := Subgroup.normal_in_normalizer
  have h := @Subgroup.pow_index_mem ↥(normalizer (T : Set K)) _
    (T.subgroupOf (normalizer (T : Set K))) hN ⟨n, hn⟩
  have hval : (((⟨n, hn⟩ : ↥(normalizer (T : Set K))) ^
      (T.subgroupOf (normalizer (T : Set K))).index : ↥(normalizer (T : Set K))) : K) ∈
      (T : Subgroup K) := h
  rw [Subgroup.coe_pow] at hval
  simpa using hval

omit [Finite K] in
private lemma map_conj_pow_odd_of_swap {D F : Subgroup K} {n : K}
    (hswap : D.map (MulAut.conj n).toMonoidHom = F)
    (hback : F.map (MulAut.conj n).toMonoidHom = D) :
    ∀ k : ℕ, D.map (MulAut.conj (n ^ (2 * k + 1))).toMonoidHom = F := by
  have hn2 : D.map (MulAut.conj (n * n)).toMonoidHom = D := by
    rw [← Subgroup.map_conj_map_conj, hswap, hback]
  intro k
  induction k with
  | zero => simpa using hswap
  | succ k ih =>
      have hpow : n ^ (2 * (k + 1) + 1) = n ^ (2 * k + 1) * n ^ 2 := by
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add]
      rw [hpow, ← Subgroup.map_conj_map_conj, show n ^ 2 = n * n from pow_two n, hn2, ih]

private lemma normalizer_T_le_normalizer_left {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    normalizer (T : Set K) ≤ normalizer (D : Set K) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hDn
  have hswap : D.map (MulAut.conj n).toMonoidHom = F := by
    rcases map_conj_left_eq_left_or_right hDT hFT hDF hn with h | h
    · exact absurd h hDn
    · exact h
  have hDFne : D ≠ F := fun h => hDF.ne (by rw [h])
  have hback : F.map (MulAut.conj n).toMonoidHom = D := by
    rcases map_conj_right_eq_right_or_left hDT hFT hDF hn with h | h
    · exact absurd (Subgroup.map_injective (MulAut.conj n).injective (hswap.trans h.symm)) hDFne
    · exact h
  have hTnorm : (T : Subgroup K) ≤ normalizer (D : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDT).1 hDF.normal_left
  have hpowmem : n ^ (T.subgroupOf (normalizer (T : Set K))).index ∈ (T : Subgroup K) :=
    pow_index_mem_normalizer hn
  have hpowD : D.map (MulAut.conj (n ^ (T.subgroupOf (normalizer (T : Set K))).index)).toMonoidHom
      = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm hpowmem)
  obtain ⟨k, hk⟩ := odd_index_normalizer (T := T)
  rw [hk] at hpowD
  exact hDFne (hpowD.symm.trans (map_conj_pow_odd_of_swap hswap hback k))

private lemma normalizer_T_le_normalizer_right {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    normalizer (T : Set K) ≤ normalizer (F : Set K) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hFn
  have hswap : F.map (MulAut.conj n).toMonoidHom = D := by
    rcases map_conj_right_eq_right_or_left hDT hFT hDF hn with h | h
    · exact absurd h hFn
    · exact h
  have hDFne : D ≠ F := fun h => hDF.ne (by rw [h])
  have hback : D.map (MulAut.conj n).toMonoidHom = F := by
    rcases map_conj_left_eq_left_or_right hDT hFT hDF hn with h | h
    · exact absurd (Subgroup.map_injective (MulAut.conj n).injective (hswap.trans h.symm))
        (fun h' => hDFne h'.symm)
    · exact h
  have hTnorm : (T : Subgroup K) ≤ normalizer (F : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFT).1 hDF.normal_right
  have hpowmem : n ^ (T.subgroupOf (normalizer (T : Set K))).index ∈ (T : Subgroup K) :=
    pow_index_mem_normalizer hn
  have hpowF : F.map (MulAut.conj (n ^ (T.subgroupOf (normalizer (T : Set K))).index)).toMonoidHom
      = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm hpowmem)
  obtain ⟨k, hk⟩ := odd_index_normalizer (T := T)
  rw [hk] at hpowF
  exact hDFne ((map_conj_pow_odd_of_swap hswap hback k).symm.trans hpowF)

private lemma false_of_map_conj_eq_left {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hNF : normalizer (T : Set K) ≤ normalizer (F : Set K)) {g : K}
    (hFg : F.map (MulAut.conj g).toMonoidHom = D) : False := by
  have hTND : (T : Subgroup K) ≤ normalizer (D : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDT).1 hDF.normal_left
  have hTNF : (T : Subgroup K) ≤ normalizer (F : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFT).1 hDF.normal_right
  have hDginv : D.map (MulAut.conj g⁻¹).toMonoidHom = F := by
    have h1 : (F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = F := by
      rw [Subgroup.map_conj_map_conj F g g⁻¹, inv_mul_cancel, map_one]
      exact Subgroup.map_id F
    rw [← hFg]
    exact h1
  have hQg : T.map (MulAut.conj g).toMonoidHom ≤ normalizer (D : Set K) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    calc D.map (MulAut.conj (g * t * g⁻¹)).toMonoidHom
        = (D.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (g * t)).toMonoidHom := by
          rw [show g * t * g⁻¹ = (g * t) * g⁻¹ from by group, ← Subgroup.map_conj_map_conj]
      _ = F.map (MulAut.conj (g * t)).toMonoidHom := by rw [hDginv]
      _ = (F.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [← Subgroup.map_conj_map_conj]
      _ = F.map (MulAut.conj g).toMonoidHom := by
          exact congrArg (fun H => H.map (MulAut.conj g).toMonoidHom)
            (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTNF ht))
      _ = D := hFg
  let Q : Sylow 2 K := g • T
  have hQcoe : (Q : Subgroup K) = T.map (MulAut.conj g).toMonoidHom :=
    Sylow.coe_subgroup_smul
  have hQND : (Q : Subgroup K) ≤ normalizer (D : Set K) := by
    rw [hQcoe]
    exact hQg
  obtain ⟨n, hn⟩ :=
    MulAction.exists_smul_eq ↥(normalizer (D : Set K)) (T.subtype hTND) (Q.subtype hQND)
  rw [Sylow.smul_subtype] at hn
  have hSylow : (n : K) • T = Q := Sylow.subtype_injective hn
  have hmap : (T : Subgroup K).map (MulAut.conj (n : K)).toMonoidHom =
      (T : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 K => (P : Subgroup K)) hSylow
    rw [hQcoe, Sylow.coe_subgroup_smul] at h1
    exact h1
  have hng : ((n : K)⁻¹ * g) ∈ normalizer (T : Set K) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    calc T.map (MulAut.conj ((n : K)⁻¹ * g)).toMonoidHom
        = (T.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj ((n : K)⁻¹)).toMonoidHom := by
          rw [← Subgroup.map_conj_map_conj]
      _ = (T.map (MulAut.conj (n : K)).toMonoidHom).map
            (MulAut.conj ((n : K)⁻¹)).toMonoidHom := by rw [hmap]
      _ = T := by
          rw [Subgroup.map_conj_map_conj T (n : K) (n : K)⁻¹, inv_mul_cancel, map_one]
          exact Subgroup.map_id (T : Subgroup K)
  have hDn : D.map (MulAut.conj (n : K)).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp n.2
  have hconjFD : F.map (MulAut.conj ((n : K)⁻¹ * g)).toMonoidHom = D := by
    rw [← Subgroup.map_conj_map_conj, hFg]
    exact map_conj_inv_eq_self hDn
  have hFN : F.map (MulAut.conj ((n : K)⁻¹ * g)).toMonoidHom = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNF hng)
  have hDFne : D ≠ F := fun h' => hDF.ne (by rw [h'])
  exact hDFne (hconjFD.symm.trans hFN)

private lemma map_conj_eq_self_of_le {T : Sylow 2 K} {D F : Subgroup K} (hDT : D ≤ T)
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hNF : normalizer (T : Set K) ≤ normalizer (F : Set K)) {g : K}
    (hg : F.map (MulAut.conj g).toMonoidHom ≤ T) :
    F.map (MulAut.conj g).toMonoidHom = F := by
  have hcardF : Nat.card F = 16 := by
    rw [← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hEcard : Nat.card ((F.map (MulAut.conj g).toMonoidHom).subgroupOf T) = 16 := by
    rw [card_subgroupOf_of_le hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcardF]
  have hEsq : ∀ x ∈ (F.map (MulAut.conj g).toMonoidHom).subgroupOf T, x * x = 1 := by
    intro x hx
    obtain ⟨d, hd, hd'⟩ := hx
    have hxd : (x : K) = MulAut.conj g d := hd'.symm
    have hval : (x : K) * (x : K) = 1 := by
      rw [hxd, ← map_mul, sq_eq_one_of_mem_right hFT hDF hd, map_one]
    exact Subtype.ext hval
  rcases hDF.eq_or ((F.map (MulAut.conj g).toMonoidHom).subgroupOf T) hEsq hEcard with h | h
  · exfalso
    exact false_of_map_conj_eq_left hDT hFT hDF hNF (eq_of_subgroupOf_eq hg hDT h)
  · exact eq_of_subgroupOf_eq hg hFT h

private lemma exists_conj_mem_normalizer_right {T : Sylow 2 K} {D F : Subgroup K}
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hinv : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hweak : ∀ g : K, F.map (MulAut.conj g).toMonoidHom ≤ T →
      F.map (MulAut.conj g).toMonoidHom = F)
    {x y : K} (hxF : x ∈ F) (hyF : y ∈ F) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ k ∈ normalizer (F : Set K), k * x * k⁻¹ = y := by
  have hx2 : orderOf x = 2 := by
    rw [orderOf_eq_two_iff_sq]
    exact ⟨sq_eq_one_of_mem_right hFT hDF hxF, hx1⟩
  have hy2 : orderOf y = 2 := by
    rw [orderOf_eq_two_iff_sq]
    exact ⟨sq_eq_one_of_mem_right hFT hDF hyF, hy1⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (hinv x y hx2 hy2)
  let C : Subgroup K := Subgroup.centralizer ({y} : Set K)
  have hCcard : Nat.card C = 64 := hcent y hy2
  have hC2 : IsPGroup 2 C := IsPGroup.of_card (n := 6) (by rw [hCcard]; norm_num)
  have hFC : F ≤ C := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_right hFT hDF hf hyF
  have hFgC : F.map (MulAut.conj g).toMonoidHom ≤ C := by
    intro z hz
    obtain ⟨f, hf, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfx : f * x = x * f := comm_of_mem_right hFT hDF hf hxF
    change (g * f * g⁻¹) * y = y * (g * f * g⁻¹)
    rw [← hg]
    calc (g * f * g⁻¹) * (g * x * g⁻¹) = g * (f * x) * g⁻¹ := by group
      _ = g * (x * f) * g⁻¹ := by rw [hfx]
      _ = (g * x * g⁻¹) * (g * f * g⁻¹) := by group
  obtain ⟨Q, hQ⟩ := hC2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq K Q T
  have hQmap : (Q : Subgroup K).map (MulAut.conj h).toMonoidHom = (T : Subgroup K) := by
    have h1 := congrArg (fun P : Sylow 2 K => (P : Subgroup K)) hh
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hFQ : F ≤ Q := hFC.trans hQ
  have hFgQ : F.map (MulAut.conj g).toMonoidHom ≤ Q := hFgC.trans hQ
  have hFhT : F.map (MulAut.conj h).toMonoidHom ≤ T :=
    (Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hFQ).trans hQmap.le
  have hFhgT : F.map (MulAut.conj (h * g)).toMonoidHom ≤ T := by
    have hmono := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hFgQ
    rw [Subgroup.map_conj_map_conj F g h] at hmono
    exact hmono.trans hQmap.le
  have hFh_eq : F.map (MulAut.conj h).toMonoidHom = F := hweak h hFhT
  have hFhg_eq : F.map (MulAut.conj (h * g)).toMonoidHom = F := hweak (h * g) hFhgT
  have hFg_eq : F.map (MulAut.conj g).toMonoidHom = F := by
    have h1 : (F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
        F.map (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.map_conj_map_conj F g h]
      exact hFhg_eq.trans hFh_eq.symm
    exact Subgroup.map_injective (MulAut.conj h).injective h1
  exact ⟨g, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hFg_eq, hg⟩

private lemma centralizer_le_normalizer_right {T : Sylow 2 K} {D F : Subgroup K}
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hweak : ∀ g : K, F.map (MulAut.conj g).toMonoidHom ≤ T →
      F.map (MulAut.conj g).toMonoidHom = F)
    {x : K} (hxF : x ∈ F) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set K) ≤ normalizer (F : Set K) := by
  have hx2 : orderOf x = 2 := by
    rw [orderOf_eq_two_iff_sq]
    exact ⟨sq_eq_one_of_mem_right hFT hDF hxF, hx1⟩
  let C : Subgroup K := Subgroup.centralizer ({x} : Set K)
  have hCcard : Nat.card C = 64 := hcent x hx2
  have hC2 : IsPGroup 2 C := IsPGroup.of_card (n := 6) (by rw [hCcard]; norm_num)
  have hFC : F ≤ C := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_right hFT hDF hf hxF
  obtain ⟨Q, hQ⟩ := hC2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq K Q T
  have hQmap : (Q : Subgroup K).map (MulAut.conj h).toMonoidHom = (T : Subgroup K) := by
    have h1 := congrArg (fun P : Sylow 2 K => (P : Subgroup K)) hh
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hFhT : F.map (MulAut.conj h).toMonoidHom ≤ T :=
    (Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) (hFC.trans hQ)).trans hQmap.le
  have hFh_eq : F.map (MulAut.conj h).toMonoidHom = F := hweak h hFhT
  intro c hc
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hFcC : F.map (MulAut.conj c).toMonoidHom ≤ C := by
    intro z hz
    obtain ⟨f, hf, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfx : f * x = x * f := comm_of_mem_right hFT hDF hf hxF
    have hcx : c * x = x * c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      exact hc
    change c * f * c⁻¹ * x = x * (c * f * c⁻¹)
    have hcx' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [← hcx]
        _ = x * c⁻¹ := by group
    calc c * f * c⁻¹ * x = (c * f) * (c⁻¹ * x) := by group
      _ = (c * f) * (x * c⁻¹) := by rw [hcx']
      _ = c * (f * x) * c⁻¹ := by group
      _ = c * (x * f) * c⁻¹ := by rw [hfx]
      _ = (c * x) * f * c⁻¹ := by group
      _ = (x * c) * f * c⁻¹ := by rw [hcx]
      _ = x * (c * f * c⁻¹) := by group
  have hFcQ : F.map (MulAut.conj c).toMonoidHom ≤ Q := hFcC.trans hQ
  have hFchT : F.map (MulAut.conj (h * c)).toMonoidHom ≤ T := by
    have hmono := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hFcQ
    rw [Subgroup.map_conj_map_conj F c h] at hmono
    exact hmono.trans hQmap.le
  have hFch_eq : F.map (MulAut.conj (h * c)).toMonoidHom = F := hweak (h * c) hFchT
  have h1 : (F.map (MulAut.conj c).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      F.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_conj_map_conj F c h]
    exact hFch_eq.trans hFh_eq.symm
  exact Subgroup.map_injective (MulAut.conj h).injective h1

private lemma card_normalizer_right {T : Sylow 2 K} {D F : Subgroup K} (hFT : F ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hweak : ∀ g : K, F.map (MulAut.conj g).toMonoidHom ≤ T →
      F.map (MulAut.conj g).toMonoidHom = F)
    (htrans : ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (F : Set K), k * x * k⁻¹ = y) :
    Nat.card ↥(normalizer (F : Set K)) = 960 := by
  classical
  have hNF : NormalizesSet (normalizer (F : Set K)) (F : Set K) :=
    ⟨fun a ha x hx => by
      have hmap : F.map (MulAut.conj a).toMonoidHom = F :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
      have hx' : MulAut.conj a x ∈ F.map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hx
      rwa [hmap] at hx'⟩
  let _ : NormalizesSet (normalizer (F : Set K)) (F : Set K) := hNF
  have hFcard : Nat.card ↥F = 16 := by
    rw [← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨x', hx'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have hxF : (x' : K) ∈ F := x'.2
  have hx1 : (x' : K) ≠ 1 := fun h => hx'1 (Subtype.ext h)
  have hx2 : orderOf (x' : K) = 2 := by
    rw [orderOf_eq_two_iff_sq]
    exact ⟨sq_eq_one_of_mem_right hFT hDF hxF, hx1⟩
  let C : Subgroup K := Subgroup.centralizer ({(x' : K)} : Set K)
  have hCcard : Nat.card C = 64 := hcent (x' : K) hx2
  have hCN : C ≤ normalizer (F : Set K) :=
    centralizer_le_normalizer_right hFT hDF hcent hweak hxF hx1
  have hstab : MulAction.stabilizer ↥(normalizer (F : Set K)) x' = C.subgroupOf
      (normalizer (F : Set K)) := stabilizer_normalizesSet x'
  have hstabCard : Nat.card (MulAction.stabilizer ↥(normalizer (F : Set K)) x') = 64 := by
    rw [hstab, card_subgroupOf_of_le hCN]
    exact hCcard
  have horb : (MulAction.orbit ↥(normalizer (F : Set K)) x' : Set ↥F) = {y : ↥F | y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      intro hy
      have hval : (n : K) * (x' : K) * (n : K)⁻¹ = 1 := by
        rw [← conjMulActionOfNormalizesSet_smul_coe]
        simpa using congrArg Subtype.val hy
      apply hx1
      calc (x' : K) = (n : K)⁻¹ * ((n : K) * (x' : K) * (n : K)⁻¹) * (n : K) := by group
        _ = 1 := by rw [hval]; simp
    · intro hy
      have hy' : (y.1 : K) ≠ 1 := fun h => hy (Subtype.ext h)
      obtain ⟨k, hk, hky⟩ := htrans (x' : K) hxF (y.1 : K) y.2 hx1 hy'
      exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have horbCard : (MulAction.orbit ↥(normalizer (F : Set K)) x').ncard = 15 := by
    have hcard : ({y : ↥F | y ≠ 1} : Set ↥F).ncard = 15 := by
      let : Fintype ↥F := Fintype.ofFinite _
      rw [← Set.fintypeCard_eq_ncard, Set.card_ne_eq]
      rw [Nat.card_eq_fintype_card] at hFcard
      omega
    calc (MulAction.orbit ↥(normalizer (F : Set K)) x').ncard
        = ({y : ↥F | y ≠ 1} : Set ↥F).ncard := congrArg Set.ncard horb
      _ = 15 := hcard
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(normalizer (F : Set K)) x')
  rw [MulAction.index_stabilizer, hstabCard, horbCard] at hmul
  omega

omit [Finite K] in
private lemma card_normalizer_T {T : Sylow 2 K} (hT : IsT ↥T) {D F : Subgroup K} (hDT : D ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hND : normalizer (T : Set K) ≤ normalizer (D : Set K))
    (hπ : ∃ π : ↥(normalizer (D : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf (normalizer (D : Set K))) :
    Nat.card ↥(normalizer (T : Set K)) = 192 := by
  classical
  obtain ⟨π, hπsurj, hπker⟩ := hπ
  let ND : Subgroup K := normalizer (D : Set K)
  have hTND : (T : Subgroup K) ≤ ND := le_trans le_normalizer hND
  have hDND : D ≤ ND := hDT.trans hTND
  let TD : Subgroup ↥ND := (T : Subgroup K).subgroupOf ND
  let DD : Subgroup ↥ND := D.subgroupOf ND
  have hTDcard : Nat.card TD = 64 := by
    rw [show Nat.card TD = Nat.card (T : Subgroup K) from card_subgroupOf_of_le hTND]
    exact hT.card_eq
  have hDcard : Nat.card DD = 16 := by
    rw [show Nat.card DD = Nat.card D from card_subgroupOf_of_le hDND,
      ← card_subgroupOf_of_le hDT]
    exact hDF.card_left
  have hDDTD : DD ≤ TD := Subgroup.subgroupOf_mono ND hDT
  let U : Subgroup (alternatingGroup (Fin 5)) := TD.map π
  have hUcard : Nat.card U = 4 := by
    have h := CFSG.EvenSporadicStandard.M24Std.CResH4.natCard_map_mul_natCard_inf_ker π TD
    have hinf : TD ⊓ π.ker = DD := by
      rw [hπker]
      exact inf_eq_right.mpr hDDTD
    rw [hinf, hTDcard, hDcard] at h
    change Nat.card U * 16 = 64 at h
    omega
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  have hA5card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hUindex : U.index = 15 := by
    rw [Subgroup.index_eq_card_div, hA5card, hUcard]
  have hUnotdvd : ¬ 2 ∣ U.index := by
    rw [hUindex]
    norm_num
  let P : Sylow 2 (alternatingGroup (Fin 5)) := hU2.toSylow hUnotdvd
  have hPcoe : (P : Subgroup (alternatingGroup (Fin 5))) = U :=
    IsPGroup.toSylow_coe hU2 hUnotdvd
  have hnormUcard : Nat.card ↥(Subgroup.normalizer (U : Set (alternatingGroup (Fin 5)))) = 12 := by
    rw [← hPcoe]
    exact CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two P
  have hrange : U ≤ π.range := by
    rw [MonoidHom.range_eq_top.mpr hπsurj]
    exact le_top
  have hUcomap : U.comap π = TD := by
    rw [show U = TD.map π from rfl]
    exact Subgroup.comap_map_eq_self (hπker.le.trans hDDTD)
  have hnorm : Subgroup.normalizer TD = (Subgroup.normalizer U).comap π := by
    rw [← hUcomap, ← Subgroup.comap_normalizer_eq_of_le_range (f := π) hrange]
  have hnormT : (Subgroup.normalizer (T : Set K)).subgroupOf ND = Subgroup.normalizer TD :=
    Subgroup.subgroupOf_normalizer_eq hTND
  have hkercard : Nat.card ↥π.ker = 16 := by
    rw [hπker]
    exact hDcard
  have hNND : Subgroup.normalizer (T : Set K) ≤ ND := hND
  have step1 : Nat.card ↥(normalizer (T : Set K)) =
      Nat.card ↥((Subgroup.normalizer (T : Set K)).subgroupOf ND) :=
    (card_subgroupOf_of_le hNND).symm
  have step2 : Nat.card ↥((Subgroup.normalizer (T : Set K)).subgroupOf ND) =
      Nat.card ↥(Subgroup.normalizer (TD : Set ↥ND)) := by
    rw [hnormT]
  have step3 : Nat.card ↥(Subgroup.normalizer (TD : Set ↥ND)) =
      Nat.card ↥((Subgroup.normalizer (U : Set (alternatingGroup (Fin 5)))).comap π) := by
    rw [hnorm]
  have step4 : Nat.card ↥((Subgroup.normalizer (U : Set (alternatingGroup (Fin 5)))).comap π) =
      Nat.card ↥π.ker * Nat.card ↥(Subgroup.normalizer (U : Set (alternatingGroup (Fin 5)))) :=
    (CFSG.EvenSporadicStandard.M24Std.CResH4.natCard_comap_eq π _
      fun x _ => MonoidHom.mem_range.mpr (hπsurj x)).trans (mul_comm _ _)
  have step5 : Nat.card ↥π.ker *
      Nat.card ↥(Subgroup.normalizer (U : Set (alternatingGroup (Fin 5)))) = 192 := by
    rw [hkercard, hnormUcard]
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

private lemma card_sylow_normalizer_right {T : Sylow 2 K} {F : Subgroup K}
    (hNT : normalizer (T : Set K) ≤ normalizer (F : Set K))
    (hN : Nat.card ↥(normalizer (F : Set K)) = 960)
    (hNTcard : Nat.card ↥(normalizer (T : Set K)) = 192) :
    Nat.card (Sylow 2 ↥(normalizer (F : Set K))) = 5 := by
  classical
  let N := normalizer (F : Set K)
  have hTN : (T : Subgroup K) ≤ N := le_normalizer.trans hNT
  let TN : Subgroup ↥N := (T : Subgroup K).subgroupOf N
  have hnormTN : Subgroup.normalizer (TN : Set ↥N) =
      (Subgroup.normalizer (T : Set K)).subgroupOf N :=
    (Subgroup.subgroupOf_normalizer_eq hTN).symm
  have hnormTNcard : Nat.card ↥(Subgroup.normalizer (TN : Set ↥N)) = 192 := by
    rw [hnormTN, card_subgroupOf_of_le hNT, hNTcard]
  have hindex : (Subgroup.normalizer (TN : Set ↥N)).index = 5 := by
    rw [Subgroup.index_eq_card_div, hN, hnormTNcard]
  have hPcoe : ((T.subtype hTN : Sylow 2 ↥N) : Subgroup ↥N) = TN :=
    Sylow.coe_subtype (P := T) (N := N) hTN
  calc Nat.card (Sylow 2 ↥N)
      = (Subgroup.normalizer (TN : Set ↥N)).index := by
        rw [← hPcoe]
        exact Sylow.card_eq_index_normalizer (T.subtype hTN)
    _ = 5 := hindex

omit [Finite K] in
private lemma subgroupOf_le_toPermHom_ker {T : Sylow 2 K} {D F : Subgroup K} (hFT : F ≤ T)
    (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T)) :
    F.subgroupOf (normalizer (F : Set K)) ≤
      (MulAction.toPermHom ↥(normalizer (F : Set K))
        (Sylow 2 ↥(normalizer (F : Set K)))).ker := by
  intro f hf
  rw [MonoidHom.mem_ker]
  have hFcard : Nat.card ↥(F.subgroupOf (normalizer (F : Set K))) = 16 := by
    rw [card_subgroupOf_of_le (le_normalizer : F ≤ normalizer (F : Set K)),
      ← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hF2 : IsPGroup 2 ↥(F.subgroupOf (normalizer (F : Set K))) :=
    IsPGroup.of_card (n := 4) (by rw [hFcard]; norm_num)
  have hFnormal : (F.subgroupOf (normalizer (F : Set K))).Normal :=
    Subgroup.normal_in_normalizer
  refine Equiv.Perm.ext fun Q => ?_
  show f • Q = Q
  exact Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer (IsPGroup.le_sylow_of_normal hF2 Q hf))

omit [Finite K] in
private lemma toPermHom_ker_le_normalizer_T {T : Sylow 2 K} {F : Subgroup K}
    (hNT : normalizer (T : Set K) ≤ normalizer (F : Set K)) :
    (MulAction.toPermHom ↥(normalizer (F : Set K))
      (Sylow 2 ↥(normalizer (F : Set K)))).ker ≤
      (Subgroup.normalizer (T : Set K)).subgroupOf (normalizer (F : Set K)) := by
  intro r hr
  let N := normalizer (F : Set K)
  have hTN : (T : Subgroup K) ≤ N := le_normalizer.trans hNT
  have hfix : (r : ↥N) • (T.subtype hTN : Sylow 2 ↥N) = T.subtype hTN := by
    have h1 := MonoidHom.mem_ker.mp hr
    have h2 := congrArg (fun σ : Equiv.Perm (Sylow 2 ↥N) => σ (T.subtype hTN)) h1
    simpa using h2
  have hmem : (r : ↥N) ∈
      Subgroup.normalizer ((T.subtype hTN : Sylow 2 ↥N) : Set ↥N) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hfix
  have hnorm : Subgroup.normalizer ((T.subtype hTN : Sylow 2 ↥N) : Set ↥N) =
      (Subgroup.normalizer (T : Set K)).subgroupOf N := by
    change Subgroup.normalizer ((T.subgroupOf N : Subgroup ↥N) : Set ↥N) =
      (Subgroup.normalizer (T : Set K)).subgroupOf N
    exact (Subgroup.subgroupOf_normalizer_eq hTN).symm
  rw [hnorm, Subgroup.mem_subgroupOf] at hmem
  exact hmem

private lemma card_ker_eq_mul_card_inf {T : Sylow 2 K} {N : Subgroup K}
    {R : Subgroup ↥N} (hTN : (T : Subgroup K) ≤ N)
    (hNT : Subgroup.normalizer (T : Set K) ≤ N)
    (hTcard : Nat.card ↥T = 64)
    (hNTcard : Nat.card ↥(Subgroup.normalizer (T : Set K)) = 192)
    (hR : R ≤ (Subgroup.normalizer (T : Set K)).subgroupOf N) :
    ∃ k : ℕ, k ∣ 3 ∧ Nat.card ↥R = Nat.card ↥(R ⊓ (T.subgroupOf N)) * k := by
  classical
  let P : Subgroup ↥N := T.subgroupOf N
  let L : Subgroup ↥N := Subgroup.normalizer (P : Set ↥N)
  have hL : L = (Subgroup.normalizer (T : Set K)).subgroupOf N :=
    (Subgroup.subgroupOf_normalizer_eq hTN).symm
  have hRL : R ≤ L := hR.trans hL.ge
  have hLcard : Nat.card ↥L = 192 := by
    rw [hL, card_subgroupOf_of_le hNT, hNTcard]
  have hPcard : Nat.card ↥P = 64 := by
    rw [show Nat.card ↥P = Nat.card ↥(T : Subgroup K) from card_subgroupOf_of_le hTN]
    exact hTcard
  have hPnorm : (P.subgroupOf L).Normal := Subgroup.normal_in_normalizer
  have hidx : (P.subgroupOf L).index = 3 := by
    rw [Subgroup.index_eq_card_div, hLcard, card_subgroupOf_of_le le_normalizer, hPcard]
  have hdvd : (P.subgroupOf L).relIndex (R.subgroupOf L) ∣ 3 := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal (H := P.subgroupOf L) (K := R.subgroupOf L)
  have hrel : (P.subgroupOf L).relIndex (R.subgroupOf L) = P.relIndex R :=
    Subgroup.relIndex_subgroupOf hRL
  rw [hrel] at hdvd
  have hmul := Subgroup.relIndex_mul_card (H := P) (K := R)
  refine ⟨P.relIndex R, hdvd, ?_⟩
  have hmul' : Nat.card ↥R = Nat.card ↥(R ⊓ P) * P.relIndex R := by
    rw [inf_comm, mul_comm]
    exact hmul.symm
  exact hmul'


@[instance_reducible]
private def conjActionOfNorm {G : Type*} [Group G] {P : Subgroup G} {τ : G}
    (hzp : Subgroup.zpowers τ ≤ Subgroup.normalizer (P : Set G)) :
    MulAction ↥(Subgroup.zpowers τ) ↥P where
  smul g x :=
    ⟨(g : G) * (x : G) * (g : G)⁻¹, by
      have hg : (g : G) ∈ Subgroup.normalizer (P : Set G) := hzp g.2
      exact (Subgroup.mem_set_normalizer_iff.mp hg (x : G)).mp x.2⟩
  one_smul x := by
    apply Subtype.ext
    show ((1 : ↥(Subgroup.zpowers τ)) : G) * (x : G) * (((1 : ↥(Subgroup.zpowers τ)) : G))⁻¹ =
      (x : G)
    simp
  mul_smul a b x := by
    apply Subtype.ext
    show ((a * b : ↥(Subgroup.zpowers τ)) : G) * (x : G) *
      (((a * b : ↥(Subgroup.zpowers τ)) : G))⁻¹ =
      ((a : ↥(Subgroup.zpowers τ)) : G) * (((b : ↥(Subgroup.zpowers τ)) : G) * (x : G) *
        (((b : ↥(Subgroup.zpowers τ)) : G))⁻¹) * (((a : ↥(Subgroup.zpowers τ)) : G))⁻¹
    rw [Subgroup.coe_mul]
    group

private lemma exists_fixed_ne_one_of_three {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} {τ : G} (hτ3 : orderOf τ = 3)
    (hτP : ∀ x ∈ P, τ * x * τ⁻¹ ∈ P) (hPcard : Nat.card ↥P % 3 = 2) :
    ∃ x ∈ P, x ≠ 1 ∧ τ * x * τ⁻¹ = x := by
  classical
  have hτ3' : τ ^ 3 = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ3] at this
  have hτmap : P.map (MulAut.conj τ).toMonoidHom = P := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hτP x hx
    · intro x hx
      have h2 : τ * (τ * x * τ⁻¹) * τ⁻¹ ∈ P := hτP _ (hτP x hx)
      have h5 : τ⁻¹ = τ ^ 2 :=
        inv_eq_of_mul_eq_one_right (by rw [show τ * τ ^ 2 = τ ^ 3 by group, hτ3'])
      have h6 : τ ^ 4 = τ := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hτ3', one_mul]
      have hz : τ⁻¹ * x * τ ∈ P := by
        have h7 : τ⁻¹ * x * τ = τ * (τ * x * τ⁻¹) * τ⁻¹ := by
          rw [h5]
          have hR : τ * (τ * x * τ ^ 2) * τ ^ 2 = τ ^ 2 * x * τ ^ 4 := by
            rw [show τ ^ 4 = τ ^ 2 * τ ^ 2 by
              rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]]
            rw [pow_two]
            group
          rw [hR, h6]
        rw [h7]
        exact h2
      refine ⟨τ⁻¹ * x * τ, hz, ?_⟩
      change τ * (τ⁻¹ * x * τ) * τ⁻¹ = x
      group
  have hzp : Subgroup.zpowers τ ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hτmap)
  let _ : MulAction ↥(Subgroup.zpowers τ) ↥P := conjActionOfNorm hzp
  have h3group : IsPGroup 3 ↥(Subgroup.zpowers τ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hτ3]
    norm_num
  have hmod := h3group.card_modEq_card_fixedPoints (α := ↥P)
  have hfix : ∃ x : ↥P, x ∈ MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥P ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥P : Set ↥P) ⊆ {1} := by
      intro x hx
      exact Set.mem_singleton_iff.mpr (hcon x hx)
    have hmem1 : (1 : ↥P) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥P := by
      rw [MulAction.mem_fixedPoints]
      intro g
      apply Subtype.ext
      show ((g : ↥(Subgroup.zpowers τ)) : G) * ((1 : ↥P) : G) *
        (((g : ↥(Subgroup.zpowers τ)) : G))⁻¹ = ((1 : ↥P) : G)
      simp
    have heq : (MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥P : Set ↥P) = {1} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hmem1, fun x hx => hsub hx⟩
    rw [Nat.card_coe_set_eq, heq, Set.ncard_singleton] at hmod
    have h2 : Nat.card ↥P % 3 = 1 % 3 := hmod
    omega
  obtain ⟨x, hxfix, hxne⟩ := hfix
  refine ⟨(x : P), x.2, fun h => hxne (Subtype.ext h), ?_⟩
  have h1 : (⟨τ, Subgroup.mem_zpowers τ⟩ : ↥(Subgroup.zpowers τ)) • x = x :=
    MulAction.mem_fixedPoints.mp hxfix ⟨τ, Subgroup.mem_zpowers τ⟩
  have h2 := congrArg (fun y : ↥P => (y : G)) h1
  change ((⟨τ, Subgroup.mem_zpowers τ⟩ : ↥(Subgroup.zpowers τ)) : G) * (x : G) *
    (((⟨τ, Subgroup.mem_zpowers τ⟩ : ↥(Subgroup.zpowers τ)) : G))⁻¹ = (x : G) at h2
  simpa using h2

@[instance_reducible]
private def conjActionOnNormal {G : Type*} [Group G] {H : Subgroup G} (hH : H.Normal)
    (A : Subgroup G) : MulAction ↥A ↥H where
  smul a x := ⟨(a : G) * (x : G) * (a : G)⁻¹, hH.conj_mem x x.2 (a : G)⟩
  one_smul x := by
    apply Subtype.ext
    show ((1 : ↥A) : G) * (x : G) * (((1 : ↥A) : G))⁻¹ = (x : G)
    simp
  mul_smul a b x := by
    apply Subtype.ext
    show ((a * b : ↥A) : G) * (x : G) * (((a * b : ↥A) : G))⁻¹ =
      ((a : ↥A) : G) * (((b : ↥A) : G) * (x : G) * (((b : ↥A) : G))⁻¹) *
        (((a : ↥A) : G))⁻¹
    rw [Subgroup.coe_mul]
    group

private lemma ker_eq_of_card_inf_eq_sixteen {T : Sylow 2 K} {F : Subgroup K} {Ng : Subgroup K}
    {R : Subgroup Ng} {j : ℕ} (hT : IsT ↥T)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hRnorm : R.Normal)
    (hTNcard : Nat.card ↥((T : Subgroup K).subgroupOf Ng) = 64)
    (hFcardN : Nat.card ↥(F.subgroupOf Ng) = 16) (hFR : F.subgroupOf Ng ≤ R)
    (hFRTN : F.subgroupOf Ng ≤ R ⊓ (T : Subgroup K).subgroupOf Ng)
    (hRj : Nat.card ↥R = Nat.card ↥(R ⊓ (T : Subgroup K).subgroupOf Ng) * j) (hj3 : j ∣ 3)
    (hPcard : Nat.card ↥(R ⊓ (T : Subgroup K).subgroupOf Ng) = 16) :
    R = F.subgroupOf Ng := by
  classical
  have hPeq : R ⊓ (T : Subgroup K).subgroupOf Ng = F.subgroupOf Ng :=
    (Subgroup.eq_of_le_of_card_ge hFRTN (by rw [hPcard, hFcardN])).symm
  rw [hPeq, hFcardN] at hRj
  have hk13 : j = 1 ∨ j = 3 := (Nat.dvd_prime (by norm_num)).mp hj3
  rcases hk13 with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hFR (by rw [hRj, hFcardN])).symm
  · exfalso
    have hR48 : Nat.card ↥R = 48 := by
      rw [hRj]
    have h3dvd : 3 ∣ Nat.card ↥R := by rw [hR48]; norm_num
    obtain ⟨r, hr3⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 h3dvd
    let _ : MulAction ↥((T : Subgroup K).subgroupOf Ng) ↥R :=
      conjActionOnNormal hRnorm ((T : Subgroup K).subgroupOf Ng)
    have hmul := Subgroup.card_mul_index
      (MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r)
    rw [MulAction.index_stabilizer, hTNcard] at hmul
    have horb_le : Nat.card (MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) ≤ 48 := by
      have h1 : Nat.card (MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) ≤ Nat.card ↥R :=
        Nat.card_le_card_of_injective
          (fun x : ↥(MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) => (x.1 : ↥R))
          (fun a b hab => Subtype.ext hab)
      omega
    have hstab2 : 2 ≤ Nat.card ↥(MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r) := by
      by_contra hle
      push Not at hle
      have hle1 : Nat.card ↥(MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r) ≤ 1 := by
        omega
      have h64 : Nat.card (MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) *
          Nat.card ↥(MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r) = 64 := by
        rw [Nat.card_coe_set_eq, mul_comm]
        exact hmul
      have hle' : Nat.card (MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) *
          Nat.card ↥(MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r) ≤
          Nat.card (MulAction.orbit ↥((T : Subgroup K).subgroupOf Ng) r) * 1 :=
        Nat.mul_le_mul_left _ hle1
      rw [h64, mul_one] at hle'
      omega
    have hne : MulAction.stabilizer ↥((T : Subgroup K).subgroupOf Ng) r ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hstab2
      omega
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hfix : ((t : ↥((T : Subgroup K).subgroupOf Ng)) : ↥Ng) * (r : ↥Ng) *
        ((t : ↥((T : Subgroup K).subgroupOf Ng)) : ↥Ng)⁻¹ = (r : ↥Ng) :=
      congrArg (fun y : ↥R => (y : ↥Ng)) (MulAction.mem_stabilizer_iff.mp t.2)
    have hcomm : ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) * ((r : ↥R) : K) =
        ((r : ↥R) : K) * ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) := by
      have h := congrArg (fun y : ↥Ng => (y : K)) hfix
      calc ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) * ((r : ↥R) : K)
          = (((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) * ((r : ↥R) : K) *
              ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K)⁻¹) *
              ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) := by group
        _ = ((r : ↥R) : K) * ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) := by
          rw [show ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) * ((r : ↥R) : K) *
              ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K)⁻¹ = ((r : ↥R) : K) from h]
    have hrK : orderOf ((r : ↥R) : K) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hr3
    have ht1' : ((t : ↥((T : Subgroup K).subgroupOf Ng)) : K) ≠ 1 := by
      intro h
      exact ht1 (Subtype.ext (Subtype.ext (Subtype.ext h)))
    exact false_of_centralizes_orderOf_three hT hcent
      (t : ↥((T : Subgroup K).subgroupOf Ng)).2 ht1' hrK hcomm

private lemma false_of_card_inf_eq_thirtytwo {T : Sylow 2 K} {F : Subgroup K}
    {Ng : Subgroup K} {R : Subgroup Ng} (hT : IsT ↥T)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hNT : normalizer (T : Set K) ≤ normalizer (F : Set K))
    (hNTcard : Nat.card ↥(Subgroup.normalizer (T : Set K)) = 192)
    (hNg : Ng = normalizer (F : Set K)) (hRnorm : R.Normal)
    (hPcard : Nat.card ↥(R ⊓ (T : Subgroup K).subgroupOf Ng) = 32) : False := by
  classical
  have hPmod : Nat.card ↥(R ⊓ (T : Subgroup K).subgroupOf Ng) % 3 = 2 := by rw [hPcard]
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.normalizer (T : Set K)) := by
    rw [hNTcard]
    norm_num
  obtain ⟨t', ht'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (T : Set K))) 3 h3dvd
  have hτ3 : orderOf (t' : K) = 3 := by rw [Subgroup.orderOf_coe, ht']
  let τN : ↥Ng := ⟨(t' : K), hNg ▸ hNT t'.2⟩
  have hτN3 : orderOf τN = 3 := by
    rw [← Subgroup.orderOf_coe τN]
    exact hτ3
  have hτN_R : ∀ x ∈ R, τN * x * τN⁻¹ ∈ R := fun x hx => hRnorm.conj_mem x hx τN
  have hτN_TN : ∀ x ∈ (T : Subgroup K).subgroupOf Ng, τN * x * τN⁻¹ ∈
      (T : Subgroup K).subgroupOf Ng := by
    intro x hx
    have h1 : ((τN * x * τN⁻¹ : ↥Ng) : K) = (t' : K) * (x : K) * (t' : K)⁻¹ := rfl
    rw [Subgroup.mem_subgroupOf, h1]
    exact (Subgroup.mem_normalizer_iff.mp t'.2 (x : K)).mp hx
  have hτN_P : ∀ x ∈ R ⊓ (T : Subgroup K).subgroupOf Ng,
      τN * x * τN⁻¹ ∈ R ⊓ (T : Subgroup K).subgroupOf Ng :=
    fun x hx => ⟨hτN_R x hx.1, hτN_TN x hx.2⟩
  obtain ⟨x, hxP, hx1, hxfix⟩ := exists_fixed_ne_one_of_three (P := R ⊓
    (T : Subgroup K).subgroupOf Ng) (τ := τN) hτN3 hτN_P hPmod
  have hx1' : (x : K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcomm : (x : K) * (t' : K) = (t' : K) * (x : K) := by
    have hfixK : (t' : K) * (x : K) * (t' : K)⁻¹ = (x : K) := by
      have h := congrArg (fun y : ↥Ng => (y : K)) hxfix
      simpa using h
    have h1 : (t' : K) * (x : K) = (x : K) * (t' : K) := by
      calc (t' : K) * (x : K)
          = ((t' : K) * (x : K) * (t' : K)⁻¹) * (t' : K) := by group
        _ = (x : K) * (t' : K) := by rw [hfixK]
    exact h1.symm
  exact false_of_centralizes_orderOf_three hT hcent hxP.2 hx1' hτ3 hcomm

private lemma false_of_card_inf_eq_sixtyfour {T : Sylow 2 K} {Ng : Subgroup K}
    {R : Subgroup Ng} (hT : IsT ↥T) (hN : Nat.card ↥Ng = 960)
    (hNTcard : Nat.card ↥(Subgroup.normalizer (T : Set K)) = 192)
    (hTN : (T : Subgroup K) ≤ Ng) (hRnorm : R.Normal)
    (hRL : R ≤ (Subgroup.normalizer (T : Set K)).subgroupOf Ng)
    (hPcard : Nat.card ↥(R ⊓ (T : Subgroup K).subgroupOf Ng) = 64) : False := by
  classical
  have hTNcard : Nat.card ↥((T : Subgroup K).subgroupOf Ng) = 64 := by
    rw [card_subgroupOf_of_le hTN]
    exact hT.card_eq
  have hPle : (T : Subgroup K).subgroupOf Ng ≤ R := by
    have hEq : R ⊓ (T : Subgroup K).subgroupOf Ng = (T : Subgroup K).subgroupOf Ng :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hPcard, hTNcard])
    exact hEq ▸ inf_le_left
  have hfr := @Sylow.normalizer_sup_eq_top' ↥Ng _ 2 _ R hRnorm _ (T.subtype hTN) hPle
  have hnormTNP : Subgroup.normalizer ((T.subtype hTN : Sylow 2 ↥Ng) : Set ↥Ng) =
      (Subgroup.normalizer (T : Set K)).subgroupOf Ng :=
    (Subgroup.subgroupOf_normalizer_eq hTN).symm
  have hRle : R ≤ Subgroup.normalizer ((T.subtype hTN : Sylow 2 ↥Ng) : Set ↥Ng) := by
    rw [hnormTNP]
    exact hRL
  rw [sup_eq_left.mpr hRle] at hfr
  have hNle : Ng ≤ Subgroup.normalizer (T : Set K) := by
    rw [hnormTNP, Subgroup.subgroupOf_eq_top] at hfr
    exact hfr
  have hle : Nat.card ↥Ng ≤ Nat.card ↥(Subgroup.normalizer (T : Set K)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hNle)
  rw [hN, hNTcard] at hle
  omega

private lemma toPermHom_ker_eq {T : Sylow 2 K} (hT : IsT ↥T) {D F : Subgroup K}
    (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hNT : normalizer (T : Set K) ≤ normalizer (F : Set K))
    (hN : Nat.card ↥(normalizer (F : Set K)) = 960)
    (hNTcard : Nat.card ↥(normalizer (T : Set K)) = 192) :
    (MulAction.toPermHom ↥(normalizer (F : Set K))
      (Sylow 2 ↥(normalizer (F : Set K)))).ker =
      F.subgroupOf (normalizer (F : Set K)) := by
  classical
  let Ng := normalizer (F : Set K)
  let TN : Subgroup ↥Ng := (T : Subgroup K).subgroupOf Ng
  let R : Subgroup ↥Ng := (MulAction.toPermHom ↥Ng (Sylow 2 ↥Ng)).ker
  change R = F.subgroupOf Ng
  have hTN : (T : Subgroup K) ≤ Ng := le_normalizer.trans hNT
  have hFR : F.subgroupOf Ng ≤ R := subgroupOf_le_toPermHom_ker hFT hDF
  have hRL : R ≤ (Subgroup.normalizer (T : Set K)).subgroupOf Ng :=
    toPermHom_ker_le_normalizer_T hNT
  have hRnorm : R.Normal := MonoidHom.normal_ker _
  have hTNcard : Nat.card ↥TN = 64 := by
    rw [show Nat.card ↥TN = Nat.card ↥(T : Subgroup K) from card_subgroupOf_of_le hTN]
    exact hT.card_eq
  have hFcardN : Nat.card ↥(F.subgroupOf Ng) = 16 := by
    rw [card_subgroupOf_of_le (le_normalizer : F ≤ Ng), ← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hFleTN : F.subgroupOf Ng ≤ TN := Subgroup.subgroupOf_mono Ng hFT
  have hFRTN : F.subgroupOf Ng ≤ R ⊓ TN := le_inf hFR hFleTN
  have hPge : 16 ≤ Nat.card ↥(R ⊓ TN) := by
    have hdvd := Subgroup.card_dvd_of_le hFRTN
    rw [hFcardN] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hPdvd : Nat.card ↥(R ⊓ TN) ∣ 64 := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right : R ⊓ TN ≤ TN)
    rwa [hTNcard] at hdvd
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow (p := 2) (m := 6)
    (i := Nat.card ↥(R ⊓ TN)) Nat.prime_two).mp (by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact hPdvd)
  have hk4 : 4 ≤ k := by
    rw [hk] at hPge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (by simpa using hPge)
  obtain ⟨j, hj3, hRj⟩ := card_ker_eq_mul_card_inf hTN hNT hT.card_eq hNTcard hRL
  have hcase : Nat.card ↥(R ⊓ TN) = 16 ∨ Nat.card ↥(R ⊓ TN) = 32 ∨
      Nat.card ↥(R ⊓ TN) = 64 := by
    have hk456 : k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk456 with rfl | rfl | rfl
    · exact Or.inl (by rw [hk]; norm_num)
    · exact Or.inr (Or.inl (by rw [hk]; norm_num))
    · exact Or.inr (Or.inr (by rw [hk]; norm_num))
  rcases hcase with hcase | hcase | hcase
  · exact ker_eq_of_card_inf_eq_sixteen hT hcent hRnorm hTNcard hFcardN hFR hFRTN hRj hj3 hcase
  · exfalso
    exact false_of_card_inf_eq_thirtytwo hT hcent hNT hNTcard rfl hRnorm hcase
  · exfalso
    exact false_of_card_inf_eq_sixtyfour hT hN hNTcard hTN hRnorm hRL hcase

theorem exists_alt5_of_normalizer_other_e16 (T : Sylow 2 K) (hT : IsT ↥T) {D F : Subgroup K}
    (hDT : D ≤ T) (hFT : F ≤ T) (hDF : IsTwoE16 ↥T (D.subgroupOf T) (F.subgroupOf T))
    (hinv : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hcent : ∀ v : K, orderOf v = 2 → Nat.card (centralizer ({v} : Set K)) = 64)
    (hπ : ∃ π : ↥(normalizer (D : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = D.subgroupOf (normalizer (D : Set K))) :
    (∃ π : ↥(normalizer (F : Set K)) →* alternatingGroup (Fin 5),
      Function.Surjective π ∧ π.ker = F.subgroupOf (normalizer (F : Set K))) ∧
    ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 → ∃ k ∈ normalizer (F : Set K), k * x * k⁻¹ = y := by
  classical
  have hNT : normalizer (T : Set K) ≤ normalizer (F : Set K) :=
    normalizer_T_le_normalizer_right hDT hFT hDF
  have hweak : ∀ g : K, F.map (MulAut.conj g).toMonoidHom ≤ T →
      F.map (MulAut.conj g).toMonoidHom = F :=
    fun g hg => map_conj_eq_self_of_le hDT hFT hDF hNT hg
  have htrans : ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 →
      ∃ k ∈ normalizer (F : Set K), k * x * k⁻¹ = y :=
    fun x hx y hy hx1 hy1 =>
      exists_conj_mem_normalizer_right hFT hDF hinv hcent hweak hx hy hx1 hy1
  have hN : Nat.card ↥(normalizer (F : Set K)) = 960 :=
    card_normalizer_right hFT hDF hcent hweak htrans
  have hNTcard : Nat.card ↥(normalizer (T : Set K)) = 192 :=
    card_normalizer_T hT hDT hDF (normalizer_T_le_normalizer_left hDT hFT hDF) hπ
  have hker : (MulAction.toPermHom ↥(normalizer (F : Set K))
      (Sylow 2 ↥(normalizer (F : Set K)))).ker = F.subgroupOf (normalizer (F : Set K)) :=
    toPermHom_ker_eq hT hFT hDF hcent hNT hN hNTcard
  have hcardSylow : Nat.card (Sylow 2 ↥(normalizer (F : Set K))) = 5 :=
    card_sylow_normalizer_right hNT hN hNTcard
  let Ng := normalizer (F : Set K)
  have hNcard : Nat.card ↥Ng = 960 := hN
  let e : Sylow 2 ↥Ng ≃ Fin 5 := Finite.equivFinOfCardEq hcardSylow
  let φ : ↥Ng →* Equiv.Perm (Sylow 2 ↥Ng) := MulAction.toPermHom ↥Ng (Sylow 2 ↥Ng)
  let ψ : ↥Ng →* Equiv.Perm (Fin 5) := e.permCongrHom.toMonoidHom.comp φ
  have hψker : ψ.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact MulEquiv.map_eq_one_iff e.permCongrHom
  have hFcard : Nat.card ↥(F.subgroupOf Ng) = 16 := by
    rw [card_subgroupOf_of_le (le_normalizer : F ≤ Ng), ← card_subgroupOf_of_le hFT]
    exact hDF.card_right
  have hrangeCard : Nat.card ↥ψ.range = 60 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψker, hker, hFcard, hNcard] at h
    omega
  have hPerm120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hrange : ψ.range = alternatingGroup (Fin 5) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    rw [Subgroup.index_eq_card_div, hrangeCard, hPerm120]
  let π : ↥Ng →* alternatingGroup (Fin 5) :=
    ψ.codRestrict (alternatingGroup (Fin 5)) (fun n => by
      rw [← hrange]
      exact ⟨n, rfl⟩)
  have hπsurj : Function.Surjective π := by
    intro σ
    have hσ : (σ : Equiv.Perm (Fin 5)) ∈ ψ.range := by
      rw [hrange]
      exact σ.2
    obtain ⟨n, hn⟩ := hσ
    exact ⟨n, Subtype.ext hn⟩
  have hπker : π.ker = F.subgroupOf Ng := by
    change (ψ.codRestrict (alternatingGroup (Fin 5)) _).ker = F.subgroupOf Ng
    rw [MonoidHom.ker_codRestrict, hψker, hker]
  exact ⟨⟨π, hπsurj, hπker⟩, htrans⟩

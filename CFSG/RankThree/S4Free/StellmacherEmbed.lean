module

public import CFSG.Quasithin.Background.A1cTransfer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.RankThree.S4Free.Basic

public section

namespace CFSG.RankThree.S4Free

open Subgroup CFSG.Quasithin

theorem normal_pResidual (p : ℕ) (X : Type*) [Group X] : (pResidual p X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [pResidual, mem_iInf] at hn ⊢
  intro N hN hNp
  exact hN.conj_mem n (hn N hN hNp) g

theorem exists_pow_mem_pResidual {X : Type*} [Group X] [Finite X] (p : ℕ) (x : X) :
    ∃ k : ℕ, x ^ p ^ k ∈ pResidual p X := by
  let 𝒩 : Set (Subgroup X) := {N | N.Normal ∧ ∀ x : X, ∃ k : ℕ, x ^ p ^ k ∈ N}
  have hinf : ∀ N₁ ∈ 𝒩, ∀ N₂ ∈ 𝒩, N₁ ⊓ N₂ ∈ 𝒩 := by
    rintro N₁ ⟨h₁, h₁'⟩ N₂ ⟨h₂, h₂'⟩
    refine ⟨Subgroup.normal_inf_normal N₁ N₂, fun x => ?_⟩
    obtain ⟨k₁, hk₁⟩ := h₁' x
    obtain ⟨k₂, hk₂⟩ := h₂' x
    refine ⟨k₁ + k₂, mem_inf.2 ⟨?_, ?_⟩⟩
    · rw [pow_add, pow_mul]
      exact pow_mem hk₁ _
    · rw [pow_add, mul_comm, pow_mul]
      exact pow_mem hk₂ _
  obtain ⟨N₀, hN₀, hmin⟩ := (InvImage.wf (fun N : Subgroup X => Nat.card N)
    Nat.lt_wfRel.wf).has_min 𝒩 ⟨⊤, normal_top, fun x => ⟨0, mem_top _⟩⟩
  have hle : N₀ ≤ pResidual p X := by
    refine le_iInf fun N => le_iInf fun hN => le_iInf fun hNp => ?_
    have hmem := hinf N ⟨hN, hNp⟩ N₀ hN₀
    have hcard : Nat.card N₀ ≤ Nat.card (N ⊓ N₀ : Subgroup X) := not_lt.1 (hmin _ hmem)
    have heq : N ⊓ N₀ = N₀ := eq_of_le_of_card_ge inf_le_right hcard
    rw [← heq]
    exact inf_le_left
  obtain ⟨k, hk⟩ := hN₀.2 x
  exact ⟨k, hle hk⟩

theorem isPGroup_quotient_pResidual {X : Type*} [Group X] [Finite X] (p : ℕ) :
    letI := normal_pResidual p X
    IsPGroup p (X ⧸ pResidual p X) := by
  letI := normal_pResidual p X
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidual p x
  exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

theorem sylow_sup_pResidual_eq_top {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) : (P : Subgroup X) ⊔ pResidual p X = ⊤ := by
  letI := normal_pResidual p X
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (X := X) p).exists_card_eq
  have h1 : ((P : Subgroup X) ⊔ pResidual p X).index ∣ p ^ n := by
    rw [← hn, ← index_eq_card]
    exact index_dvd_of_le le_sup_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
  have h2 : ¬ p ∣ ((P : Subgroup X) ⊔ pResidual p X).index := fun h =>
    P.not_dvd_index (h.trans (index_dvd_of_le le_sup_left))
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact index_eq_one.1 hj
  · exact absurd (hj ▸ dvd_pow_self p (Nat.succ_ne_zero j)) h2

theorem range_sup_pResidual_eq_top {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range) :
    ι.range ⊔ pResidual 2 X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hsyl
  rw [← hP]
  exact sylow_sup_pResidual_eq_top P

theorem range_le_normalizer_map {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X)
    {W : Subgroup S} (hW : W.Normal) : ι.range ≤ normalizer ((W.map ι : Subgroup X) : Set X) := by
  rintro _ ⟨s, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨s * w * s⁻¹, hW.conj_mem w hw s, by simp⟩
  · rintro ⟨w, hw, hx⟩
    refine ⟨s⁻¹ * w * s, by simpa using hW.conj_mem w hw s⁻¹, ?_⟩
    rw [map_mul, map_mul, hx, map_inv]
    group

theorem normal_map_iff_pResidual_le_normalizer {S : Type*} [Group S] {X : Type*} [Group X]
    [Finite X] {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range)
    {W : Subgroup S} (hW : W.Normal) :
    (W.map ι).Normal ↔ pResidual 2 X ≤ normalizer ((W.map ι : Subgroup X) : Set X) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [normalizer_eq_top_iff.2 h]
    exact le_top
  · rw [← normalizer_eq_top_iff, eq_top_iff, ← range_sup_pResidual_eq_top hsyl]
    exact sup_le (range_le_normalizer_map ι hW) h

@[expose] def CondM {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X) : Prop :=
  ∀ N : Subgroup X, N.Normal → ι.range ⊓ N ≤ oTwo X ∨ pResidual 2 X ≤ N

theorem exists_lt_top_of_not_condM {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range) (h : ¬ CondM ι) :
    ∃ K₁ K₂ : Subgroup X, ι.range ≤ K₁ ∧ ι.range ≤ K₂ ∧ K₁ ≠ ⊤ ∧ K₂ ≠ ⊤ ∧ K₁ ⊔ K₂ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hsyl
  simp only [CondM, not_forall, not_or] at h
  obtain ⟨N, hN, hSN, hON⟩ := h
  have hR2 : IsPGroup 2 ι.range := hP ▸ P.isPGroup'
  refine ⟨normalizer ((ι.range ⊓ N : Subgroup X) : Set X), ι.range ⊔ N, ?_, le_sup_left, ?_, ?_,
    ?_⟩
  · intro s hs
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨ι.range.mul_mem (ι.range.mul_mem hs hx1) (ι.range.inv_mem hs),
        hN.conj_mem x hx2 s⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨?_, ?_⟩
      · have := ι.range.mul_mem (ι.range.mul_mem (ι.range.inv_mem hs) hx1) hs
        rwa [show s⁻¹ * (s * x * s⁻¹) * s = x by group] at this
      · have := hN.conj_mem _ hx2 s⁻¹
        rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this
  · intro htop
    apply hSN
    have hn : (ι.range ⊓ N).Normal := normalizer_eq_top_iff.1 htop
    exact CFSG.LocalCores.le_piCore_of_normal hn
      (CFSG.isPiSubgroup_singleton_of_isPGroup (q := ⟨2, Nat.prime_two⟩) (hR2.to_le inf_le_left))
  · intro htop
    apply hON
    refine pResidual_le fun x => ?_
    have hx : x ∈ ((ι.range ⊔ N : Subgroup X) : Set X) := by rw [htop]; trivial
    rw [Subgroup.mul_normal] at hx
    obtain ⟨r, hr, n, hn, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff n).2 hn, mul_one, ← QuotientGroup.mk_pow, hk',
      QuotientGroup.mk_one]
  · obtain ⟨Q, hQ⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal P N
    have hfr := Sylow.normalizer_sup_eq_top (N := N) Q
    rw [hQ, hP] at hfr
    rw [eq_top_iff, ← hfr]
    exact sup_le_sup_left le_sup_right _

theorem exists_sylow_codRestrict {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range) {K : Subgroup X}
    (hK : ι.range ≤ K) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = (ι.codRestrict K fun s => hK ⟨s, rfl⟩).range := by
  obtain ⟨P, hP⟩ := hsyl
  refine ⟨P.subtype (hP.le.trans hK), ?_⟩
  rw [Sylow.coe_subtype, hP]
  exact MonoidHom.subgroupOf_range_eq_of_le ι hK

theorem eq_top_of_forall_condM {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range) (L : Subgroup X)
    (hL : ∀ (K : Subgroup X) (hK : ι.range ≤ K),
      CondM (ι.codRestrict K fun s => hK ⟨s, rfl⟩) → K ≤ L) : L = ⊤ := by
  suffices key : ∀ n : ℕ, ∀ H : Subgroup X, Nat.card H = n → ι.range ≤ H → H ≤ L from
    eq_top_iff.2 (key _ ⊤ rfl le_top)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hH
  by_cases hM : CondM (ι.codRestrict H fun s => hH ⟨s, rfl⟩)
  · exact hL H hH hM
  obtain ⟨K₁, K₂, h₁, h₂, h₁', h₂', htop⟩ :=
    exists_lt_top_of_not_condM (exists_sylow_codRestrict hsyl hH) hM
  have hrange : (ι.codRestrict H fun s => hH ⟨s, rfl⟩).range.map H.subtype = ι.range := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, map_map]
    rfl
  have hstep : ∀ K : Subgroup H, (ι.codRestrict H fun s => hH ⟨s, rfl⟩).range ≤ K → K ≠ ⊤ →
      K.map H.subtype ≤ L := by
    intro K hK hK'
    have hcard : Nat.card (K.map H.subtype) < n := by
      rw [← hn, Nat.card_congr (K.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm]
      exact lt_of_le_of_ne (card_le_card_group K) fun h => hK' ((card_eq_iff_eq_top K).1 h)
    refine ih _ hcard _ rfl ?_
    rw [← hrange]
    exact map_mono hK
  calc H = (⊤ : Subgroup H).map H.subtype := by rw [← MonoidHom.range_eq_map, range_subtype]
    _ = (K₁ ⊔ K₂).map H.subtype := by rw [htop]
    _ = K₁.map H.subtype ⊔ K₂.map H.subtype := map_sup _ _ _
    _ ≤ L := sup_le (hstep K₁ h₁ h₁') (hstep K₂ h₂ h₂')

theorem normal_of_forall_condM {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range) (W : Subgroup S)
    (h : ∀ (K : Subgroup X) (hK : ι.range ≤ K),
      CondM (ι.codRestrict K fun s => hK ⟨s, rfl⟩) →
        K ≤ normalizer ((W.map ι : Subgroup X) : Set X)) : (W.map ι).Normal :=
  normalizer_eq_top_iff.1 (eq_top_of_forall_condM hsyl _ h)

end CFSG.RankThree.S4Free

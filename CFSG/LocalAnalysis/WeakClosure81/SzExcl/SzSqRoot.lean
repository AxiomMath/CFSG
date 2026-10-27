module

public import CFSG.GH74.Uniqueness.Section162Suzuki
public import CFSG.GH74.Uniqueness.Section4Lift
public import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.GH74.Uniqueness CFSG.GH74.Uniqueness.Bender CFSG.RankThree.OddKernel
open Subgroup

theorem exists_mul_self_eq_of_mem_sylow {K : Type*} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 2 1) (Q : Sylow 2 K) {r : K} (hrQ : r ∈ (Q : Subgroup K))
    (hr : r * r = 1) (hr1 : r ≠ 1) :
    ∃ x ∈ (Q : Subgroup K), x * x = r := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRD := h.suzuki_rootData Q
  let r' : ↥Q := ⟨r, hrQ⟩
  have hrne : r' ≠ 1 := fun hh => hr1 (by
    have := congrArg Subtype.val hh
    simpa [r'] using this)
  have hrsq : r' ^ 2 = 1 := by
    apply Subtype.ext
    show r ^ 2 = (1 : K)
    rw [sq, hr]
  have hcard : Nat.card {x : ↥Q // x ^ 2 = r'} = 2 ^ n := hRD.card_sq r' hrne hrsq
  have hne : Nat.card {x : ↥Q // x ^ 2 = r'} ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero _ (by norm_num)
  obtain ⟨⟨x, hxQ⟩, hx⟩ := (Nat.card_ne_zero.mp hne).1
  refine ⟨x, hxQ, ?_⟩
  have := congrArg Subtype.val hx
  simpa [sq, r'] using this

private theorem exists_mul_self_eq_of_benderType_quot {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (hB : BenderType (Y ⧸ pPrimeCore 2 Y) n 2 1)
    (hodd : Odd (Nat.card (pPrimeCore 2 Y))) {s : Y} (hs : s * s = 1)
    (hs1 : (s : Y ⧸ pPrimeCore 2 Y) ≠ 1) :
    ∃ γ : Y, γ * γ = s := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsne : s ≠ 1 := fun h => hs1 (by rw [h, QuotientGroup.mk_one])
  have hs2 : orderOf s = 2 := by
    apply orderOf_eq_prime _ hsne
    rw [sq]
    exact hs
  have hps : IsPGroup 2 (Subgroup.zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs2]
    norm_num
  obtain ⟨T, hT⟩ := hps.exists_le_sylow
  have hsT : s ∈ (T : Subgroup Y) := hT (Subgroup.mem_zpowers s)
  let R : Sylow 2 (Y ⧸ pPrimeCore 2 Y) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' (pPrimeCore 2 Y))
      (QuotientGroup.mk'_surjective (pPrimeCore 2 Y)) T
  have hrR : (s : Y ⧸ pPrimeCore 2 Y) ∈ (R : Subgroup (Y ⧸ pPrimeCore 2 Y)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ hsT
  have hrsq : (s : Y ⧸ pPrimeCore 2 Y) * (s : Y ⧸ pPrimeCore 2 Y) = 1 := by
    have := congrArg (QuotientGroup.mk' (pPrimeCore 2 Y)) hs
    simpa using this
  obtain ⟨x, hxR, hx⟩ := exists_mul_self_eq_of_mem_sylow hB R hrR hrsq hs1
  rw [Sylow.coe_mapSurjective] at hxR
  obtain ⟨γ₀, hγ₀T, hγ₀x⟩ := Subgroup.mem_map.mp hxR
  have hker : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 Y)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hodd
  have hinj := injective_restrict_of_odd (QuotientGroup.mk' (pPrimeCore 2 Y)) hker T.isPGroup'
  have hsq : (⟨γ₀, hγ₀T⟩ : ↥T) ^ 2 = ⟨s, hsT⟩ := by
    apply hinj
    change (QuotientGroup.mk' (pPrimeCore 2 Y)) (γ₀ ^ 2) =
      (QuotientGroup.mk' (pPrimeCore 2 Y)) s
    calc (QuotientGroup.mk' (pPrimeCore 2 Y)) (γ₀ ^ 2)
        = ((QuotientGroup.mk' (pPrimeCore 2 Y)) γ₀) ^ 2 := by rw [map_pow]
      _ = x ^ 2 := by rw [hγ₀x]
      _ = x * x := by rw [sq]
      _ = (QuotientGroup.mk' (pPrimeCore 2 Y)) s := hx
  refine ⟨γ₀, ?_⟩
  have := congrArg Subtype.val hsq
  simpa [sq] using this

private theorem not_three_dvd_card_of_benderType_suzuki {S : Type*} [Group S] [Finite S]
    {n : ℕ} (h : BenderType S n 2 1) :
    ¬ 3 ∣ Nat.card S := by
  obtain ⟨a, -, hn⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨h1, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨h3, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  rw [h.card_eq, hn]
  exact not_three_dvd_sz_card a

private theorem eq_two_one_of_not_three_dvd_card {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e)
    (h3 : ¬ 3 ∣ Nat.card K) : i = 2 ∧ e = 1 := by
  rcases h.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -⟩ | ⟨hi, he, -⟩
  · exfalso
    apply h3
    rw [h.card_eq, hi, he]
    exact three_dvd_linear_card n
  · exact ⟨hi, he⟩
  · exfalso
    apply h3
    rw [h.card_eq, hi, he]
    exact three_dvd_unitary_card n ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))

private theorem exists_sylow_stronglyEmbedded
    {S : Type*} [Group S] [Finite S] {n : ℕ} (h : BenderType S n 2 1)
    {s₁ s₃ : S} (h₁ : s₁ * s₁ = 1) (hs₁2 : orderOf s₁ = 2) (hs₃2 : orderOf s₃ = 2)
    (h₁₃ : s₁ * s₃ ≠ s₃ * s₁) (L : Subgroup S) (hs₁L : s₁ ∈ L) (hs₃L : s₃ ∈ L) :
    ∃ Q : Sylow 2 S, s₁ ∈ (Q : Subgroup S) ∧ s₃ ∉ borel (Q : Subgroup S) ∧
      IsStronglyEmbedded ((borel (Q : Subgroup S) ⊓ L).subgroupOf L) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hps : IsPGroup 2 (Subgroup.zpowers s₁) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs₁2]
    norm_num
  obtain ⟨Q, hQ⟩ := hps.exists_le_sylow
  have hs₁Q : s₁ ∈ (Q : Subgroup S) := hQ (Subgroup.mem_zpowers s₁)
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  have hs₃B : s₃ ∉ borel (Q : Subgroup S) := by
    intro hs₃b
    have hs₃Z : s₃ ∈ rootCenter (Q : Subgroup S) := hc.center_of_involution s₃ hs₃b hs₃2
    exact h₁₃ ((mem_rootCenter_iff.mp hs₃Z).2 s₁ hs₁Q)
  exact ⟨Q, hs₁Q, hs₃B,
    isStronglyEmbedded_subgroupOf hc.strong (le_borel _ hs₁Q) hs₁L hs₁2 hs₃L hs₃B⟩

private theorem two_le_pRank_involutionClosure {S : Type*} [Group S] [Finite S]
    (L : Subgroup S) {s₁ s₂ : S} (hs₁L : s₁ ∈ L) (hs₂L : s₂ ∈ L)
    (hs₁2 : orderOf s₁ = 2) (hs₂2 : orderOf s₂ = 2)
    (h₁₂ : s₁ * s₂ = s₂ * s₁) (h₁₂' : s₂ ≠ s₁) :
    2 ≤ Open.pRank 2 (involutionClosure ↥L) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine two_le_pRank_of_commute_involutions (H := involutionClosure ↥L)
    (a := (⟨s₁, hs₁L⟩ : ↥L)) (b := (⟨s₂, hs₂L⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subgroup.subset_closure (by simpa using hs₁2)
  · exact Subgroup.subset_closure (by simpa using hs₂2)
  · simpa using hs₁2
  · simpa using hs₂2
  · intro hEq
    exact h₁₂' (congrArg Subtype.val hEq).symm
  · exact Subtype.ext h₁₂

private theorem exists_mul_self_eq_of_benderSection
    {S : Type*} [Group S] [Finite S] {n : ℕ} (h : BenderType S n 2 1)
    {s₁ : S} (h₁ : s₁ * s₁ = 1) (hs₁2 : orderOf s₁ = 2) (L : Subgroup S) (hs₁L : s₁ ∈ L)
    (hBender : CFSG.BenderSuzuki.IsBenderGroup
      (↥(involutionClosure ↥L) ⧸ pPrimeCore 2 ↥(involutionClosure ↥L))) :
    ∃ γ ∈ L, γ * γ = s₁ := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xc : Subgroup ↥L := involutionClosure ↥L with hXc
  have hS3 : ¬ 3 ∣ Nat.card S := not_three_dvd_card_of_benderType_suzuki h
  have hdvdS : Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) ∣ Nat.card S :=
    (Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card Xc).trans (Subgroup.card_subgroup_dvd_card L))
  obtain ⟨n', i', e', hS⟩ := isBenderGroup_iff_exists_benderType.mp hBender
  have hdvdK3 : ¬ 3 ∣ Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) := fun h3 => hS3 (h3.trans hdvdS)
  obtain ⟨rfl, rfl⟩ := eq_two_one_of_not_three_dvd_card hS hdvdK3
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥Xc)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2d =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥Xc)) h2d)
  have hS' : BenderType (↥Xc ⧸ pPrimeCore 2 ↥Xc) n' 2 1 := hS
  let s : ↥Xc := ⟨⟨s₁, hs₁L⟩, Subgroup.subset_closure (by simpa using hs₁2)⟩
  have hssq : s * s = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using h₁
  have hsorder : orderOf s = 2 := by
    rw [← Subgroup.orderOf_coe s]
    simpa [s] using hs₁2
  have hs1q : (s : ↥Xc ⧸ pPrimeCore 2 ↥Xc) ≠ 1 := by
    intro h1
    have hord := orderOf_mk_eq_two (pPrimeCore 2 ↥Xc) hodd hsorder
    rw [h1, orderOf_one] at hord
    omega
  obtain ⟨γ₀, hγ₀⟩ := exists_mul_self_eq_of_benderType_quot hS' hodd hssq hs1q
  refine ⟨((γ₀ : ↥Xc) : ↥L), (γ₀ : ↥L).2, ?_⟩
  have := congrArg (fun x : ↥Xc => ((x : ↥L) : S)) hγ₀
  simpa [s] using this

theorem exists_mul_self_eq_of_mem_closure
    {S : Type} [Group S] [Finite S] {n : ℕ}
    (h : BenderType S n 2 1) {s₁ s₂ s₃ : S} (h₁ : s₁ * s₁ = 1) (h₁' : s₁ ≠ 1)
    (h₂ : s₂ * s₂ = 1) (h₂' : s₂ ≠ 1) (h₁₂ : s₁ * s₂ = s₂ * s₁) (h₁₂' : s₂ ≠ s₁)
    (h₃ : s₃ * s₃ = 1) (h₁₃ : s₁ * s₃ ≠ s₃ * s₁) :
    ∃ γ ∈ Subgroup.closure ({s₁, s₂, s₃} : Set S), γ * γ = s₁ := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup S := Subgroup.closure ({s₁, s₂, s₃} : Set S)
  have hs₁L : s₁ ∈ L := Subgroup.subset_closure (by simp [L])
  have hs₂L : s₂ ∈ L := Subgroup.subset_closure (by simp [L])
  have hs₃L : s₃ ∈ L := Subgroup.subset_closure (by simp [L])
  have hs₁2 : orderOf s₁ = 2 := by
    apply orderOf_eq_prime _ h₁'
    rw [sq]
    exact h₁
  have hs₂2 : orderOf s₂ = 2 := by
    apply orderOf_eq_prime _ h₂'
    rw [sq]
    exact h₂
  have hs₃ne : s₃ ≠ 1 := by
    intro h1
    exact h₁₃ (by rw [h1, mul_one, one_mul])
  have hs₃2 : orderOf s₃ = 2 := by
    apply orderOf_eq_prime _ hs₃ne
    rw [sq]
    exact h₃
  obtain ⟨Q, -, -, hMX⟩ :=
    exists_sylow_stronglyEmbedded h h₁ hs₁2 hs₃2 h₁₃ L hs₁L hs₃L
  rcases S_SE_proof ↥L ((borel (Q : Subgroup S) ⊓ L).subgroupOf L) hMX with
    hrank | ⟨hBender, -, -⟩
  · exfalso
    have h2le := two_le_pRank_involutionClosure L hs₁L hs₂L hs₁2 hs₂2 h₁₂ h₁₂'
    omega
  · exact exists_mul_self_eq_of_benderSection h h₁ hs₁2 L hs₁L hBender

end CFSG.LocalAnalysis.WeakClosure81.SzExcl

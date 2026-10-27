module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

private lemma s16kOm8_mem_map_mk'_iff {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Subgroup G) (hN : N ≤ S) (b : G) :
    QuotientGroup.mk' N b ∈ S.map (QuotientGroup.mk' N) ↔ b ∈ S := by
  constructor
  · intro hb
    have hb' : b ∈ Subgroup.comap (QuotientGroup.mk' N) (S.map (QuotientGroup.mk' N)) :=
      Subgroup.mem_comap.mpr hb
    rwa [QuotientGroup.comap_map_mk', sup_eq_right.mpr hN] at hb'
  · intro hb
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hb

private lemma s16kOm8_eq_six_of_two_lt_dvd_six {n : ℕ} (h2 : 2 ∣ n) (h6 : n ∣ 6)
    (h : 2 < n) : n = 6 := by
  obtain ⟨k, rfl⟩ := h2
  have hk : k ∣ 3 := by
    have h6' : 2 * k ∣ 2 * 3 := by
      simpa [show (6 : ℕ) = 2 * 3 by norm_num] using h6
    exact (Nat.mul_dvd_mul_iff_left (show (0 : ℕ) < 2 by norm_num)).mp h6'
  rcases (Nat.dvd_prime Nat.prime_three).mp hk with hk | hk
  · omega
  · omega

theorem s16kOm8_inner_of_stab {Ω : Type} [Group Ω] [Finite Ω]
    (hcard : Nat.card (MulAut Ω) = 6 * Nat.card Ω) (hZ : Subgroup.center Ω = ⊥)
    (S : Subgroup (MulAut Ω)) (hI : inner Ω ≤ S) {ρ t : MulAut Ω} (hρS : ρ ∈ S)
    (hρ2 : ρ * ρ = 1) (htS : t ∉ S) (ht3 : t ^ 3 = 1) (hρt : ρ * t * ρ = t⁻¹)
    {α θ : MulAut Ω} (hα : α ∈ S) (hθ : θ ∉ S) (hαθ : θ * α * θ⁻¹ ∈ S) : α ∈ inner Ω := by
  let I : Subgroup (MulAut Ω) := inner Ω
  let π : MulAut Ω →* Outer Ω := QuotientGroup.mk' I
  let S' : Subgroup (Outer Ω) := S.map π
  let ρ' : Outer Ω := π ρ
  let t' : Outer Ω := π t
  let a' : Outer Ω := π α
  let θ' : Outer Ω := π θ
  haveI : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Ω
  have hNpos : 0 < Nat.card Ω := Nat.card_pos
  have hIcard : Nat.card I = Nat.card Ω := by
    simpa [I] using CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hZ
  have hΓcard : Nat.card (Outer Ω) = 6 := by
    have hq : Nat.card (MulAut Ω) = Nat.card (Outer Ω) * Nat.card Ω := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup I, hIcard]
    have h : 6 * Nat.card Ω = Nat.card (Outer Ω) * Nat.card Ω := by
      rw [← hcard, hq]
    exact Nat.mul_right_cancel hNpos h.symm
  have hρ'S' : ρ' ∈ S' := Subgroup.mem_map_of_mem π hρS
  have ht'S' : t' ∉ S' := by
    intro h
    exact htS ((s16kOm8_mem_map_mk'_iff I S hI t).mp (by simpa [t', S', π] using h))
  have hθ'S' : θ' ∉ S' := by
    intro h
    exact hθ ((s16kOm8_mem_map_mk'_iff I S hI θ).mp (by simpa [θ', S', π] using h))
  have hρ'2 : ρ' * ρ' = 1 := by
    change π ρ * π ρ = 1
    rw [← map_mul, hρ2, map_one]
  have ht'3 : t' ^ 3 = 1 := by
    change π t ^ 3 = 1
    rw [← map_pow, ht3, map_one]
  have hρt' : ρ' * t' * ρ' = t'⁻¹ := by
    change π ρ * π t * π ρ = (π t)⁻¹
    rw [← map_mul, ← map_mul, ← map_inv, hρt]
  have ha'S' : a' ∈ S' := by
    change π α ∈ S.map π
    exact Subgroup.mem_map_of_mem π hα
  have hαθ' : θ' * a' * θ'⁻¹ ∈ S' := by
    change π θ * π α * (π θ)⁻¹ ∈ S.map π
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem π hαθ
  have hρ'ne : ρ' ≠ 1 := by
    intro hρ'one
    have ht'inv : t' = t'⁻¹ := by
      have h := hρt'
      rw [hρ'one, one_mul, mul_one] at h
      exact h
    have ht'2 : t' * t' = 1 := by
      have h := congrArg (fun z => t' * z) ht'inv
      exact h.trans (mul_inv_cancel t')
    have ht'one : t' = 1 := by
      have h3 : t' ^ 3 = t' := by
        calc t' ^ 3 = t' ^ 2 * t' := by rw [pow_succ]
             _ = (t' * t') * t' := by rw [pow_two]
             _ = 1 * t' := by rw [ht'2]
             _ = t' := one_mul t'
      exact h3.symm.trans ht'3
    rw [ht'one] at ht'S'
    exact ht'S' S'.one_mem
  have hρ'order : orderOf ρ' = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using hρ'2) hρ'ne
  have h2dvd : 2 ∣ Nat.card S' := by
    have hle : Subgroup.zpowers ρ' ≤ S' := Subgroup.zpowers_le.mpr hρ'S'
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hρ'order] at hdvd
  have hS'dvd6 : Nat.card S' ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card S'
    rwa [hΓcard] at h
  have hS'ne6 : Nat.card S' ≠ 6 := by
    intro hcard6
    have htop : S' = ⊤ := Subgroup.eq_top_of_card_eq S' (by rw [hcard6, hΓcard])
    rw [htop] at ht'S'
    exact ht'S' (Subgroup.mem_top t')
  have hcard2 : Nat.card S' = 2 := by
    obtain ⟨k, hk⟩ := h2dvd
    have hk3 : k ∣ 3 := by
      rw [hk] at hS'dvd6
      have h6' : 2 * k ∣ 2 * 3 := by
        simpa [show (6 : ℕ) = 2 * 3 by norm_num] using hS'dvd6
      exact (Nat.mul_dvd_mul_iff_left (show (0 : ℕ) < 2 by norm_num)).mp h6'
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with hk1 | hk3'
    · omega
    · exfalso
      apply hS'ne6
      rw [hk, hk3']
  have hS'eq : ∀ {x : Outer Ω}, x ∈ S' → x = 1 ∨ x = ρ' := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨y, hyne, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : S')).mp hcard2
      have hxne : (⟨x, hx⟩ : S') ≠ 1 := fun h => hx1 (Subtype.ext_iff.mp h)
      have hρ'neS : (⟨ρ', hρ'S'⟩ : S') ≠ 1 := fun h => hρ'ne (Subtype.ext_iff.mp h)
      have h1 := hyuniq ⟨x, hx⟩ hxne
      have h2 := hyuniq ⟨ρ', hρ'S'⟩ hρ'neS
      exact Subtype.ext_iff.mp (h1.trans h2.symm)
  have ha'one : a' = 1 := by
    by_contra ha'ne
    rcases hS'eq ha'S' with ha'1 | ha'ρ
    · exact ha'ne ha'1
    · have hθρ'S' : θ' * ρ' * θ'⁻¹ ∈ S' := by
        simpa [ha'ρ] using hαθ'
      have hθρ'ne1 : θ' * ρ' * θ'⁻¹ ≠ 1 := by
        intro h
        have hρ'one : ρ' = 1 := by
          calc ρ' = θ'⁻¹ * (θ' * ρ' * θ'⁻¹) * θ' := by group
               _ = 1 := by rw [h]; group
        exact hρ'ne hρ'one
      have hθρ'eq : θ' * ρ' * θ'⁻¹ = ρ' := by
        rcases hS'eq hθρ'S' with h1 | h2
        · exact absurd h1 hθρ'ne1
        · exact h2
      have hcommρθ : θ' * ρ' = ρ' * θ' := by
        calc θ' * ρ' = (θ' * ρ' * θ'⁻¹) * θ' := by group
             _ = ρ' * θ' := by rw [hθρ'eq]
      let C : Subgroup (Outer Ω) := Subgroup.closure ({ρ', θ'} : Set (Outer Ω))
      have hρ'C : ρ' ∈ C := Subgroup.subset_closure (by simp)
      have hθC : θ' ∈ C := Subgroup.subset_closure (by simp)
      have hS'leC : S' ≤ C := by
        intro x hx
        rcases hS'eq hx with rfl | rfl
        · exact C.one_mem
        · exact hρ'C
      have hnotCleS' : ¬ C ≤ S' := by
        intro hle
        exact hθ'S' (hle hθC)
      have hS'ltC : S' < C := lt_iff_le_not_ge.mpr ⟨hS'leC, hnotCleS'⟩
      have hS'cardltC : Nat.card S' < Nat.card C := Subgroup.card_lt_of_lt hS'ltC
      have hC2dvd : 2 ∣ Nat.card C := by
        have hle : Subgroup.zpowers ρ' ≤ C := Subgroup.zpowers_le.mpr hρ'C
        have hdvd := Subgroup.card_dvd_of_le hle
        rwa [Nat.card_zpowers, hρ'order] at hdvd
      have hCdvd6 : Nat.card C ∣ 6 := by
        have h := Subgroup.card_subgroup_dvd_card C
        rwa [hΓcard] at h
      have hCcard : Nat.card C = 6 :=
        s16kOm8_eq_six_of_two_lt_dvd_six hC2dvd hCdvd6 (by rw [← hcard2]; exact hS'cardltC)
      have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hCcard, hΓcard])
      have hpair : ({ρ', θ'} : Set (Outer Ω)).Pairwise Commute := by
        rw [Set.pairwise_pair]
        intro _
        exact ⟨hcommρθ.symm, hcommρθ⟩
      have hCcomm : IsMulCommutative C := Subgroup.isMulCommutative_closure hpair
      have htopcomm : IsMulCommutative (⊤ : Subgroup (Outer Ω)) := hCtop ▸ hCcomm
      have hΓcomm : IsMulCommutative (Outer Ω) :=
        Function.Surjective.isMulCommutative
          (Subgroup.topEquiv (G := Outer Ω)).surjective htopcomm
      have hcommρt : ρ' * t' = t' * ρ' := hΓcomm.is_comm.comm ρ' t'
      have hρt'2 : ρ' * t' * ρ' = t' := by
        rw [hcommρt, mul_assoc, hρ'2, mul_one]
      have ht'inv : t' = t'⁻¹ := by
        calc t' = ρ' * t' * ρ' := hρt'2.symm
             _ = t'⁻¹ := hρt'
      have ht'2 : t' * t' = 1 := by
        have h := congrArg (fun z => t' * z) ht'inv
        exact h.trans (mul_inv_cancel t')
      have ht'one : t' = 1 := by
        have h3 : t' ^ 3 = t' := by
          calc t' ^ 3 = t' ^ 2 * t' := by rw [pow_succ]
               _ = (t' * t') * t' := by rw [pow_two]
               _ = 1 * t' := by rw [ht'2]
               _ = t' := one_mul t'
        exact h3.symm.trans ht'3
      rw [ht'one] at ht'S'
      exact ht'S' S'.one_mem
  have hπα : (QuotientGroup.mk' I) α = 1 := by
    simpa [a', π] using ha'one
  have hmem : α ∈ I := (QuotientGroup.eq_one_iff (N := I) α).mp (by simpa [π] using hπα)
  simpa [I] using hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

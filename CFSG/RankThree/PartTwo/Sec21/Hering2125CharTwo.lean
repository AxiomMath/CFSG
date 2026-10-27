module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.Open CFSG.LieType.BorelTits

section General

variable {X : Type} [Group X]

theorem normalizer_le_normalizer_centralizer (U : Subgroup X) :
    Subgroup.normalizer (U : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) := by
  have key : ∀ n ∈ Subgroup.normalizer (U : Set X), ∀ m ∈ Subgroup.centralizer (U : Set X),
      n * m * n⁻¹ ∈ Subgroup.centralizer (U : Set X) := by
    intro n hn m hm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : n⁻¹ * u * n ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) u).mp hu
      simpa using this
    have h1 : (n⁻¹ * u * n) * m = m * (n⁻¹ * u * n) := Subgroup.mem_centralizer_iff.mp hm _ hu'
    calc u * (n * m * n⁻¹) = n * ((n⁻¹ * u * n) * m) * n⁻¹ := by group
      _ = n * (m * (n⁻¹ * u * n)) * n⁻¹ := by rw [h1]
      _ = n * m * n⁻¹ * u := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using this

end General

section CharTwo

variable {X : Type} [Group X] [Finite X]

theorem exists_moved_of_charTwo (hX : IsCharTwoType X) {U : Subgroup X} (hU : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) {g : X} (hg : g ∈ Subgroup.centralizer (U : Set X)) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) :
    ∃ x ∈ pCoreOf 2 (Subgroup.centralizer (U : Set X)), g * x * g⁻¹ ≠ x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set M := Subgroup.centralizer (U : Set X) with hM
  set N := Subgroup.normalizer (U : Set X) with hN
  set R := pCoreOf 2 M with hR
  set N' := pCoreOf 2 N with hN'
  have hMN : M ≤ N := Subgroup.centralizer_le_normalizer _
  have hNnormM : N ≤ Subgroup.normalizer (M : Set X) := normalizer_le_normalizer_centralizer U
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  have hN'2 : IsPGroup 2 N' := pCoreOf_isPGroup 2 N
  have hNnormN' : N ≤ Subgroup.normalizer (N' : Set X) := le_normalizer_pCoreOf 2 N
  have hK : N' ⊓ M ≤ R := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hN'2.to_le inf_le_left)
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hNnormN' (hMN hm)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hm) x
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
    rw [h1, h2]
  have hcent : ∀ n ∈ N', g * n * g⁻¹ = n := by
    intro n hn
    have hgN : g ∈ N := hMN hg
    have hnN : n ∈ N := pCoreOf_le 2 N hn
    obtain ⟨o, ho⟩ : ∃ o : X, o = g * n * g⁻¹ * n⁻¹ := ⟨_, rfl⟩
    have hgn' : g * n * g⁻¹ ∈ N' := (Subgroup.mem_normalizer_iff.mp (hNnormN' hgN) n).mp hn
    have hoN' : o ∈ N' := by
      rw [ho]
      exact N'.mul_mem hgn' (N'.inv_mem hn)
    have hoM : o ∈ M := by
      rw [hM, Subgroup.mem_centralizer_iff]
      intro u hu
      have hu1 : n⁻¹ * u * n ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnN) u).mp hu
        simpa using this
      have hgc : g * (n⁻¹ * u * n) = (n⁻¹ * u * n) * g :=
        (Subgroup.mem_centralizer_iff.mp hg _ hu1).symm
      have hgu : u * g = g * u := Subgroup.mem_centralizer_iff.mp hg u hu
      have hgc' : (n⁻¹ * u * n) * g⁻¹ = g⁻¹ * (n⁻¹ * u * n) := by
        calc (n⁻¹ * u * n) * g⁻¹ = g⁻¹ * (g * (n⁻¹ * u * n)) * g⁻¹ := by group
          _ = g⁻¹ * ((n⁻¹ * u * n) * g) * g⁻¹ := by rw [hgc]
          _ = g⁻¹ * (n⁻¹ * u * n) := by group
      calc u * o = u * g * n * g⁻¹ * n⁻¹ := by rw [ho]; group
        _ = g * u * n * g⁻¹ * n⁻¹ := by rw [hgu]
        _ = g * n * (n⁻¹ * u * n) * g⁻¹ * n⁻¹ := by group
        _ = g * n * ((n⁻¹ * u * n) * g⁻¹) * n⁻¹ := by group
        _ = g * n * (g⁻¹ * (n⁻¹ * u * n)) * n⁻¹ := by rw [hgc']
        _ = o * u := by rw [ho]; group
    have hoR : o ∈ R := hK ⟨hoN', hoM⟩
    have hgo : g * o * g⁻¹ = o := hcon o hoR
    have hgn : g * n * g⁻¹ = o * n := by rw [ho]; group
    have hit : ∀ k : ℕ, g ^ k * n * (g ^ k)⁻¹ = o ^ k * n := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc g ^ (k + 1) * n * (g ^ (k + 1))⁻¹ = g * (g ^ k * n * (g ^ k)⁻¹) * g⁻¹ := by group
          _ = g * (o ^ k * n) * g⁻¹ := by rw [ih]
          _ = (g * o * g⁻¹) ^ k * (g * n * g⁻¹) := by
            rw [conj_pow]
            group
          _ = o ^ (k + 1) * n := by rw [hgo, hgn]; group
    have h3 := hit 3
    rw [hg3] at h3
    simp only [inv_one, mul_one, one_mul] at h3
    have ho3 : o ^ 3 = 1 := by
      have : o ^ 3 * n = 1 * n := by rw [one_mul]; exact h3.symm
      exact mul_right_cancel this
    obtain ⟨k, hk⟩ := hR2 ⟨o, hoR⟩
    have hk' : o ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have ho1 : o = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hk', ho3⟩
    rw [ho1] at hgn
    simpa using hgn
  have hgN' : g ∈ N' := by
    refine hX N ⟨U, hU1, hU, rfl⟩ (Subgroup.mem_inf.mpr ⟨hMN hg, ?_⟩)
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    have := hcent n hn
    calc n * g = (g * n * g⁻¹) * g := by rw [this]
      _ = g * n := by group
  obtain ⟨k, hk⟩ := hN'2 ⟨g, hgN'⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact hg1 ((pow_eq_one_iff_of_coprime hcop).mp ⟨hk', hg3⟩)

theorem exists_two_pow_of_mem_center (hX : IsCharTwoType X) {U : Subgroup X} (hU : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) {z : X} (hz : z ∈ Subgroup.center X) : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzN : z ∈ Subgroup.normalizer (U : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hzx : z * x = x * z := (Subgroup.mem_center_iff.mp hz x).symm
    rw [hzx]
    simp
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (U : Set X)) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun n _ => Subgroup.mem_center_iff.mp hz n
  have hz' : z ∈ pCoreOf 2 (Subgroup.normalizer (U : Set X)) :=
    hX _ ⟨U, hU1, hU, rfl⟩ (Subgroup.mem_inf.mpr ⟨hzN, hzC⟩)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Subgroup.normalizer (U : Set X)) ⟨z, hz'⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end CharTwo

end CFSG.RankThree.PartTwo.Sec21.Hering2125

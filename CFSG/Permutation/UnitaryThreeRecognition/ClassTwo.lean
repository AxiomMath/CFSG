module

public import CFSG.Permutation.UnitaryThreeRecognition.ZCentral
public import CFSG.Permutation.UnitaryThreeRecognition.Irreducible

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem commutator_mem_centQ [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hd3 : d ≤ 3)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {x : G} (hx : x ∈ Q) {y : G} (hy : y ∈ Q) : x * y * x⁻¹ * y⁻¹ ∈ centQ Q j := by
  classical
  set Z := centQ Q j with hZdef
  have hZQ : Z ≤ Q := inf_le_left
  have hcen : ∀ u ∈ Q, ∀ z ∈ Z, u * z = z * u := fun u hu z hz =>
    hQ.centQ_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard
      hTcard hsa hs2 hu hz
  have hnorm : ∀ u ∈ Q, ∀ z ∈ Z, u * z * u⁻¹ ∈ Z := fun u hu z hz =>
    hQ.centQ_conj_mem hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard
      hTcard hsa hs2 hu hz
  let C : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z}
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, h₁⟩ ⟨hx₂, h₂⟩
        refine ⟨Q.mul_mem hx₁ hx₂, fun y hy => ?_⟩
        have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
            x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹ * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
        rw [e]
        exact Z.mul_mem (hnorm x₁ hx₁ _ (h₂ y hy)) (h₁ y hy)
      one_mem' := ⟨Q.one_mem, fun y _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hx, h⟩
        refine ⟨Q.inv_mem hx, fun y hy => ?_⟩
        have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hnorm _ (Q.inv_mem hx) _ (Z.inv_mem (h y hy)) }
  have memC : ∀ x : G, x ∈ C ↔ x ∈ Q ∧ ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z := fun x => Iff.rfl
  have hZC : Z ≤ C := by
    intro z hz
    refine ⟨hZQ hz, fun y hy => ?_⟩
    have : z * y = y * z := (hcen y hy z hz).symm
    rw [this]
    simp
  have hCQ : C ≤ Q := fun x hx => hx.1
  have hTC : ∀ t ∈ pairStab G a b, ∀ n ∈ C, t * n * t⁻¹ ∈ C := by
    intro t ht n hn
    refine ⟨hQ.normal t ht.1 n hn.1, fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t⁻¹⁻¹ ∈ Q := hQ.normal t⁻¹ ((pairStab G a b).inv_mem ht).1 y hy
    have h1 := hn.2 _ hy'
    have h2 := hQ.conj_mem_centQ hcomm hj ht h1
    have e : t * (n * (t⁻¹ * y * t⁻¹⁻¹) * n⁻¹ * (t⁻¹ * y * t⁻¹⁻¹)⁻¹) * t⁻¹ =
        t * n * t⁻¹ * y * (t * n * t⁻¹)⁻¹ * y⁻¹ := by group
    rw [← e]; exact h2
  rcases hQ.eq_centQ_or_eq_of_conj_mem hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3
    hQcard hΩcard hTcard hsa hs2 C hZC hCQ hTC with hCZ | hCQ'
  ·
    exfalso
    have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
    have hZcard := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf
      hQcard hΩcard hTdvd
    let : Fact p.Prime := ⟨hpp⟩
    have hQp : IsPGroup p Q := IsPGroup.of_card hQcard
    let Z' : Subgroup Q := Z.subgroupOf Q
    have hZ'n : Z'.Normal := ⟨fun n hn g => by
      have : (g : G) * n * (g : G)⁻¹ ∈ Z := hnorm g g.2 n hn
      exact this⟩
    have hlt : Nat.card Z < Nat.card Q := by
      rw [hZcard, hQcard]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hex : ∃ x₀ ∈ Q, x₀ ∉ Z := by
      by_contra h
      push Not at h
      have : Q ≤ Z := fun x hx => h x hx
      have := Subgroup.card_le_of_le this
      omega
    obtain ⟨x₀, hx₀Q, hx₀Z⟩ := hex
    have hnt : Nontrivial (Q ⧸ Z') := by
      refine ⟨⟨QuotientGroup.mk (⟨x₀, hx₀Q⟩ : Q), 1, ?_⟩⟩
      rw [ne_eq, QuotientGroup.eq_one_iff]
      exact hx₀Z
    have hQZp : IsPGroup p (Q ⧸ Z') := hQp.to_quotient Z'
    have hcent := hQZp.center_nontrivial
    obtain ⟨ξ, hξ1⟩ := exists_ne (1 : Subgroup.center (Q ⧸ Z'))
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ξ : Q ⧸ Z')
    have huC : (u : G) ∈ C := by
      refine ⟨u.2, fun y hy => ?_⟩
      have hξ := Subgroup.mem_center_iff.mp ξ.2 (QuotientGroup.mk (⟨y, hy⟩ : Q))
      rw [← hu, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hξ
      have h1 : (u : G)⁻¹ * y⁻¹ * u * y ∈ Z := by
        have : ((⟨y, hy⟩ * u)⁻¹ * (u * ⟨y, hy⟩) : Q) ∈ Z' := hξ
        have h2 : (((⟨y, hy⟩ * u)⁻¹ * (u * ⟨y, hy⟩) : Q) : G) ∈ Z := this
        simpa [mul_assoc] using h2
      have e : (u : G) * y * (u : G)⁻¹ * y⁻¹ =
          (y * u) * ((u : G)⁻¹ * y⁻¹ * u * y) * (y * u)⁻¹ := by group
      rw [e]
      exact hnorm _ (Q.mul_mem hy u.2) _ h1
    rw [hCZ] at huC
    apply hξ1
    apply Subtype.ext
    rw [← hu]
    exact (QuotientGroup.eq_one_iff _).mpr huC
  · have : x ∈ C := by rw [hCQ']; exact hx
    exact this.2 y hy

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition

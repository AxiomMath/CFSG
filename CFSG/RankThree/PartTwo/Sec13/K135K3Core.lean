module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hcen : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun a : MulAut S => a g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [hcen] at hz'
  exact hz'

theorem inner_of_not_dvd_outer {S : Type*} [Group S] {p : ℕ} (hp : p.Prime)
    (hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) :
    ∀ P : Subgroup (MulAut S), IsPGroup p P → P ≤ (MulAut.conj : S →* MulAut S).range := by
  intro P hP π hπ
  obtain ⟨k, hk⟩ := hP ⟨π, hπ⟩
  have hk' : π ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  let x : CFSG.ComponentClassification.OuterAutomorphisms.Outer S := QuotientGroup.mk π
  have hx : x ^ (p ^ k) = 1 := by
    change (QuotientGroup.mk π : MulAut S ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner S)
      ^ (p ^ k) = 1
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    orderOf_dvd_natCard x
  have hcop : Nat.Coprime (p ^ k)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hout).pow_left k
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner S) π).1 h3

theorem eq_one_of_pow_three_of_coprime {G : Type*} [Group G] (H : Subgroup G)
    (hH : Nat.Coprime 3 (Nat.card H)) {l : G} (hl : l ∈ H) (h3 : l ^ 3 = 1) : l = 1 := by
  have h1 : orderOf (⟨l, hl⟩ : H) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨l, hl⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
  have h4 : orderOf (⟨l, hl⟩ : H) = 1 := Nat.eq_one_of_dvd_one (hH.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h4
  simpa using congrArg Subtype.val h4

theorem k3_of_data {S : Type*} [Group S] {p : ℕ} (hcen : Subgroup.center S = ⊥)
    (hodd : ∀ β : MulAut S, Odd (orderOf β) → ∃ l : S, β = MulAut.conj l)
    (hinner : ∀ P : Subgroup (MulAut S), IsPGroup p P → P ≤ (MulAut.conj : S →* MulAut S).range)
    (hsyl : ∀ Q : Subgroup S, IsPGroup p Q → p ^ 3 ≤ Nat.card Q → ∀ l : S, l ^ 3 = 1 →
      (∀ g ∈ Q, l * g = g * l) → l = 1)
    (P : Subgroup (MulAut S)) (hP : IsPGroup p P) (hcard : p ^ 3 ≤ Nat.card P)
    (α : MulAut S) (hα : α ^ 3 = 1) (hcomm : ∀ π ∈ P, α * π = π * α) : α = 1 := by
  have hinj := conj_injective_of_center_eq_bot hcen
  have hodd3 : Odd (orderOf α) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨l, rfl⟩ := hodd α hodd3
  have hl3 : l ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hα, map_one]
  have hPle := hinner P hP
  let Q : Subgroup S := P.comap (MulAut.conj : S →* MulAut S)
  have hinjQ : Function.Injective ((MulAut.conj : S →* MulAut S).subgroupComap P) := by
    intro a b h
    exact Subtype.ext (hinj (show MulAut.conj (a : S) = MulAut.conj (b : S) from
      congrArg Subtype.val h))
  have hQp : IsPGroup p Q := IsPGroup.of_injective hP _ hinjQ
  have hQcard : Nat.card Q = Nat.card P := by
    refine Nat.card_congr (Equiv.ofBijective ((MulAut.conj : S →* MulAut S).subgroupComap P)
      ⟨hinjQ, ?_⟩)
    rintro ⟨π, hπ⟩
    obtain ⟨s, hs⟩ := hPle hπ
    exact ⟨⟨s, by simpa [Q, hs] using hπ⟩, Subtype.ext hs⟩
  have hcommQ : ∀ g ∈ Q, l * g = g * l := by
    intro g hg
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ hg
  have hl1 := hsyl Q hQp (hQcard ▸ hcard) l hl3 hcommQ
  rw [hl1, map_one]

end CFSG.RankThree.PartTwo.Sec13.F135Last

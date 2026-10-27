module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

private theorem card_le_mul_card_inf_ker_of_cyclic_image {G C : Type*} [Group G] [Group C]
    {p : ℕ} (hp : 0 < p) {A : Subgroup G} [Finite A] (hA : ∀ x ∈ A, x ^ p = 1)
    (α : G →* C) {c : C} (hα : ∀ x ∈ A, α x ∈ Subgroup.zpowers c) :
    Nat.card A ≤ p * Nat.card (A ⊓ α.ker : Subgroup G) := by
  let β : A →* C := α.comp A.subtype
  have hβ : β.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨x, rfl⟩
    exact hα x x.2
  haveI : IsCyclic β.range := Subgroup.isCyclic_of_le hβ
  haveI : Finite β.range :=
    (MonoidHom.finite_iff_finite_ker_range β).mp (inferInstance : Finite A) |>.2
  have hrange : Nat.card β.range ≤ p := by
    obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := β.range)
    have hyp : y ^ p = 1 := by
      obtain ⟨x, hx⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← map_pow]
      simpa [β] using congrArg α (hA (x : G) x.2)
    calc
      Nat.card β.range = orderOf y := hy.symm
      _ ≤ p := orderOf_le_of_pow_eq_one hp hyp
  have hker : β.ker = (A ⊓ α.ker).subgroupOf A := by
    ext x
    change α (x : G) = 1 ↔ ((x : G) ∈ A ∧ α (x : G) = 1)
    simp
  have hcardker : Nat.card β.ker = Nat.card (A ⊓ α.ker : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc
    Nat.card A = Nat.card β.ker * Nat.card β.range :=
      (Subgroup.card_ker_mul_card_range β).symm
    _ ≤ Nat.card β.ker * p := Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card (A ⊓ α.ker : Subgroup G) := by rw [hcardker, mul_comm]

theorem card_le_sq_of_two_cyclic_layers {G : Type*} [Group G] {p : ℕ} (hp : 0 < p)
    {N J S A : Subgroup G} [N.Normal] {φ₀ g : G} (hJn : (J.subgroupOf S).Normal) (hg : g ∈ S)
    (hgen : ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) (hJ : J ≤ N ⊔ Subgroup.zpowers φ₀) (hAS : A ≤ S)
    (hexp : ∀ x ∈ A, x ^ p = 1) (hAN : A ⊓ N = ⊥) : Nat.card A ≤ p ^ 2 := by
  by_cases hfin : Finite A
  · letI := hfin
    haveI : (J.subgroupOf S).Normal := hJn
    have hcyc : ∀ x ∈ A.subgroupOf S,
        QuotientGroup.mk' (J.subgroupOf S) x ∈
          Subgroup.zpowers (QuotientGroup.mk' (J.subgroupOf S) ⟨g, hg⟩) := by
      intro x hx
      obtain ⟨k, hk⟩ := hgen x.1 x.2
      have h1 : QuotientGroup.mk' (J.subgroupOf S) ((⟨g, hg⟩ : S) ^ k * x) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa [Subgroup.mem_subgroupOf] using hk
      rw [map_mul, map_zpow] at h1
      have h2 : QuotientGroup.mk' (J.subgroupOf S) x =
          (QuotientGroup.mk' (J.subgroupOf S) ⟨g, hg⟩) ^ (-k) := by
        rw [eq_inv_of_mul_eq_one_right h1, zpow_neg]
      exact h2.symm ▸ Subgroup.zpow_mem_zpowers _ _
    have hA' : ∀ x ∈ A.subgroupOf S, x ^ p = 1 := fun x hx =>
      Subtype.ext (by simpa using hexp x.1 hx)
    haveI : Finite (A.subgroupOf S) :=
      Finite.of_equiv A (Subgroup.subgroupOfEquivOfLe hAS).toEquiv.symm
    have h1 : Nat.card A ≤ p * Nat.card (A ⊓ J : Subgroup G) := by
      have h := card_le_mul_card_inf_ker_of_cyclic_image hp hA'
        (QuotientGroup.mk' (J.subgroupOf S)) hcyc
      have hinf : A.subgroupOf S ⊓ J.subgroupOf S = (A ⊓ J).subgroupOf S := by
        ext x; simp [Subgroup.mem_subgroupOf]
      rw [QuotientGroup.ker_mk', hinf] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAS)).toEquiv] at h
    have h2 : Nat.card (A ⊓ J : Subgroup G) ≤ p := by
      haveI : Finite (A ⊓ J : Subgroup G) :=
        Finite.of_injective (Subgroup.inclusion inf_le_left)
          (Subgroup.inclusion_injective inf_le_left)
      have hmap : (N ⊔ Subgroup.zpowers φ₀).map (QuotientGroup.mk' N) =
          Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, MonoidHom.map_zpowers, bot_sup_eq]
      have hα : ∀ x ∈ A ⊓ J,
          QuotientGroup.mk' N x ∈ Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
        intro x hx
        exact hmap ▸ Subgroup.mem_map_of_mem _ (hJ (Subgroup.mem_inf.mp hx).2)
      have h := card_le_mul_card_inf_ker_of_cyclic_image (A := A ⊓ J) hp
        (fun x hx => hexp x (Subgroup.mem_inf.mp hx).1) (QuotientGroup.mk' N) hα
      have hbot : (A ⊓ J) ⊓ (QuotientGroup.mk' N).ker = ⊥ := by
        rw [QuotientGroup.ker_mk',
          show A ⊓ J ⊓ N = A ⊓ N ⊓ J by ac_rfl, hAN, bot_inf_eq]
      rwa [hbot, Subgroup.card_bot, mul_one] at h
    exact le_trans h1 (by simpa [pow_two] using Nat.mul_le_mul_left p h2)
  · haveI : Infinite A := not_finite_iff_infinite.mp hfin
    simp

end CFSG

end

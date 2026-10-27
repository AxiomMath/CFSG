module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeHyperplanes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u v

theorem quotient_fixed_eq_bot_of_fixed_le_kernel
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A M] (hM : IsPGroup 2 M) (hA : Odd (Nat.card A))
    (Q : Subgroup M) [Q.Normal] (hQinv : CFSG.IsInvariant A M Q)
    (hfixed : ∀ x : M, (∀ a : A, a • x = x) → x ∈ Q) :
    letI : MulDistribMulAction A (M ⧸ Q) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
    CFSG.fixedPointSubgroup A (M ⧸ Q) = ⊥ := by
  let : MulDistribMulAction A (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
  obtain ⟨hQsolv, hQcop⟩ := two_subgroup_solvable_coprime hM hA Q
  rw [CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting Q hQinv hQsolv hQcop]
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
  apply Subgroup.mem_bot.mpr
  exact (QuotientGroup.eq_one_iff m).mpr (hfixed m hm)

theorem quotient_element_fixed_eq_one_of_kernel_dichotomy
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A M] (hM : IsPGroup 2 M) (hA : Odd (Nat.card A))
    (Q : Subgroup M) [Q.Normal] (hQinv : CFSG.IsInvariant A M Q)
    (hInv : ∀ x : M, orderOf x = 2 → x ∈ Q) (a : A)
    (ha : (∀ x : M, x ∈ Q → a • x = x → x = 1) ∨
      (∀ x : M, a • x = x → x ∈ Q)) :
    letI : MulDistribMulAction A (M ⧸ Q) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
    ∀ x : M ⧸ Q, a • x = x → x = 1 := by
  let : MulDistribMulAction A (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
  let C := Subgroup.zpowers a
  have hCodd : Odd (Nat.card C) := Odd.of_dvd_nat hA C.card_subgroup_dvd_card
  have hQcinv : CFSG.IsInvariant C M Q :=
    ⟨fun c m => hQinv.invariant c m⟩
  let : MulDistribMulAction C (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := C) (G := M) Q hQcinv
  have hCfixed : CFSG.fixedPointSubgroup C (M ⧸ Q) = ⊥ := by
    rcases ha with hscalar | hkernel
    · exact (fixedPointSubgroup_and_quotient_eq_bot_of_involution_capture
        hM hCodd Q hQcinv hInv (fun m hm hfix =>
          hscalar m hm (hfix ⟨a, Subgroup.mem_zpowers a⟩))).2
    · exact quotient_fixed_eq_bot_of_fixed_le_kernel hM hCodd Q hQcinv
        (fun m hfix => hkernel m (hfix ⟨a, Subgroup.mem_zpowers a⟩))
  intro x hx
  have hxC : x ∈ CFSG.fixedPointSubgroup C (M ⧸ Q) := by
    intro c
    change (c : A) • x = x
    exact smul_eq_self_of_mem_zpowers c.property hx
  rw [hCfixed] at hxC
  exact Subgroup.mem_bot.mp hxC

theorem isCyclic_elementary_odd_actor_of_kernel_dichotomy
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A M] {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    [CFSG.IsElementaryAbelian p A] (hM : IsPGroup 2 M)
    (Q : Subgroup M) [Q.Normal] (hQinv : CFSG.IsInvariant A M Q)
    (hQproper : Q ≠ ⊤) (hInv : ∀ x : M, orderOf x = 2 → x ∈ Q)
    (hdichotomy : ∀ a : A, a ≠ 1 →
      (∀ x : M, x ∈ Q → a • x = x → x = 1) ∨
        (∀ x : M, a • x = x → x ∈ Q)) :
    IsCyclic A := by
  by_contra hAnc
  let : MulDistribMulAction A (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
  have hAodd := (noncyclic_elementary_odd_actor_card hp hpOdd hAnc).2
  obtain ⟨a, ha, x, hx, hax⟩ :=
    exists_nonidentity_actor_with_nonidentity_fixed_two_quotient hp hpOdd hAnc hM
      Q hQinv hQproper
  exact hx (quotient_element_fixed_eq_one_of_kernel_dichotomy hM hAodd Q hQinv hInv
    a (hdichotomy a ha) x hax)

theorem ambient_conjugation_subgroupOf_invariant
    {G : Type u} [Group G] (M Q A : Subgroup G) [Subgroup.Normalizes A M]
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    CFSG.IsInvariant A M (Q.subgroupOf M) := by
  constructor
  intro a x
  change (x : G) ∈ Q ↔ ((a • x : M) : G) ∈ Q
  rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  exact Subgroup.mem_normalizer_iff.mp (hAQ a.property) x

theorem isCyclic_ambient_elementary_actor_of_kernel_dichotomy
    {G : Type u} [Group G] [Finite G] (M Q A : Subgroup G)
    [Subgroup.Normalizes A M] [Q.Normal] {p : ℕ}
    (hp : p.Prime) (hpOdd : Odd p) [CFSG.IsElementaryAbelian p A]
    (hM : IsPGroup 2 M) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQproper : ¬ M ≤ Q)
    (hInv : ∀ x : G, x ∈ M → orderOf x = 2 → x ∈ Q)
    (hdichotomy : ∀ a : G, a ∈ A → a ≠ 1 →
      (∀ x : G, x ∈ M → x ∈ Q → a * x * a⁻¹ = x → x = 1) ∨
        (∀ x : G, x ∈ M → a * x * a⁻¹ = x → x ∈ Q)) :
    IsCyclic A := by
  have hQinv := ambient_conjugation_subgroupOf_invariant M Q A hAQ
  have hproper : Q.subgroupOf M ≠ ⊤ := by
    intro h
    exact hQproper (Subgroup.subgroupOf_eq_top.mp h)
  apply isCyclic_elementary_odd_actor_of_kernel_dichotomy hp hpOdd hM
    (Q.subgroupOf M) hQinv hproper
  · intro x hx
    exact hInv x x.property (by simpa only [orderOf_submonoid] using hx)
  · intro a ha
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    rcases hdichotomy a a.property haG with hs | hk
    · left
      intro x hx hax
      apply Subtype.ext
      exact hs x x.property hx (by
        simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          using congrArg Subtype.val hax)
    · right
      intro x hax
      exact hk x x.property (by
        simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          using congrArg Subtype.val hax)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

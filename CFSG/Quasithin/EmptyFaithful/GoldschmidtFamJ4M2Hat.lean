module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

theorem eq_one_of_forall_mul_comm_of_simple {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {s : S} (hs : ∀ t : S, s * t = t * s) : s = 1 := by
  have := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · have hsc : s ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun t => (hs t).symm
    rwa [h, Subgroup.mem_bot] at hsc
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center S := by rw [h]; trivial
    exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab

theorem isHat_of_perfect_central {X S : Type} [Group X] [Finite X] [Group S]
    (hperf : commutator X = ⊤) (Zc : Subgroup X) [Zc.Normal] (hZc : Zc ≤ Subgroup.center X)
    (hZ : Nat.card Zc = 3) (e : X ⧸ Zc ≃* S) (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : IsHat X S := by
  have := hS
  have hcen : Subgroup.center X = Zc := by
    refine le_antisymm (fun z hz => ?_) hZc
    have h1 : e (z : X ⧸ Zc) = 1 := by
      refine eq_one_of_forall_mul_comm_of_simple hS hnab fun t => ?_
      obtain ⟨y, rfl⟩ := e.surjective t
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        (Subgroup.mem_center_iff.1 hz x).symm]
    exact (QuotientGroup.eq_one_iff z).1 (by simpa using h1)
  let e' : X ⧸ Subgroup.center X ≃* S := (QuotientGroup.quotientMulEquivOfEq hcen).trans e
  refine ⟨⟨⟨hperf⟩, e'.isSimpleGroup, ?_⟩, by rw [hcen]; exact hZ, ⟨e'⟩⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩

theorem le_center_of_perfect_of_card_three {X : Type*} [Group X] (hperf : commutator X = ⊤)
    (W : Subgroup X) [W.Normal] (hW : Nat.card W = 3) : W ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic W := isCyclic_of_prime_card hW
  have hcomm : ∀ f g : MulAut W, f * g = g * f := fun f g =>
    (IsCyclic.mulAutMulEquiv W).injective (by simp only [map_mul, mul_comm])
  let φ : X →* MulAut W := MulAut.conjNormal
  have hker : commutator X ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  intro w hw
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ φ.ker := hker (by rw [hperf]; exact Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have h1 : g * w * g⁻¹ = w := by
    have := congrArg (fun f : MulAut W => ((f ⟨w, hw⟩ : W) : X)) hg
    simpa [φ, MulAut.conjNormal_apply] using this
  calc g * w = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [h1]

theorem isHat_of_quotient_of_normal_order_three {X S : Type} [Group X] [Finite X] [Group S]
    (hperf : commutator X = ⊤) (W : Subgroup X) [W.Normal] (hW : Nat.card W = 3)
    (e : X ⧸ W ≃* S) (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) : IsHat X S :=
  isHat_of_perfect_central hperf W (le_center_of_perfect_of_card_three hperf W hW) hW e hS hnab

theorem eq_of_mem_cComp_of_simple {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hNX : N ≤ X) (_hNn : (N.subgroupOf X).Normal) (hNs : IsSimpleGroup ↥N)
    (hab : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ N) {L : Subgroup G} (hL : L ∈ cComp X) : L = N := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLN : L ≤ N := by
    have h1 : ⁅L, L⁆ ≤ N :=
      Subgroup.commutator_le.2 fun x hx y hy => hab x (hLX hx) y (hLX hy)
    rwa [perfect_of_mem_cComp hL] at h1
  by_contra hne
  obtain ⟨P, hPN, hPn, hLP⟩ := A3.subnormal_exists_normal_of_lt
    (A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hL) hLN hNX) (lt_of_le_of_ne hLN hne)
  rcases hNs.eq_bot_or_eq_top_of_normal (P.subgroupOf N) with h | h
  · refine ne_bot_of_mem_cComp hL (le_bot_iff.1 (hLP.trans fun x hx => ?_))
    have hx' : (⟨x, hPN.le hx⟩ : N) ∈ P.subgroupOf N := Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
  · exact hPN.not_ge (Subgroup.subgroupOf_eq_top.1 h)

section IndexTwo

private theorem commutatorElement_mem_of_index_two {K : Type*} [Group K] {H : Subgroup K}
    (h : H.index = 2) (a b : K) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group]
  simp only [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff]

variable {G : Type*} [Group G] [Finite G] {N M : Subgroup G}

theorem index_subgroupOf_eq_two_of_card_eq_two_mul (hNM : N ≤ M)
    (hcard : Nat.card M = 2 * Nat.card N) : (N.subgroupOf M).index = 2 := by
  have h := Subgroup.relIndex_mul_card (H := N) (K := M)
  rw [inf_of_le_left hNM, hcard] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem normal_subgroupOf_of_card_eq_two_mul (hNM : N ≤ M)
    (hcard : Nat.card M = 2 * Nat.card N) : (N.subgroupOf M).Normal :=
  Subgroup.normal_of_index_eq_two (index_subgroupOf_eq_two_of_card_eq_two_mul hNM hcard)

theorem commutatorElement_mem_of_card_eq_two_mul (hNM : N ≤ M)
    (hcard : Nat.card M = 2 * Nat.card N) : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N := fun x hx y hy =>
  Subgroup.mem_subgroupOf.1
    (commutatorElement_mem_of_index_two
      (index_subgroupOf_eq_two_of_card_eq_two_mul hNM hcard) ⟨x, hx⟩ ⟨y, hy⟩)

theorem mem_or_mul_inv_mem_of_card_eq_two_mul (hNM : N ≤ M)
    (hcard : Nat.card M = 2 * Nat.card N) {t : G} (htM : t ∈ M) (htN : t ∉ N) :
    ∀ y ∈ M, y ∈ N ∨ y * t⁻¹ ∈ N := by
  intro y hy
  by_cases hyN : y ∈ N
  · exact Or.inl hyN
  · refine Or.inr (Subgroup.mem_subgroupOf.1 ((Subgroup.mul_mem_iff_of_index_two
      (index_subgroupOf_eq_two_of_card_eq_two_mul hNM hcard) (a := ⟨y, hy⟩)
      (b := (⟨t, htM⟩ : M)⁻¹)).2 ?_))
    simp only [inv_mem_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => absurd h hyN, fun h => absurd h htN⟩

theorem card_eq_two_mul_facts (hNM : N ≤ M) (hcard : Nat.card M = 2 * Nat.card N) :
    (N.subgroupOf M).Normal ∧ (∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N) ∧
      ∀ t ∈ M, t ∉ N → ∀ y ∈ M, y ∈ N ∨ y * t⁻¹ ∈ N :=
  ⟨normal_subgroupOf_of_card_eq_two_mul hNM hcard,
    commutatorElement_mem_of_card_eq_two_mul hNM hcard,
    fun _ htM htN => mem_or_mul_inv_mem_of_card_eq_two_mul hNM hcard htM htN⟩

end IndexTwo

end CFSG.Quasithin.J4M2

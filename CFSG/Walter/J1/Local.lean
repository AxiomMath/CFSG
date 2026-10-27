module

public import CFSG.Walter.J1.HStruct

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem sylow_structure (S : Sylow 2 G) :
    Nat.card (S : Subgroup G) = 8 ∧ (∀ x ∈ S, x * x = 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) = S :=
  ⟨h.card_sylow' S, fun _ hx => h.mul_self_of_mem_sylow' S hx,
    fun x hx y hy => congrArg Subtype.val ((h.abelian_sylow S).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    h.centralizer_sylow'' S⟩

include h in
theorem isConj_involutions {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  h.isConj_of_orderOf_eq_two hx hy

include h in
theorem normalizer_quotient (S : Sylow 2 G) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))) = 21 ∧
    ¬ ∀ a b : Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)),
        a * b = b * a := by
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  refine ⟨?_, fun hcomm => ?_⟩
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((S : Subgroup G).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    have h2 : Nat.card ((S : Subgroup G).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, h.card_sylow' S]
    rw [h2, h.card_normalizer_sylow'' S] at h1
    omega
  · obtain ⟨s, hsS, -, -, hs, -⟩ := h.exists_four_of_sylow S
    obtain ⟨g, hg⟩ := h.exists_conj_t_eq hs
    obtain ⟨a, haN, b, hbN, hab⟩ := (h.conj g).exists_not_mem_sylow_commutator S (hg ▸ hsS)
    apply hab
    have := hcomm (QuotientGroup.mk ⟨a, haN⟩) (QuotientGroup.mk ⟨b, hbN⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at this
    change _ ∈ (S : Subgroup G)
    simpa using this

include h in
theorem card_sylow_three_five {p : ℕ} (hp : p = 3 ∨ p = 5) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p :=
  h.card_sylow_odd hp P

end JankoHyp

end CFSG.Walter.J1

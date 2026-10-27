module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ASVolI

variable {G : Type*} [Group G]

theorem burnsideJ4NP_map_conj_eq_iff {A : Subgroup G} {n : G} :
    A.map (MulAut.conj n).toMonoidHom = A ↔ n ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff'', SetLike.ext_iff]
  refine forall_congr' fun x => ?_
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact Iff.comm

theorem burnsideJ4NP_map_conj_map_conj (A : Subgroup G) (g k : G) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * k)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideJ4NP_map_conj_eq_map_conj_iff {A : Subgroup G} {k k' : G} :
    A.map (MulAut.conj k).toMonoidHom = A.map (MulAut.conj k').toMonoidHom ↔
      k⁻¹ * k' ∈ Subgroup.normalizer (A : Set G) := by
  have e : A.map (MulAut.conj k').toMonoidHom =
      (A.map (MulAut.conj (k⁻¹ * k')).toMonoidHom).map (MulAut.conj k).toMonoidHom := by
    rw [burnsideJ4NP_map_conj_map_conj, mul_inv_cancel_left]
  rw [← burnsideJ4NP_map_conj_eq_iff, e, (Subgroup.map_injective (MulAut.conj k).injective).eq_iff,
    eq_comm]

theorem burnsideJ4NP_forall_mem_of_closed {X : Type*} {K : Subgroup G} [Finite K] {gens : Set G}
    (hK : Subgroup.closure gens = K) (f : G → X) (O : Set X) (h1 : f 1 ∈ O)
    (hcl : ∀ k ∈ K, f k ∈ O → ∀ g ∈ gens, f (g * k) ∈ O) : ∀ k ∈ K, f k ∈ O := by
  have hfin : ∀ g ∈ gens, IsOfFinOrder g := fun g hg => by
    have hgK : g ∈ K := by
      rw [← hK]
      exact Subgroup.subset_closure hg
    rw [← orderOf_pos_iff, ← Subgroup.orderOf_mk (H := K) g hgK]
    exact orderOf_pos _
  have hmon : ∀ k ∈ Submonoid.closure gens, k ∈ K := fun k hk => by
    rw [← hK]
    exact Subgroup.le_closure_toSubmonoid gens hk
  intro k hk
  rw [← hK, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid_of_isOfFinOrder hfin] at hk
  induction hk using Submonoid.closure_induction_left with
  | one => exact h1
  | mul_left g hg k hk ih => exact hcl k (hmon k hk) ih g hg

theorem burnsideJ4NP_card_eq_of_fibers {X : Type*} {K S : Subgroup G} [Finite K] (hSK : S ≤ K)
    (f : G → X) (hfib : ∀ k ∈ K, ∀ k' ∈ K, f k = f k' ↔ k⁻¹ * k' ∈ S) :
    Nat.card K = Nat.card ↥(f '' (K : Set G)) * Nat.card S := by
  rw [(S.subgroupOf K).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
  congr 1
  refine Nat.card_eq_of_bijective (Quotient.lift (fun k : K => (⟨f k, k, k.2, rfl⟩ :
    ↥(f '' (K : Set G)))) fun a b hab => Subtype.ext ((hfib a a.2 b b.2).mpr ?_)) ⟨?_, ?_⟩
  · simpa [Subgroup.mem_subgroupOf] using QuotientGroup.leftRel_apply.mp hab
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine QuotientGroup.eq.mpr ?_
    simpa [Subgroup.mem_subgroupOf] using (hfib a a.2 b b.2).mp (congrArg Subtype.val hab)
  · rintro ⟨x, k, hk, rfl⟩
    exact ⟨QuotientGroup.mk ⟨k, hk⟩, rfl⟩

theorem burnsideJ4NP_card_eq_of_orbit {X : Type*} {K S : Subgroup G} [Finite K] {gens : Set G}
    (hK : Subgroup.closure gens = K) (hSK : S ≤ K) (f : G → X)
    (hfib : ∀ k ∈ K, ∀ k' ∈ K, f k = f k' ↔ k⁻¹ * k' ∈ S) (O : Finset X) (h1 : f 1 ∈ O)
    (hcl : ∀ k ∈ K, f k ∈ O → ∀ g ∈ gens, f (g * k) ∈ O) (hsound : ∀ x ∈ O, ∃ k ∈ K, f k = x) :
    Nat.card K = O.card * Nat.card S := by
  have hO : f '' (K : Set G) = O := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨k, hk, rfl⟩
      exact burnsideJ4NP_forall_mem_of_closed hK f O h1 hcl k hk
    · obtain ⟨k, hk, rfl⟩ := hsound x hx
      exact ⟨k, hk, rfl⟩
  rw [burnsideJ4NP_card_eq_of_fibers hSK f hfib, hO, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem burnsideJ4NP_card_eq_orbit_mul_centralizer_enc {R : Type*} {K : Subgroup G} [Finite K]
    {gens : Set G} (hK : Subgroup.closure gens = K) (y : G) (enc : G → R)
    (hinj : ∀ k ∈ K, ∀ k' ∈ K, enc (k * y * k⁻¹) = enc (k' * y * k'⁻¹) →
      k * y * k⁻¹ = k' * y * k'⁻¹)
    (O : Finset R) (hy : enc y ∈ O)
    (hcl : ∀ k ∈ K, enc (k * y * k⁻¹) ∈ O → ∀ g ∈ gens, enc (g * (k * y * k⁻¹) * g⁻¹) ∈ O)
    (hsound : ∀ r ∈ O, ∃ k ∈ K, enc (k * y * k⁻¹) = r) :
    Nat.card K = O.card * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) := by
  refine burnsideJ4NP_card_eq_of_orbit hK inf_le_left (fun k => enc (k * y * k⁻¹))
    (fun k hk k' hk' => ?_) O (by simpa using hy) (fun k hk h g hg => ?_) hsound
  · rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun h => ⟨K.mul_mem (K.inv_mem hk) hk', ?_⟩, fun ⟨_, h⟩ => ?_⟩
    · calc k⁻¹ * k' * y = k⁻¹ * (k' * y * k'⁻¹) * k' := by group
        _ = k⁻¹ * (k * y * k⁻¹) * k' := by rw [hinj k hk k' hk' h]
        _ = y * (k⁻¹ * k') := by group
    · show enc (k * y * k⁻¹) = enc (k' * y * k'⁻¹)
      congr 1
      calc k * y * k⁻¹ = k * (y * (k⁻¹ * k')) * k'⁻¹ := by group
        _ = k * (k⁻¹ * k' * y) * k'⁻¹ := by rw [h]
        _ = k' * y * k'⁻¹ := by group
  · show enc (g * k * y * (g * k)⁻¹) ∈ O
    rw [show g * k * y * (g * k)⁻¹ = g * (k * y * k⁻¹) * g⁻¹ by group]
    exact hcl k hk h g hg

end CFSG.ASVolI

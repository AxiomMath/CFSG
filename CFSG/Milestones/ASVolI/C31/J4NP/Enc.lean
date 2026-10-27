module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.ASVolI

variable {G : Type*} [Group G]

theorem burnsideJ4NP_closure_subset_of_closed {gens S : Set G} (hS : S.Finite) (h1 : 1 ∈ S)
    (hcl : ∀ x ∈ S, ∀ g ∈ gens, x * g ∈ S) : (Subgroup.closure gens : Set G) ⊆ S := by
  intro x hx
  rw [SetLike.mem_coe] at hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x _ g hg ih => exact hcl x ih g hg
  | mul_inv_cancel x _ g hg ih =>
    have hbij := (hS.injOn_iff_bijOn_of_mapsTo fun s hs => hcl s hs g hg).mp
      (mul_left_injective g).injOn
    obtain ⟨s, hs, rfl⟩ := hbij.surjOn ih
    simpa using hs

section Enc

variable {R : Type*} [Mul R] [One R] {H : Subgroup G} {enc : G → R}

theorem burnsideJ4NP_enc_mem_of_closed (hinj : Set.InjOn enc H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, enc (x * y) = enc x * enc y) (hone : enc 1 = 1) {gens : Set G}
    (hgH : gens ⊆ H) (S : Finset R) (h1 : (1 : R) ∈ S) (hcl : ∀ r ∈ S, ∀ g ∈ gens, r * enc g ∈ S)
    {x : G} (hx : x ∈ Subgroup.closure gens) : enc x ∈ S := by
  have hfin : {x | x ∈ H ∧ enc x ∈ S}.Finite :=
    Set.Finite.of_injOn (fun x hx => hx.2) (hinj.mono fun x hx => hx.1) S.finite_toSet
  have hsub := burnsideJ4NP_closure_subset_of_closed hfin ⟨H.one_mem, by rw [hone]; exact h1⟩
    fun y hy g hg => ⟨H.mul_mem hy.1 (hgH hg), by
      rw [hmul y hy.1 g (hgH hg)]
      exact hcl _ hy.2 g hg⟩
  exact (hsub hx).2

theorem burnsideJ4NP_mem_closure_iff_of_closed_enc (hinj : Set.InjOn enc H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, enc (x * y) = enc x * enc y) (hone : enc 1 = 1) {gens : Set G}
    (hgH : gens ⊆ H) (S : Finset R) (h1 : (1 : R) ∈ S) (hcl : ∀ r ∈ S, ∀ g ∈ gens, r * enc g ∈ S)
    (hsound : ∀ r ∈ S, ∃ x ∈ Subgroup.closure gens, enc x = r) {x : G} (hx : x ∈ H) :
    x ∈ Subgroup.closure gens ↔ enc x ∈ S := by
  refine ⟨burnsideJ4NP_enc_mem_of_closed hinj hmul hone hgH S h1 hcl, fun h => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hsound _ h
  rwa [← hinj ((Subgroup.closure_le H).mpr hgH hy) hx hyx]

theorem burnsideJ4NP_card_closure_of_closed_enc (hinj : Set.InjOn enc H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, enc (x * y) = enc x * enc y) (hone : enc 1 = 1) {gens : Set G}
    (hgH : gens ⊆ H) (S : Finset R) (h1 : (1 : R) ∈ S) (hcl : ∀ r ∈ S, ∀ g ∈ gens, r * enc g ∈ S)
    (hsound : ∀ r ∈ S, ∃ x ∈ Subgroup.closure gens, enc x = r) :
    Nat.card (Subgroup.closure gens) = S.card := by
  have hle : Subgroup.closure gens ≤ H := (Subgroup.closure_le H).mpr hgH
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_eq_of_bijective
    (fun x => ⟨enc x, burnsideJ4NP_enc_mem_of_closed hinj hmul hone hgH S h1 hcl x.2⟩)
    ⟨fun a b hab => Subtype.ext (hinj (hle a.2) (hle b.2) (congrArg Subtype.val hab)), fun r => ?_⟩
  obtain ⟨x, hx, hxr⟩ := hsound r.1 r.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxr⟩

end Enc

theorem burnsideJ4NP_eq_of_le_of_card_dvd {L K : Subgroup G} [Finite K] (hLK : L ≤ K)
    (hdvd : Nat.card K ∣ Nat.card L) : L = K :=
  Subgroup.eq_of_le_of_card_ge hLK (Nat.dvd_antisymm (Subgroup.card_dvd_of_le hLK) hdvd).ge

theorem burnsideJ4NP_dvd_of_primePow_dvd {d n : ℕ} (hd : d ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ d → p ^ d.factorization p ∣ n) : d ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact dvd_zero _
  refine (Nat.factorization_prime_le_iff_dvd hd hn.ne').mp fun p hp => ?_
  by_cases hpd : p ∣ d
  · exact (hp.pow_dvd_iff_le_factorization hn.ne').mp (h p hp hpd)
  · simp [Nat.factorization_eq_zero_of_not_dvd hpd]

theorem burnsideJ4NP_eq_of_le_of_primePow_dvd {L K : Subgroup G} [Finite K] (hLK : L ≤ K)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p ^ (Nat.card K).factorization p ∣ Nat.card L) :
    L = K :=
  burnsideJ4NP_eq_of_le_of_card_dvd hLK (burnsideJ4NP_dvd_of_primePow_dvd Nat.card_pos.ne' h)

theorem burnsideJ4NP_eq_of_le_of_lcm_dvd {L K : Subgroup G} [Finite K] (hLK : L ≤ K)
    (Ps : List (Subgroup G)) (hPs : ∀ P ∈ Ps, P ≤ L)
    (hdvd : Nat.card K ∣ (Ps.map fun P : Subgroup G => Nat.card ↥P).foldr Nat.lcm 1) : L = K := by
  have key : ∀ Qs : List (Subgroup G), (∀ P ∈ Qs, P ≤ L) →
      (Qs.map fun P : Subgroup G => Nat.card ↥P).foldr Nat.lcm 1 ∣ Nat.card L := by
    intro Qs hQs
    induction Qs with
    | nil => exact one_dvd _
    | cons P Qs ih =>
      exact Nat.lcm_dvd (Subgroup.card_dvd_of_le (hQs P List.mem_cons_self))
        (ih fun Q hQ => hQs Q (List.mem_cons_of_mem _ hQ))
  exact burnsideJ4NP_eq_of_le_of_card_dvd hLK (hdvd.trans (key Ps hPs))

end CFSG.ASVolI

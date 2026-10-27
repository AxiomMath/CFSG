module

public import CFSG.Quasithin.H13.NQCatT513Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem cycOddPerm_of_sylow {X : Type} [Group X] [Finite X] {c : ℕ → Prop} {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (h : ∀ Dc : Subgroup X, IsCyclic ↥Dc → Odd (Nat.card ↥Dc) →
      (Dc : Set X) * (S₀ : Set X) = (S₀ : Set X) * (Dc : Set X) →
        (∃ k : ℕ, Nat.card ↥Dc = 3 ^ k) ∨ c (Nat.card ↥Dc)) : CycOddPerm X c := by
  intro T Dc hT hcyc hodd hperm
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hT hS₀
  let α : X ≃* X := MulAut.conj g
  have hcard : Nat.card ↥(Dc.map α.toMonoidHom) = Nat.card ↥Dc :=
    Subgroup.card_map_of_injective α.injective
  have hcyc' : IsCyclic ↥(Dc.map α.toMonoidHom) :=
    isCyclic_of_surjective (Dc.equivMapOfInjective α.toMonoidHom α.injective).toMonoidHom
      (MulEquiv.surjective _)
  have hperm' : ((Dc.map α.toMonoidHom : Subgroup X) : Set X) * (S₀ : Set X) =
      (S₀ : Set X) * ((Dc.map α.toMonoidHom : Subgroup X) : Set X) := by
    rw [← hg]
    simp only [Subgroup.coe_map]
    rw [← Set.image_mul, hperm, Set.image_mul]
  have h1 := h _ hcyc' (hcard ▸ hodd) hperm'
  rwa [hcard] at h1

theorem card_sup_of_perm {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hperm : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G))
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K)) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  apply le_antisymm
  · have hset := coe_sup_eq_mul H K hperm
    let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
      ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      have hx' : x ∈ (H : Set G) * (K : Set G) := by
        rw [← hset]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    calc Nat.card ↥(H ⊔ K) ≤ Nat.card (↥H × ↥K) := Nat.card_le_card_of_surjective f hf
      _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _
  · refine Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd ?_ ?_)
    · exact Subgroup.card_dvd_of_le le_sup_left
    · exact Subgroup.card_dvd_of_le le_sup_right

theorem exists_orderOf_eq_card {G : Type} [Group G] [Finite G] {D : Subgroup G}
    (hD : IsCyclic ↥D) : ∃ g ∈ D, orderOf g = Nat.card ↥D := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥D)
  exact ⟨g, g.2, by rw [← Subgroup.orderOf_coe] at hg; exact hg⟩

theorem prime_dvd_of_dvd_lcm {s : Multiset ℕ} {p : ℕ} (hp : p.Prime) (h : p ∣ s.lcm) :
    ∃ a ∈ s, p ∣ a := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd (Nat.le_of_dvd one_pos h) (by have := hp.two_le; omega)
  | cons a t ih =>
    rw [Multiset.lcm_cons] at h
    have h1 : p ∣ a * t.lcm := h.trans (lcm_dvd_mul a t.lcm)
    rcases hp.dvd_mul.mp h1 with h2 | h2
    · exact ⟨a, Multiset.mem_cons_self a t, h2⟩
    · obtain ⟨b, hb, hpb⟩ := ih h2
      exact ⟨b, Multiset.mem_cons_of_mem hb, hpb⟩

theorem add_le_sum_of_ne {s : Multiset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    a + b ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hbt : b ∈ t := by
    rcases Multiset.mem_cons.mp hb with h | h
    · exact absurd h.symm hab
    · exact h
  rw [Multiset.sum_cons]
  exact Nat.add_le_add_left (Multiset.le_sum_of_mem hbt) a

end CFSG.Quasithin.H13.NQCat.T513P

module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.QuasithinUnique

theorem exists_mem_normalizer_orderOf_of_mulEquiv {Y G : Type} [Group Y] [Finite Y] [Group G]
    [Finite G] (e : Y ≃* G) {U₀ : Subgroup G} (hU₀ : IsSylowTwoOf U₀ ⊤) {d₀ : G}
    (hd₀ : d₀ ∈ Subgroup.normalizer (U₀ : Set G)) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    ∃ d : Y, d ∈ Subgroup.normalizer (S : Set Y) ∧ orderOf d = orderOf d₀ := by
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf
    (CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hS) hU₀
  set e₂ : Y ≃* G := e.trans (MulAut.conj g) with he₂
  have hS₂ : S.map e₂.toMonoidHom = U₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have h1 : d₀ ∈ (Subgroup.normalizer (S : Set Y)).map e₂.toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hS₂]
    exact hd₀
  obtain ⟨d, hd, hde⟩ := h1
  refine ⟨d, hd, ?_⟩
  rw [← hde]
  exact (orderOf_injective e₂.toMonoidHom e₂.injective d).symm

theorem exists_mem_orderOf_of_dvd_card {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hD : IsCyclic D) {m : ℕ} (hm : m ∣ Nat.card D) : ∃ d ∈ D, orderOf d = m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  obtain ⟨k, hk⟩ := hm
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  refine ⟨((g ^ k : D) : X), (g ^ k).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hk0 (by rw [hg, hk]; exact dvd_mul_left _ _), hg,
    hk, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

theorem exists_mem_normalizer_orderOf_of_borelSetup {X : Type} [Group X] [Finite X]
    {T : Sylow 2 X} {D : Subgroup X} (h : CFSG.Goldschmidt.G3a.BorelSetup T D) {m : ℕ}
    (hm : m ∣ Nat.card D) :
    ∃ d : X, d ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) ∧ orderOf d = m := by
  obtain ⟨d, hd, hdm⟩ := exists_mem_orderOf_of_dvd_card h.cyc hm
  exact ⟨d, h.le hd, hdm⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

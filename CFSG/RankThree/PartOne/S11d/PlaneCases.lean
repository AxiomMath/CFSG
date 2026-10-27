module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo LocalRankAut innerAut PlaneT)

namespace PlaneCases

theorem outPNice_of_not_dvd_outer {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    OutStructure.OutPNice p X := by
  refine ⟨⊤, ⊤, le_top, ?_, fun _ _ => trivial, fun _ _ _ => trivial,
    fun α _ β _ _ _ => Or.inl ⟨0, trivial⟩⟩
  intro δ _ k hk
  have h1 : (QuotientGroup.mk δ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hd1 : orderOf (QuotientGroup.mk δ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (QuotientGroup.mk δ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have h2 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff δ).mp (orderOf_eq_one_iff.mp h2)

theorem no_plane_of_outPChain {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : OutStructure.OutPChain p T) (E : Subgroup (MulAut T)) (hE : IsElementaryAbelian p ↥E)
    (hcard : Nat.card E = p ^ 2) (hEinn : E ⊓ innerAut T = ⊥) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, E', hID, hD2, hE1, hE3⟩ := h
  have hnc : ¬ IsCyclic E := IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨β, hβ1⟩ : ∃ β : E, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton E := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hcard] at h1
    have := hp.one_lt
    nlinarith
  obtain ⟨α, hαβ⟩ : ∃ α : E, α ∉ Subgroup.zpowers β := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨⟨β, fun x => hcon x⟩⟩
  have hαp : (α : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ α.2
  have hβp : (β : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have hαpE : α ^ p = 1 := Subtype.ext hαp
  have hβpE : β ^ p = 1 := Subtype.ext hβp
  have hα1 : α ≠ 1 := fun h => hαβ (h ▸ (Subgroup.zpowers β).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαpE hα1
  have hβord : orderOf β = p := orderOf_eq_prime hβpE hβ1
  have hpD : ∀ x : MulAut T, x ^ p = 1 → ∃ k : ℕ, x ^ (p ^ k) ∈ D := fun x hx =>
    ⟨1, by rw [pow_one, hx]; exact D.one_mem⟩
  have hαE : (α : MulAut T) ∈ E' := hE1 _ (hpD _ hαp)
  have hβE : (β : MulAut T) ∈ E' := hE1 _ (hpD _ hβp)
  have hDinn : ∀ δ : MulAut T, δ ∈ D → δ ^ p = 1 → δ ∈ innerAut T := by
    intro δ hδ hδp
    exact hD2 δ hδ 1 (by rw [pow_one, hδp]; exact (OutStructure.Inn T).one_mem)
  have hsubInn : ∀ x : E, (x : MulAut T) ∈ innerAut T → x = 1 := by
    intro x hx
    have hxm : (x : MulAut T) ∈ E ⊓ innerAut T := ⟨x.2, hx⟩
    rw [hEinn, Subgroup.mem_bot] at hxm
    exact Subtype.ext hxm
  rcases hE3 _ hαE _ hβE (hpD _ hαp) (hpD _ hβp) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hγp : ((α * β ^ m : E) : MulAut T) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) ((α * β ^ m : E) : MulAut T)
        (α * β ^ m).2
    have hγD : ((α * β ^ m : E) : MulAut T) ∈ D := by
      have : ((α * β ^ m : E) : MulAut T) = (α : MulAut T) * (β : MulAut T) ^ m := by simp
      rw [this]
      exact hm
    have hγ1 := hsubInn _ (hDinn _ hγD hγp)
    apply hαβ
    have hαeq : α = β ^ (-m) := by
      rw [mul_eq_one_iff_eq_inv] at hγ1
      rw [hγ1, zpow_neg]
    rw [hαeq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers β) _
  · have hγp : ((β * α ^ m : E) : MulAut T) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) ((β * α ^ m : E) : MulAut T)
        (β * α ^ m).2
    have hγD : ((β * α ^ m : E) : MulAut T) ∈ D := by
      have : ((β * α ^ m : E) : MulAut T) = (β : MulAut T) * (α : MulAut T) ^ m := by simp
      rw [this]
      exact hm
    have hγ1 := hsubInn _ (hDinn _ hγD hγp)
    have hβα : β = α ^ (-m) := by
      rw [mul_eq_one_iff_eq_inv] at hγ1
      rw [hγ1, zpow_neg]
    have hβmem : β ∈ Subgroup.zpowers α := by
      rw [hβα]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers α) _
    have hle : Subgroup.zpowers β ≤ Subgroup.zpowers α := (Subgroup.zpowers_le).mpr hβmem
    have hcα : Nat.card (Subgroup.zpowers α) = p := by rw [Nat.card_zpowers, hαord]
    have hcβ : Nat.card (Subgroup.zpowers β) = p := by rw [Nat.card_zpowers, hβord]
    have heq : Subgroup.zpowers β = Subgroup.zpowers α :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcα, hcβ])
    exact hαβ (heq ▸ Subgroup.mem_zpowers α)

theorem planeT_of_outPChain {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : OutStructure.OutPChain p T) : PlaneT p T :=
  fun _ E hE hcard hEinn _ => no_plane_of_outPChain hp h E hE hcard hEinn

theorem catalog_cases {T : Type} [Group T] (hT : Catalog T) :
    (∃ q : ℕ, q.Prime ∧ Nonempty (T ≃* Multiplicative (ZMod q))) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
      (∃ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f ∧ LieModel T t n ℓ f) ∨
      NativeSporadic.SporadicRep T := by
  rcases hT with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨t, n, ℓ, f, hmodel⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨t, n, ℓ, f, hmodel.1, Or.inl ⟨?_, hmodel⟩⟩))
    have h2 := hmodel.2
    cases t <;> first | exact h2.elim | simp [classicalTags]
  · rcases h with ⟨t, ℓ, f, ht, hmodel⟩ | ⟨t, ℓ, f, ht, hmodel⟩ | ⟨ℓ, f, hmodel⟩
    · exact Or.inr (Or.inr (Or.inl ⟨t, 0, ℓ, f, hmodel.1, Or.inr (Or.inl ⟨rfl, ht, hmodel⟩)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨t, 0, ℓ, f, hmodel.1,
        Or.inr (Or.inr (Or.inl ⟨rfl, ht, hmodel⟩))⟩))
    · have hmodel' := hmodel
      obtain ⟨hℓ, a, ha, K, _, _, hf, -, -⟩ := hmodel'
      refine Or.inr (Or.inr (Or.inl ⟨.twistedB2, 0, ℓ, f, ⟨?_, ?_, rfl, hℓ, ⟨a, hf⟩, ?_⟩,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hmodel⟩))⟩))
      · rw [hℓ]
        exact Nat.prime_two
      · omega
      · omega
  · exact Or.inr (Or.inr (Or.inr h))

end PlaneCases

end CFSG.RankThree.PartOne

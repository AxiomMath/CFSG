module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.Blueprint.LieModelAPI
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

theorem lieModel_classical_iff {G : Type} [Group G] {t : StatedLieTag} (ht : t ∈ classicalTags)
    {n p f : ℕ} : LieModel G t n p f ↔ StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.classical_iff ht

theorem no_plane_of_outPNice {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : OutStructure.OutPNice p T) (E : Subgroup (MulAut T)) (hE : IsElementaryAbelian p ↥E)
    (hcard : Nat.card E = p ^ 2) (hEinn : E ⊓ innerAut T = ⊥) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, E', hID, hD2, hE1, -, hE3⟩ := h
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
    have := hD2 δ hδ 1 (by rw [pow_one, hδp]; exact (OutStructure.Inn T).one_mem)
    exact this
  have hsubInn : ∀ x : E, (x : MulAut T) ∈ innerAut T → x = 1 := by
    intro x hx
    have hxm : (x : MulAut T) ∈ E ⊓ innerAut T := ⟨x.2, hx⟩
    rw [hEinn, Subgroup.mem_bot] at hxm
    exact Subtype.ext hxm
  rcases hE3 _ hαE _ hβE (hpD _ hαp) (hpD _ hβp) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hγp : ((α * β ^ m : E) : MulAut T) ^ p = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) ((α * β ^ m : E) : MulAut T)
        (α * β ^ m).2
      exact this
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
  ·
    have hγp : ((β * α ^ m : E) : MulAut T) ^ p = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) ((β * α ^ m : E) : MulAut T)
        (β * α ^ m).2
      exact this
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

end CFSG.RankThree.PartOne.Sec66T

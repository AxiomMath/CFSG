module

public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.Ch4.E443.F4411

open Subgroup

variable {G : Type*} [Group G]

@[expose] def PerfCentral (G : Type*) [Group G] : Prop :=
  ∀ U Y : Subgroup G, IsPGroup 2 U → ⁅Y, Y⁆ = Y → Y ≤ normalizer (U : Set G) → ⁅U, Y⁆ = ⊥

theorem commutator_eq_top_of_perfect {Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) :
    commutator Y = ⊤ := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_subtype_commutator, hY, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem range_eq_bot_of_perfect {A S : Type*} [Group A] [Group S] [Group.IsSolvable S]
    (hA : commutator A = ⊤) (f : A →* S) : f.range = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := S)
  have h : ∀ k, derivedSeries A k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hA]
  rw [MonoidHom.range_eq_map, ← h n, ← le_bot_iff, ← hn]
  exact map_derivedSeries_le_derivedSeries f n

theorem map_eq_one_of_perfect {Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) {S : Type*} [Group S]
    [Group.IsSolvable S] (f : Y →* S) (y : Y) : f y = 1 := by
  have h : f y ∈ f.range := ⟨y, rfl⟩
  rwa [range_eq_bot_of_perfect (commutator_eq_top_of_perfect hY), Subgroup.mem_bot] at h

theorem eq_bot_of_perfect_of_le {Y H : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hYH : Y ≤ H)
    [Group.IsSolvable H] : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have h := congrArg Subtype.val (map_eq_one_of_perfect hY (Subgroup.inclusion hYH) ⟨y, hy⟩)
  exact Subgroup.mem_bot.mpr h

theorem perfCentral_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (h : PerfCentral H) :
    PerfCentral G := by
  intro U Y hU hY hYU
  have h1 : ⁅U.map e.toMonoidHom, Y.map e.toMonoidHom⁆ = ⊥ := by
    refine h _ _ (hU.map _) ?_ ?_
    · rw [← Subgroup.map_commutator, hY]
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hYU
  rwa [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1

theorem commutator_eq_bot_of_card_le_four {U Y : Subgroup G} [Finite U] (hU : Nat.card U ≤ 4)
    (hY : ⁅Y, Y⁆ = Y) (hYU : Y ≤ normalizer (U : Set G)) : ⁅U, Y⁆ = ⊥ := by
  have hUN : U ≤ normalizer (U : Set G) := le_normalizer
  set V := U.subgroupOf (normalizer (U : Set G))
  have : V.Normal := normal_in_normalizer
  have eV := Subgroup.subgroupOfEquivOfLe hUN
  have : Finite V := Finite.of_equiv _ eV.toEquiv.symm
  have hinj : Function.Injective (MulAut.toPerm V) := fun a b h =>
    MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm V => e x) h
  have : Group.IsSolvable (Equiv.Perm V) :=
    Equiv.Perm.isSolvable (by rwa [Nat.card_congr eV.toEquiv])
  have : Group.IsSolvable (MulAut V) := Group.isSolvable_of_isSolvable_injective hinj
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := map_eq_one_of_perfect hY ((MulAut.conjNormal (H := V)).comp (inclusion hYU)) ⟨y, hy⟩
  have h2 := congrArg (fun φ : MulAut V => ((φ ⟨⟨u, hUN hu⟩, hu⟩ : normalizer (U : Set G)) : G)) h
  simp only [MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply, coe_mul, coe_inv,
    coe_inclusion] at h2
  calc y * u = y * u * y⁻¹ * y := by group
    _ = u * y := by rw [h2]

theorem center_eq_bot_of_perfect {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : commutator K = ⊤) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    have hc : commutator K = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have hx' : x ∈ commutator K := hK ▸ Subgroup.mem_top x
    rw [hc, Subgroup.mem_bot] at hx'
    exact hx hx'

theorem perfCentral_quot_of_mulEquiv {K X : Type*} [Group K] [Group X] [IsSimpleGroup X]
    (hK : CFSG.IsQuasisimple K) (e : K ≃* X) (hX : PerfCentral X) :
    PerfCentral (K ⧸ center K) := by
  have : IsSimpleGroup K := e.isSimpleGroup
  have hc : center K = ⊥ := center_eq_bot_of_perfect hK.1.commutator_eq_top
  exact perfCentral_of_mulEquiv
    (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e) hX

end CFSG.Quasithin.H13.Ch4.E443.F4411

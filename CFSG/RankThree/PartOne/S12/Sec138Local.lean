module

public import CFSG.RankThree.PartOne.S12.Sec138141
public import CFSG.RankThree.PartOne.S12.InputsFischer
import CFSG.RankThree.PartOne.S12.TerminalWeylPerm

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7 (localSet)

@[expose] def ThreeTranspD (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, orderOf (s * t) ≤ 3

@[expose] def TransitiveD (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E,
    ∃ x ∈ reflectionGroup p E, x * s * x⁻¹ = t

@[expose] def LocalSThree (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∀ t ∈ reflectionSet p E,
    Nonempty (↥(Subgroup.closure {s : MulAut E | s ∈ reflectionSet p E ∧ s * t = t * s ∧ s ≠ t})
      ≃* Equiv.Perm (Fin 3))

@[expose] def ThreeCoreCentral (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  CFSG.pCore 3 ↥(reflectionGroup p E) ≤ Subgroup.center ↥(reflectionGroup p E)

@[expose] def Node136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → ¬ RowModel p L 10

@[expose] def Node138I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
      ¬ (RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11) ∧
        ¬ (RowModel p L 12 ∧ RowWeylIso E (torusImage E L) 12)

@[expose] def Node137 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 9 → ThreeTranspD p E

@[expose] def Node138Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 9 → ThreeTranspD p E →
      TransitiveD p E

@[expose] def Node138II : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 9 → ThreeTranspD p E →
    TransitiveD p E → LocalSThree p E ∧ ThreeCoreCentral p E

namespace Sec138Local

open Equiv

theorem swap_structure {X : Type} [Group X] {D : Set X} (ψ : X ≃* Perm (Fin 5))
    (hconj : ∀ g : X, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hord : ∀ x ∈ D, orderOf x = 2)
    (hgen : Subgroup.closure D = ⊤) (htrans : ∀ d ∈ D, ∀ e ∈ D, ∃ g : X, g * d * g⁻¹ = e)
    (hne : D.Nonempty) :
    (∀ x ∈ D, (ψ x).IsSwap) ∧ ∀ σ : Perm (Fin 5), σ.IsSwap → ∃ x ∈ D, ψ x = σ := by
  have hsgn : ∀ x ∈ D, Perm.sign (ψ x) = -1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, htne⟩ := hcon
    have ht1 : Perm.sign (ψ t) = 1 := (Int.units_eq_one_or _).resolve_right htne
    have hall : ∀ x ∈ D, Perm.sign (ψ x) = 1 := by
      intro x hx
      obtain ⟨g, hg⟩ := htrans t ht x hx
      rw [← hg]
      simp only [map_mul, map_inv, ht1]
      simp
    have htop : ∀ y : X, Perm.sign (ψ y) = 1 := by
      intro y
      have hy : y ∈ Subgroup.closure D := by
        rw [hgen]
        trivial
      induction hy using Subgroup.closure_induction with
      | mem x hx => exact hall x hx
      | one => simp
      | mul x y _ _ hx hy => simp [map_mul, hx, hy]
      | inv x _ hx => simp [hx]
    have h := htop (ψ.symm (swap 0 1))
    rw [MulEquiv.apply_symm_apply, Perm.sign_swap (by decide)] at h
    exact absurd h (by decide)
  have hswap : ∀ x ∈ D, (ψ x).IsSwap := by
    intro x hx
    have h2 : x ^ 2 = 1 := by
      rw [← hord x hx]
      exact pow_orderOf_eq_one x
    have h3 : ψ x * ψ x = 1 := by
      rw [← map_mul, ← pow_two, h2, map_one]
    exact TerminalPerm.isSwap_of_odd_involution (ψ x) h3 (hsgn x hx)
  refine ⟨hswap, fun σ hσ => ?_⟩
  obtain ⟨t0, ht0⟩ := hne
  obtain ⟨h, hh⟩ := TerminalPerm.swap_conj_swap (ψ t0) σ (hswap t0 ht0) hσ
  refine ⟨ψ.symm h * t0 * (ψ.symm h)⁻¹, hconj _ t0 ht0, ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hh

end Sec138Local

theorem node138Struct_of_local (hF : InFischer44) (h136 : Node136) (h138I : Node138I)
    (h137 : Node137) (h138T : Node138Trans) (h138II : Node138II) : Node138Struct := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA
  have hp : p.Prime := h.prime
  obtain ⟨hclosure, r, hr1, hr12, hmodel, hweyl, hr8, hr9⟩ := hF12.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hcard : Nat.card E = p ^ 4 := hr9 hr9'
  have hnot10 := h136 G p A c L E h hF12 hF13 hT hEA
  obtain ⟨hnot11, hnot12⟩ := h138I G p A c L E h hF12 hF13 hT hEA
  have hr : r = 9 := by
    by_contra hne9
    have h10 : r = 10 ∨ r = 11 ∨ r = 12 := by omega
    rcases h10 with rfl | rfl | rfl
    · exact hnot10 hmodel
    · exact hnot11 ⟨hmodel, hweyl⟩
    · exact hnot12 ⟨hmodel, hweyl⟩
  subst hr
  have hT3 := h137 G p A c L E h hF12 hF13 hT hEA hmodel
  have hTr := h138T G p A c L E h hF12 hF13 hT hEA hmodel hT3
  obtain ⟨hLoc, hCore⟩ := h138II G p A c L E h hF12 hF13 hT hEA hmodel hT3 hTr
  have hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 4)) := hweyl
  have hL24 : Nat.card (torusImage E L) = 24 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hne : ∃ t ∈ reflectionSet p E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    rw [hempty, Subgroup.closure_empty] at hclosure
    rw [hclosure, Subgroup.card_bot] at hL24
    omega
  obtain ⟨d0, hd0D, -⟩ := hne
  have hLX : torusImage E L ≤ reflectionGroup p E := by
    calc torusImage E L = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set _)) :=
          hclosure
      _ ≤ reflectionGroup p E := Subgroup.closure_mono Set.inter_subset_left
  let D' : Set ↥(reflectionGroup p E) := {x | (x : MulAut E) ∈ reflectionSet p E}
  have hD'mem : ∀ t (ht : t ∈ reflectionSet p E),
      (⟨t, Subgroup.subset_closure ht⟩ : ↥(reflectionGroup p E)) ∈ D' := fun t ht => ht
  have hconj : ∀ g : ↥(reflectionGroup p E), ∀ x ∈ D', g * x * g⁻¹ ∈ D' := fun g x hx =>
    WeylIso.conj_mem_reflectionSet_of_weyl hp (WeylIso.closure_le_weyl g.2) hx
  have hord : ∀ x ∈ D', orderOf x = 2 := fun x hx => by
    rw [← Subgroup.orderOf_coe]
    exact hx.1.1
  have hle3 : ∀ x ∈ D', ∀ y ∈ D', orderOf (x * y) ≤ 3 := fun x hx y hy => by
    rw [← Subgroup.orderOf_coe]
    exact hT3 _ hx _ hy
  have hgen : Subgroup.closure D' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    change x ∈ Subgroup.closure (reflectionSet p E) at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hD'mem x hx)
    | one => exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => exact Subgroup.inv_mem _ ih
  have hthree : IsThreeTranspositions D' :=
    ⟨⟨hconj, hord, hgen, fun x hx y hy => (hle3 x hx y hy).trans (by norm_num),
      fun x hx y hy h4 => absurd h4 (by have := hle3 x hx y hy; omega)⟩, hle3⟩
  have htrans : ∀ d ∈ D', ∀ e ∈ D', ∃ g : ↥(reflectionGroup p E), g * d * g⁻¹ = e := by
    intro d hd e he
    obtain ⟨x, hx, hxe⟩ := hTr _ hd _ he
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hdD' : (⟨d0, Subgroup.subset_closure hd0D⟩ : ↥(reflectionGroup p E)) ∈ D' := hd0D
  have hlocal : Nonempty (↥(Subgroup.closure (localSet D'
      (⟨d0, Subgroup.subset_closure hd0D⟩ : ↥(reflectionGroup p E)))) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := hLoc d0 hd0D
    have himage : (reflectionGroup p E).subtype '' localSet D'
        (⟨d0, Subgroup.subset_closure hd0D⟩ : ↥(reflectionGroup p E)) =
        {s : MulAut E | s ∈ reflectionSet p E ∧ s * d0 = d0 * s ∧ s ≠ d0} := by
      ext s
      constructor
      · rintro ⟨x, ⟨hx, hcomm, hne⟩, rfl⟩
        exact ⟨hx, congrArg Subtype.val hcomm, fun h => hne (Subtype.ext h)⟩
      · rintro ⟨hs, hcomm, hne⟩
        exact ⟨⟨s, Subgroup.subset_closure hs⟩,
          ⟨hs, Subtype.ext hcomm, fun h => hne (congrArg Subtype.val h)⟩, rfl⟩
    have hmap : (Subgroup.closure (localSet D'
        (⟨d0, Subgroup.subset_closure hd0D⟩ : ↥(reflectionGroup p E)))).map
          (reflectionGroup p E).subtype =
        Subgroup.closure {s : MulAut E | s ∈ reflectionSet p E ∧ s * d0 = d0 * s ∧ s ≠ d0} := by
      rw [MonoidHom.map_closure, himage]
    exact ⟨(Subgroup.equivMapOfInjective _ (reflectionGroup p E).subtype
      (reflectionGroup p E).subtype_injective).trans ((MulEquiv.subgroupCongr hmap).trans e)⟩
  have hS5 : Nonempty (↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)) := by
    rcases hF ↥(reflectionGroup p E) D' hthree htrans _ hdD' 3 le_rfl (by norm_num) hlocal with
      h5 | ⟨-, hnc⟩
    · exact h5
    · exact absurd hCore hnc
  obtain ⟨ψ⟩ := hS5
  obtain ⟨hswap, hsurj⟩ := Sec138Local.swap_structure ψ hconj hord hgen htrans ⟨_, hdD'⟩
  have hS : Nat.card (((torusImage E L).subgroupOf (reflectionGroup p E)).map ψ.toMonoidHom) =
      24 := by
    rw [Subgroup.card_map_of_injective ψ.injective, ← hL24]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
  obtain ⟨k, hk⟩ := TerminalPerm.exists_fixed_point_of_card_24 _ hS
  refine ⟨hmodel, hweyl, hcard, ⟨⟨ψ, fun t ht => hswap _ (hD'mem t ht), fun σ hσ => ?_, k,
    fun x hx => ?_⟩⟩⟩
  · obtain ⟨y, hy, hyσ⟩ := hsurj σ hσ
    exact ⟨y, hy, hyσ⟩
  · refine ⟨hLX hx, hk _ ?_⟩
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom (Subgroup.mem_subgroupOf.2 hx)

end CFSG.RankThree.PartOne

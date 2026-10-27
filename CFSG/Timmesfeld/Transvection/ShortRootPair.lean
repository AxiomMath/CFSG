module

public import CFSG.Timmesfeld.Transvection.ShortRoot
public import CFSG.Timmesfeld.Transvection.ShortRootField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem conjSub_lineGroup_of_mem_lineStab {A B : Subgroup G} {g : G} (hg : g ∈ lineStab Δ A B) :
    conjSub (lineGroup Δ A B) g = lineGroup Δ A B := by
  have key : ∀ {g : G}, g ∈ lineStab Δ A B → conjSub (lineGroup Δ A B) g ≤ lineGroup Δ A B := by
    intro g hg
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun C hC => ?_)
    exact Subgroup.map_le_iff_le_comap.1 (le_lineGroup ((hg C).2 hC))
  refine le_antisymm (key hg) ?_
  have h := key (Subgroup.inv_mem _ hg)
  intro x hx
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ lineGroup Δ A B := h (conj_mem_conjSub g⁻¹ hx)
  have : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
  rw [this]
  exact conj_mem_conjSub g hx'

namespace PairFrame

variable {A E D E' : Subgroup G} (F : PairFrame Δ A E D E')
include F

theorem noIsolated (hR : IsRootClass Δ) : NoIsolated Δ := by
  obtain ⟨A₀, hA₀⟩ := hR.conj_class
  intro B hB
  have hA : A ∈ Set.range (conjSub A₀) := hA₀ ▸ F.memA
  have hB' : B ∈ Set.range (conjSub A₀) := hA₀ ▸ hB
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨g', rfl⟩ := hB'
  refine ⟨conjSub E (g' * g⁻¹), hR.conjSub_mem F.memE _, ?_⟩
  have h1 := F.oppA.symm.conj (g' * g⁻¹)
  rwa [conjSub_mul, ← conjSub_mul A₀ g⁻¹ g, inv_mul_cancel, conjSub_one] at h1

theorem commutator_mem_of_mem_shortRootGroup [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) {x u : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hu : u ∈ shortRootGroup Δ A E D E') : ⁅x, u⁆ ∈ D := by
  have hiso := F.noIsolated hΔ.root
  have hAD : ⁅x, u⁆ ∈ lineGroup Δ A D := by
    have h1 : x * u * x⁻¹ ∈ lineGroup Δ A D := by
      have := conj_mem_conjSub x hu.1.1
      rwa [conjSub_lineGroup_of_mem_lineStab hx.1.2] at this
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hu.1.1)
  have hED : ⁅x, u⁆ ∈ lineGroup Δ E D := by
    have h1 : u * x⁻¹ * u⁻¹ ∈ lineGroup Δ E D := by
      have := conj_mem_conjSub u (Subgroup.inv_mem _ hx.1.1)
      rwa [conjSub_lineGroup_of_mem_lineStab hu.1.2] at this
    rw [commutatorElement_def, show x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ hx.1.1 h1
  obtain ⟨k, φ, h, μ, hh, hμ, hμ1⟩ := exists_sl2Coords_torus hΔ.root F.memA F.memE F.oppA hq
  have hcA : ∀ a ∈ A, Commute ⁅x, u⁆ a := fun a ha =>
    commute_of_mem_lineGroup hΔ F.memA F.memD F.commuting_AD hAD
      (le_lineGroup (left_mem_lineOf F.memA) ha)
  have hcE : ∀ e ∈ E, Commute ⁅x, u⁆ e := fun e he =>
    commute_of_mem_lineGroup hΔ F.memE F.memD F.commuting_ED hED
      (le_lineGroup (left_mem_lineOf F.memE) he)
  exact (commute_lineGroup_iff φ hh hμ hΔ hiso hpts F.memA F.memE F.memD F.oppA F.commuting_AD
    F.commuting_ED F.ne_AD.symm hq hμ1 hAD).1 (commute_of_mem_sup_of_commute hcA hcE hh)


theorem eq_one_of_commutator_mem_shortRootGroup [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hX : ShortRootFieldHyp Δ A E D E') {x a : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (ha : a ∈ A) (ha1 : a ≠ 1)
    (h : ⁅x, a⁆ ∈ shortRootGroup Δ A E D E') : x = 1 := by
  by_contra hx1
  obtain ⟨hC, hCA, hCD, -⟩ := hX.1 x hx hx1
  set C := conjSub A x with hCdef
  have hR := hΔ.root
  have hAD := F.ne_AD
  have hcAD := F.commuting_AD
  have hCE' : C ≠ E' := by
    intro h'
    have := (commuting_of_mem_lineOf' hΔ F.memA F.memD hcAD hC).2
    rw [h'] at this
    exact F.oppD.not_commuting (hR.ne_bot _ F.memE') this.symm
  have hopp : Opposite C E' := by
    rcases hΔ.commuting_or_opposite hC.1 F.memE' hCE' with hc | ho
    · exfalso
      have := commuting_of_commuting_of_mem_lineOf hΔ hpts F.memA F.memD hAD hcAD
        (left_mem_lineOf F.memA) hC hCA.symm (right_mem_lineOf F.memD) F.memE'
        F.commuting_AE'.symm hc.symm
      exact F.oppD.not_commuting (hR.ne_bot _ F.memE') this
    · exact ho
  set c := x * a * x⁻¹ with hc
  have hcC : c ∈ C := conj_mem_conjSub x ha
  have hc1 : c ≠ 1 := by
    intro h1
    apply ha1
    calc a = x⁻¹ * c * x := by rw [hc]; group
      _ = 1 := by rw [h1]; group
  have hcstab : c ∈ lineStab Δ A E' := by
    have h1 : c = ⁅x, a⁆ * a := by
      rw [hc, commutatorElement_def]
      group
    rw [h1]
    refine Subgroup.mul_mem _ h.2 ?_
    exact mem_lineStab_of_commute hR (fun a' ha' => hR.commuting_self F.memA a ha a' ha')
      (fun e he => F.commuting_AE' a ha e he)
  have hE'c : conjSub E' c ∈ lineOf Δ A E' := (hcstab E').2 (right_mem_lineOf F.memE')
  have hcomm : Commuting E' (conjSub E' c) :=
    (commuting_of_mem_lineOf' hΔ F.memA F.memE' F.commuting_AE' hE'c).2
  have hne : conjSub E' c ≠ E' := by
    intro h'
    obtain ⟨e, he, -, he'⟩ := hopp.2.1 c hcC hc1
    rw [h'] at he'
    apply hopp.1
    calc C = conjSub (conjSub C e) e⁻¹ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      _ = E' := by rw [he', conjSub_of_mem (E'.inv_mem he)]
  have hopp' := opposite_conjSub_of_ne hΔ hC.1 hopp (Subgroup.mem_sup_right hcC) hne
  exact hopp'.not_commuting (hR.ne_bot _ F.memE') hcomm

end PairFrame

end CFSG.Timmesfeld.Transvection

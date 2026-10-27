module

public import CFSG.Timmesfeld.Transvection.ShortRoot
import CFSG.Timmesfeld.Transvection.ShortRootReg
import CFSG.Timmesfeld.Transvection.ShortRootPair
import CFSG.GroupTheory.Commutator.ScalingInvariant
import CFSG.GroupTheory.FixedPointFreeCommutator

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem mem_lineStab_of_conjSub_eq (hR : IsRootClass Δ) {A B : Subgroup G} {g : G}
    (hgA : conjSub A g = A) (hgB : conjSub B g = B) : g ∈ lineStab Δ A B := by
  intro C
  simpa [hgA, hgB] using conjSub_mem_lineOf_conjSub_iff (Δ := Δ) (A := A) (B := B) (D := C) hR g

theorem mem_lineStab_of_mem_sup_of_conjSub_eq [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) {A E C : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hEA : Opposite E A) (hC : C ∈ Δ) (hCA : C ≠ A) (hAC : Commuting A C)
    {t : G} (ht : t ∈ A ⊔ E) (htA : conjSub A t = A) : t ∈ lineStab Δ A C := by
  obtain ⟨D, hDl, hED⟩ := hlines A hA C hC (Ne.symm hCA) hAC E hE
  have hDA : D ≠ A := fun hDA => ModelRank.not_commuting_of_opposite hEA (hDA ▸ hED)
  have hAD : Commuting A D := (commuting_of_mem_lineOf' hΔ hA hC hAC hDl).1
  have htD : conjSub D t = D :=
    conjSub_of_forall_commute fun d hd => (commute_of_mem_sup_left hAD hED ht hd).symm
  have hl : lineOf Δ A D = lineOf Δ A C :=
    lineOf_eq_of_mem_of_ne hΔ hpts hA hC (Ne.symm hCA) hAC hDl hDA
  intro D'
  rw [← hl]
  exact mem_lineStab_iff.1 (mem_lineStab_of_conjSub_eq hΔ.root htA htD) D'

theorem le_lineStab_of_forall_eq_commutatorElement [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) {A E C : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hEA : Opposite E A) (hC : C ∈ Δ) (hCA : C ≠ A) (hAC : Commuting A C)
    {t : G} (ht : t ∈ A ⊔ E) (htA : conjSub A t = A) {K : Subgroup G}
    (hKA : ∀ y ∈ K, conjSub A y = A) (hK : ∀ x ∈ K, ∃ y ∈ K, x = ⁅y, t⁆) :
    K ≤ lineStab Δ A C := by
  refine CFSG.GroupTheory.le_of_forall_eq_commutatorElement (S := lineStab Δ A C) (g := t)
    (mem_lineStab_of_mem_sup_of_conjSub_eq hΔ hpts hlines hA hE hEA hC hCA hAC ht htA) ?_ hK
  intro y hy
  have hKA' : conjSub A y⁻¹ = A := by
    rw [conjSub_eq_self_iff]
    exact (Subgroup.normalizer (A : Set G)).inv_mem (conjSub_eq_self_iff.1 (hKA y hy))
  have hEA' : Opposite (conjSub E y) A := by
    have h := hEA.conj y
    rwa [hKA y hy] at h
  have ht' : y * t * y⁻¹ ∈ A ⊔ conjSub E y := by
    have h := conj_mem_conjSub y ht
    rwa [conjSub_sup_eq_sup, hKA y hy] at h
  have htA' : conjSub A (y * t * y⁻¹) = A := by
    calc conjSub A (y * t * y⁻¹) = conjSub (conjSub A y⁻¹) (y * t) := by rw [conjSub_mul]
      _ = conjSub A (y * t) := by rw [hKA']
      _ = conjSub (conjSub A t) y := by rw [conjSub_mul]
      _ = A := by rw [htA, hKA y hy]
  exact mem_lineStab_of_mem_sup_of_conjSub_eq hΔ hpts hlines hA
    (hΔ.root.conjSub_mem hE y) hEA' hC hCA hAC ht' htA'

theorem PairFrame.shortRootGroup_le_lineStab [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) {C : Subgroup G} (hC : C ∈ Δ)
    (hCA : C ≠ A) (hAC : Commuting A C) : shortRootGroup Δ A E D E' ≤ lineStab Δ A C := by
  obtain ⟨k, φ, h, μ, hh, hμ, hμ1⟩ := exists_sl2Coords_torus hΔ.root P.memA P.memE P.oppA hq
  have hiso : NoIsolated Δ := P.noIsolated hΔ.root
  have hN : h ∈ Subgroup.normalizer (shortRootGroup Δ A E D E' : Set G) :=
    conjSub_eq_self_iff.1 (P.conjSub_shortRootGroup_torus hΔ.root φ hh hμ).2
  have hfree : ∀ x ∈ shortRootGroup Δ A E D E', h * x * h⁻¹ = x → x = 1 := by
    intro x hx hxfix
    have hcomm : Commute x h := by
      calc x * h = (h * x * h⁻¹) * h := by rw [hxfix]
        _ = h * x := by group
    exact (P.commute_shortRootGroup_iff hΔ hiso hpts hq φ hh hμ hμ1 hx).1 hcomm
  have hK : ∀ x ∈ shortRootGroup Δ A E D E',
      ∃ y ∈ shortRootGroup Δ A E D E', x = ⁅y, h⁆ := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ :=
      CFSG.exists_eq_conj_mul_inv_of_fixedPointFree hN hfree x⁻¹
        (T := shortRootGroup Δ A E D E') (Subgroup.inv_mem _ hx)
    refine ⟨s, hs, ?_⟩
    calc x = (x⁻¹)⁻¹ := by rw [inv_inv]
      _ = (h * s * h⁻¹ * s⁻¹)⁻¹ := by rw [hxs]
      _ = ⁅s, h⁆ := by rw [commutatorElement_def]; group
  have hKA : ∀ y ∈ shortRootGroup Δ A E D E', conjSub A y = A := fun y hy =>
    conjSub_eq_of_le_lineGroup hΔ P.memA P.memD P.commuting_AD hy.1.1
      (le_lineGroup (left_mem_lineOf P.memA))
  exact le_lineStab_of_forall_eq_commutatorElement hΔ hpts hlines P.memA P.memE P.oppA hC hCA
    hAC hh (φ.conjSub_eq_of_mat_eq_diagElt hh hμ).1 hKA hK

end CFSG.Timmesfeld.Transvection

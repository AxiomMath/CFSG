module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUU3Mod
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Setup CFSG.LinearAlgebra.CoprimeActions

theorem exists_unitary_of_isSU3 {X : Type} [Group X] {n : ℕ} (h : IsSU3 X n) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData 2 n K),
      Nonempty (X ⧸ center X ≃* unitaryPSU hU 3) := by
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (X ⧸ center X) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel h.2 (by decide)
  obtain ⟨⟨-, hf1, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  refine ⟨?_, K, inferInstance, hU, ⟨e.trans (unitaryPSUEquiv hU (by norm_num)).symm⟩⟩
  by_contra hlt
  have : n = 1 := by omega
  subst this
  exact h3 (by norm_num)

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Bounds

set_option linter.unusedSectionVars false

theorem two_mul_le_of_commute [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {L : Subgroup G} (hLn : L.Normal)
    (hq : CFSG.Open.IsQuasisimple ↥L) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    (hU : UnitaryFieldData 2 n K) (β : ↥L ⧸ center ↥L ≃* unitaryPSU hU 3) {t : G} (ht1 : t ≠ 1)
    (hc : ∀ x ∈ L, t * x = x * t) :
    2 * n ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
  set W : Submodule (ZMod 2) V := LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1) with hWdef
  have hWinv : ∀ c ∈ L, ∀ w ∈ W, ρ c w ∈ W := by
    rintro c hcL _ ⟨v, rfl⟩
    refine ⟨ρ c v, ?_⟩
    have h1 : ρ t (ρ c v) = ρ c (ρ t v) := by
      rw [← Module.End.mul_apply, ← map_mul, hc c hcL, map_mul, Module.End.mul_apply]
    simp [h1]
  let R : Subrepresentation (ρ.comp L.subtype) := ⟨W, fun g v hv => hWinv g g.2 v hv⟩
  have hmov : ∃ g, R.toRepresentation g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hfix : ∀ y ∈ L, ∀ w ∈ W, ρ y w = w := fun y hy w hw => by
      have := congrArg (fun T => ((T ⟨w, hw⟩ : W) : V)) (hcon ⟨y, hy⟩)
      exact this
    have hL1 : L ≠ ⊥ := by
      haveI := hq.2
      haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (center ↥L)).nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
    have htop := CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed.commSpace_eq_top_of_normal
      hρ hirr hLn hL1
    have hker : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρ L ≤
        LinearMap.ker ((ρ t : V →ₗ[ZMod 2] V) - 1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, hy, v, rfl⟩
      have h1 : ρ t (ρ y v) = ρ y (ρ t v) := by
        rw [← Module.End.mul_apply, ← map_mul, hc y hy, map_mul, Module.End.mul_apply]
      have hw : ρ t v - v ∈ W := ⟨v, by simp⟩
      have h2 : ρ y (ρ t v - v) = ρ t v - v := hfix y hy _ hw
      rw [map_sub, sub_eq_iff_eq_add] at h2
      show ((ρ t : V →ₗ[ZMod 2] V) - 1) (ρ y v - v) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, h2]
      abel
    apply ht1
    apply hρ
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker ((ρ t : V →ₗ[ZMod 2] V) - 1) := hker (by rw [htop]; exact Submodule.mem_top)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  exact two_mul_le_finrank hq hn hU β R.toRepresentation hmov

theorem two_mul_le_of_not_commute [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {L : Subgroup G} (hLn : L.Normal)
    (hq : CFSG.Open.IsQuasisimple ↥L) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    (hU : UnitaryFieldData 2 n K) (β : ↥L ⧸ center ↥L ≃* unitaryPSU hU 3) {t : G} (htt : t * t = 1)
    (hc : ∃ x ∈ L, t * x ≠ x * t) :
    2 * n ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
  haveI := hLn
  let τ : MulAut ↥L := MulAut.conjNormal t
  have hτ : ∃ g : ↥L, τ g ≠ g := by
    obtain ⟨x, hx, hxt⟩ := hc
    refine ⟨⟨x, hx⟩, fun h => hxt ?_⟩
    have h' : t * x * t⁻¹ = x := congrArg Subtype.val h
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h']
  let s : V ≃ₗ[ZMod 2] V := X7b.repLinEquiv ρ t
  have hss : ∀ v, s (s v) = v := fun v => by
    show ρ t (ρ t v) = v
    rw [← Module.End.mul_apply, ← map_mul, htt, map_one, Module.End.one_apply]
  have hs : ∀ (g : ↥L) (v : V), s ((ρ.comp L.subtype) g v) = (ρ.comp L.subtype) (τ g) (s v) := by
    intro g v
    show ρ t (ρ (g : G) v) = ρ (t * (g : G) * t⁻¹) (ρ t v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have hnt : ∃ g : ↥L, (ρ.comp L.subtype) g ≠ 1 := by
    haveI := hq.2
    haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (center ↥L)).nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    refine ⟨x, fun h1 => hx ?_⟩
    change ρ (x : G) = 1 at h1
    exact Subtype.ext (hρ (h1.trans (map_one ρ).symm))
  have h := X7b.gamma_reduction (F := ZMod 2) (G := ↥L) ⟨hq.1⟩ τ (2 * n)
    (fun ρ' s' hss' hs' hgs hW hnt' =>
      two_mul_le_of_gsIrreducible hq hn hU β τ hτ ρ' s' hss' hs' hgs hW hnt')
    (ρ.comp L.subtype) s hss hs hnt
  have hrk := LinearMap.finrank_range_add_finrank_ker ((ρ t : V →ₗ[ZMod 2] V) - 1)
  have heq : s.toLinearMap - 1 = (ρ t : V →ₗ[ZMod 2] V) - 1 := rfl
  rw [heq] at h
  omega

theorem su3_lt_mGV [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L : Subgroup G} (hLn : L.Normal) {n : ℕ} (hSU : IsSU3 ↥L n) :
    n + 1 < F05.mGV ρ := by
  obtain ⟨hn, K, _, hU, ⟨β⟩⟩ := exists_unitary_of_isSU3 hSU
  have hev : ∃ t : G, orderOf t = 2 := by
    obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_unitary hn hU β
    exact ⟨x, by rw [Subgroup.orderOf_coe, hx]⟩
  have key : ∀ t : G, orderOf t = 2 →
      n + 2 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - 1)) := by
    intro t ht
    obtain ⟨htt, ht1⟩ := Excl147.mul_self_and_ne_one ht
    by_cases hc : ∀ x ∈ L, t * x = x * t
    · have := two_mul_le_of_commute ρ hρ hirr hLn hSU.1 hn hU β ht1 hc
      omega
    · push Not at hc
      have := two_mul_le_of_not_commute ρ hρ hLn hSU.1 hn hU β htt hc
      omega
  have := Excl147.le_mGV ρ (k := n + 2) hev fun t ht => by
    rw [Excl147.finrank_quotient_fixSub_eq ρ ht,
      InvolutionDimensionBounds.commSpace_zpowers_eq_range ρ t
        (orderOf_pos_iff.mp (by omega))]
    exact key t ht
  omega

end Bounds

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

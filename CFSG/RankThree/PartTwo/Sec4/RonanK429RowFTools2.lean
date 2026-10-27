module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem noCfgS429_of_model_e27 {S T : Type} [Group S] [Group T] [Finite S] (e : S ≃* T)
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → ∀ x ∈ E, x ≠ 1 →
      Good429 (Subgroup.centralizer ({x} : Set T))) :
    NoCfgS429 S := by
  intro A σ K hc
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  have hin : ∀ τ : MulAut S, τ ^ 3 = 1 → τ ∈ (MulAut.conj : S →* MulAut S).range :=
    fun τ h3 => cubeInner_of_not_three_dvd_card_outer hout τ h3
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  obtain ⟨s, rfl⟩ := hin _ h3
  have hs1 : s ≠ 1 := fun h1 => hc.ne_one (by rw [h1, map_one])
  set E := A.comap (MulAut.conj : S →* MulAut S) with hEdef
  have hAle : A ≤ (MulAut.conj : S →* MulAut S).range := fun a ha => hin a (hc.isE27.1.2 a ha)
  have hEA : E.map (MulAut.conj : S →* MulAut S) = A := Subgroup.map_comap_eq_self hAle
  have hE27 : Nat.card E = 27 := by
    rw [← hc.isE27.2, ← hEA, Subgroup.card_map_of_injective hconj]
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
    · have := hc.isE27.1.1.is_comm.comm ⟨MulAut.conj (x : S), x.2⟩ ⟨MulAut.conj (y : S), y.2⟩
      have h' := congrArg Subtype.val this
      simpa only [Subgroup.coe_mul, map_mul] using h'
    · rw [map_pow, map_one]
      exact hc.isE27.1.2 _ hx
  have hsE : s ∈ E := hc.mem
  have hgood : Good429 (Subgroup.centralizer ({s} : Set S)) := by
    refine Good429.of_mulEquiv_centralizer e (h (E.map e.toMonoidHom)
      (Res423Two.isElemAbelian_map' _ hEab) ?_ (e s) ⟨s, hsE, rfl⟩ ?_)
    · rw [Subgroup.card_map_of_injective e.injective, hE27]
    · intro h1
      exact hs1 (e.injective (by rw [h1, map_one]))
  have hfix : autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) := autFix_conj s
  have hKle : K ≤ Subgroup.centralizer ({s} : Set S) := hfix ▸ hc.le_autFix
  have hsn : (K.subgroupOf (Subgroup.centralizer ({s} : Set S))).IsSubnormal := by
    have h' := hc.isSubnormal
    rw [hfix] at h'
    exact h'
  exact hgood K hKle hc.isPerfect hsn hc.isType

end CFSG.RankThree.PartTwo.Sec4.RonanK429F

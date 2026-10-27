module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63L2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open Subgroup

theorem asch1413_normalizes {Q : Type} [Group Q] [Finite Q] {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V}
    (hρ : Function.Injective ρ) {G₀ X A : Subgroup Q} (hX : IsComponentOf X G₀) {z : Q}
    (hz2 : orderOf z = 2) (hzX : z ∈ X) (hZX : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) ↔ x ∈ zpowers z)
    (hAG : A ≤ G₀) (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (X : Set Q) = ⊥) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hmod : F6.IsL2 p 1 (↥X ⧸ Subgroup.center ↥X)) :
    A ≤ normalizer (X : Set Q) := by
  intro a ha
  by_cases ha1 : a = 1
  · subst ha1
    exact Subgroup.one_mem _
  · have ha2 : a ^ 2 = 1 := hAe.2 a ha
    let Q' := ↥G₀
    haveI : Finite Q' := Subtype.finite
    let ρ' : Q' →* MulAut V := ρ.comp G₀.subtype
    have hρ' : Function.Injective ρ' := fun x y h => G₀.subtype_injective (hρ h)
    let X' : Subgroup Q' := X.subgroupOf G₀
    let A' : Subgroup Q' := A.subgroupOf G₀
    let a' : Q' := ⟨a, hAG ha⟩
    let e : ↥X' ≃* ↥X := Subgroup.subgroupOfEquivOfLe hX.1
    have hcomp' : IsComponentOf X' ⊤ := by
      refine ⟨le_top, ?_, ?_⟩
      · exact CFSG.Open.IsSubnormal.of_mathlib (CFSG.Open.IsSubnormal.subgroupOf hX.2.1)
      · exact CFSG.Open.IsQuasisimple.of_mulEquiv e hX.2.2
    have hA' : Nat.card A' = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv, hA]
    have hAe' : IsElemAbelian 2 A' := by
      refine ⟨?_, ?_⟩
      · refine IsMulCommutative.of_comm (fun x y => ?_)
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : A => (z : Q))
          (hAe.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
      · intro x hx
        apply Subtype.ext
        exact hAe.2 x.1 hx
    have ha' : a' ∈ A' := ha
    have hq' : IsQuadraticOn ρ' A' := by
      intro x hx y hy v
      exact hq x.1 hx y.1 hy v
    have hord' : orderOf a' = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        exact ha2
      · intro h
        exact ha1 (Subtype.ext_iff.mp h)
    have hAC' : A' ⊓ centralizer (X' : Set Q') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      have hxA : (x : Q) ∈ A := hx.1
      have hxCent : (x : Q) ∈ centralizer (X : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (⟨y, hX.1 hy⟩ : Q') ∈ X' := hy
        exact Subtype.ext_iff.mp ((Subgroup.mem_centralizer_iff.mp hx.2) ⟨y, hX.1 hy⟩ hy')
      exact Subgroup.mem_bot.mp (hAC ▸ ⟨hxA, hxCent⟩)
    have hmod' : F6.IsL2 p 1 (↥X' ⧸ Subgroup.center ↥X') :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center ↥X') (Subgroup.center ↥X) e
          (Subgroup.map_center_eq e)).symm hmod
    have hp2 : p ≠ 2 := by omega
    have hp7 : 7 ≤ p ^ 1 := by
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      obtain ⟨k, hk⟩ := hpodd
      rw [pow_one]
      omega
    have hnorm := asch6_3_mem_normalizer_of_psl2
      hV hρ' hord' hcomp' hA' hAe' ha' (hq' a' ha') hAC' hp2 hp7 hmod'
    have hmem : a' ∈ (Subgroup.normalizer (X : Set Q)).subgroupOf G₀ := by
      rw [Subgroup.subgroupOf_normalizer_eq hX.1]
      exact hnorm
    have : (a' : Q) ∈ Subgroup.normalizer (X : Set Q) := Subgroup.mem_subgroupOf.mp hmem
    simpa using this

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end

module

import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.FusionDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open Subgroup

private noncomputable def w16l_autRestrict {X : Type} [Group X] {O : Subgroup X}
    (f : MulAut X) (hf : O.map (f : X →* X) = O) : MulAut O :=
  (Subgroup.equivMapOfInjective O (f : X →* X) f.injective).trans
    (MulEquiv.subgroupCongr hf)

private theorem w16l_autRestrict_coe {X : Type} [Group X] {O : Subgroup X}
    (f : MulAut X) (hf : O.map (f : X →* X) = O) (z : O) :
    (w16l_autRestrict f hf z : X) = f z := rfl

private theorem w16l_eq_of_agree_on_sup {X : Type} [Group X] {Y O : Subgroup X} [O.Normal]
    (hsup : Y ⊔ O = ⊤) {f g : MulAut X}
    (hY : ∀ y ∈ Y, f y = g y) (hO : ∀ z ∈ O, f z = g z) : f = g := by
  ext x
  have hx : x ∈ (↑(Y ⊔ O) : Set X) := by rw [hsup, Subgroup.coe_top]; trivial
  rw [Subgroup.mul_normal] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  rw [map_mul, map_mul, hY y hy, hO z hz]

theorem autRank166_dih {X : Type} [Group X] [Finite X] (Y : Subgroup X) (hY : Nat.card Y = 2)
    (hX : Y ⊔ fusionOddCore X = ⊤) (hp : ∃ p : ℕ, p.Prime ∧ Nat.card (fusionOddCore X) = p)
    (E : Subgroup (MulAut X)) (hE : IsElemAbelian 2 E) (hEY : ∀ α ∈ E, ∀ y ∈ Y, α y = y) :
    Nat.card E ≤ 2 := by
  classical
  obtain ⟨p, hpprime, hOcard⟩ := hp
  let O : Subgroup X := fusionOddCore X
  have hOcard' : Nat.card O = p := hOcard
  have hOnorm : O.Normal := fusionOddCore_normal X
  haveI : O.Normal := hOnorm
  have hX' : Y ⊔ O = ⊤ := hX
  have hchar : ∀ α : MulAut X, O.map (α : X →* X) = O := by
    intro α
    have hOddO : Odd (Nat.card O) := CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore X
    have hle : O.map (α : X →* X) ≤ O :=
      le_sSup ⟨hOnorm.map (α : X →* X) α.surjective,
        by rw [Subgroup.card_map_of_injective (K := O) α.injective]; exact hOddO⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (K := O) α.injective).symm)
  have hfinj : Function.Injective
      (fun α : E => w16l_autRestrict (α : MulAut X) (hchar α)) := by
    intro a b hab
    refine Subtype.ext ?_
    refine w16l_eq_of_agree_on_sup hX' (f := (a : MulAut X)) (g := (b : MulAut X)) ?_ ?_
    · intro y hy
      rw [hEY (a : MulAut X) a.2 y hy, hEY (b : MulAut X) b.2 y hy]
    · intro z hz
      have h := congrArg (fun β : MulAut O => (β ⟨z, hz⟩ : X)) hab
      rwa [w16l_autRestrict_coe, w16l_autRestrict_coe] at h
  have hOprime : (Nat.card O).Prime := by rw [hOcard']; exact hpprime
  haveI : Fact (Nat.card O).Prime := ⟨hOprime⟩
  haveI : IsCyclic O := isCyclic_of_prime_card (p := Nat.card O) rfl
  haveI : IsCyclic (ZMod (Nat.card O))ˣ := ZMod.isCyclic_units_prime hOprime
  let e := IsCyclic.mulAutMulEquiv O
  let φ : E → {a : (ZMod (Nat.card O))ˣ // a ^ 2 = 1} :=
    fun α => ⟨e (w16l_autRestrict (α : MulAut X) (hchar α)), by
      have hαα : (α : MulAut X) * (α : MulAut X) = 1 := by
        simpa [pow_two] using hE.2 (α : MulAut X) α.2
      have hsq : w16l_autRestrict (α : MulAut X) (hchar α) *
          w16l_autRestrict (α : MulAut X) (hchar α) = 1 := by
        ext z
        show (α : MulAut X) ((α : MulAut X) (z : X)) = (z : X)
        have h := congrArg (fun β : MulAut X => β (z : X)) hαα
        simpa using h
      rw [pow_two, ← map_mul, hsq, map_one]⟩
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply hfinj
    exact e.injective (Subtype.ext_iff.mp hab)
  have hcardS : Nat.card {a : (ZMod (Nat.card O))ˣ // a ^ 2 = 1} ≤ 2 := by
    have h := IsCyclic.card_pow_eq_one_le (α := (ZMod (Nat.card O))ˣ) (n := 2) (by norm_num)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  calc Nat.card E ≤ Nat.card {a : (ZMod (Nat.card O))ˣ // a ^ 2 = 1} :=
        Nat.card_le_card_of_injective φ hφ_inj
    _ ≤ 2 := hcardS

end CFSG.LocalAnalysis.WeakClosure81

end

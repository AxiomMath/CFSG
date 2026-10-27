module

public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.QuasithinUnique.Setup.Family CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Rank

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_not_sqt_of_inj {ι : Type} [Fintype ι] (hι : 3 ≤ Fintype.card ι) {G : Type*}
    [Group G] [Finite G] (φ : (ι → Multiplicative (ZMod 3)) →* G) (hφ : Function.Injective φ) :
    ¬ CFSG.IsStronglyQuasithin G := by
  intro hsqt
  have hk : Fintype.card ι ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm a b)
      (fun a => pow_r_domain ι 3 a) (card_pi_cyclic ι 3) φ hφ (H := ⊤) le_top
  have := CFSG.SectionRank.isStronglyQuasithin_iff.1 hsqt 3 Nat.prime_three (by norm_num)
  omega

theorem p4insporth_not_sqt_of_earank [Finite U] {ι : Type} [Fintype ι] (hι : 3 ≤ Fintype.card ι)
    (hE : EARank (K := ZMod 2) 3 ι q) {H : Subgroup (GLV U)} (hH : ⁅orthSub q, orthSub q⁆ ≤ H) :
    ¬ CFSG.IsStronglyQuasithin ↥H := by
  obtain ⟨φ, hφ, hmem⟩ := hE
  have hiso : isoGroup q = orthSub q := Subgroup.ext fun _ => Iff.rfl
  rw [hiso] at hmem
  exact p4insporth_not_sqt_of_inj hι (φ.codRestrict H fun x => hH (hmem x))
    (fun a b hab => hφ (congrArg Subtype.val hab))

theorem p4insporth_not_sqt_plus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 4 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hplus : IsPlusType (p4insporth_quad hq))
    {H : Subgroup (GLV U)} (hH : ⁅orthSub q, orthSub q⁆ ≤ H) : ¬ CFSG.IsStronglyQuasithin ↥H := by
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (p4insporth_nondegenerate_quad hf hq) hdim hplus
  have hE : EARank (K := ZMod 2) 3 (Fin (2 * (n / 2))) q := by
    refine EARank.of_isometry e.toLinearEquiv (fun v => ?_) (EARank.quadPlus Nat.prime_three
      (by rw [Nat.card_zmod]) n)
    have := e.map_app v
    rw [p4insporth_quad_apply] at this
    rw [← this, ← CFSG.LieType.Universal.Spin.coe_quadPlus]
    rfl
  exact p4insporth_not_sqt_of_earank (by simp; omega) hE hH

theorem p4insporth_not_sqt_minus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hminus : ¬ IsPlusType (p4insporth_quad hq))
    {H : Subgroup (GLV U)} (hH : ⁅orthSub q, orthSub q⁆ ≤ H) : ¬ CFSG.IsStronglyQuasithin ↥H := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType (p4insporth_nondegenerate_quad hf hq)
    (by omega) hdim hminus hirr
  have hE : EARank (K := ZMod 2) 3 (Fin (2 * ((n - 1) / 2)) ⊕ Unit) q := by
    refine EARank.of_isometry e.toLinearEquiv (fun v => ?_) (EARank.quadMinus Nat.prime_three
      (by rw [Nat.card_zmod]) n 1 1 hirr)
    have := e.map_app v
    rw [p4insporth_quad_apply] at this
    rw [← this, ← CFSG.LieType.Universal.Spin.coe_quadMinus]
    rfl
  exact p4insporth_not_sqt_of_earank (by simp; omega) hE hH

end Rank

end P4InspOrth

end G11

end CFSG.Quasithin

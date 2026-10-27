module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlRefl

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

section Unit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}

theorem qtwoLGen_of_unitaryBase (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} (hB : QTwoUnitBase p B Bs x L ψ ε) :
    L ≤ ⨆ (r : MulAut ↥Bs) (_ : r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e)
        (r' : MulAut ↥Bs) (_ : r' ∈ ggAutomizer L Bs ∧ r' ∈ ggCoxRefl M e)
        (_ : r * r' ≠ r' * r), ggRankTwoIn L Bs r r' := by
  obtain rfl : p = 3 := hB.p_eq
  have hK := hB.card_field
  have hC : ∀ a b : Fin m, a ≠ b →
      ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e := fun a b hab =>
    ggCoxRefl_of_isReflection e e' (by omega) hM β hβ
      ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) (ε (Equiv.swap a b)).2)
      (hB.refl a b hab)
  refine hB.range.symm.le.trans
    ((range_eq_iSup_coordBlockSU_three hK (by omega) ψ).le.trans ?_)
  refine iSup_le fun I => iSup_le fun hI => ?_
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hI
  have hr : ∀ s : ↥Bs, (((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹ := by
    intro s
    rw [hB.perm (Equiv.swap a b) s, Equiv.swap_inv]
  have hr' : ∀ s : ↥Bs, (((ε (Equiv.swap b c) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹ := by
    intro s
    rw [hB.perm (Equiv.swap b c) s, Equiv.swap_inv]
  have hrk := ggQTwoDUnit_rankTwoIn_eq hB.hyp hK hB.diag hab hbc hac hr hr'
  rw [hB.range] at hrk
  have hnc : ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε (Equiv.swap b c) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ≠
      ((ε (Equiv.swap b c) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
        ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    intro h
    have h1 : ε (Equiv.swap a b) * ε (Equiv.swap b c) =
        ε (Equiv.swap b c) * ε (Equiv.swap a b) := Subtype.ext h
    have h2 : Equiv.swap a b * Equiv.swap b c = Equiv.swap b c * Equiv.swap a b := by
      apply ε.injective
      rw [map_mul, map_mul]
      exact h1
    have h3 := congrArg (fun f : Equiv.Perm (Fin m) => f a) h2
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac,
      Equiv.swap_apply_left] at h3
    exact hbc h3
  rw [← hrk]
  exact le_iSup_of_le _ (le_iSup_of_le ⟨(ε (Equiv.swap a b)).2, hC a b hab⟩
    (le_iSup_of_le _ (le_iSup_of_le ⟨(ε (Equiv.swap b c)).2, hC b c hbc⟩
      (le_iSup (fun _ => _) hnc))))

end Unit

end CFSG.StandardType.QTwo

end

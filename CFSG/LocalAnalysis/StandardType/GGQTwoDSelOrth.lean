module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentActs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlRefl

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.PhanDn.QTwo

section Orth

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}

theorem qtwoLGen_of_orthChart [Fact p.Prime] (hp : p = 3) (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    (Φ : OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥L = ⊥)
    (hBs : IsElemAbelian p Bs) :
    L ≤ ⨆ (r : MulAut ↥Bs) (_ : r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e)
        (r' : MulAut ↥Bs) (_ : r' ∈ ggAutomizer L Bs ∧ r' ∈ ggCoxRefl M e)
        (_ : r * r' ≠ r' * r), ggRankTwoIn L Bs r r' := by
  refine (Φ.le_iSup_img_rank2 hF).trans ?_
  refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
  obtain ⟨ρ, hρA, hρr, hx⟩ := qtwoOrth_exists_refl_acts Φ x
  obtain ⟨ρ', hρ'A, hρ'r, hy⟩ := qtwoOrth_exists_refl_acts Φ y
  have hnc : ρ * ρ' ≠ ρ' * ρ := by
    intro h
    refine hxy (MulEquiv.ext fun f => ?_)
    obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ f) (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)
    have h1 := hx (ρ' b) _ (hy b f hb)
    have h2 := hy (ρ b) _ (hx b f hb)
    have h3 : ρ (ρ' b) = ρ' (ρ b) := by
      have := congrArg (fun a : MulAut ↥Bs => a b) h
      simpa [MulAut.mul_apply] using this
    rw [h3] at h1
    exact Φ.Δ.τ_inj (h1.symm.trans h2)
  have hC : ∀ {a : MulAut ↥Bs}, a ∈ ggAutomizer L Bs → GGIsReflection p a → a ∈ ggCoxRefl M e :=
    fun {a} haA har => by
      subst hp
      exact ggCoxRefl_of_isReflection e e' hm hM β hβ
        ((le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) haA) har
  have hrk := qtwoOrth_rankTwoIn Φ hF hZ hBs hρA hρ'A hρr hρ'r hx hy hnc
  rw [← hrk]
  exact le_iSup_of_le ρ (le_iSup_of_le ⟨hρA, hC hρA hρr⟩ (le_iSup_of_le ρ'
    (le_iSup_of_le ⟨hρ'A, hC hρ'A hρ'r⟩ (le_iSup (fun _ : ρ * ρ' ≠ ρ' * ρ =>
      ggRankTwoIn L Bs ρ ρ') hnc))))

end Orth

end CFSG.StandardType.QTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCfg
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofAutCommute
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueSwap
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueInj

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix CFSG.Assembly

section Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}

theorem ggTypeABstarFar_of_bstarDiag {B : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {y : G} {K : Subgroup G} (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} (hL : φ₁.range = L)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hK : φ₂.range = K)
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (hc : φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
      φ₂.comp (slUpperBlockHom n (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Bs, GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c) {i j : Fin n} (hi : i.val = 0)
    (hj : j.val + 1 = n) :
    φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) *
        φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) ∈
      Subgroup.centralizer (Bs : Set G) := by
  have hC : GGFarCtx p Bs φ₁ φ₂ x y := ggFarCtx_of_cfg hN hL hk₁ hK hk₂ hc hdiag
  haveI : Fact p.Prime := ⟨hC.prime⟩
  have hW : GGWeylOfType p (CoxeterMatrix.A (n + 1))
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hW, -⟩ := hN
    exact hW
  have hBs : IsElemAbelian p Bs := by
    obtain ⟨⟨-, hBs, -⟩, -, -, -, -⟩ := hN
    exact hBs.2.1
  have hmem₁ : ∀ π, hC.permAut₁ π ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro π
    refine Subgroup.mem_sup_left ?_
    have hg : φ₁ (slPerm hC.two π) ∈ L := hL ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    exact ggConjAut_mem_ggAutomizer hg (hC.perm_mem_normalizer₁ π)
  have hmem₂ : ∀ π, hC.permAut₂ π ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro π
    refine Subgroup.mem_sup_right ?_
    have hg : φ₂ (slPerm hC.two π) ∈ K := hK ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    exact ggConjAut_mem_ggAutomizer hg (hC.perm_mem_normalizer₂ π)
  have hr₁ : ∀ a b, a ≠ b → GGIsReflection p (hC.permAut₁ (Equiv.swap a b)) :=
    fun a b hab => hC.permAut₁_swap_isReflection hab
  have hr₂ : ∀ a b, a ≠ b → GGIsReflection p (hC.permAut₂ (Equiv.swap a b)) :=
    fun a b hab => hC.permAut₂_swap_isReflection hab
  have hout : ∀ σ, hC.permAut₁ σ ≠ hC.permAut₂ (Equiv.swap j.castSucc j.succ) := by
    intro σ heq
    have hx := congrArg (fun g : MulAut ↥Bs => g ⟨x, hC.x_mem⟩) heq
    rw [hC.permAut₁_fix_x σ] at hx
    exact hC.permAut₂_swap_ne_x hj hx.symm
  have hcomm := ggFar_aut_commute hC.odd hBs hC.three_le hW hC.permAut₁ hC.permAut₂
    hmem₁ hmem₂ hC.permAut₁_injective hC.permAut₂_injective hr₁ hr₂ hC.permAut_compat
    hi hj hout
  exact hC.abab_mem_centralizer hcomm

end Assembly

end CFSG.StandardType

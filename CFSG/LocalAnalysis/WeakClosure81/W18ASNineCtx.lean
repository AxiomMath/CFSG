module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmall
public import CFSG.LocalAnalysis.WeakClosure81.W18PackG
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem pCoreOf_img_eq_bot (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    pCoreOf 2 (M.img H) = ⊥ := by
  have hZcent : D.T ≤ Subgroup.centralizer (omegaOneCenterOf D.T : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hΩ : omegaOneCenterOf D.T ≤ centerOf D.T := by
      rw [omegaOneCenterOf, omegaOneOf]
      exact (Subgroup.closure_le _).mpr fun u hu => hu.1
    have hz' : z ∈ centerOf D.T := hΩ hz
    exact (Subgroup.mem_centralizer_iff.1 hz'.2 t ht).symm
  exact M.pCoreOf_img_eq_bot (J := H) (T := D.T) (Z := omegaOneCenterOf D.T)
    x.hyp.isSylowIn_T (Hyp183.omegaOneCenterOf_le_eOmegaZ H D.T) hZcent (le_refl _)

theorem exists_involution_img (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {g : G} (hgK : ¬ vInH V H g ≤ kerMV V H)
    (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hidx : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2) :
    Gam188 V H (eOmegaZ H D.T) i x.iStar g ∧
      ∃ a₁ : ↥H, (a₁ : G) ∈ vInH V H g ∧ (a₁ : G) ∉ kerMV V H ∧
        M.img (vInH V H g) = Subgroup.zpowers (M.ρ a₁) ∧ orderOf (M.ρ a₁) = 2 := by
  have hDH : vInH V H g ≤ H := inf_le_right
  have hnotC : ¬ vInH V H g ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := fun h =>
    hgK fun d hd => x.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨hDH hd, h hd⟩
  have hm1 : E3.mQuot (vInH V H g)
      (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) = 1 := by
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left, hidx]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact padicValNat_self
  refine ⟨⟨⟨hgi, hnotC⟩, by rw [hm1]; exact x.iStar_pos⟩, ?_⟩
  obtain ⟨d, hdD, hdK⟩ : ∃ d ∈ vInH V H g, d ∉ kerMV V H := by
    by_contra h
    exact hgK fun d hd => by_contra fun hd' => h ⟨d, hd, hd'⟩
  have hdH : d ∈ H := hDH hdD
  have hne : M.ρ ⟨d, hdH⟩ ≠ 1 := by
    intro h1
    exact hdK (x.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨hdH, (M.ρ_eq_one_iff ⟨d, hdH⟩).1 h1⟩)
  have hS : Nat.card (M.img (vInH V H g)) = 2 := by
    rw [M.card_img hDH, hidx]
  have hs : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H g) := M.mem_img.2 ⟨⟨d, hdH⟩, hdD, rfl⟩
  refine ⟨⟨d, hdH⟩, hdD, hdK, (seven_eleven_small_zpowers_eq hS hs hne).symm, ?_⟩
  have hdvd : orderOf (M.ρ ⟨d, hdH⟩) ∣ Nat.card (M.img (vInH V H g)) :=
    Subgroup.orderOf_dvd_natCard _ hs
  rw [hS] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.1 h1) hne
  · exact h2

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end

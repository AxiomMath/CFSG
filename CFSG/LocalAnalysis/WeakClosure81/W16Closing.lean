module

public import CFSG.LocalAnalysis.WeakClosure81.W16Cfg
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cex16

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem sup_ne_conjClosure (h : Cex16 M V₀ V U S) (hR : IsSylowIn 2 R (F11.CTilde M V₀ V))
    (hQ : Fam16Q M V₀ U R H) (hg : g ∈ centralizer (U : Set G))
    (hL : V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) = U)
    (hBR : B ≤ R) (hnot : ¬ U ≤ centralizer (B : Set G)) :
    V ⊔ conjSubgroup V g ⊔ conjClosure (U ⊔ V₀) H ≠ conjClosure V H := by
  intro hLK
  have hIC : conjClosure (U ⊔ V₀) H ≤ centralizer (U : Set G) := hQ.le_centralizer h
  have hLC : V ⊔ conjSubgroup V g ≤ centralizer (U : Set G) :=
    sup_le h.V_le_centralizer (h.conj_le_centralizer hg)
  have hKC : conjClosure V H ≤ centralizer (U : Set G) := by
    rw [← hLK]
    exact sup_le hLC hIC
  have hLK' : V ⊔ conjSubgroup V g ≤ conjClosure V H := by
    rw [← hLK]
    exact le_sup_left
  have hKU : V ⊓ centralizer (conjClosure V H : Set G) = U := by
    apply le_antisymm
    · calc V ⊓ centralizer (conjClosure V H : Set G)
          ≤ V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) :=
            inf_le_inf_left V (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hLK'))
        _ = U := hL
    · refine le_inf h.le fun u hu => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.1 (hKC hk) u hu).symm
  have hBU : ∀ b ∈ B, b ∈ normalizer (U : Set G) := by
    intro b hb
    have hbR : b ∈ R := hBR hb
    have hbC : b ∈ F11.CTilde M V₀ V := hR.le hbR
    have hbV : b ∈ normalizer (V : Set G) := by
      rw [h.hyp.h6.normalizer_eq]
      exact cTilde_le_M M V₀ V hbC
    have hbK : b ∈ normalizer (conjClosure V H : Set G) :=
      le_normalizer_conjClosure V H (hQ.1 hbR)
    have := mem_normalizer_inf_centralizer_wc16 hbV hbK
    rwa [hKU] at this
  apply hnot
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.1
    (h.mem_centralizer_of_mem_normalizer (hR.le (hBR hb)) (hBU b hb)) u hu).symm

end Cex16

end CFSG.LocalAnalysis.WeakClosure81

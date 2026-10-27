module

public import CFSG.Quasithin.Vol2.Ch11SecA15Excl
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G]

theorem injective_of_ker_eq_bot_subgroupOf {U : Subgroup G} {M : Type*} [Group M]
    {β : ↥U →* M} (h : β.ker = (⊥ : Subgroup G).subgroupOf U) : Function.Injective β := by
  rw [← MonoidHom.ker_eq_bot_iff, h, Subgroup.bot_subgroupOf]

theorem le_normalizer_centerOf {L X : Subgroup G} (hX : L ≤ Subgroup.normalizer (X : Set G)) :
    L ≤ Subgroup.normalizer (centerOf X : Set G) := fun _ hl =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hX hl, mem_normalizer_centralizer (hX hl)⟩

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem false_of_notCentralizerCore (h : Hyp11 G T L I n)
    (hNC : C134NotCentralizerCore (L ⊔ ROf T L V₁) (ROf T L V₁))
    (heq : ROf T L V₁ = pCoreOf 2 ((L ⊔ ROf T L V₁) ⊓
      Subgroup.centralizer (omegaOneCenterOf (T ⊓ (L ⊔ ROf T L V₁)) : Set G))) : False :=
  hNC _ (isSylowTwoOf_inf_msG0 h) (le_inf (ROf_le_T h) le_sup_right) heq

theorem not_isC134Case2 (hF : Facts15) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : ¬ IsC134Case2 (L ⊔ ROf T L V₁) (ROf T L V₁) L := by
  rintro ⟨⟨a, F, _, _, α, hF', hα, hLQ, -, β, hβs, hβker, hβ⟩, hNC⟩
  exact false_of_notCentralizerCore h hNC (ROf_eq_pCoreOf_centralizer hF hF11 hG2 h1102 h1103
    h1110 h hU hF' hα β hβs (injective_of_ker_eq_bot_subgroupOf hβker)
    (fun l u v huv i => by simpa [moduleAct] using hβ l u v huv i) hLQ (fsuV_le_c134Q h1102 h)
    (fun z hz l hl => (commutator_mem_centerOf_c134Q h hz hl).1))

theorem not_isC134Case3 (hF : Facts15) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : ¬ IsC134Case3 (L ⊔ ROf T L V₁) (ROf T L V₁) L := by
  rintro ⟨⟨a, F, _, _, α, hF', hα, ⟨hLQ, -, β, hβs, hβker, hβ⟩, -⟩, hNC⟩
  exact false_of_notCentralizerCore h hNC (ROf_eq_pCoreOf_centralizer hF hF11 hG2 h1102 h1103
    h1110 h hU hF' hα β hβs (injective_of_ker_eq_bot_subgroupOf hβker)
    (fun l u v huv i => by simpa [moduleAct] using hβ l u v huv i) hLQ
    (fsuV_le_centerOf_c134Q h1102 h) (fun z hz l hl => commutator_mem_centerOf_c134Q h hz hl))

end CFSG.Quasithin.Vol2.Ch11.SecA

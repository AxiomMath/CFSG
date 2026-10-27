module

public import CFSG.Quasithin.MS93.S4L5Flat
public import CFSG.Quasithin.MS93.SkAssembly
import CFSG.Quasithin.MS93.S33SpCoord

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def NoNonlinSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    critDist (puAmalgam h.le) = 4 → IsSp4U M T L → ¬ IsSp4Full M T L → False

@[expose] def NoNonlinSpGt4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    4 < critDist (puAmalgam h.le) → IsSp4U M T L → ¬ IsSp4Full M T L → False

@[expose] def NoNonlinSp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) → IsSp4U M T L → ¬ IsSp4Full M T L → False

theorem noNonlinSp_of (h4 : NoNonlinSp4) (hg : NoNonlinSpGt4) : NoNonlinSp := by
  intro G _ _ M T L h hmin hb hU hF
  obtain ⟨m, hm⟩ := h.critDist_even
  rcases (show critDist (puAmalgam h.le) = 4 ∨ 4 < critDist (puAmalgam h.le) by omega)
    with hb4 | hb4
  · exact h4 G M T L h hmin hb4 hU hF
  · exact hg G M T L h hmin hb4 hU hF

theorem NoNonlinSp.eq4 (hs : NoNonlinSp) : NoNonlinSp4 := fun G _ _ M T L h hmin hb =>
  hs G M T L h hmin (by omega)

theorem NoNonlinSp.gt4 (hs : NoNonlinSp) : NoNonlinSpGt4 := fun G _ _ M T L h hmin hb =>
  hs G M T L h hmin (by omega)

section Data

variable {G : Type} [Group G]

variable [Finite G] {M T L : Subgroup G}

theorem sup_le_coordGroup_sp (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥L →* ↥(StatedSp 2 F)}
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i)) :
    L ⊔ pCoreOf 2 M ≤
      coordGroup β (StatedSp 2 F) M (le_normalizer_Uq h.le_normalizer) := by
  refine sup_le (fun l hl => ⟨h.L_le hl, a ⟨l, hl⟩, S33.isCoordAct_of_natSp hβα ⟨l, hl⟩⟩)
    (fun t ht => ⟨pCoreOf_le' M ht, 1, ?_⟩)
  exact (isCoordAct_id_of_mem_centralizer (S34F.pCoreOf_le_centralizer_Uq h ht)).congr
    fun x => by simp

theorem not_le_flat_of_nonfull (h : PUHyp M T L) (hU : IsSp4U M T L) (hF : ¬ IsSp4Full M T L) :
    ¬ T ≤ L ⊔ pCoreOf 2 M := by
  intro hT
  rcases hU with ⟨k, F, _, _, a, hk, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ | ⟨a, ha, hnat⟩
  · refine hF (S34R.sp4Full_of_le_linPart h hk hcard ha hLV hZV hβ hβker hβα fun t ht => ?_)
    obtain ⟨-, γ, hγ⟩ := sup_le_coordGroup_sp h hβα (hT ht)
    exact ⟨ht, ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), Subgroup.mem_top _⟩, hγ⟩
  · exact hF ⟨1, ZMod 2, inferInstance, inferInstance, a, le_rfl, by simp, ha, hnat⟩

end Data

end CFSG.Quasithin.MS93.S4L

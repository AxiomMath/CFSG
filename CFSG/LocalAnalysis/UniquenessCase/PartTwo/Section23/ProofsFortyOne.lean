module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s23_41_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h37 : S23_37 D Ch) (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) :
    S23_41 D Ch := by
  intro h1930 c F hFE hFindex g hFg
  by_contra hne
  have hF : F ≤ conjSubgroup D.T g⁻¹ := by
    have h := CFSG.Quasithin.E3.conjSubgroup_mono_left g⁻¹ hFg
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CFSG.Quasithin.conjSubgroup_one] at h
  let X : Ctx23L.S2341Frame D Ch c :=
    ⟨F, hFE, hFindex, g⁻¹, hF, conjSubgroup c.V g⁻¹, rfl,
      conjSubgroup D.Z g⁻¹, rfl⟩
  have hWmap : X.W = c.V.map (MulAut.conj g).toMonoidHom := by
    change conjSubgroup c.V g⁻¹ = c.V.map (MulAut.conj g).toMonoidHom
    simp [CFSG.Quasithin.conjSubgroup]
  have hFmap : (conjSubgroup F g).map (MulAut.conj g).toMonoidHom = F := by
    rw [CFSG.Quasithin.conjSubgroup, Subgroup.map_map]
    rw [show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        (MulAut.conj (g * g⁻¹)).toMonoidHom by
      ext x
      simp [MulAut.conj_apply, mul_assoc]]
    rw [mul_inv_cancel, map_one (MulAut.conj)]
    exact Subgroup.map_id F
  have hneq : ⁅X.W, X.F⁆ ≠ ⊥ := by
    intro hbot
    apply hne
    have hmap : (⁅c.V, conjSubgroup F g⁆).map (MulAut.conj g).toMonoidHom =
        ⁅X.W, X.F⁆ := by
      rw [Subgroup.map_commutator, ← hWmap, hFmap]
    have h' : (⁅c.V, conjSubgroup F g⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
      rw [hmap, hbot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h'
  have hn3 := Ctx23L.three_le_pRank_Z D Ch hE h207 h52 h23 h1930 c
  exact X.false_of_noOddInverted h4 h23 h37 h39 h40 h1930 hneq hn3
    (X.noOddInverted h4 h23 h39 h40 h1930 hneq hn3)

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoC
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem false_of_card_hatBar (hK : KFacts1234) {n : ℕ} (hnn : E3.mQuot V (U ⊔ V₀) = n)
    (hn : 2 ≤ n) (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hY : Nat.card (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) = 2 ^ n * (4 ^ n - 1) ∨
      Nat.card (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) =
        (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) : False := by
  subst hnn
  have hne := c.hatBarSub_L_ne_top hn h1 h5 h15 hS Mo
  have hcardL := c.card_hatBarSub_L hn h1 h5 h15 hS Mo
  obtain ⟨hshape, -⟩ := c.hatL_shape h1 h5 h15 hS Mo c.g_mem c.g_not
  have hL : Nat.card (hatBarSub Mo V (V ⊔ conjSubgroup V g)) =
        2 ^ E3.mQuot V (U ⊔ V₀) * (4 ^ E3.mQuot V (U ⊔ V₀) - 1) ∨
      Nat.card (hatBarSub Mo V (V ⊔ conjSubgroup V g)) =
        (2 ^ E3.mQuot V (U ⊔ V₀)) ^ 2 * (2 ^ E3.mQuot V (U ⊔ V₀) - 1) *
          ((2 ^ E3.mQuot V (U ⊔ V₀)) ^ 2 + 1) := by
    rw [hcardL]
    rcases hshape with hL2 | hSz | ⟨h1', -⟩
    · exact Or.inl (hK.card_L2 _ _ (by omega) hL2)
    · exact Or.inr (hK.card_Sz _ _ hSz)
    · omega
  exact hne (eq_top_of_card_L2_Sz _ (by omega) hL hY)

theorem false_of_linear (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hLin : SevenElevenLinearShape (hatX Mo V) (hatS Mo V)) : False := by
  obtain ⟨m, n', hm, -, ⟨F, hFfield, hFfin, hF, e, a, ha, hSa⟩, -⟩ := hLin
  obtain ⟨γ₀, hγ₀⟩ := c.exists_conj_hatBarSub_of_mem h15 hS Mo c.g_mem.1
  refine false_of_transvection_config hK hm e ha (hatBarSub Mo V V)
    (hatBarSub Mo V (conjSubgroup V g)) ?_ ?_ γ₀ hγ₀
    (c.inf_normalizer_hatBarSub hn h1 h5 h15 hS Mo)
  · intro y
    rw [← hatS_map_eq_hatBarSub, Subgroup.mem_map]
    exact hSa y
  · intro h
    have hc := c.card_hatBarSub_V hn h1 h5 h15 hS Mo
    rw [h, Subgroup.card_bot] at hc
    have : 2 ^ 2 ≤ 2 ^ E3.mQuot V (U ⊔ V₀) := Nat.pow_le_pow_right (by norm_num) hn
    omega

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

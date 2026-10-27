module

public import CFSG.LocalAnalysis.StandardType.GGTwAutBasic
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusFacts
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusRankLE
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusScRank
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwOmPlus_signed_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ}
    (hK : Nat.card K = 2 ^ n) (hr : 3 ≤ r) (hev : Even r) (hmr : m = r + 1)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusSignedEltSC 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  subst hmr
  have h5 : 5 ≤ r + 1 := by
    obtain ⟨k, hk⟩ := hev
    omega
  exact ggOrthSignedTorusInput_holds.1 K (r + 1) 3 h5 hev.add_one Nat.prime_three
    (by rw [hK]; exact h3)

theorem ggTwOmPlus_label_of_rec {r f : ℕ} (hr : 3 ≤ r)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (r + 1)))) (LargeEvenInnSet _)) :
    LargeEvenLabelAll ⟨.D, r + 1, f⟩ fun R _ I _ => P R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega)] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', h K hK⟩

theorem ggTwOmPlus_label
    {r f : ℕ} (hr : 3 ≤ r) (hev : Even r) (h3 : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.D, r + 1, f⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial) :=
  ggTwOmPlus_label_of_rec (P := fun R _ I => GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial)) hr
    fun K _ _ _ hK =>
    ggTwTorus_recipe_of_pieces Nat.prime_three (by norm_num)
      (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).1
      (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).2.1
      (ggTwOmPlus_facts_rec (m := r + 1) hr rfl).2.2
      (ggTwOmPlus_signed_rec hK hr hev rfl h3)
      (ggTwOmPlus_rankLE_rec hK hr hev rfl h3)
      (ggTwOmPlus_scRank_rec hK hr hev rfl h3)

end CFSG.StandardType

end

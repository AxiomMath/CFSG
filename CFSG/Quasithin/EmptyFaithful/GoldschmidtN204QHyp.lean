module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QCore

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G]

structure Hyp111Mod (L1 L2 S : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S (L1 ⊔ L2 ⊔ S)
  pgroup : IsPGroup 2 ↥S
  normalizes₁ : S ≤ Subgroup.normalizer (L1 : Set G)
  normalizes₂ : S ≤ Subgroup.normalizer (L2 : Set G)
  sylow₁ : IsSylowTwoOf (S ⊓ L1) L1
  sylow₂ : IsSylowTwoOf (S ⊓ L2) L2
  listed₁ : IsRankOneListed (oTwoQuot ↥L1)
  listed₂ : IsRankOneListed (oTwoQuot ↥L2)
  borel₁ : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)
  borel₂ : borelOf L1 S ≤ Subgroup.normalizer (L2 : Set G)
  charTwo₁ : CharTwoMod (L1 ⊔ S ⊔ borelOf L2 S) (pCoreOf 2 (L1 ⊔ L2 ⊔ S))
  charTwo₂ : CharTwoMod (L2 ⊔ S ⊔ borelOf L1 S) (pCoreOf 2 (L1 ⊔ L2 ⊔ S))

variable [Finite G]

theorem hyp111At_twoImg {N Li Lj S : Subgroup G} (hLi : Li ≤ N) (hLj : Lj ≤ N) (hS : S ≤ N)
    (hQS : pCoreOf 2 N ≤ S) (hSp : IsPGroup 2 ↥S) (hSn : S ≤ Subgroup.normalizer (Li : Set G))
    (hsi : IsSylowTwoOf (S ⊓ Li) Li) (hsj : IsSylowTwoOf (S ⊓ Lj) Lj)
    (hli : IsRankOneListed (oTwoQuot ↥Li)) (hb : borelOf Lj S ≤ Subgroup.normalizer (Li : Set G))
    (hc : CharTwoMod (Li ⊔ S ⊔ borelOf Lj S) (pCoreOf 2 N)) :
    Hyp111At (twoImg N Li) (twoImg N Lj) (twoImg N S) := by
  have hbj : borelOf (twoImg N Lj) (twoImg N S) = twoImg N (borelOf Lj S) :=
    twoImg_borelOf hSp hLj hQS hsj
  have hBN : borelOf Lj S ≤ N := (F1.borelOf_le _ _).trans hLj
  refine ⟨inferInstance, isPGroup_twoImg hSp, twoImg_le_normalizer hSn, ?_, ?_, ?_, ?_⟩
  · rw [twoImg_inf_of_sylow hSp hLi hsi]
    exact isSylowTwoOf_twoImg hLi hsi
  · exact hli.of_mulEquiv (nonempty_oTwoQuot_twoImg hLi).some.symm
  · rw [hbj]
    exact twoImg_le_normalizer hb
  · rw [hbj, ← twoImg_sup hLi hS, ← twoImg_sup (sup_le hLi hS) hBN]
    exact charTwo_twoImg (sup_le (sup_le hLi hS) hBN) hc

omit [Finite G] in
theorem twoImg_sup_eq_top {L1 L2 S : Subgroup G} :
    twoImg (L1 ⊔ L2 ⊔ S) L1 ⊔ twoImg (L1 ⊔ L2 ⊔ S) L2 ⊔ twoImg (L1 ⊔ L2 ⊔ S) S = ⊤ := by
  have h1 : L1 ≤ L1 ⊔ L2 ⊔ S := le_sup_left.trans le_sup_left
  have h2 : L2 ≤ L1 ⊔ L2 ⊔ S := le_sup_right.trans le_sup_left
  rw [← twoImg_sup h1 h2, ← twoImg_sup (sup_le h1 h2) le_sup_right, twoImg_self]

theorem hyp111_twoImg {L1 L2 S : Subgroup G} (h : Hyp111Mod L1 L2 S) :
    Hyp111 (twoImg (L1 ⊔ L2 ⊔ S) L1) (twoImg (L1 ⊔ L2 ⊔ S) L2) (twoImg (L1 ⊔ L2 ⊔ S) S) where
  h1 := hyp111At_twoImg (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
    le_sup_right (F7.isSylowTwoOf_pCoreOf_le h.sylow) h.pgroup h.normalizes₁ h.sylow₁ h.sylow₂
    h.listed₁ h.borel₁ h.charTwo₁
  h2 := hyp111At_twoImg (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
    le_sup_right (F7.isSylowTwoOf_pCoreOf_le h.sylow) h.pgroup h.normalizes₂ h.sylow₂ h.sylow₁
    h.listed₂ h.borel₂ h.charTwo₂
  o2 := by rw [twoImg_sup_eq_top]; exact pCoreOf_twoQuot_top

end CFSG.Quasithin.N204

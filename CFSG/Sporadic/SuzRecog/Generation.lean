module

public import CFSG.Sporadic.Co1Patterson.GenerationAlt
public import CFSG.Sporadic.SuzRecog.NativeType
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Classes
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Monster.GMS.TwoCentral
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18He
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.Monster.Schur.Restriction
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup Equiv CFSG.Open CFSG.LargeExtraspecial CFSG.RankThree.PartTwo.Sec21
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson CFSG.ComponentClassification.AS81

section Classes

theorem suzInv_mem_suzM {i : ℕ} (hi : i < 2) : suzInv i ∈ suzM := by
  obtain ⟨-, -, -, -, -, h0, h1, -⟩ := CTUC_Suz_four_exact_involution_centralizers
  interval_cases i
  · exact h0
  · exact h1

theorem card_centralizer_suzInv {i : ℕ} (hi : i < 2) :
    Nat.card (centralizer ({(⟨suzInv i, suzInv_mem_suzM hi⟩ : suzM)} : Set suzM)) =
      invInnerOrders.getD i 0 := by
  rw [← card_suzM_inf_centralizer (i := i) (by omega)]
  have h := map_centralizer_subtype suzM (⟨suzInv i, suzInv_mem_suzM hi⟩ : suzM)
  rw [← h]
  exact (card_map_of_injective suzM.subtype_injective).symm

theorem card_centralizer_eq_of_isConj {Y : Type*} [Group Y] {a b : Y} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set Y)) = Nat.card (centralizer ({b} : Set Y)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact CFSG.Sporadic.Co1Block.card_centralizer_equiv (MulAut.conj c) a

theorem exists_involution_classes_suz {Y : Type*} [Group Y] (e : Y ≃* suzM) :
    ∃ a b : Y, (∀ y : Y, orderOf y = 2 → IsConj a y ∨ IsConj b y) ∧ ¬ IsConj a b ∧
      Nat.card (centralizer ({a} : Set Y)) = 3317760 ∧
      Nat.card (centralizer ({b} : Set Y)) = 161280 ∧ orderOf b = 2 := by
  set a₀ : suzM := ⟨suzInv 1, suzInv_mem_suzM (by norm_num)⟩
  set b₀ : suzM := ⟨suzInv 0, suzInv_mem_suzM (by norm_num)⟩
  have hCa : Nat.card (centralizer ({e.symm a₀} : Set Y)) = 3317760 := by
    rw [CFSG.Sporadic.Co1Block.card_centralizer_equiv e, MulEquiv.apply_symm_apply]
    exact card_centralizer_suzInv (i := 1) (by norm_num)
  have hCb : Nat.card (centralizer ({e.symm b₀} : Set Y)) = 161280 := by
    rw [CFSG.Sporadic.Co1Block.card_centralizer_equiv e, MulEquiv.apply_symm_apply]
    exact card_centralizer_suzInv (i := 0) (by norm_num)
  have hb2 : orderOf (e.symm b₀) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_suzInv (by norm_num)
  refine ⟨e.symm a₀, e.symm b₀, fun y hy => ?_, fun h => ?_, hCa, hCb, hb2⟩
  · have h2 : orderOf ((e y : suzM) : Equiv.Perm (Fin 1782)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    have hconj : ∀ {r : suzM} {m : Equiv.Perm (Fin 1782)} (hm : m ∈ suzM),
        ((e y : suzM) : Equiv.Perm (Fin 1782)) = m * r * m⁻¹ → IsConj (e.symm r) y := by
      intro r m hm he
      refine isConj_iff.mpr ⟨e.symm ⟨m, hm⟩, ?_⟩
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact Subtype.ext he.symm
    rcases suzM_conj_cases (e y).2 h2 with ⟨m, hm, he⟩ | ⟨m, hm, he⟩
    · exact Or.inr (hconj hm he)
    · exact Or.inl (hconj hm he)
  · have := card_centralizer_eq_of_isConj h
    rw [hCa, hCb] at this
    norm_num at this

end Classes

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

end CFSG.Sporadic.SuzRecog

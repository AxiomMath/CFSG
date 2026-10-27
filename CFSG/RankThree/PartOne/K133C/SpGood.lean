module

public import CFSG.RankThree.PartOne.K133C.SpInnerCase
public import CFSG.RankThree.PartOne.K133C.SpOuterCase
public import CFSG.RankThree.PartOne.K133C.LinearLeaves
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.PartOne.S11d.PSpGood
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.OutStructure
  CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KCSpComm
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem good_statedProj_sp {K : Type} [Field K] [Finite K] {r m p : ℕ} (hK : Nat.card K = 2 ^ m)
    (hm : 1 ≤ m) (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥)
    (hO : OutPChain p (StatedProj (StatedSp r K))) : Good p (StatedProj (StatedSp r K)) := by
  intro Ē hE hc
  have hCharP : CharP K 2 := charP_two_of_card_eq_pow hK
  have hinj : Function.Injective (proj r K) := CFSG.RankThree.PartOne.proj_injective_sp hK hm (by omega)
  by_cases hin : Ē ≤ inner (StatedProj (StatedSp r K))
  · exact goodAction_sp_inner hp hp2 (by omega) hinj hZ hE hc hin
  · obtain ⟨a, haĒ, haH⟩ := Set.not_subset.1 hin
    have : NeZero r := ⟨by omega⟩
    have O := spOuter Nat.prime_two hm hr hK
    have : IsElementaryAbelian p Ē := hE
    obtain ⟨-, σ, hσ, h, -, hah⟩ := noninner_element_data O hp hp2 haĒ haH
    let e : StatedProj (StatedSp r K) ≃* StatedProj (StatedSp r K) :=
      (h⁻¹ : MulAut (StatedProj (StatedSp r K)))
    have hinjc : Function.Injective (MulAut.congr e).toMonoidHom := MulEquiv.injective _
    set Ē' : Subgroup (MulAut (StatedProj (StatedSp r K))) :=
      Ē.map (MulAut.congr e).toMonoidHom with hĒ'
    have hmem : ∀ φ : MulAut (StatedProj (StatedSp r K)), φ ∈ Ē ↔ MulAut.congr e φ ∈ Ē' := fun φ => by
      rw [hĒ', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    have hE' : IsElementaryAbelian p Ē' :=
      isElementaryAbelian_of_equiv (Ē.equivMapOfInjective _ hinjc) hE
    have hc' : Nat.card Ē' = p ^ 3 := by
      rw [hĒ', Subgroup.card_map_of_injective hinjc, hc]
    have hfa : MulAut.congr e a = fieldAut r K σ := by
      have : MulAut.congr e a = h⁻¹ * a * h⁻¹⁻¹ := rfl
      rw [this, hah]
      group
    have hfĒ' : fieldAut r K σ ∈ Ē' := by
      rw [← hfa]
      exact (hmem a).1 haĒ
    have hfin : fieldAut r K σ ∉ inner (StatedProj (StatedSp r K)) := by
      intro hf
      apply haH
      rw [hah]
      exact (inner_normal (StatedProj (StatedSp r K))).conj_mem _ hf h
    obtain ⟨P, hPĒ', hPin, hPc⟩ := exists_inner_plane hp hO hE' hc'
    exact GoodAction.of_mulEquiv e hmem
      (goodAction_sp_outer hp hp2 (by omega) hinj hZ hE' hσ hfĒ' hfin hPĒ' hPin hPc)

theorem good_of_model_PSp {X : Type} [Group X] [Finite X] {r m p : ℕ} (hr : 2 ≤ r) (hp : p.Prime)
    (h5 : 5 ≤ p) (hZ : Subgroup.center X = ⊥) (h : StatedClassicalModel X .PSp r 2 m) :
    Good p X := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id h
  have hm : 1 ≤ m := hadm.2.1
  have hZT : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have : e.symm t ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff] at ht ⊢
      intro x
      have := ht (e x)
      apply e.injective
      simpa using this
    rw [hZ, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg e this
  have hT : StatedClassicalModel (StatedProj (StatedSp r K)) .PSp r 2 m :=
    ⟨hadm, K, hKf, hKfin, hK, ⟨MulEquiv.refl _⟩⟩
  have hO : OutPChain p (StatedProj (StatedSp r K)) := by
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · obtain rfl : r = 2 := by omega
      exact (outPNice_PSp_two hp hT).toChain
    · exact (outPNice_PSp_ge_three hp h3 hT).toChain
  exact Good.of_mulEquiv e (good_statedProj_sp hK hm hr hp hp2 hZT hO)

theorem kf133ResMaxAt_leaf7_four (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 4) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
  rw [hq2] at hmod
  exact (good_of_model_PSp (by norm_num) hp h5 (center_bot_of_simple hne) hmod).goodRes

theorem kf133ResMaxAt_leaf8_one (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf8 1) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2 le_rfl e0
  rw [hq2] at hmod
  exact (good_of_model_PSp (by norm_num) hp h5 (center_bot_of_simple hne) hmod).goodRes

end CFSG.RankThree.PartOne.K133C

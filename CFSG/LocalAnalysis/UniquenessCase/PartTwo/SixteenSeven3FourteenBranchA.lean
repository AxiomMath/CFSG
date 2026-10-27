module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapM
public import CFSG.LocalAnalysis.WeakClosure81.ElevenTen
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_one_le_k (D : Data G) : 1 ≤ D.k := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  split_ifs <;> omega

theorem s16c1614_lt_rMV_of_counterex (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) :
    ((D.k : ℕ) : ℕ∞) < rMV D.M V := by
  have h := s16n9b_k_add_lt_rMV D hSg h1219 hx h61 h127 hc.setting.hyp16
  have h0 : mSub (⊥ : Subgroup G) = 0 := rk_bot
  rw [h0, Nat.add_zero] at h
  exact h

theorem s16c1614_exists_mQuot_eq_rMV (D : Data G) {V : Subgroup G}
    (hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M) :
    ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M ∧
      (E3.mQuot V U : ℕ∞) = rMV D.M V := by
  classical
  set S : Set (Subgroup G) := {U | U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M} with hSdef
  obtain ⟨U, hUS, hmin⟩ :=
    Set.exists_min_image S (fun U => (E3.mQuot V U : ℕ∞)) (Set.toFinite S) hne
  refine ⟨U, hUS.1, hUS.2, ?_⟩
  unfold rMV
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun U' hU' => hmin U' hU'
  · exact iInf₂_le U hUS

theorem s16c1614_rMV_eq_top (D : Data G) {V : Subgroup G}
    (hempty : ∀ U : Subgroup G, U ≤ V → centralizer (U : Set G) ≤ D.M) : rMV D.M V = ⊤ := by
  have hS : {U : Subgroup G | U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M} = ∅ := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => h.2 (hempty U h.1)
  unfold rMV
  rw [hS]
  simp

private theorem s16c1614_inCalWStar {D : Data G} {V : Subgroup G} (hV : Hyp125 D ⊥ V) :
    InCalWStar D.M D.T V := by
  rcases hV.1 with ⟨hW, -⟩ | ⟨hV0, -, -⟩
  · exact hW
  · exact absurd rfl hV0.1.1

private theorem s16c1614_setting11 {D : Data G} {V : Subgroup G} (hV : Hyp125 D ⊥ V) :
    Setting11 D.M V (D.T ⊓ centralizer (V : Set G)) :=
  TwelveShort.setting11_of_inCalV1 D (s16c1614_inCalWStar hV).1.1

theorem s16c1614_cartan_of_mem_gamma (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (hM : S16GapMGtOne D) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G} (hU : Min1614 D V U)
    (hΓ : U ∈ gammaEleven D.M V) : Cartan1614 D V U := by
  classical
  obtain ⟨-, -, hrU, -⟩ := hU
  have hH : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hset : Setting11 D.M V (D.T ⊓ centralizer (V : Set G)) := s16c1614_setting11 hH
  have hm : 1 < mBar D.M ⊥ V hset.isElemAbelian := by
    have hEq : hset.isElemAbelian = hV := Subsingleton.elim _ _
    rw [hEq]
    exact hM V L hV hc
  have hr : 1 < rMV D.M V := by
    have hk := s16c1614_lt_rMV_of_counterex D hSg h1219 hx h61 h127 hc
    have h1 : ((1 : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast s16c1614_one_le_k D) hk
    simpa using h1
  have hKproper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G := D.standing.kProper
  obtain ⟨K, hK⟩ := exists_mem_elevenBlocks (Q := D.T ⊓ centralizer (V : Set G)) hset
    hKproper hΓ
  obtain ⟨T, Y', hY', hmap, hKM⟩ := hK
  have hKblock : CFSG.CGT.PushingUp.IsBlockOfInX (centralizer (U : Set G)) K :=
    isBlockOfInX_of_mem_elevenBlocks ⟨T, Y', hY', hmap, hKM⟩
  obtain ⟨n, -, hnat, hrMV, -, -, hrel, ⟨X, hXhall⟩, hXstruct⟩ :=
    eleven_ten_of_one_lt hset hr hm ⟨hΓ, hrU⟩ hKblock hKM
  obtain ⟨hcyc, hcard, hCV, hreg⟩ := hXstruct X hXhall
  exact ⟨n, K, X, hrMV, hKblock, hKM, hnat, hrel, hXhall.1, hcyc, hcard, hCV, hreg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

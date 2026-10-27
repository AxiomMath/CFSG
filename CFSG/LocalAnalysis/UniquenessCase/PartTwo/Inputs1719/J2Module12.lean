module

public import CFSG.RankThree.GF2n.Tim79aCitedASProved
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverCenterOddHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2QuadFour : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsSpor ↥L .J2 → IsIrrOn L ⊤ ⊥ → rk W = 12 →
      ∃ A : Subgroup (MulAut W), A ∈ E3.aSet 2 L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem twelve_le_dMinDeg_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J2) :
    12 ≤ dMinDeg X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup X := (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have : Nontrivial X := IsSimpleGroup.toNontrivial
  obtain ⟨f, hf⟩ := S17.exists_nontrivial_repr_dMinDeg X
  have hker : f.ker = ⊥ := by
    rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hf
  have hinj : Function.Injective (f.comp e.symm.toMonoidHom) :=
    ((MonoidHom.ker_eq_bot_iff f).mp hker).comp e.symm.injective
  exact CFSG.RankThree.GF2n.Tim79a.AschbacherHJRepresentationStatement_proof _ _ hinj

theorem isSpor_J2_of_odd_center
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) (hs : IsSpor (X ⧸ Subgroup.center X) .J2) :
    IsSpor X .J2 := by
  obtain ⟨e⟩ := hs
  have : Group.IsPerfect X := (Group.isPerfect_def).2 hq.1
  have hZ : Subgroup.center X = ⊥ :=
    Inputs1719.center_eq_bot_of_perfect_odd_cover e hodd
      CFSG.SectionRank.J2_perfect_odd_cover_trivial
  obtain ⟨e2⟩ := uc22p21k_quotCenter_equiv hZ
  exact ⟨e2.symm.trans e⟩

theorem eq_one_of_rk_lt_dMinDeg {K U : Type} [Group K] [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (ρ : K →* MulAut U) (hlt : rk U < dMinDeg K) : ρ = 1 := by
  classical
  by_contra hρ
  have h2 : IsPGroup 2 U := fun u => ⟨1, by simpa using hU u⟩
  obtain ⟨e⟩ := CFSG.Quasithin.Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one hU
    (CFSG.Quasithin.card_eq_two_pow_of_isPGroup h2)
  let f : K →* Matrix.GeneralLinearGroup (Fin (rk U)) (ZMod 2) :=
    (CFSG.Quasithin.H13.H9Coord.vecEquiv (n := rk U)).symm.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp ρ)
  have hf : f ≠ 1 := by
    intro hf1
    apply hρ
    ext k u
    have hk : f k = 1 := by rw [hf1]; rfl
    have h1 : (MulAut.congr e) (ρ k) = 1 := by
      have := congrArg (CFSG.Quasithin.H13.H9Coord.vecEquiv (n := rk U)) hk
      simpa [f] using this
    have h2 : ρ k = 1 := (MulAut.congr e).injective (by rw [h1, map_one])
    rw [h2]
    rfl
  have hle : dMinDeg K ≤ rk U := Nat.sInf_le ⟨f, hf⟩
  omega

theorem aParam_le_of_isSylowIn_le {W : Type} [CommGroup W] [Finite W]
    {Y T Y' : Subgroup (MulAut W)} (hT : CFSG.Quasithin.IsSylowIn 2 T Y) (hTY' : T ≤ Y') :
    E3.aParam Y ≤ E3.aParam Y' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos (E3.aParam Y) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hev : Even (Nat.card Y) := by
      by_contra hodd
      rw [E3.aParam_of_odd hodd] at hpos
      exact lt_irrefl 0 hpos
    have hS : {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : E3.aParam Y = 0 := by
        simp only [E3.aParam, hev, ↓reduceIte, hne, csSup_empty]
        rfl
      omega
    have hmem : E3.aParam Y ∈ {k : ℕ | 0 < k ∧ (E3.aSet k Y).Nonempty} := by
      have h := Nat.sSup_mem hS (E3.aSet_bddAbove Y)
      simpa only [E3.aParam, hev, ↓reduceIte] using h
    obtain ⟨hk0, A, hA⟩ := hmem
    obtain ⟨g, hgY, hle⟩ := exists_conj_le_of_quasithin_isSylowIn hT hA.1
      (E3.isPGroup_of_isElemAbelian2 hA.2.2.1)
    have hYconj : Y.map (MulAut.conj g).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hgY)
    have hA'Y : A.map (MulAut.conj g).toMonoidHom ∈ E3.aSet (E3.aParam Y) Y := by
      have h1 := aSet_conjAutSub (g := g) hA
      simpa only [conjAutSub, hYconj] using h1
    exact E3.le_aParam_of_mem_aSet hk0 (mem_aSet_of_le hA'Y (hle.trans hTY'))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

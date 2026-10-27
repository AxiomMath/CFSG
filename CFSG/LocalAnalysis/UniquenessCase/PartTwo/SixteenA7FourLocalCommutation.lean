module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourBlockInvolutions
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourBlockUniqueness
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.Quasithin.Background.B1ChiefCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_axis_contradiction
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (h154 : Hyp154 D V₀ V L)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    (hsle : s15 D.M V₀ V hV L ≤ 3)
    (hδγ : delta15 D.M V₀ V hV L + 2 ≤ gamma15 D.M V₀ V hV L)
    {g' : G} (hg' : s15SixAdm D V g') (hgM : g' ∉ D.M)
    (hWnot : ¬ wSub V₀ V hV L ≤
      normalizer (conjSubgroup (wSub V₀ V hV L) g' : Set G)) : False := by
  classical
  let W := wSub V₀ V hV L
  let V₁ := v1Sub D.M V₀ V hV L
  let B : Subgroup G := conjSubgroup W g'
  let K : Subgroup G := (W ⊓ normalizer (B : Set G)) ⊔ V₁
  let C : Subgroup G := s15SixKer B ((W ⊔ V₁ : Subgroup G) : Set G) V₁
  have h125 := c.setting.hyp151.hyp125
  have hWV : W ≤ V := preTil_le V₀ V hV _
  have hV₁V : V₁ ≤ V := s15_Infra_v1Sub_le h125 hV
  have hker := s15_Six_two_le_mQuot_ker D c.setting.hyp151 hV c.ne hg' hδγ hWnot
  have hBN := s15_Six_le_normalizer_of_ker D c.setting.hyp151 hV hg' hsle hker
  have hmK := s15_Six_mQuot_axis_eq_one D h154 hV hgM hg' hsle hBN hker
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg'
  have hCB : C ≤ B := fun x hx => hx.1
  have hCBne : C ≠ B := by
    intro h
    have h1 := hker
    change 2 ≤ E3.mQuot B C at h1
    rw [h, E3.mQuot_self] at h1
    omega
  have hnotBC : ¬ B ≤ C := fun h => hCBne (le_antisymm hCB h)
  obtain ⟨b, hbB, hbC⟩ := SetLike.not_le_iff_exists.1 hnotBC
  have hbM : b ∈ D.M := hBM hbB
  have hb2 : b * b = 1 := by
    have h := (E3.isElemAbelian_conjSubgroup hV g').2 b (hBA hbB)
    simpa [pow_two] using h
  have hbV₁ : b ∈ normalizer (V₁ : Set G) := s15_Infra_le_normalizer_v1Sub h125 hV hbM
  have hbW : b ∈ normalizer (W : Set G) := hBN hbB
  have hbsup : b ∈ normalizer ((W ⊔ V₁ : Subgroup G) : Set G) :=
    CFSG.Quasithin.ChiefCount.mem_normalizer_sup hbW hbV₁
  have hKU : K ≤ W ⊔ V₁ :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hWmem : W ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by rw [conjSubgroup_one]⟩
  have hvM1 : b ∈ conjSubgroup D.M 1 := by rwa [conjSubgroup_one]
  have hvN1 : b ∈ normalizer (conjSubgroup (W ⊔ V₁) 1 : Set G) := by
    rw [conjSubgroup_one]
    exact hbsup
  have hUK : conjSubgroup V₁ 1 ≤ K := by
    rw [conjSubgroup_one]
    exact le_sup_right
  have hKD : K ≤ conjSubgroup (W ⊔ V₁) 1 := by
    rw [conjSubgroup_one]
    exact hKU
  have hmK' : E3.mQuot (conjSubgroup (W ⊔ V₁) 1) K = 1 := by
    rw [conjSubgroup_one]
    exact hmK
  have hfix' : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ conjSubgroup V₁ 1 := by
    intro k hk
    rw [conjSubgroup_one]
    exact s15_Six_comm_mem_v1Sub_of_mem_axis D h154 hV hgM hg' hBN hbB hk
  have hcomm := s168e3_block_comm_mem_v1Sub_of_hyperplane c hrow hInv hWmem
    (g := 1) (X := W) (K := K) hvM1 hb2 hvN1 hUK hKD hmK' hfix'
  have hbC' : b ∈ C := by
    refine ⟨hbB, hbV₁, fun d hd => ?_⟩
    have hd1 : d ∈ conjSubgroup (W ⊔ V₁) 1 := by
      rw [conjSubgroup_one]
      exact hd
    have h := hcomm d hd1
    rwa [conjSubgroup_one] at h
  exact hbC hbC'

theorem s168e3_fifteen_six_local
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    {g : G} (hVg : V ≤ conjSubgroup D.M g)
    (hgV : conjSubgroup V g ≤ D.M) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  classical
  have h151 := c.setting.hyp151
  have h125 := h151.hyp125
  have hdata := s168e3_a7Four_spaceData c hrow
  have h154 : Hyp154 D V₀ V L := s168e3_hyp154_of_a7Four_of_s15_eq_two c hrow hs
  have hδγ : delta15 D.M V₀ V hV L + 2 ≤ gamma15 D.M V₀ V hV L := by
    have h1 := hdata.gamma15_eq
    have h2 := hdata.delta15_le
    omega
  have hsle : s15 D.M V₀ V hV L ≤ 3 := by omega
  refine s15_Six_reduce D c.std.h1217 h151 hV c.ne (H := ?_) (g := g) ⟨hVg, hgV⟩
  intro g' hg'
  by_cases hgM : g' ∈ D.M
  · exact s15_Six_commutator_of_mem D h125 hV hgM
  · by_cases h1 : wSub V₀ V hV L ≤
        normalizer (conjSubgroup (wSub V₀ V hV L) g' : Set G)
    · by_cases h2 : wSub V₀ V hV L ≤
          normalizer (conjSubgroup (wSub V₀ V hV L) g'⁻¹ : Set G)
      · exact s15_Six_commutator_of_normalizes D h154 hV hgM h1 h2
      · have hgMinv : g'⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
        exact (s168e3_axis_contradiction c hrow h154 hInv hsle hδγ
          (s15_Six_adm_inv hg') hgMinv h2).elim
    · exact (s168e3_axis_contradiction c hrow h154 hInv hsle hδγ
        hg' hgM h1).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

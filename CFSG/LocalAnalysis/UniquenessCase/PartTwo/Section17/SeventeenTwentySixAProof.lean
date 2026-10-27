module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveHall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixA
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen
public import CFSG.GroupTheory.WeakClosureZeroPCore
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_26a_U (D : Data G) (V₀ V L : Subgroup G) (c : Ctx17_17 D V₀ V L) : Prop :=
  4 < mSub V₀ → IsSpor (Bar2 L) .J2 → (L.subgroupOf D.M).Normal →
    P17_24_2 D V₀ V L c.hyp125.isElemAbelian →
    (∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L →
      normalizer (centerOf P : Set G) ≤ D.M ∧
        conjSetOf (⊤ : Subgroup G) (centerOf P) ∩ {X : Subgroup G | X ≤ D.M} =
          conjSetOf D.M (centerOf P)) →
    ∀ X : Subgroup G, X ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ Nat.card X = p) → UC6.InU D.M X

@[expose] def Gap17_26a_Alt (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ¬ CFSG.Blueprint.Catalog G →
  ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L), 4 < mSub V₀ → IsSpor (Bar2 L) .J2 →
    D.sig = {5} → (L.subgroupOf D.M).Normal → P17_24_2 D V₀ V L c.hyp125.isElemAbelian →
    ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M →
    IsPGroup 2 ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊓
      centralizer (E3.cClos V₀ 2 D.T : Set G)) →
    ∀ A ∈ E3.gammaSet V₀ 0 D.T,
      ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) →
      ∃ h ∈ H17_25_one D V₀ V L c.hyp125.isElemAbelian,
        (InCalO 2 (normalizer (A : Set G)) ⊥ A h ∧
          twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian) =
            (A ⊔ conjSubgroup A h) ⊔
              pCoreOf 2 (twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian))) ∨
        (InCalO 1 (normalizer (A : Set G)) ⊥ A h ∧
          A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) ≤
            pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ∧
          ∀ x ∈ A ⊔ conjSubgroup A h, Odd (orderOf x) → x ≠ 1 →
            ∀ b ∈ (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) ⊔
                conjSubgroup (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) h,
              x * b = b * x → b = 1)

@[expose] def Gap17_26a_First (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L), 4 < mSub V₀ → IsSpor (Bar2 L) .J2 →
    (L.subgroupOf D.M).Normal → P17_24_2 D V₀ V L c.hyp125.isElemAbelian →
    ∀ A ∈ E3.gammaSet V₀ 0 D.T,
      ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) →
      ∀ h ∈ H17_25_one D V₀ V L c.hyp125.isElemAbelian,
        InCalO 2 (normalizer (A : Set G)) ⊥ A h →
        twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian) =
          (A ⊔ conjSubgroup A h) ⊔
            pCoreOf 2 (twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian)) →
        3 ∣ Nat.card ↥((A ⊔ conjSubgroup A h) ⊓ normalizer (A : Set G))

@[expose] def Config17_26a_II (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∃ (L : Subgroup G) (c : Ctx17_17 D V₀ V L), 4 < mSub V₀ ∧
    ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M ∧
    IsPGroup 2 ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊓
      centralizer (E3.cClos V₀ 2 D.T : Set G)) ∧
    ∃ A ∈ E3.gammaSet V₀ 0 D.T,
      ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ∧
      ∃ h ∈ H17_25_one D V₀ V L c.hyp125.isElemAbelian,
        InCalO 1 (normalizer (A : Set G)) ⊥ A h ∧
        A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) ≤
          pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ∧
        ∀ x ∈ A ⊔ conjSubgroup A h, Odd (orderOf x) → x ≠ 1 →
          ∀ b ∈ (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) ⊔
              conjSubgroup (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)) h,
            x * b = b * x → b = 1

theorem centralizer_inf_centerOf_wClos_two_le {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hm : 4 < mSub V₀) :
    centralizer ((V₀ ⊓ centerOf (E3.wClos V₀ 2 D.T) : Subgroup G) : Set G) ≤ D.M := by
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  have hCU : CentralizersUnique D.M D.T := by
    rcases hV.1 with ⟨-, hbot⟩ | ⟨-, hCU, -⟩
    · exact absurd hbot hV0ne
    · exact hCU
  have hV0M : V₀ ≤ D.M := hV.pairFacts.le.trans hV.pairFacts.le_M
  have hV0T : V₀ ≤ D.T :=
    IsSylowIn.le_of_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le) hV0M
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hV0M).2 hV.pairFacts.le_normalizer₀)
      (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV.pairFacts.elemAbelian₀)
  have hVW : V₀ ≤ E3.wClos V₀ 2 D.T :=
    E3.le_wClos_of_mQuot_le_self hV.pairFacts.elemAbelian₀ hV0T le_rfl (k := 2)
      (by rw [E3.mQuot_self]; norm_num) (by unfold mSub at hm; omega)
  have hnil : Group.IsNilpotent D.T := D.sylowM.isPGroup.isNilpotent
  have hnorm : (V₀.subgroupOf D.T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (D.sylowM.le.trans hV.pairFacts.le_normalizer₀)
  have hne : V₀.subgroupOf D.T ≠ ⊥ := by
    intro hb
    apply hV0ne
    rw [← Subgroup.map_subgroupOf_eq_of_le hV0T, hb, Subgroup.map_bot]
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hzV : (z : G) ∈ V₀ := hz.1
  have hzc : ∀ t ∈ D.T, (z : G) * t = t * z := fun t ht =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.2 ⟨t, ht⟩)).symm
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hCz : centralizer ({(z : G)} : Set G) ≤ D.M := (hCU z z.2 hzc hz1').1
  have hzC : (z : G) ∈ centralizer (E3.wClos V₀ 2 D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hzc w (E3.wClos_le 2 D.T hw)).symm
  intro x hx
  apply hCz
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hx _ (Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_inf.mpr ⟨hVW hzV, hzC⟩⟩)

theorem seventeen_twentytwo_two_of_J2 {D : Data G}
    {V₀ V L : Subgroup G} (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L →
      normalizer (centerOf P : Set G) ≤ D.M ∧
        conjSetOf (⊤ : Subgroup G) (centerOf P) ∩ {X : Subgroup G | X ≤ D.M} =
          conjSetOf D.M (centerOf P) := by
  intro P hP
  rcases h22 L P (centerOf P) c hP rfl with hHe | ⟨-, -, -, -, hNZ, hF, -⟩
  · exact absurd (h23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · exact ⟨hNZ, hF⟩

theorem pCoreOf_H17_25_one_le_T {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) :
    pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≤ D.T :=
  IsSylowIn.le_of_normal
    (TwelveShort.isSylowIn_of_le D (T_le_H17_25_one c.hyp125))
    (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
    (normal_pCoreOf_subgroupOf _)
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _)

theorem exists_gammaZero_not_le_pCoreOf {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L)
    (hH₁ : ¬ H17_25_one D V₀ V L c.hyp125.isElemAbelian ≤
      normalizer (E3.wClos V₀ 0 D.T : Set G)) :
    ∃ A ∈ E3.gammaSet V₀ 0 D.T,
      ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) :=
  CFSG.GroupTheory.exists_gammaSet_zero_not_le_pCoreOf (pCoreOf_H17_25_one_le_T c) hH₁

theorem isPGroup_inf_centralizer_cClos_two {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hm : 4 < mSub V₀) (hJ2 : IsSpor (Bar2 L) .J2)
    (hN : (L.subgroupOf D.M).Normal) (h242 : P17_24_2 D V₀ V L c.hyp125.isElemAbelian)
    (hfus : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L →
      normalizer (centerOf P : Set G) ≤ D.M ∧
        conjSetOf (⊤ : Subgroup G) (centerOf P) ∩ {X : Subgroup G | X ≤ D.M} =
          conjSetOf D.M (centerOf P))
    (hsp : IsStronglyPEmbedded 5 D.M) (hgU : Gap17_26a_U D V₀ V L c)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) :
    IsPGroup 2 ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊓
      centralizer (E3.cClos V₀ 2 D.T : Set G)) := by
  classical
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁def
  set X : Subgroup G := H₁ ⊓ centralizer (E3.cClos V₀ 2 D.T : Set G) with hXdef
  have hMn : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hH₁M : H₁ ≤ D.M := H17_25_one_le_M c.hyp125 c.mem_calC.1.le
  rw [isPGroup_iff_primeFactors_card_subset (p := 2) (by norm_num)]
  intro q hq
  obtain ⟨hqprime, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
  have hq2 : q = 2 := by
    by_contra hqne
    have hfact : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) q hqdvd
    have hzH : (z : G) ∈ H₁ := (Subgroup.mem_inf.mp z.2).1
    have hzC : (z : G) ∈ centralizer (E3.cClos V₀ 2 D.T : Set G) := (Subgroup.mem_inf.mp z.2).2
    have hzordG : orderOf (z : G) = q := by rw [Subgroup.orderOf_coe, hzord]
    let Y : Subgroup G := Subgroup.zpowers (z : G)
    have hYH : Y ≤ H₁ := Subgroup.zpowers_le.mpr hzH
    have hYcard : Nat.card Y = q := by rw [Nat.card_zpowers, hzordG]
    obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp hN2
    have hYZ : Y ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) := Subgroup.zpowers_le.mpr hzC
    have hconj : ∀ y ∈ Y, g⁻¹ * y * g ∈ D.M := by
      intro y hy
      have hmem : g⁻¹ * y * g ∈
          centralizer ((V₀ ⊓ centerOf (E3.wClos V₀ 2 D.T) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvW : v ∈ E3.wClos V₀ 2 D.T := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).1
        have hvCw : v ∈ centralizer (E3.wClos V₀ 2 D.T : Set G) :=
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).2
        have hvC2 : g * v * g⁻¹ ∈ E3.cClos V₀ 2 D.T := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · exact E3.wClos_le 2 D.T ((Subgroup.mem_normalizer_iff.mp hgN v).mp hvW)
          · rw [Subgroup.mem_centralizer_iff]
            intro w hw
            have hw' : g⁻¹ * w * g ∈ E3.wClos V₀ 2 D.T := by
              simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) w).mp hw
            have hvw := Subgroup.mem_centralizer_iff.mp hvCw (g⁻¹ * w * g) hw'
            calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
              _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [hvw]
              _ = (g * v * g⁻¹) * w := by group
        have hyc := Subgroup.mem_centralizer_iff.mp (hYZ hy) (g * v * g⁻¹) hvC2
        calc v * (g⁻¹ * y * g) = g⁻¹ * ((g * v * g⁻¹) * y) * g := by group
          _ = g⁻¹ * (y * (g * v * g⁻¹)) * g := by rw [hyc]
          _ = (g⁻¹ * y * g) * v := by group
      exact centralizer_inf_centerOf_wClos_two_le c.hyp125 hm hmem
    have hle : Y ≤ uniqueFourConj g⁻¹ D.M := fun y hy => by
      rw [UC6.mem_uniqueFourConj_iff]
      simpa using hconj y hy
    have hg' : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
    by_cases hq5 : q = 5
    · apply hsp.2.2 (g⁻¹)⁻¹ (by simpa using hgM)
      rw [← hq5, ← hYcard]
      exact Subgroup.card_dvd_of_le (le_inf (hYH.trans hH₁M) hle)
    · exact ((UC6.inU_iff_not_le hMn).mp
        (hgU hm hJ2 hN h242 hfus Y hYH ⟨q, hqprime, hqne, hq5, hYcard⟩)).2 g⁻¹ hg' hle
  subst hq2
  exact Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_rfl, by norm_num⟩

theorem false_of_first_case_17_26a {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hm : 4 < mSub V₀) (hJ2 : IsSpor (Bar2 L) .J2)
    (hN : (L.subgroupOf D.M).Normal) (h242 : P17_24_2 D V₀ V L c.hyp125.isElemAbelian)
    (hfus : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L →
      normalizer (centerOf P : Set G) ≤ D.M ∧
        conjSetOf (⊤ : Subgroup G) (centerOf P) ∩ {X : Subgroup G | X ≤ D.M} =
          conjSetOf D.M (centerOf P))
    (hgU : Gap17_26a_U D V₀ V L c) (hFirst : Gap17_26a_First D V₀ V)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian))
    {h : G} (hh : h ∈ H17_25_one D V₀ V L c.hyp125.isElemAbelian)
    (hO : InCalO 2 (normalizer (A : Set G)) ⊥ A h)
    (hres : twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian) =
      (A ⊔ conjSubgroup A h) ⊔
        pCoreOf 2 (twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian))) : False := by
  classical
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁def
  have h3dvd : 3 ∣ Nat.card ↥((A ⊔ conjSubgroup A h) ⊓ normalizer (A : Set G)) :=
    hFirst L c hm hJ2 hN h242 A hA hAO h hh hO hres
  obtain ⟨z, hzord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥((A ⊔ conjSubgroup A h) ⊓ normalizer (A : Set G))) 3
      h3dvd
  have hzA : (z : G) ∈ A ⊔ conjSubgroup A h := (Subgroup.mem_inf.mp z.2).1
  have hzN : (z : G) ∈ normalizer (A : Set G) := (Subgroup.mem_inf.mp z.2).2
  have hAH : A ≤ H₁ := hA.1.trans (T_le_H17_25_one c.hyp125)
  have hAhH : conjSubgroup A h ≤ H₁ := by
    intro x hx
    change x ∈ A.map (MulAut.conj h⁻¹).toMonoidHom at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hh) (hAH ha)) (by simpa using hh)
  let Y : Subgroup G := Subgroup.zpowers (z : G)
  have hYH : Y ≤ H₁ := Subgroup.zpowers_le.mpr ((sup_le hAH hAhH) hzA)
  have hYcard : Nat.card Y = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
  have hYU : UC6.InU D.M Y :=
    hgU hm hJ2 hN h242 hfus Y hYH ⟨3, by norm_num, by norm_num, by norm_num, hYcard⟩
  obtain ⟨-, g, hAg, hquot⟩ := hA
  have hV0p : IsPGroup 2 V₀ :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.pairFacts.elemAbelian₀
  have hAg' : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0p g) hAg).mp hquot
  have hV0cal : InCalV D.M V₀ := by
    have hV0ne : V₀ ≠ ⊥ := by
      intro hbot
      rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
      omega
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.1
  have hNA : normalizer (A : Set G) = conjSubgroup D.M g := by
    rw [hAg']
    change normalizer (V₀.map (MulAut.conj g⁻¹).toMonoidHom) =
      D.M.map (MulAut.conj g⁻¹).toMonoidHom
    rw [← Subgroup.map_normalizer_eq_of_bijective (H := V₀)
      (f := (MulAut.conj g⁻¹).toMonoidHom) (hf := (MulAut.conj g⁻¹).bijective),
      normalizer_eq_of_inCalV D hV0cal]
  have hzMg : (z : G) ∈ conjSubgroup D.M g := hNA ▸ hzN
  have hYle : Y ≤ conjSubgroup D.M g := Subgroup.zpowers_le.mpr hzMg
  have hconjM : conjSubgroup D.M g = D.M := hYU.2 g hYle
  have hgN : g ∈ Subgroup.normalizer (D.M : Set G) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hconjM
  rw [UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at hgN
  have hAV0 : A = V₀ := by
    rw [hAg']
    exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
      (c.hyp125.pairFacts.le_normalizer₀ hgN)
  refine hAO ?_
  rw [hAV0]
  have hVcal : InCalV D.M V := c.hyp125.inCalV
  have hVT : V ≤ D.T :=
    IsSylowIn.le_of_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le) hVcal.2.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVcal.2.1).2 hVcal.2.2.1)
      (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.isElemAbelian)
  refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf
    ((c.hyp125.pairFacts.le.trans hVT).trans (T_le_H17_25_one c.hyp125)) ?_ hV0p
  intro x hx y hy
  exact (c.hyp125.pairFacts.le_normalizer₀
    (H17_25_one_le_M c.hyp125 c.mem_calC.1.le hx) y).mp hy

theorem le_normalizer_wClos_zero_of_H2 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h93 : Thm93 V₀ D.T)
    (hSg : UC6S846.SigmaStd D) (h5 : 5 ∈ D.sig) (hm : 4 < mSub V₀)
    {H₂ : Subgroup G} (hTH : D.T ≤ H₂) (hHM : H₂ ≤ D.M) (hidx : D.T.relIndex H₂ = 5) :
    H₂ ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  classical
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub c.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardH₂ : Nat.card ↥H₂ = 5 * Nat.card ↥D.T := by
    have h := Subgroup.relIndex_mul_card D.T H₂
    rw [hidx, inf_of_le_left hTH] at h
    exact h.symm
  have h5H₂ : 5 ∣ Nat.card H₂ := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_card (H := D.T) (K := H₂)
  obtain ⟨y₀, hy₀ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H₂) 5 h5H₂
  set y : G := (y₀ : G) with hydef
  have hyH₂ : y ∈ H₂ := y₀.2
  have hyord : orderOf y = 5 := by rw [hydef, Subgroup.orderOf_coe, hy₀ord]
  let X : Subgroup G := Subgroup.zpowers y
  have hXH : X ≤ H₂ := Subgroup.zpowers_le.mpr hyH₂
  have hXcard : Nat.card X = 5 := by rw [Nat.card_zpowers, hyord]
  have hXp : IsPGroup 5 X := IsPGroup.of_card (hXcard.trans (pow_one 5).symm)
  have hXinfT : X ⊓ D.T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hXcard]
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
  have hcsup : Nat.card ↥(X ⊔ D.T) ≤ Nat.card X * Nat.card D.T := by
    rw [hXcard, ← hcardH₂]
    exact Subgroup.card_le_of_le (sup_le hXH hTH)
  have hXT : (X : Set G) * (D.T : Set G) = (D.T : Set G) * (X : Set G) :=
    CFSG.Quasithin.H.L3Wr.permute_of_card hXinfT hcsup
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC c.mem_calC) h5
  have hXM : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥ := by
    intro g hg _
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    have h := hsp.inf_map_conj_eq_bot (by norm_num) (hXH.trans hHM) hXp g⁻¹ hg'
    simpa [conjSubgroup] using h
  have hΓ : rankThreeGamma 1 5 X ≤ D.M :=
    hsp.rankThreeGamma_one_le_of_le (by norm_num) hXp (hXH.trans hHM)
  have h16 := twelve_sixteen hTim hcat D h66 h88 c.hyp125 h8 h93 (p := 5) (by norm_num)
    (by norm_num) hXp hXM hΓ hXT
  have hXsupT : X ⊔ D.T = H₂ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hXH hTH) ?_
    rw [hcardH₂]
    have h := CFSG.card_mul_card_le_of_inf_eq_bot (A := X ⊔ D.T) le_sup_left le_sup_right hXinfT
    rwa [hXcard] at h
  rw [← hXsupT]
  exact h16.2

theorem uniqueMax_sup_H17_25_one_of_H2
    {D : Data G} {V₀ V L H₂ : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V)
    (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V) (h61 : UC6.R6_1 D)
    (hJ2center : K_J2_center_five)
    (hTH : D.T ≤ H₂) (hHC : H₂ ≤ D.T ⊔ centSection D.M L (pCoreOf 2 L))
    (hidx : D.T.relIndex H₂ = 5) :
    UniqueMax D.M (H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂) := by
  classical
  set hV : IsElemAbelian 2 V := c.hyp125.isElemAbelian with hVdef
  set H₁ : Subgroup G := H17_25_one D V₀ V L hV with hH₁def
  have hJ2 : IsSpor (Bar2 L) .J2 := h23 L c
  have hsig : D.sig = {5} := sig_eq_five_of_J2 h22 h23 c
  have hsig5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  have hH₂M : H₂ ≤ D.M := hHC.trans (sup_le D.sylowM.le (centSection_le _ _ _))
  have hH₁M : H₁ ≤ D.M := H17_25_one_le_M c.hyp125 c.mem_calC.1.le
  have hcardH₂ : Nat.card ↥H₂ = 5 * Nat.card ↥D.T := by
    have h := Subgroup.relIndex_mul_card D.T H₂
    rw [hidx, inf_of_le_left hTH] at h
    exact h.symm
  have h5H₂ : 5 ∣ Nat.card H₂ := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_card (H := D.T) (K := H₂)
  have hL1 : barSub V₀ V hV L ≠ ⊥ := by
    have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hcardW : Nat.card (Vtil V₀ V hV) = 2 ^ 12 := by
      rw [← Subgroup.card_top (G := Vtil V₀ V hV),
        CFSG.Quasithin.card_eq_two_pow hsq ⊤, CFSG.Quasithin.rk_top, (h25 L c).2.1]
    exact ne_bot_of_isIrrOn_of_two_lt_card hsq (h25 L c).1 (by rw [hcardW]; norm_num)
  obtain ⟨y₀, hy₀ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H₂) 5 h5H₂
  set y : G := (y₀ : G) with hydef
  have hyH₂ : y ∈ H₂ := y₀.2
  have hyord : orderOf y = 5 := by rw [hydef, Subgroup.orderOf_coe, hy₀ord]
  have hyM : y ∈ D.M := hH₂M hyH₂
  have hys : y ∈ stabTil V₀ V :=
    (le_stabTil c.hyp125.pairFacts.le_normalizer c.hyp125.pairFacts.le_normalizer₀) hyM
  have hbar : barSub V₀ V hV H₂ ≤ barSub V₀ V hV D.T ⊔
      Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    have hCY : centSection D.M L (pCoreOf 2 L) ≤ D.M := centSection_le _ _ _
    have hMstab : D.M ≤ stabTil V₀ V :=
      le_stabTil c.hyp125.pairFacts.le_normalizer c.hyp125.pairFacts.le_normalizer₀
    have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMstab
    have hCstab : centSection D.M L (pCoreOf 2 L) ≤ stabTil V₀ V := hCY.trans hMstab
    have hsup := s16c7_barSub_sup V₀ V hV hTstab hCstab
    calc barSub V₀ V hV H₂
        ≤ barSub V₀ V hV (D.T ⊔ centSection D.M L (pCoreOf 2 L)) :=
          barSub_mono V₀ V hV hHC
      _ = barSub V₀ V hV D.T ⊔ barSub V₀ V hV (centSection D.M L (pCoreOf 2 L)) := hsup
      _ ≤ barSub V₀ V hV D.T ⊔ Subgroup.centralizer (barSub V₀ V hV L :
          Set (MulAut (Vtil V₀ V hV))) :=
          sup_le_sup_left (barSub_centSection_le_centralizer c.hyp125 c) _
  have hyC : actTil V₀ V hV ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    actTil_mem_centralizer_of_le_sup c.hyp125 c hMnorm hbar hyH₂ hyord hys
  obtain ⟨x, hxL, hxH₁, hxord, hxy⟩ :=
    exists_five_mem_H17_25_one_commute hJ2center c.hyp125 c hJ2 hL1 hMnorm hyM hys hyord hyC
  let E : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxE : x ∈ E := Subgroup.subset_closure (by simp [E])
  have hyE : y ∈ E := Subgroup.subset_closure (by simp [E])
  have hEM : E ≤ D.M := by
    refine (Subgroup.closure_le D.M).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hH₁M hxH₁
    · exact hH₂M hyH₂
  have hE5 : IsPGroup 5 E := by
    have hcomm : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
      intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hxy
      · exact hxy.symm
      · rfl
    have hp : ∀ a ∈ ({x, y} : Set G), a ^ 5 = 1 := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [← hxord, pow_orderOf_eq_one]
      · rw [← hyord, pow_orderOf_eq_one]
    exact (IsElemAbelian.closure_of_commute hcomm hp).isPGroup
  have hEnc : ¬ IsCyclic ↥E :=
    not_isCyclic_closure_pair_of_J2 c.hyp125 c hJ2 hL1 hxL hxord hys hyord hyC
  have hU : UniqueMax D.M E := h61 5 hsig5 E hEM hE5 hEnc
  have hEH : E ≤ H₁ ⊔ H₂ := by
    refine (Subgroup.closure_le (H₁ ⊔ H₂)).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_sup_left hxH₁
    · exact Subgroup.mem_sup_right hyH₂
  exact uc22p22u_uniqueMax_mono D hEH (sup_le hH₁M hH₂M) hU

theorem not_le_normalizer_wClos_zero_H1
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) (h61 : UC6.R6_1 D) (h861 : W3Lem86_1 G) (h126 : R126 D)
    (hJ2center : K_J2_center_five) (hm : 4 < mSub V₀)
    {H₂ : Subgroup G} (hTH : D.T ≤ H₂) (hHC : H₂ ≤ D.T ⊔ centSection D.M L (pCoreOf 2 L))
    (hidx : D.T.relIndex H₂ = 5) (hH₂N : H₂ ≤ normalizer (E3.wClos V₀ 0 D.T : Set G)) :
    ¬ H17_25_one D V₀ V L c.hyp125.isElemAbelian ≤
      normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  classical
  intro hH₁N
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  have hV0cal : InCalV D.M V₀ := by
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.1
  have hTI : IsTI V₀ := by
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.2.2.2.1
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub c.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hU : UniqueMax D.M (H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂) :=
    uniqueMax_sup_H17_25_one_of_H2 c h20 h22 h23 h25 h61 hJ2center hTH hHC hidx
  have hH₂M : H₂ ≤ D.M := hHC.trans (sup_le D.sylowM.le (centSection_le _ _ _))
  have hle : H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂ ≤
      D.M ⊓ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    le_inf (sup_le (H17_25_one_le_M c.hyp125 c.mem_calC.1.le) hH₂M) (sup_le hH₁N hH₂N)
  have hUN : UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V₀ 0 D.T : Set G)) :=
    uc22p22u_uniqueMax_mono D hle inf_le_left hU
  exact twelve_seven_one hTim hcat D h861 h126 c.hyp125.2 hV0cal hTI h8 hUN

theorem seventeen_twentysix_a_reduction
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (D : Data G) (V₀ V : Subgroup G) (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V)
    (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V) (hSg : UC6S846.SigmaStd D)
    (h880 : F08.R880 D) (hJ2aut : K_J2_aut_five_rank) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h88 : W3Thm88 G) (h126 : R126 D) (h861 : W3Lem86_1 G)
    (h93 : ∀ L, Ctx17_17 D V₀ V L → Thm93 V₀ D.T) (hNE : ∀ H₀, Gap17_26_NE D V₀ V H₀)
    (hJ2center : K_J2_center_five)
    (hgU : ∀ L (c : Ctx17_17 D V₀ V L), Gap17_26a_U D V₀ V L c)
    (hAlt : Gap17_26a_Alt D V₀ V) (hFirst : Gap17_26a_First D V₀ V) :
    R17_26aAt D V₀ V ∨ Config17_26a_II D V₀ V := by
  classical
  by_cases hR : R17_26aAt D V₀ V
  · exact Or.inl hR
  right
  have hR' : ∃ L, ∃ c : Ctx17_17 D V₀ V L, 4 < mSub V₀ := by
    by_contra hno
    exact hR fun L c => by
      by_contra hle
      exact hno ⟨L, c, by omega⟩
  obtain ⟨L, c, hm⟩ := hR'
  have hJ2 : IsSpor (Bar2 L) .J2 := h23 L c
  have hsig : D.sig = {5} := sig_eq_five_of_J2 h22 h23 c
  have h5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  have hN : (L.subgroupOf D.M).Normal := (h20 L c).2.1
  have h242 : P17_24_2 D V₀ V L c.hyp125.isElemAbelian := h25 L c
  have hfus := seventeen_twentytwo_two_of_J2 h22 h23 c
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC c.mem_calC) h5
  obtain ⟨H₂, hTH₂, hH₂C, hidx⟩ :=
    exists_H2_of_J2 c h20 h22 h23 hSg h880 hJ2aut hJ2 hsig
  have hH₂M : H₂ ≤ D.M := hH₂C.trans (sup_le D.sylowM.le (centSection_le _ _ _))
  have hH₂N := le_normalizer_wClos_zero_of_H2 hTim hcat c h66 h88 (h93 L c) hSg h5 hm
    hTH₂ hH₂M hidx
  have hH₁N := not_le_normalizer_wClos_zero_H1 hTim hcat c h20 h22 h23 h25 h61 h861 h126
    hJ2center hm hTH₂ hH₂C hidx hH₂N
  obtain ⟨H₀, hmin⟩ := c.hyp125.exists_hyp124Min
  have hN2 := normalizer_Wi_two_not_le D V₀ V H₀ c.hyp125 hmin h126 h861 hm hTim hcat (hNE H₀)
  have h2grp := isPGroup_inf_centralizer_cClos_two c hm hJ2 hN h242 hfus hsp (hgU L c) hN2
  obtain ⟨A, hA, hAO⟩ := exists_gammaZero_not_le_pCoreOf c hH₁N
  obtain ⟨h, hh, hcase⟩ := hAlt hcat L c hm hJ2 hsig hN h242 hN2 h2grp A hA hAO
  rcases hcase with ⟨hO, hres⟩ | ⟨hO1, hB, hfpf⟩
  · exact (false_of_first_case_17_26a c hm hJ2 hN h242 hfus (hgU L c) hFirst hA hAO hh hO
      hres).elim
  · exact ⟨L, c, hm, hN2, h2grp, A, hA, hAO, h, hh, hO1, hB, hfpf⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

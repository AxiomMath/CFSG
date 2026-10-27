module

import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M

variable {G : Type} [Group G] [Finite G]

theorem isZ3PGLThreeAt_of_mulEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X')
    {p f : ℕ} (h : IsZ3PGLThreeAt X' p f) : IsZ3PGLThreeAt X p f := by
  obtain ⟨π, K, hK, h1, h2, ⟨ψ⟩⟩ := h
  exact ⟨π, K, hK, h1, h2, ⟨φ.trans ψ⟩⟩

section Frame

variable {A Y J : Subgroup G} [(ker148 A Y).Normal] [(ker148 A (centPre148 A Y J)).Normal]

theorem img148_eq_of_centPre148
    (hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y) {X X' : Subgroup G}
    (hX : X ≤ centPre148 A Y J ⊔ A) (hX' : X' ≤ centPre148 A Y J ⊔ A)
    (h : img148 A (centPre148 A Y J) X = img148 A (centPre148 A Y J) X') :
    img148 A Y X = img148 A Y X' := by
  rw [← Ronan148M.map_img148_compare148 hcore.le hX, h,
    Ronan148M.map_img148_compare148 hcore.le hX']

theorem isZ3PGLThreeAt_of_centPre148
    (hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y) {X : Subgroup G}
    (hX : X ≤ centPre148 A Y J ⊔ A) {p f : ℕ}
    (h : IsZ3PGLThreeAt ↥(img148 A (centPre148 A Y J) X) p f) :
    IsZ3PGLThreeAt ↥(img148 A Y X) p f := by
  obtain ⟨φ⟩ := Ronan148M.nonempty_img148_centPre148_equiv hcore hX
  exact isZ3PGLThreeAt_of_mulEquiv φ.symm h

end Frame

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
private theorem alpha148_congr_eq {a b : G} (ha : a ∈ A) (hb : b ∈ A) (h : a = b) :
    alpha148 A Y a ha = alpha148 A Y b hb := by
  subst h
  rfl

omit [Finite G] in
private theorem alpha148_one_eq : alpha148 A Y 1 A.one_mem = 1 :=
  (alpha148_eq_mk' A.one_mem).trans (mk'_ker148_eq_one_iff.mpr (Subgroup.one_mem _))

omit [Finite G] in
private theorem mem_of_mk_eq_mk {a j : G} (haM : a ∈ Y ⊔ A) (hjM : j ∈ Y ⊔ A) (hjY : j ∈ Y)
    (h : QuotientGroup.mk' (ker148 A Y) (⟨a, haM⟩ : ↥(Y ⊔ A)) =
      QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩) : a ∈ Y := by
  have hay : a⁻¹ * j ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_iff.mp h
  have h1 : j * (a⁻¹ * j)⁻¹ ∈ Y := Y.mul_mem hjY (Y.inv_mem (pPrimeCoreOf_le 3 Y hay))
  have h2 : j * (a⁻¹ * j)⁻¹ = a := by group
  rwa [h2] at h1

theorem img148_le_normalizer_of_map_normal {X : Subgroup G} (hXY : X ≤ Y)
    (hN : ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal) :
    img148 A Y Y ≤ Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have hY : Y ≤ Subgroup.normalizer ((X ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G) :=
    (map_mk_normal_iff hXY).mp hN
  have hO : img148 A Y (pPrimeCoreOf 3 Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨g, hg, hgO, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
    exact hgO
  have hXA : X ≤ Y ⊔ A := hXY.trans le_sup_left
  have hOA : pPrimeCoreOf 3 Y ≤ Y ⊔ A := (pPrimeCoreOf_le 3 Y).trans le_sup_left
  have hsup : img148 A Y (X ⊔ pPrimeCoreOf 3 Y) = img148 A Y X := by
    rw [img148_sup hXA hOA, hO, sup_bot_eq]
  have h := img148_le_normalizer (A := A) (Y := Y) hY
  rwa [hsup] at h

theorem inf_centPre148_le_zpowers {J : Subgroup G} (hA3 : ∀ a ∈ A, a ^ 3 = 1) {e : G}
    (he : e ∈ A)
    (hAJc : img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers (alpha148 A Y e he)) :
    A ⊓ centPre148 A Y J ≤ Subgroup.zpowers e := by
  rintro a ⟨haA, haC⟩
  obtain ⟨haY, hc⟩ := mem_centPre148_iff.mp haC
  have hmem : alpha148 A Y a haA ∈ Subgroup.zpowers (alpha148 A Y e he) := by
    rw [← hAJc]
    exact Subgroup.mem_inf.mpr ⟨alpha148_mem_img148 haA, hc⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  have hinj : e ^ n = a :=
    alpha148_injective hA3 (A.pow_mem he n) haA ((alpha148_pow he n).trans hn)
  rw [← hinj]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers e) n

theorem mem_zpowers_of_commute148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A)
    (hAe : A ⊓ Y ≤ Subgroup.zpowers e) {w : ↥(Y ⊔ A) ⧸ ker148 A Y} (hwY : w ∈ img148 A Y Y)
    (hwA : w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hw3 : w ^ 3 = 1) : w ∈ Subgroup.zpowers (alpha148 A Y e he) := by
  obtain ⟨a, haM, haA, hmA⟩ := mem_img148_iff.mp (mem_img148_of_commute hAF hAY hwA hw3)
  obtain ⟨y, hyM, hyY, hmY⟩ := mem_img148_iff.mp hwY
  have haY : a ∈ Y := mem_of_mk_eq_mk haM hyM hyY (hmA.trans hmY.symm)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hAe (Subgroup.mem_inf.mpr ⟨haA, haY⟩)))
  have hw : alpha148 A Y a haA = w := hmA
  have hαeq : alpha148 A Y a haA = alpha148 A Y e he ^ n :=
    (alpha148_congr_eq haA (A.pow_mem he n) hn.symm).trans (alpha148_pow he n)
  rw [← hw, hαeq]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n

theorem alpha148_mem_of_inf (hA3 : ∀ a ∈ A, a ^ 3 = 1) {J : Subgroup G} (hJY : J ≤ Y) {e : G}
    (he : e ∈ A) (hAe : A ⊓ Y ≤ Subgroup.zpowers e) {b : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hbA : b ∈ img148 A Y A) (hbJ : b ∈ img148 A Y J) (hb1 : b ≠ 1) :
    alpha148 A Y e he ∈ img148 A Y J := by
  obtain ⟨a, haM, haA, hmA⟩ := mem_img148_iff.mp hbA
  obtain ⟨j, hjM, hjJ, hmJ⟩ := mem_img148_iff.mp hbJ
  have haY : a ∈ Y := mem_of_mk_eq_mk haM hjM (hJY hjJ) (hmA.trans hmJ.symm)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hAe (Subgroup.mem_inf.mpr ⟨haA, haY⟩)))
  have hbα : b = alpha148 A Y a haA := hmA.symm
  have hb_eq : b = alpha148 A Y e he ^ n :=
    hbα.trans ((alpha148_congr_eq haA (A.pow_mem he n) hn.symm).trans (alpha148_pow he n))
  have hx3 : alpha148 A Y e he ^ 3 = 1 := by
    rw [← alpha148_pow he 3]
    exact (alpha148_congr_eq (A.pow_mem he 3) A.one_mem (hA3 e he)).trans alpha148_one_eq
  have hn3 : n % 3 ≠ 0 := by
    intro h0
    apply hb1
    rw [hb_eq, pow_eq_pow_mod n hx3, h0, pow_zero]
  have hsq : n * n % 3 = 1 := by
    rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h | h <;> simp [Nat.mul_mod, h]
  have hxb : alpha148 A Y e he = b ^ n := by
    rw [hb_eq, ← pow_mul, pow_eq_pow_mod (n * n) hx3, hsq, pow_one]
  rw [hxb]
  exact Subgroup.pow_mem _ hbJ n

theorem img148_deltaZero_eq_bot_of_case148One {Y' : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hcore : pPrimeCoreOf 3 Y' = pPrimeCoreOf 3 Y) (h1 : Case148One A LB Y') :
    img148 A Y (deltaZero A LB Y') = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  obtain ⟨g, hg, hgD, rfl⟩ := mem_img148_iff.mp hx
  have hgY' : g ∈ pPrimeCoreOf 3 Y' := h1 hgD
  rw [hcore] at hgY'
  rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
  exact hgY'

end Quot

theorem yBOne_of_le {A Y Y' B : Subgroup G} {LB : Subgroup G → Subgroup G} (hY'Y : Y' ≤ Y)
    (h : YBOne A LB Y B) : YBOne A LB Y' B := by
  unfold YBOne at h ⊢
  have hYC : Y' ⊓ Subgroup.centralizer (B : Set G) ≤ Y ⊓ Subgroup.centralizer (B : Set G) :=
    inf_le_inf_right _ hY'Y
  have hD1 : deltaZero A LB (Y' ⊓ Subgroup.centralizer (B : Set G)) ≤
      Y' ⊓ Subgroup.centralizer (B : Set G) :=
    sSup_le fun _ hQ => hQ.2
  have hD2 : deltaZero A LB (Y' ⊓ Subgroup.centralizer (B : Set G)) ≤
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
    (deltaZero_mono148 hYC).trans h
  have hN : deltaZero A LB (Y' ⊓ Subgroup.centralizer (B : Set G)) ≤
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊓
        (Y' ⊓ Subgroup.centralizer (B : Set G)) :=
    le_inf hD2 hD1
  have hcop : Nat.Coprime 3 (Nat.card ↥(pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊓
      (Y' ⊓ Subgroup.centralizer (B : Set G)))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)))
  have hnorm : Y' ⊓ Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊓
        (Y' ⊓ Subgroup.centralizer (B : Set G)) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) (hYC hx),
        Subgroup.le_normalizer hx⟩
  exact hN.trans (le_pPrimeCoreOf inf_le_right hnorm hcop)

end CFSG.RankThree.PartTwo.Sec14.Ronan148A

module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QY1
public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConj
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalPGL
import CFSG.RankThree.PartTwo.Sec14.Concl142Item
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalLeaves

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

private theorem le_of_isSimpleGroup_of_le_normalizer' {Γ : Type} [Group Γ] {D K : Subgroup Γ}
    {e : Γ} (hD : IsSimpleGroup ↥D) (hDN : D ≤ Subgroup.normalizer (K : Set Γ)) (heD : e ∈ D)
    (heK : e ∈ K) (he1 : e ≠ 1) : D ≤ K := by
  have hnorm : ((K ⊓ D).subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    obtain ⟨hhK, hhD⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨?_, D.mul_mem (D.mul_mem hk hhD) (D.inv_mem hk)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hDN hk) h).mp hhK
  haveI := hnorm
  rcases hD.eq_bot_or_eq_top_of_normal ((K ⊓ D).subgroupOf D) with h | h
  · exfalso
    have hmem : (⟨e, heD⟩ : ↥D) ∈ (K ⊓ D).subgroupOf D :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨heK, heD⟩)
    rw [h, Subgroup.mem_bot] at hmem
    exact he1 (congrArg Subtype.val hmem)
  · intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.subgroupOf_eq_top.mp h hx)).1

end

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem le_img148_deltaZero_of_ne_botQ (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    [(ker148 A Y).Normal] (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hkt : KType148 A Y e K Le) (he : e ∈ A) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hKJ : K ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hEq : Lift148Eq A Y K J)
    {p f : ℕ} (hf : 1 ≤ f) (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)
    (heΩ : Subgroup.zpowers e ∈ omegaA A) (hLeA : Le ∈ lA A e)
    (hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) ≠ ⊥)
    {D : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hDs : IsSimpleGroup ↥D) (hDY : D ≤ img148 A Y Y)
    (hDC : D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (heD : alpha148 A Y e he ∈ D) :
    D ≤ img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨hJc, -⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hA3' : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hA3' h27
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    have hord : orderOf b = 3 := orderOf_eq_prime (hA3' b hbA) hb1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hbJ
  have he1' : alpha148 A Y e he ≠ 1 := fun h' =>
    he1 (alpha148_injective hA3 he (one_mem A) (h'.trans (map_one _).symm))
  obtain ⟨e', K', Le', p₂, f₂, e₂, hp₂, he'Ω, hLe'A, hK'Le', hK'Y₁, hK', hK'Δ, he'A, hsec', hf₂,
    he₂, hX1eq, hpgl₂, hL₂⟩ := y1_survivorQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift
      hD4 h hY hs ih hYB hP hkt he hJ hKJ hAJ hEq hf hpgl heΩ hLeA hX1
  have hY₁ : Ronan148M.centPre148 A Y J ∈ scriptY A := Ronan148M.centPre148_mem_scriptY hY hAJ
  have hcore : pPrimeCoreOf 3 (Ronan148M.centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    Ronan148J.pPrimeCoreOf_centPre148_eq_of_isComponent hAY hJY hJc h3J
  have hK'M : K' ≤ Y ⊔ A := (hK'Y₁.trans Ronan148M.centPre148_le).trans le_sup_left
  have : Group.IsPerfect ↥K' := isPerfect_of_mem_thetaComponentsIn hK'
  have hK'p : Group.IsPerfect ↥(img148 A Y K') := isPerfect_img148 hK'M
  have hK'nt : Nontrivial ↥(img148 A Y K') := by
    rw [← hX1eq]
    exact (Subgroup.nontrivial_iff_ne_bot _).mpr hX1
  have hAN' : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y K' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (le_normalizer_of_eq_deltaZero hK'Δ)
  have hpglK := hpgl₂
  rw [img148_sup hK'M le_sup_right] at hpglK
  obtain ⟨b', ⟨hb'A, hb'K⟩, hb'1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpglK hK'p hK'nt hAN' hA3' h27
  have hAY₁ : A ⊓ Ronan148M.centPre148 A Y J ≤ Subgroup.zpowers e :=
    inf_centPre148_le_zpowers hA3 he hAJc
  have heK' : alpha148 A Y e he ∈ img148 A Y K' :=
    alpha148_mem_of_inf_of_le hA3 hK'Y₁ Ronan148M.pPrimeCoreOf_le_centPre148 he hAY₁ hb'A hb'K
      hb'1
  have hJne : img148 A Y J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hJnt
  have hlt : Nat.card (Ronan148M.centPre148 A Y J) < Nat.card Y :=
    Ronan148M.card_centPre148_lt hJY (Ronan148M.exists_ne_comm_of_isPerfect hJp hJne)
  have h148₁ : Item148At A (lB A) (Ronan148M.centPre148 A Y J) hY₁ := ih _ hY₁ hlt
  letI := ker148_normal hY₁.2
  have hX1Y₁ : deltaZero A (lB A) (Ronan148M.centPre148 A Y J) ≤
      Ronan148M.centPre148 A Y J := sSup_le fun _ hQ => hQ.2
  have hN₁ := img148_le_normalizer_of_map_normal (A := A) hX1Y₁ h148₁.1
  have hY₁K' : img148 A Y (Ronan148M.centPre148 A Y J) ≤
      Subgroup.normalizer (img148 A Y K' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [← hX1eq, ← Ronan148M.map_img148_compare148 hcore.le le_sup_left,
      ← Ronan148M.map_img148_compare148 hcore.le (hX1Y₁.trans le_sup_left)]
    exact (Subgroup.map_mono hN₁).trans (Subgroup.le_normalizer_map _)
  have hDY₁ : D ≤ img148 A Y (Ronan148M.centPre148 A Y J) := by
    rw [Ronan148J.img148_centPre148_eq]
    exact le_inf hDY hDC
  rw [hX1eq]
  exact le_of_isSimpleGroup_of_le_normalizer' hDs (hDY₁.trans hY₁K') heD heK' he1'

theorem step148PGLConjQ_of (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (hΩ : Step148PGLConjOmega) (hKF : KFact148L3Cent) (hU3 : Step148PGLConjU3) :
    Step148PGLConj := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpq heΩ hLeA y hy D
    hDne hDC hAD heD
  letI := ker148_normal hY.2
  obtain ⟨p, f, hf, hpgl⟩ := hpq
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  have hDs : IsSimpleGroup ↥D := by
    haveI := hJs
    exact ((img148 A Y J).equivMapOfInjective _ (MulAut.conj _).injective).symm.isSimpleGroup
  have hDY : D ≤ img148 A Y Y := by
    rintro _ ⟨j, hj, rfl⟩
    exact (Item148Res5.img148_normal hAY).conj_mem j (img148_mono hJY hj) _
  by_cases hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥
  swap
  · exact le_img148_deltaZero_of_ne_botQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift
      hD4 h hY hs ih hYB hP hkt he hJ hKJ hAJ hEq hf hpgl heΩ hLeA hX1 hDs hDY hDC heD
  exfalso
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hA3' : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hA3' h27
  obtain ⟨a₀, ha₀M, ha₀A, hab⟩ := mem_img148_iff.mp hbA
  have hα : alpha148 A Y a₀ ha₀A = b := (alpha148_eq_mk' ha₀A).trans hab
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    apply hb1
    rw [← hab]
    have h1' : (⟨a₀, ha₀M⟩ : ↥(Y ⊔ A)) = 1 := Subtype.ext h1
    rw [h1', map_one]
  have ha₀J : alpha148 A Y a₀ ha₀A ∈ img148 A Y J := hα ▸ hbJ
  have h142c : Concl142S14 := concl142_forall_of_item142 h422 h45 h142
  have hHe : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D →
      V ≤ Subgroup.centralizer {alpha148 A Y e he} → ¬ 3 ∣ Nat.card V →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ⁅V, img148 A Y A⁆ = ⊥ := fun V hVD hVe hV3 hAV =>
    commutator_eq_bot_of_omega h134 h48 h415 h142c h hY hP hkt he hJ hAJ hEq hf hpgl heΩ hLeA
      hX1 hDY hDC hAD he heΩ hVD hVe hV3 hAV
  have hcent : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D → ¬ 3 ∣ Nat.card V →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ⁅V, img148 A Y A⁆ = ⊥ := by
    by_contra hne
    push Not at hne
    obtain ⟨V, hVD, hV3, hAV, hVne⟩ := hne
    have ha₀Ω := hΩ G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq
      ⟨p, f, hf, hpgl⟩ heΩ hLeA hX1 y hy hDne hDC hAD heD hHe ⟨V, hVD, hV3, hAV, hVne⟩ a₀
      ha₀A ha₀1 ha₀J
    exact hVne (commutator_eq_bot_of_omega h134 h48 h415 h142c h hY hP hkt he hJ hAJ hEq hf hpgl
      heΩ hLeA hX1 hDY hDC hAD ha₀A ha₀Ω hVD
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hDC (hVD hv)) _ ha₀J).symm) hV3 hAV)
  obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
  haveI := hp
  have hDpi : Sec4.IsoLThreePi ↥D p f :=
    isoLThreePi_of_mulEquiv148
      ((img148 A Y J).equivMapOfInjective _ (MulAut.conj _).injective).symm hJpi
  have hbC : b ∈ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hDC hd) b hbJ).symm
  have heAD : alpha148 A Y e he ∈ img148 A Y A ⊓ D := ⟨alpha148_mem_img148 he, heD⟩
  have he1' : alpha148 A Y e he ≠ 1 := fun h' =>
    he1 (alpha148_injective hA3 he (one_mem A) (h'.trans (map_one _).symm))
  have hAD' : img148 A Y A ⊓ D ≤ Subgroup.zpowers (alpha148 A Y e he) := by
    rw [← hAJc]
    exact inf_le_inf_left _ hDC
  have hF3 : ∀ w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      w ^ 3 = 1 → w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hAF hAY hw hw3
  obtain ⟨rfl, hq3, hq9⟩ := hKF _ D (img148 A Y A) p f hf hDpi hAD hAE.1 hA3' h27
    ⟨b, hbA, hb1, hbC⟩ _ heAD he1' hAD' hF3 hcent
  exact hU3 G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq f hf hq3 hq9 hpgl heΩ
    hLeA hX1 y hy hDne hDC hAD heD hcent

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q

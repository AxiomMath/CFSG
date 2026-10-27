module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QY1
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalPGL
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ACentInd
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalProof
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalGroup
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalTwo
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofComp
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalRank
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec14.Item148Res9Proof
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalLeaves

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem normal_of_pglQ (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) (hConj : Step148PGLConj)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    [(ker148 A Y).Normal] (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hkt : KType148 A Y e K Le) (he : e ∈ A) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hKJ : K ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hEq : Lift148Eq A Y K J)
    {p f : ℕ} (hf : 1 ≤ f) (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)
    (heΩ : Subgroup.zpowers e ∈ omegaA A) (hLeA : Le ∈ lA A e) :
    (((deltaZero A (lB A) Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKY : K ≤ Y := hKYC.trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hA3' : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAc' : ∀ a ∈ img148 A Y A, ∀ a' ∈ img148 A Y A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hAE.1.1.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        w ^ 3 = 1 → w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hAF hAY hw hw3
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have hZJ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  have hE9 := Item148Res6.e9Closed_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hA3' h27
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    have hord : orderOf b = 3 := orderOf_eq_prime (hA3' b hbA) hb1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hbJ
  have hAJconj : ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y, img148 A Y A ≤
      Subgroup.normalizer (((img148 A Y J).map (MulAut.conj x).toMonoidHom :
        Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x a ha =>
    Item148Res5.mem_normalizer_map_conj_iff.mpr
      (Item148Res6.conj_mem_normalizer_of_component_inf hJc hZJ hE9 h3J hA3' hAc' h27 hAN hF3
        (alpha148_mem_img148 he) hAJc.le hbA hbJ hb1 x ha)
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have he1' : alpha148 A Y e he ≠ 1 := fun h' =>
    he1 (alpha148_injective hA3 he (one_mem A) (h'.trans (map_one _).symm))
  have hFP : ∀ D : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      3 ∣ Nat.card D → alpha148 A Y e he ∈ D := fun D hDC hAD h3D =>
    mem_of_three_dvd_of_le_centralizer hDC (isPGroup_three_of_pow148 hA3') hAD h3D hF3 hAJc.le
      he3
  have hpass :=
    img148_deltaZero_le_sup_pgl h134 h48 h415 h hY hP hkt he hJ hAJ hEq hf hpgl heΩ hLeA
  have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
    rw [← hJeq]
    exact img148_mono (hKΔ.le.trans (deltaZero_mono148 hKY))
  have hXY : deltaZero A (lB A) Y ≤ Y := sSup_le fun _ hQ => hQ.2
  have hY₁le := Ronan148M.img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J)
    (LB := lB A)
  by_cases hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥
  ·
    have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J := by
      refine le_antisymm ?_ hJX
      rw [hX1, sup_bot_eq] at hpass
      exact hpass
    refine map_normal_of_img148_eq hXY hXJ fun y hy => ?_
    by_contra hny
    have hDne : (img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
        (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom ≠ img148 A Y J := fun h' =>
      hny (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')
    have hDc := Res2LBal.isComponent_conj hJc (QuotientGroup.mk' (ker148 A Y)
      (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))
    have hDC : (img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
        (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom ≤
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun z hz =>
      Res2LBal.mem_centralizer_of_mem_of_ne hJc hDc hDne.symm hz
    have hAD := hAJconj (QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ :
      ↥(Y ⊔ A)))
    have h3D : 3 ∣ Nat.card ((img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
        (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom) := by
      rw [Item148Res5.card_map_conj]
      exact h3J
    have heD := hFP _ hDC hAD h3D
    have hDX1 := hConj G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq
      ⟨p, f, hf, hpgl⟩ heΩ hLeA y hy hDne hDC hAD heD
    rw [hX1] at hDX1
    exact he1' (Subgroup.mem_bot.mp (hDX1 heD))
  obtain ⟨e', K', Le', p₂, f₂, e₂, hp₂, he'Ω, hLe'A, hK'Le', hK'Y₁, hK', hK'Δ, he'A, hsec', hf₂,
    he₂, hX1eq, hpgl₂, hL₂⟩ := y1_survivorQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift
      hD4 h hY hs ih hYB hP hkt he hJ hKJ hAJ hEq hf hpgl heΩ hLeA hX1
  have hY₁ : Ronan148M.centPre148 A Y J ∈ scriptY A := Ronan148M.centPre148_mem_scriptY hY hAJ
  have hcore : pPrimeCoreOf 3 (Ronan148M.centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    Ronan148J.pPrimeCoreOf_centPre148_eq_of_isComponent hAY hJY hJc h3J
  have hK'M : K' ≤ Y ⊔ A := (hK'Y₁.trans Ronan148M.centPre148_le).trans le_sup_left
  have hK'YC : K' ≤ Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer ({e'} : Set G) :=
    le_of_mem_thetaComponentsIn hK'
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
  obtain ⟨hp₂', hK'pi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpglK hK'p hK'nt hAN'
  have hK's : IsSimpleGroup ↥(img148 A Y K') :=
    Main148.isSimpleGroup_of_isLThreeEpsAt148 hf₂ (isLThreeEpsAt_of_isoLThreePi148 hK'pi)
  obtain ⟨b', ⟨hb'A, hb'K⟩, hb'1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpglK hK'p hK'nt hAN' hA3' h27
  have h3K' : 3 ∣ Nat.card ↥(img148 A Y K') := by
    have hord : orderOf b' = 3 := orderOf_eq_prime (hA3' b' hb'A) hb'1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hb'K
  have hAJc' : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
        Subgroup.zpowers (alpha148 A Y e he) := hAJc
  have hAY₁ : A ⊓ Ronan148M.centPre148 A Y J ≤ Subgroup.zpowers e :=
    inf_centPre148_le_zpowers hA3 he hAJc'
  have heK' : alpha148 A Y e he ∈ img148 A Y K' :=
    alpha148_mem_of_inf_of_le hA3 hK'Y₁ Ronan148M.pPrimeCoreOf_le_centPre148 he hAY₁ hb'A hb'K
      hb'1
  have hsecK : Late.sectionCentralizer A K' (pPrimeCoreOf 3 Y) =
      (Subgroup.zpowers e' : Set G) := by
    rw [← hcore]
    exact hsec'
  have hAK'c := img148_inf_centralizer_eq hK'M he'A (hK'YC.trans inf_le_right) hsecK rfl
  have hK'Z : Subgroup.center ↥(img148 A Y K') = ⊥ := by
    have hnc : ∃ a b : ↥(img148 A Y K'), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hcomm : IsMulCommutative ↥(img148 A Y K') := ⟨⟨fun a b => hcon a b⟩⟩
      exact Group.IsPerfect.not_isMulCommutative ↥(img148 A Y K') hcomm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(img148 A Y K')) with
      hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have ha : a ∈ Subgroup.center ↥(img148 A Y K') := ht ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hZK' : img148 A Y K' ⊓
      Subgroup.centralizer (img148 A Y K' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y K')) ∈ Subgroup.center ↥(img148 A Y K') := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hK'Z, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hE9' := Item148Res6.e9Closed_of_isZ3PGLThreeAt hpglK hK'p hK'nt hAN'
  have hAK'conj : IsComponent (img148 A Y K') → ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y,
      img148 A Y A ≤ Subgroup.normalizer (((img148 A Y K').map (MulAut.conj x).toMonoidHom :
        Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun hc x a ha =>
    Item148Res5.mem_normalizer_map_conj_iff.mpr
      (Item148Res6.conj_mem_normalizer_of_component_inf hc hZK' hE9' h3K' hA3' hAc' h27 hAN'
        hF3 (alpha148_mem_img148 he'A) hAK'c.le hb'A hb'K hb'1 x ha)
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
  have hXeq : img148 A Y (deltaZero A (lB A) Y) = img148 A Y (J ⊔ K') := by
    rw [img148_sup hJM hK'M]
    refine le_antisymm ?_ (sup_le hJX ?_)
    · rw [← hX1eq]
      exact hpass
    · rw [← hX1eq]
      exact hY₁le.trans inf_le_left
  have hK'C : img148 A Y K' ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [← hX1eq]
    exact hY₁le.trans inf_le_right
  have hJK' : img148 A Y J ⊓ img148 A Y K' = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ hK'C).trans hZJ.le)
  refine map_normal_of_img148_eq hXY hXeq fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, img148_sup hJM hK'M]
  exact sup_map_conj_eq_of_two hJc hJs hK's hK'p (img148_mono hJY)
    (Item148Res5.img148_normal hAY) Ronan148J.img148_centPre148_eq (img148_mono hK'Y₁) hY₁K'
    hJK' heK' he1' hFP hAJconj hAK'conj h3J h3K' (mem_img148_iff.mpr ⟨y, _, hy, rfl⟩)

end

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem step148PGLCentIndQ_of (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) :
    Ronan148N.Step148PGLCentInd := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl heΩ hLeA
  letI := ker148_normal hY.2
  obtain ⟨p, f, hf, hpgl⟩ := hpgl
  by_cases hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥
  · left
    rw [hX1]
    exact bot_le
  right
  obtain ⟨e', K', Le', p₂, f₂, e₂, hp₂, he'Ω, hLe'A, hK'Le', hK'Y₁, -, -, -, -, hf₂, he₂, hX1eq,
    hpgl₂, hL₂⟩ := y1_survivorQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift hD4 h hY hs ih
      hYB hP hkt he hJ hKJ hAJ hEq hf hpgl heΩ hLeA hX1
  obtain ⟨-, -, hp₁, e₁, he₁, hL₁⟩ :=
    exists_isoLThreePi_lA_of_pgl h hY hs ih hYB hP hkt he hJ hKJ hAJ hEq hf hpgl
  have hpass :=
    img148_deltaZero_le_sup_pgl h134 h48 h415 h hY hP hkt he hJ hAJ hEq hf hpgl heΩ hLeA
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKY : K ≤ Y := hKYC.trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  have hZ : img148 A Y K ⊓
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [hJeq, eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hY₁le := Ronan148M.img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J)
    (LB := lB A)
  have hK'C : img148 A Y K' ≤
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [← hX1eq, hJeq]
    exact hY₁le.trans inf_le_right
  have hX : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K ⊔ img148 A Y K' := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rw [hJeq, ← hX1eq]
      exact hpass
    · exact img148_mono (hKΔ.le.trans (deltaZero_mono148 hKY))
    · rw [← hX1eq]
      exact hY₁le.trans inf_le_left
  have hpgl₁ : IsZ3PGLThreeAt ↥(img148 A Y (K ⊔ A)) p f := by
    rw [img148_sup hKM le_sup_right, hJeq, ← img148_sup hJM le_sup_right]
    exact hpgl
  exact case148Seven_of_pgl_data heΩ he'Ω hLeA hLe'A hP.2.2.2.2.2.2.2.1 hKY hK'Le'
    (hK'Y₁.trans Ronan148M.centPre148_le) hX hK'C hZ hf he₁ hf₂ he₂ hpgl₁ hpgl₂ hL₁ hL₂

end

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step148NormalQ_of (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (hNotK : Step148RankImgGeFieldTopNotK) (hHJ : Step148NormalHJ) (hConj : Step148PGLConj) :
    Step148Normal := by
  intro G _ _ A c L h Y hY hs ih hcases h1
  letI := ker148_normal hY.2
  by_cases hHJb : ∃ B, IsHyperplane A B ∧ ¬ YBOne A (lB A) Y B
  · obtain ⟨B, hB, hnot⟩ := hHJb
    obtain ⟨YB, hYB', htype, hle, b, d, Lb, hconf, hYBle⟩ :=
      step148YB_of_shape step148YBShape_holds G A c L h Y hY hs B hB hnot
    exact hHJ G A c L h Y hY hs ih hcases h1 B hB hnot YB hYB' htype hle b d Lb hconf hYBle
  push Not at hHJb
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exact (h1 (case148One_of_core hCore h hY hs hHJb hcore)).elim
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h Y hY hs hHJb B hB Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h Y hY hs hHJb B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  have halt' : Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e heA K J := by
    rcases halt with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exact (hD4 G A c L h Y hY hs hHJb B Q e K Le hP hkt heA J hJ hKJ hAJ h4).elim
  rcases step148One_holds G A c L h Y hY hs hHJb B Q e K Le hP hkt heA J hJ hKJ hAJ halt' with
    hA | ⟨p, f, hf, hpgl⟩
  ·
    exact normal_of_rank h hY hP hkt heA hJ hKJ hAJ halt' hA
      (step148RankImg_of_notK hNotK G A c L h Y hY hs ih hHJb B Q e K Le hP hkt heA J hJ hKJ
        hAJ halt' hA)
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  rcases halt' with hEq | hTen | hField
  · obtain ⟨heΩ, hLeA, -⟩ :=
      exists_isoLThreePi_lA_of_pgl h hY hs ih hHJb hP hkt heA hJ hKJ hAJ hEq hf hpgl
    exact normal_of_pglQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift hD4 hConj h hY hs ih
      hHJb hP hkt heA hJ hKJ hAJ hEq hf hpgl heΩ hLeA
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM heA
      (eq_zpowers_sup_inf_of_inner148 kf148Inner hAF hAY hJY hAJ heA hCJ
        (Or.inr (Or.inr (Or.inr (Or.inr hTen.2))))) hpgl).elim
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM heA
      (eq_zpowers_sup_inf_of_field148 kf148Field_holds hAF hAY hJ hAJ heA hCJ
        hField) hpgl).elim

end

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step148NormalQ_nhj_of (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (hNotK : Step148RankImgGeFieldTopNotK) (hConj : Step148PGLConj)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) (Y : Subgroup G) (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y)
    (_hcases : letI := ker148_normal hY.2; Item148Cases A (lB A) Y)
    (h1 : ¬ Case148One A (lB A) Y) :
    (((deltaZero A (lB A) Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal := by
  letI := ker148_normal hY.2
  have hHJb : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) Y B := fun B hB =>
    yBOne_of_lB_eq_bot h.isElemAbelian.1 hB
      (lB_eq_bot_of_not_allPointsHJ h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
        (KFacts.KS14.center_nativeJ2_eq_bot h415) h hNHJ hB)
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exact (h1 (case148One_of_core hCore h hY hs hHJb hcore)).elim
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := exists_isPoint148_of_not_allPointsHJ h134 h48 h415 h422 h45 h142 hPΩ
    h hNHJ (h143 G A c L h hNHJ) hY hs hHJb hB hQ hQY hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h Y hY hs hHJb B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  have halt' : Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e heA K J := by
    rcases halt with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exact (hD4 G A c L h Y hY hs hHJb B Q e K Le hP hkt heA J hJ hKJ hAJ h4).elim
  rcases step148One_holds G A c L h Y hY hs hHJb B Q e K Le hP hkt heA J hJ hKJ hAJ halt' with
    hA | ⟨p, f, hf, hpgl⟩
  · exact normal_of_rank h hY hP hkt heA hJ hKJ hAJ halt' hA
      (step148RankImg_of_notK hNotK G A c L h Y hY hs ih hHJb B Q e K Le hP hkt heA J hJ hKJ
        hAJ halt' hA)
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  rcases halt' with hEq | hTen | hField
  · obtain ⟨heΩ, hLeA, -⟩ :=
      exists_isoLThreePi_lA_of_pgl h hY hs ih hHJb hP hkt heA hJ hKJ hAJ hEq hf hpgl
    exact normal_of_pglQ h134 h48 h415 h422 h45 h142 h143 hPΩ hCore hKT hLift hD4 hConj h hY hs ih
      hHJb hP hkt heA hJ hKJ hAJ hEq hf hpgl heΩ hLeA
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM heA
      (eq_zpowers_sup_inf_of_inner148 kf148Inner hAF hAY hJY hAJ heA hCJ
        (Or.inr (Or.inr (Or.inr (Or.inr hTen.2))))) hpgl).elim
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM heA
      (eq_zpowers_sup_inf_of_field148 kf148Field_holds hAF hAY hJ hAJ heA hCJ
        hField) hpgl).elim

end

section

open CFSG.RankThree.PartTwo.Sec14
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem item148CasesQ_nhj_of_s141 (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
    (h143 : Item143NNHJ) (hPΩ : Step148PointOmega) (hCore : Step148Core)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) (hOne : Step148One)
    (hRank : Step148Rank) (hPGL : Step148PGL) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y)
    (hYB1 : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) Y B) :
    letI := ker148_normal hY.2
    Item148Cases A (lB A) Y := by
  let := ker148_normal hY.2
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exact Or.inl (case148One_of_core hCore h hY hs hYB1 hcore)
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := exists_isPoint148_of_not_allPointsHJ h134 h48 h415 h422 h45 h142 hPΩ
    h hNHJ (h143 G A c L h hNHJ) hY hs hYB1 hB hQ hQY hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h Y hY hs hYB1 B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  have halt' : Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e heA K J := by
    rcases halt with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exact (hD4 G A c L h Y hY hs hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ h4).elim
  rcases hOne G A c L h Y hY hs hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' with hA | hPGLc
  · rcases hRank G A c L h Y hY hs ih hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' hA with
      h2 | h3 | h4 | h5
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · rcases hPGL G A c L h Y hY hs ih hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' hPGLc with
      h2 | h7
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q

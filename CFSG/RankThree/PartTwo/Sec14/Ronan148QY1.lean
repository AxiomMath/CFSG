module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AType
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AFrame
public import CFSG.RankThree.PartTwo.Sec14.Ronan148APass
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Ronan148AGroup
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec14.Item148Res9Proof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JCore

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148A
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem y1_survivorQ (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142AllS14)
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
    (hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) ≠ ⊥) :
    ∃ (e' : G) (K' Le' : Subgroup G) (p₂ f₂ e₂ : ℕ) (_ : Fact p₂.Prime),
      Subgroup.zpowers e' ∈ omegaA A ∧ Le' ∈ lA A e' ∧ K' ≤ Le' ∧
      K' ≤ Ronan148M.centPre148 A Y J ∧
      K' ∈ thetaComponentsIn
        (Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer ({e'} : Set G)) ∧
      K' = deltaZero A (lB A) K' ∧ e' ∈ A ∧
      Late.sectionCentralizer A K' (pPrimeCoreOf 3 (Ronan148M.centPre148 A Y J)) =
        (Subgroup.zpowers e' : Set G) ∧ 1 ≤ f₂ ∧ 1 ≤ e₂ ∧
      img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = img148 A Y K' ∧
      IsZ3PGLThreeAt ↥(img148 A Y (K' ⊔ A)) p₂ f₂ ∧
      Sec4.IsoLThreePi (↥Le' ⧸ aschbacherSolvableCore 3 ↥Le') p₂ (f₂ * e₂) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨hJc, -⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hAE.2 h27
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    have hord : orderOf b = 3 := orderOf_eq_prime (hAE.2 b hbA) hb1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hbJ
  have hNHJ : ¬ AllPointsHJ A := by
    intro hall
    obtain ⟨Lx, hLx, ⟨φ⟩⟩ := hall e heΩ
    have h3 : 3 ∣ Nat.card Lx := by
      have hc : Nat.card (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx) = 604800 := by
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
      have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Lx)
      rw [hc] at hdvd
      exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
    have hLL : Lx = Le := (h.chosen136.2 e heΩ Le hLeA).2 Lx hLx.1 h3
    subst hLL
    obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
    have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) p f := by
      rw [hJeq]
      exact hJpi
    have hKJ2 : IsEmpty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      ⟨fun χ => KFacts.KS14.ks17J2NotList.1 p f
        (isoLThreePi_of_mulEquiv148 (p := p) (e := f) χ.symm hKpi)⟩
    exact Ronan148N.false_of_kType148_j2 hkt hKJ2 φ
      (Sec15.center_eq_bot_of_types hLx.1 (h.chosen136.2 e heΩ Lx hLx).1)
  have hY₁ : Ronan148M.centPre148 A Y J ∈ scriptY A := Ronan148M.centPre148_mem_scriptY hY hAJ
  have hY₁Y : Ronan148M.centPre148 A Y J ≤ Y := Ronan148M.centPre148_le
  have hcore : pPrimeCoreOf 3 (Ronan148M.centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    Ronan148J.pPrimeCoreOf_centPre148_eq_of_isComponent hAY hJY hJc h3J
  have hJne : img148 A Y J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hJnt
  have hnc := Ronan148M.exists_ne_comm_of_isPerfect hJp hJne
  have hlt : Nat.card (Ronan148M.centPre148 A Y J) < Nat.card Y :=
    Ronan148M.card_centPre148_lt hJY hnc
  have ih₁ : Ind148 A (lB A) (Ronan148M.centPre148 A Y J) := fun Y' hY' h' =>
    ih Y' hY' (h'.trans hlt)
  have h148₁ : Item148At A (lB A) (Ronan148M.centPre148 A Y J) hY₁ := ih _ hY₁ hlt
  have hAY₁ : A ⊓ Ronan148M.centPre148 A Y J ≤ Subgroup.zpowers e :=
    inf_centPre148_le_zpowers hA3 he hAJc
  have hYB₁ : ∀ B' : Subgroup G, IsHyperplane A B' →
      YBOne A (lB A) (Ronan148M.centPre148 A Y J) B' := fun B' hB' =>
    yBOne_of_le hY₁Y (hYB B' hB')
  letI := ker148_normal hY₁.2
  have hX1Y₁ : deltaZero A (lB A) (Ronan148M.centPre148 A Y J) ≤
      Ronan148M.centPre148 A Y J := sSup_le fun _ hQ => hQ.2
  by_cases hs₁ : Group.IsSolvable ↥(Ronan148M.centPre148 A Y J)
  · exact (hX1 (img148_deltaZero_eq_bot_of_case148One hcore
      (item148Solvable_of_mem_partTwoF hAF _ hY₁ hs₁))).elim
  by_cases hcores : ∀ B' : Subgroup G, IsHyperplane A B' → ∀ Q' ∈ scriptQZero A (lB A),
      Q' ≤ Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer (B' : Set G) →
      ∀ b ∈ B', b ≠ 1 →
        Q' ≤ pPrimeCoreOf 3 (Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer ({b} : Set G))
  · exact (hX1 (img148_deltaZero_eq_bot_of_case148One hcore
      (case148One_of_core hCore h hY₁ hs₁ hYB₁ hcores))).elim
  push Not at hcores
  obtain ⟨B', hB', Q', hQ', hQ'Y, b', hb', hb'1, hQ'b⟩ := hcores
  obtain ⟨e', K', Le', hP'⟩ := exists_isPoint148_of_not_allPointsHJ h134 h48 h415 h422 h45
    h142 hPΩ h hNHJ (h143 G A c L h hNHJ) hY₁ hs₁ hYB₁ hB' hQ' hQ'Y hb' hb'1 hQ'b
  have hkt' : KType148 A (Ronan148M.centPre148 A Y J) e' K' Le' :=
    hKT G A c L h _ hY₁ hs₁ hYB₁ B' Q' e' K' Le' hP'
  have he'A : e' ∈ A := hB'.1 hP'.2.2.2.1
  have he'1 : e' ≠ 1 := hP'.2.2.2.2.1
  have hK' : K' ∈ thetaComponentsIn
      (Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer ({e'} : Set G)) :=
    hP'.2.2.2.2.2.1
  have hK'Δ : K' = deltaZero A (lB A) K' := hP'.2.2.2.2.2.2.1
  have hK'YC : K' ≤ Ronan148M.centPre148 A Y J ⊓ Subgroup.centralizer ({e'} : Set G) :=
    le_of_mem_thetaComponentsIn hK'
  have hK'Y₁ : K' ≤ Ronan148M.centPre148 A Y J := hK'YC.trans inf_le_left
  obtain ⟨J', hJ', hK'J', hAJ', halt'⟩ := hLift G A c L h _ hY₁ hs₁ e' he'A he'1 K' hK'
    (le_normalizer_of_eq_deltaZero hK'Δ) hkt'.1 (type148_of_kType148 h.chosen136 hkt')
  have halt'' : Lift148Eq A (Ronan148M.centPre148 A Y J) K' J' ∨
      Lift148Ten A (Ronan148M.centPre148 A Y J) K' J' ∨
      Lift148Field A (Ronan148M.centPre148 A Y J) e' he'A K' J' := by
    rcases halt' with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exact (hD4 G A c L h _ hY₁ hs₁ hYB₁ B' Q' e' K' Le' hP' hkt' he'A J' hJ' hK'J' hAJ'
        h4).elim
  have hJ'Y₁ : J' ≤ Ronan148M.centPre148 A Y J := le_of_mem_thetaComponentsIn hJ'
  have hJ'M : J' ≤ Ronan148M.centPre148 A Y J ⊔ A := hJ'Y₁.trans le_sup_left
  rcases step148One_holds G A c L h _ hY₁ hs₁ hYB₁ B' Q' e' K' Le' hP' hkt' he'A J' hJ' hK'J'
      hAJ' halt'' with hA1 | ⟨p₂, f₂, hf₂, hpgl₂⟩
  · exfalso
    have hle : A ≤ Subgroup.zpowers e' ⊔ Subgroup.zpowers e := by
      conv_lhs => rw [hA1]
      exact sup_le le_sup_left
        ((le_inf inf_le_left (inf_le_right.trans hJ'Y₁)).trans hAY₁ |>.trans le_sup_right)
    have h9 := card_zpowers_sup_zpowers_le (hAc e' he'A e he) (hA3 e' he'A) (hA3 e he)
    have h27' := Subgroup.card_le_of_le hle
    rw [hA.2] at h27'
    omega
  have : Group.IsPerfect ↥J' := isPerfect_of_mem_thetaComponentsIn hJ'
  have hCJ' := sectionCentralizer_subset_of_le (Y := Ronan148M.centPre148 A Y J) hK'J' hkt'.1
  rcases halt'' with hEq' | hTen' | hField'
  rotate_left
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJ'M he'A
      (eq_zpowers_sup_inf_of_inner148 kf148Inner hAF hY₁.2 hJ'Y₁ hAJ' he'A hCJ'
        (Or.inr (Or.inr (Or.inr (Or.inr hTen'.2))))) hpgl₂).elim
  · exact (false_of_isZ3PGLThreeAt148 kf148PGLAbel hJ'M he'A
      (eq_zpowers_sup_inf_of_field148 kf148Field_holds hAF hY₁.2 hJ' hAJ' he'A
        hCJ' hField') hpgl₂).elim
  obtain ⟨he'Ω, hLe'A, hp₂, e₂, he₂, hL3₂⟩ := exists_isoLThreePi_lA_of_pgl h hY₁ hs₁ ih₁ hYB₁
    hP' hkt' he'A hJ' hK'J' hAJ' hEq' hf₂ hpgl₂
  have hJ'eq : img148 A (Ronan148M.centPre148 A Y J) K' =
      img148 A (Ronan148M.centPre148 A Y J) J' := hEq'
  have hX1eq : img148 A (Ronan148M.centPre148 A Y J)
      (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) =
        img148 A (Ronan148M.centPre148 A Y J) J' := by
    have hJ's : IsSimpleGroup ↥(img148 A (Ronan148M.centPre148 A Y J) J') := by
      have h1 := isSimpleGroup_img148_of_kType148 h hkt'
      rw [hJ'eq] at h1
      exact h1
    obtain ⟨-, hJ'Z⟩ := Item148Res5.isComponent_img148 hY₁.2 hJ' hJ's
    have hZJ' : img148 A (Ronan148M.centPre148 A Y J) J' ⊓
        Subgroup.centralizer (img148 A (Ronan148M.centPre148 A Y J) J' :
          Set (↥(Ronan148M.centPre148 A Y J ⊔ A) ⧸ ker148 A (Ronan148M.centPre148 A Y J))) =
        ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : (⟨x, hx.1⟩ : ↥(img148 A (Ronan148M.centPre148 A Y J) J')) ∈
          Subgroup.center ↥(img148 A (Ronan148M.centPre148 A Y J) J') := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
      rw [hJ'Z, Subgroup.mem_bot] at hxZ
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxZ
    have hpgl₂' := hpgl₂
    rw [img148_sup hJ'M le_sup_right] at hpgl₂'
    have hJ'p : Group.IsPerfect ↥(img148 A (Ronan148M.centPre148 A Y J) J') :=
      isPerfect_img148 hJ'M
    have hJ'nt : Nontrivial ↥(img148 A (Ronan148M.centPre148 A Y J) J') := hJ's.toNontrivial
    have hAN' : img148 A (Ronan148M.centPre148 A Y J) A ≤
        Subgroup.normalizer (img148 A (Ronan148M.centPre148 A Y J) J' :
          Set (↥(Ronan148M.centPre148 A Y J ⊔ A) ⧸ ker148 A (Ronan148M.centPre148 A Y J))) :=
      img148_le_normalizer hAJ'
    obtain ⟨hAE₁, h27₁⟩ := img148_isE27 (Y := Ronan148M.centPre148 A Y J) hA
    obtain ⟨b₂, ⟨hb₂A, hb₂J⟩, hb₂1⟩ :=
      Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl₂' hJ'p hJ'nt hAN' hAE₁.2 h27₁
    have heJ' : alpha148 A (Ronan148M.centPre148 A Y J) e he ∈
        img148 A (Ronan148M.centPre148 A Y J) J' :=
      alpha148_mem_of_inf hA3 hJ'Y₁ he hAY₁ hb₂A hb₂J hb₂1
    have hAX : A ≤ Subgroup.normalizer
        ((deltaZero A (lB A) (Ronan148M.centPre148 A Y J) : Subgroup G) : Set G) :=
      le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
    refine eq_of_le_sup_centralizer_of_three
      (Y := img148 A (Ronan148M.centPre148 A Y J) (Ronan148M.centPre148 A Y J))
      (A := img148 A (Ronan148M.centPre148 A Y J) A)
      (e := alpha148 A (Ronan148M.centPre148 A Y J) e he) ?_ (img148_mono hX1Y₁) ?_ hZJ'
      (img148_le_normalizer_of_map_normal hX1Y₁ h148₁.1)
      (fun P hPY hPN hP3 => Item148Res5.eq_bot_of_le_img148_of_coprime hPY hPN hP3)
      (isPGroup_three_of_pow148 hAE₁.2) (img148_le_normalizer hAX) hAN'
      (fun w hwY hwA hw3 => mem_zpowers_of_commute148 hAF hY₁.2 he hAY₁ hwY hwA hw3) heJ'
    · rw [← hJ'eq]
      exact img148_mono (hK'Δ.le.trans (deltaZero_mono148 hK'Y₁))
    · exact img148_deltaZero_le_of_forall fun R hR hRY =>
        img148_le_sup_centralizer_pgl h hY₁ hkt' hK'YC he'A hJ' hAJ' hEq' hf₂ hpgl₂ hR hRY
  have hX1M : deltaZero A (lB A) (Ronan148M.centPre148 A Y J) ≤
      Ronan148M.centPre148 A Y J ⊔ A := hX1Y₁.trans le_sup_left
  have hK'M : K' ≤ Ronan148M.centPre148 A Y J ⊔ A := hK'Y₁.trans le_sup_left
  refine ⟨e', K', Le', p₂, f₂, e₂, hp₂, he'Ω, hLe'A, hP'.2.2.2.2.2.2.2.1, hK'Y₁, hK', hK'Δ, he'A,
    hkt'.1, hf₂, he₂, ?_, ?_, hL3₂⟩
  · exact img148_eq_of_centPre148 hcore hX1M hK'M (hX1eq.trans hJ'eq.symm)
  · have hKA : img148 A Y (K' ⊔ A) = img148 A Y (J' ⊔ A) := by
      refine img148_eq_of_centPre148 hcore (sup_le hK'M le_sup_right)
        (sup_le hJ'M le_sup_right) ?_
      rw [img148_sup hK'M le_sup_right, img148_sup hJ'M le_sup_right, hJ'eq]
    rw [hKA]
    exact isZ3PGLThreeAt_of_centPre148 hcore (sup_le hJ'M le_sup_right) hpgl₂

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q

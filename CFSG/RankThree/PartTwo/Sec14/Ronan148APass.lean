module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148NCent
import CFSG.RankThree.PartTwo.Sec14.Ronan148NKF
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofComp
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem img148_deltaZero_le_of_forall {A Y : Subgroup G} [(ker148 A Y).Normal]
    {LB : Subgroup G → Subgroup G} {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ R ∈ scriptQZero A LB, R ≤ Y → img148 A Y R ≤ T) :
    img148 A Y (deltaZero A LB Y) ≤ T := by
  have hle : deltaZero A LB Y ≤
      (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype := by
    unfold deltaZero
    refine sSup_le fun R hR => ?_
    obtain ⟨hR0, hRY⟩ := hR
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hRY hg)
    exact ⟨⟨g, hgM⟩, h R hR0 hRY (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

section Certs


theorem img148_le_sup_centralizer_pgl {A L : Subgroup G} {c : G} (hstd : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G}
    (hkt : KType148 A Y e K Le) (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G))
    (he : e ∈ A) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hEq : Lift148Eq A Y K J) {p f : ℕ}
    (hf : 1 ≤ f) (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)
    {LB : Subgroup G → Subgroup G} {R : Subgroup G} (hR : R ∈ scriptQZero A LB)
    (hRY : R ≤ Y) :
    img148 A Y R ≤
      img148 A Y J ⊔ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := (hKY.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKY.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hA : Late.IsE27 A := hstd.isE27'
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h := isSimpleGroup_img148_of_kType148 hstd hkt
    rw [hJeq] at h
    exact h
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAc : ∀ a ∈ img148 A Y A, ∀ a' ∈ img148 A Y A, a * a' = a' * a := fun a ha a' ha' =>
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
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hA3 h27
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf b = 3 := orderOf_eq_prime (hA3 b hbA) hb1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hbJ
  have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
  have hRcomm : img148 A Y R ≤ ⁅img148 A Y R, img148 A Y A⁆ := by
    conv_lhs => rw [hR.2]
    rw [Item148PtRes.img148_commutator hRM le_sup_right]
  have hnorm : img148 A Y R ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    Item148Res6.le_normalizer_of_component_inf hJc hZJ hE9 h3J hA3 hAc h27 hAN hF3
      (alpha148_mem_img148 he) hAJc.le hbA hbJ hb1 hRcomm
  have hR3 : ¬ 3 ∣ Nat.card R := (isPiSubgroup_piCompl_iff Nat.prime_three R).mp hR.1.1.2.1
  have hcomm' : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
    rw [← Item148PtRes.img148_commutator hRM le_sup_right, ← hR.2]
  have hAc' : IsMulCommutative ↥(img148 A Y A) := Item148PtRes.isMulCommutative_img148 hcomm
  exact kf148PGLInnerV _ (img148 A Y J) (img148 A Y A) (img148 A Y R) p f hf hpgl' hJp hAc'
    hAN hnorm (img148_le_normalizer hR.1.1.2.2) (Item148PtRes.not_three_dvd_card_img148 hR3) hcomm'

theorem img148_deltaZero_le_sup_pgl (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] {B Q : Subgroup G} {e : G} {K Le : Subgroup G}
    (hP : IsPoint148 A (lB A) Y B Q e K Le) (hkt : KType148 A Y e K Le) (he : e ∈ A)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hEq : Lift148Eq A Y K J) {p f : ℕ} (hf : 1 ≤ f)
    (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)
    (heΩ : Subgroup.zpowers e ∈ omegaA A) (hLeA : Le ∈ lA A e) :
    img148 A Y (deltaZero A (lB A) Y) ≤
      img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
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
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  have hZ : img148 A Y J ⊓
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
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have heJ : alpha148 A Y e he ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have h1 : alpha148 A Y e he ∈ img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [hAJc]
      exact Subgroup.mem_zpowers _
    exact h1.2
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hAbar3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hAbar3 h27
  obtain ⟨a₀, ha₀, rfl⟩ := Ronan148N.exists_alpha148_eq hbA
  have ha₀e : a₀ ∉ Subgroup.zpowers e := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hb1
    have h1 : alpha148 A Y a₀ ha₀ ∈ img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      refine ⟨hbJ, ?_⟩
      have e1 : alpha148 A Y a₀ ha₀ = alpha148 A Y e he ^ k := by
        subst hk
        rw [alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
        rfl
      rw [e1]
      exact Subgroup.zpow_mem _ heJ k
    rw [hZ] at h1
    exact h1
  have hNHJ : ¬ AllPointsHJ A := by
    intro hall
    obtain ⟨Le', hLe', ⟨φ⟩⟩ := hall e heΩ
    have h3 : 3 ∣ Nat.card Le' := by
      have hc : Nat.card (↥Le' ⧸ aschbacherSolvableCore 3 ↥Le') = 604800 := by
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
      have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le')
      rw [hc] at hdvd
      exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
    have hLL : Le' = Le := (h.chosen136.2 e heΩ Le hLeA).2 Le' hLe'.1 h3
    subst hLL
    obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
    have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) p f := by
      rw [hJeq]
      exact hJpi
    have hKJ2 : IsEmpty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      ⟨fun χ => KFacts.KS14.ks17J2NotList.1 p f
        (isoLThreePi_of_mulEquiv148 (p := p) (e := f) χ.symm hKpi)⟩
    exact Ronan148N.false_of_kType148_j2 hkt hKJ2 φ
      (Sec15.center_eq_bot_of_types hLe'.1 (h.chosen136.2 e heΩ Le' hLe').1)
  have hLB : ∀ B' : Subgroup G, IsHyperplane A B' → lB A B' = ⊥ :=
    fun B' hB' => lB_eq_bot_of_not_allPointsHJ h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      h415 (KFacts.KS14.center_nativeJ2_eq_bot h415) h hNHJ hB'
  have hQJ : ∀ Q' ∈ scriptQZero A (lB A), Q' ≤ Y → img148 A Y Q' ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun Q' hQ' hQ'Y => img148_le_sup_centralizer_pgl h hY hkt hKYC he hJ hAJ hEq hf hpgl hQ' hQ'Y
  have hKF' : ∀ (t : G) (ht : t ∈ A), ∃ s ∈ img148 A Y J ⊓
      Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      ∀ y ∈ pPrimeCoreOf 3 (img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))),
        alpha148 A Y t ht * y * (alpha148 A Y t ht)⁻¹ = s * y * s⁻¹ := by
    intro t ht
    have hta : alpha148 A Y t ht * alpha148 A Y a₀ ha₀ =
        alpha148 A Y a₀ ha₀ * alpha148 A Y t ht := by
      rw [← alpha148_mul, ← alpha148_mul]
      congr 1
      exact hcomm t ht a₀ ha₀
    exact Ronan148N.kf148PGLCentAct _ (img148 A Y J) (img148 A Y A) p f hf hpgl' hJp hAN _ hbJ
      hb1 (hAbar3 _ hbA) _ (Subgroup.mem_sup_right (alpha148_mem_img148 ht)) hta
  have hpass := Ronan148N.img148_deltaZero_le_sup148 hA hAY hJY hAJ he he1 ha₀ hbJ ha₀e heJ hZ
    hKF' hLB hQJ
  exact hpass

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148A

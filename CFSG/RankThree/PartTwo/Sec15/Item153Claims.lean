module

public import CFSG.RankThree.PartTwo.Sec15.Item153
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Item1411
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def HasFaithfulE9 (Y : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ Y ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
    Late.sectionCentralizer E Y ((aschbacherSolvableCore 3 ↥Y).map Y.subtype) ⊆ {1}

section Members

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem facts_of_mem_maximalTwoLocalsContaining (h : Sec14Std G A c L) {Y M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    Y ≤ M ∧ A ≤ M ∧ M ∈ scriptY2 A ∧ generalizedFitting ↥M = CFSG.pCore 2 ↥M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYA : Y ⊔ A ≤ M := fun x hx => hM.2 hx
  obtain ⟨P, hP1, hP2, hMP⟩ := hM.1.1
  have hPM : P ≤ M := by
    rw [hMP]
    exact Subgroup.le_normalizer
  have hO2 : P ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPM hMP.le hP2
  have hMtop : M ≠ ⊤ := by
    rw [hMP]
    exact normalizer_ne_top_of_isPGroup h.toTheoremFourHyp.isSimpleGroup
      h.toTheoremFourHyp.nonabelian hP1 hP2
  refine ⟨le_sup_left.trans hYA, le_sup_right.trans hYA,
    ⟨⟨hMtop, (le_sup_right.trans hYA).trans Subgroup.le_normalizer⟩,
      fun h0 => hP1 (le_bot_iff.mp (h0 ▸ hO2))⟩, ?_⟩
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
    (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hM.1.1)

theorem mem_thetaComponentsIn_of_item152 (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    Y ∈ thetaComponentsIn M := by
  obtain ⟨hYM, -, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨X, hX, hYX, hX0⟩ := h152 Y hY.prop.1 M hM2 hYM hF
  rwa [hY.eq_of_le hX0 hYX]

theorem map_conj_eq_of_hasFaithfulE9 (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hE : HasFaithfulE9 Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) {t : G}
    (ht : t ∈ M) : Y.map (MulAut.conj t).toMonoidHom = Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_item152 h h152 hY hM
  change Y'.map M.subtype = Y at hYY'
  set σ : ↥M ≃* ↥M := MulAut.conj (⟨t, ht⟩ : M) with hσ
  have hσY : (Y'.map σ.toMonoidHom).map M.subtype = Y.map (MulAut.conj t).toMonoidHom := by
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hY'' : Y'.map σ.toMonoidHom ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three σ hY'
  have hne' : Y' ≠ Y'.map σ.toMonoidHom := by
    intro heq
    apply hne
    rw [← hσY, ← heq]
    exact hYY'
  have hcθ := commutator_le_of_mem_thetaComponents hY' hY'' hne'
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥M).Normal := Subgroup.normal_of_characteristic _
  obtain ⟨E, hEY, hEab, hE9, hEc⟩ := hE
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  have hE₁map : E₁.map M.subtype = E := by
    rw [hE₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hEY.trans hYM)]
  have hE₁Y' : E₁ ≤ Y' := by
    rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective, hE₁map, hYY']
    exact hEY
  have hE₁card : Nat.card E₁ = 9 := by
    rw [← hE9, ← hE₁map, Subgroup.card_map_of_injective M.subtype_injective]
  have hE₁ab : CFSG.Open.IsElemAbelian 3 E₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : ((a : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp a.2
      have hb : ((b : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp b.2
      have hab : ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G) :=
        congrArg Subtype.val (hEab.1.is_comm.comm (⟨_, ha⟩ : E) ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact hab
    · exact Subtype.ext (hEab.2 _ (Subgroup.mem_subgroupOf.mp hx))
  set E₂ : Subgroup ↥M := E₁.map σ.toMonoidHom with hE₂
  have hE₂ab : CFSG.Open.IsElemAbelian 3 E₂ :=
    CFSG.SectionRank.isElemAbelian_map hE₁ab σ.toMonoidHom
  have hE₂card : Nat.card E₂ = 9 := by
    rw [hE₂, Subgroup.card_map_of_injective σ.injective, hE₁card]
  have hE₂Y : E₂ ≤ Y'.map σ.toMonoidHom := Subgroup.map_mono hE₁Y'
  have hc : ⁅E₁, E₂⁆ ≤ aschbacherSolvableCore 3 ↥M :=
    (Subgroup.commutator_mono hE₁Y' hE₂Y).trans hcθ
  have hd : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y⁻¹ ∈ aschbacherSolvableCore 3 ↥M → x = 1 := by
    intro x hx y hy hxy
    have hxz : ∀ z ∈ Y', ⁅x, z⁆ ∈ aschbacherSolvableCore 3 ↥M := by
      intro z hz
      have hyz : ⁅z, y⁆ ∈ aschbacherSolvableCore 3 ↥M :=
        hcθ (Subgroup.commutator_mem_commutator hz (hE₂Y hy))
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) x =
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) y := by
        have h1' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) (x * y⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hxy
        rwa [map_mul, map_inv, mul_inv_eq_one] at h1'
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅z, y⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hyz
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅x, z⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, h1]
        exact h2.symm
      exact (QuotientGroup.eq_one_iff _).mp h3
    have hxE : ((x : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hθN, hθs, hθ3'⟩ := map_aschbacherSolvableCore_facts M
    have hxG : ((x : ↥M) : G) ∈
        Late.sectionCentralizer E Y ((aschbacherSolvableCore 3 ↥Y).map Y.subtype) := by
      refine ⟨hxE, fun z hz => ?_⟩
      rw [← hYY'] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hxY : x ∈ Y' := hE₁Y' hx
      have hmemY : ⁅x, z'⁆ ∈ Y' := by
        rw [commutatorElement_def]
        exact Y'.mul_mem (Y'.mul_mem (Y'.mul_mem hxY hz') (Y'.inv_mem hxY)) (Y'.inv_mem hz')
      have hmem : ((⁅x, z'⁆ : ↥M) : G) ∈
          (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y :=
        ⟨Subgroup.mem_map_of_mem _ (hxz z' hz'), hYY' ▸ Subgroup.mem_map_of_mem _ hmemY⟩
      have := inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3' hmem
      rwa [commutatorElement_def] at this
    have hx1 : ((x : ↥M) : G) = 1 := hEc hxG
    exact Subtype.ext hx1
  have h4 := four_le_pRank_of_commutator_le (aschbacherSolvableCore 3 ↥M) hθ3 hE₁ab hE₂ab
    hE₁card hE₂card hc hd
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

end Members

section Restricted

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem claim153NormalE9_of (h : Sec14Std G A c L) (h152 : Item152 A (lB A)) :
    ∀ Y ∈ scriptY0Star A (lB A), HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        M ≤ Subgroup.normalizer (Y : Set G) := fun _ hY hE _ hM _ ht =>
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_eq_of_hasFaithfulE9 h h152 hY hE hM ht)

theorem maximalTwoLocalsContaining_eq_of_hasFaithfulE9 (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hE : HasFaithfulE9 Y) :
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
      {Subgroup.normalizer (Y : Set G)} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := claim153NormalE9_of h h152 Y hY hE
  have hY0 := hY.prop
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY0.2.2
  have hNN : Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
  obtain ⟨M₀, hle, hM₀⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY0.1.1.2
  have hM₀m : M₀ ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM₀, fun x hx => hle (hNN (hYA hx))⟩
  have heq : M₀ = Subgroup.normalizer (Y : Set G) := le_antisymm (hn M₀ hM₀m) (hNN.trans hle)
  ext M
  refine ⟨fun hM => ?_, fun hM => ?_⟩
  · rw [Set.mem_singleton_iff, ← heq]
    by_contra hne
    exact hM.1.2 M₀ (lt_of_le_of_ne ((hn M hM).trans heq.ge) hne) hM₀.1
  · rw [Set.mem_singleton_iff] at hM
    rw [hM, ← heq]
    exact hM₀m

theorem normalizer_x_eq_of_hasFaithfulE9 (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (h152 : Item152 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hE : HasFaithfulE9 Y) :
    Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) =
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNX, -, -, hX2⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
  have hNXle : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer hY.prop.1.1.2
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hNXle (hNX (hYA hx)))⟩
  exact le_antisymm ((hNXle.trans hle).trans (claim153NormalE9_of h h152 Y hY hE M hMm)) hNX

theorem claim153ObsE9_of (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (h152 : Item152 A (lB A)) :
    ∀ Y ∈ scriptY0Star A (lB A), HasFaithfulE9 Y →
      ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
        S ≤ Subgroup.normalizer (Y : Set G) := by
  intro Y hY hE S hS
  rw [← normalizer_x_eq_of_hasFaithfulE9 h h149 h152 hY hE]
  exact hS.prop.1.2

end Restricted

omit [Finite G] in
theorem oPrimeResidualOf_delta_le_of_forall_conj {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (h149 : Item149 A LB) {Y M : Subgroup G} (hM : M ∈ scriptY A)
    (horb : ∀ t ∈ M, A ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    oPrimeResidualOf 3 (delta A LB M) ≤
      oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) := by
  obtain ⟨heq, -, -⟩ := h149 M hM
  rw [heq]
  have hA : A ≤ Subgroup.normalizer (Y : Set G) := by
    have := horb 1 M.one_mem
    rwa [Late.map_conj_one] at this
  have hQ : ∀ Q ∈ collectionIn (scriptQZero A LB) M, Q ≤ Subgroup.normalizer (Y : Set G) := by
    rintro Q ⟨⟨-, hQA⟩, hQM⟩
    rw [hQA, Subgroup.commutator_le]
    intro x hx a ha
    have hxM : x ∈ M := hQM (hQA ▸ hx)
    have e1 : Y.map (MulAut.conj a⁻¹).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA (A.inv_mem ha))
    have e2 : (Y.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        Y.map (MulAut.conj x⁻¹).toMonoidHom :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (horb x⁻¹ (M.inv_mem hxM) ha)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc Y.map (MulAut.conj ⁅x, a⁆).toMonoidHom
        = (((Y.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom).map
            (MulAut.conj a).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
          rw [Late.map_conj_map_conj, Late.map_conj_map_conj, Late.map_conj_map_conj,
            commutatorElement_def]
      _ = Y := by
          rw [e1, e2, Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
  have hle : deltaZero A LB M ≤ deltaZero A LB (Subgroup.normalizer (Y : Set G)) :=
    sSup_le fun Q hQ' => le_deltaZero hQ'.1 (hQ Q hQ')
  exact (oPrimeResidualOf_mono 3 (inSubgroup_oResidual_le_self 2 _)).trans
    (oPrimeResidualOf_mono 3 (hle.trans (deltaZero_le_delta _)))

@[expose] def Claim153TwinX (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, ¬ HasFaithfulE9 Y →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) →
        oPrimeResidualOf 3 (delta A LB M) =
          oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G)))

theorem claim153Twin_of_twinX {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A)) (htx : Claim153TwinX A (lB A)) :
    Claim153Twin A (lB A) := by
  intro Y hY M hM hMY
  have hE : ¬ HasFaithfulE9 Y := fun hE => hMY (claim153NormalE9_of h h152 Y hY hE M hM)
  rw [← htx Y hY hE M hM hMY]
  exact normalizer_le_normalizer_oPrimeResidualOf_delta h149
    (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1.1

end CFSG.RankThree.PartTwo.Sec15

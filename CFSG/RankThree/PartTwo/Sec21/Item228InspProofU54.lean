module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4
import CFSG.RankThree.PartTwo.Sec21.Item228InspProofRefl
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL)

@[expose] def U54Torus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G), Nonempty (X ≃* projSU 5 2 2) → T ≤ X →
    IsElemAbelian 3 T → Nat.card T = 3 ^ 2 →
      ∃ Y : Subgroup G, Y ≤ X ∧ T ≤ Y ∧ Nonempty (Y ≃* projSU 4 2 2) ∧
        ∀ ℓ : Subgroup G, ℓ ≤ T → Nat.card ℓ = 3 →
          perfCent X ℓ = perfCent Y ℓ ∨
            (StatedClassicalModel (perfCent X ℓ) .PSU 3 2 2 ∧ T ⊓ perfCent X ℓ ≤ perfCent Y ℓ)

namespace Item228InspProof

variable {G : Type} [Group G]

theorem innerData_of_U54 [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    {X : Subgroup G} (hX : X ∈ lStar A) (eX : X ≃* projSU 5 2 2) : InnerData A X := by
  have hG := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAX := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
  have : IsSimpleGroup X := eX.isSimpleGroup
  have hperf : Group.IsPerfect X := isPerfect_of_mem_thetaComponentFamily hX.1
  have hZ := Item223PrintProof.center_eq_bot_of_isSimpleGroup_of_isPerfect hperf
  have hθ := inSubgroup_theta_eq_bot_of_mulEquiv hperf eX
  have hθ' : aschbacherSolvableCore 3 X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hθ
  have eθ : X ⧸ aschbacherSolvableCore 3 X ≃* projSU 5 2 2 :=
    (mulEquiv_lBar_of_theta_eq_bot hθ).symm.trans eX
  have hinner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X := fun x hxA hout =>
    Sec4.false_of_cubeInner eθ (Sec4.cubeInner_of_not_three_dvd_card_outer Sec4.outU54_holds)
      (hAe.2 x hxA) hout
  exact innerData_of_inner h66 hpair hA27 hX haA ha1 hXa hAX hZ hθ' hinner

theorem statedClassicalModel_L24_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* projSL 2 (GaloisField 2 2)) : StatedClassicalModel X .PSL 2 2 2 :=
  ⟨⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2, inferInstance, inferInstance,
    GaloisField.card 2 2 (by norm_num),
    ⟨e.trans ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (StatedSL 2 (GaloisField 2 2))).trans (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartTwo.Census.projImage_statedSL 2 (GaloisField 2 2)))).symm⟩⟩

theorem root_facts_sub [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {X Y : Subgroup G}
    (hD : InnerData A X) (hYX : Y ≤ X) {φ : MulAut A} (hφ : φ ∈ dStar A) (hKX : kOf A φ ≤ X)
    (hS : ∀ ℓ : Subgroup G, ℓ ≤ A ⊓ X → Nat.card ℓ = 3 →
      (perfCent X ℓ = perfCent Y ℓ ∧ ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (perfCent Y ℓ ≃* projSL 2 (GaloisField 2 n))) ∨
      (StatedClassicalModel (perfCent X ℓ) .PSU 3 2 2 ∧
        StatedClassicalModel (perfCent Y ℓ) .PSL 2 2 2 ∧ A ⊓ X ⊓ perfCent X ℓ ≤ perfCent Y ℓ)) :
    Nat.card (A ⊓ X ⊓ fixedInG A φ : Subgroup G) = 3 ∧
      A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A φ ∧
      kOf A φ = perfCent Y (A ⊓ X ⊓ fixedInG A φ) ∧
      (commOf φ).map A.subtype ≤ A ⊓ X := by
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨a, haA, -, hXa⟩ := hD.exists_center
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  have hjX : (j : G) ∈ X := hKX hjK
  set T := A ⊓ X with hTdef
  have hcA : (commOf φ).map A.subtype ≤ T :=
    le_inf (Subgroup.map_subtype_le _) ((map_commOf_le_kOf h222 hpair hK hφ).trans hKX)
  have hfix : A ⊓ Subgroup.centralizer (X : Set G) ≤ fixedInG A φ := by
    rintro z ⟨hzA, hzC⟩
    refine ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf, ← hj]
    apply Subtype.ext
    rw [wConj_apply]
    change (j : G) * z * (j : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzC j hjX, mul_inv_cancel_right]
  have hjT : (j : G) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨j.2, Subgroup.le_normalizer hjX⟩
  have hjφ : wConj A ⟨(j : G), j.2⟩ = φ := hj
  obtain ⟨hρ, -, hfixT⟩ := Item223PrintProof.restrict_reflection inf_le_left hAc hA3 j.2 hjT
    (by rw [hjφ]; exact hφ.1) (by rw [hjφ]; exact hcA)
  rw [hjφ] at hfixT
  have hTc : ∀ a b : T, a * b = b * a :=
    (Sec5.isElemAbelian_of_le hAe inf_le_left).1.is_comm.comm
  have hℓ3 : Nat.card (T ⊓ fixedInG A φ : Subgroup G) = 3 := by
    rw [← hfixT, fixedInG, Subgroup.card_map_of_injective T.subtype_injective]
    have h := card_eq_three_mul_card_fixed hTc hρ
    rw [hD.card_inf] at h
    omega
  have hcentEq : X ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
      X ⊓ Subgroup.centralizer ((T ⊓ fixedInG A φ : Subgroup G) : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
    · rintro g ⟨hgX, hg⟩
      exact ⟨hgX, Item223PrintProof.mem_centralizer_of_mem_centralizer_inf hD.decomp
        (Subgroup.map_subtype_le _) hfix hgX hg⟩
  have hPX : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) =
      perfCent X (T ⊓ fixedInG A φ) := by
    rw [hcentEq]
    rfl
  have hφX : φ ∈ starOf A X := ⟨j, Subgroup.mem_subgroupOf.mpr hjX, hj⟩
  have hKeq : kOf A φ = perfCent Y (T ⊓ fixedInG A φ) := by
    rcases hS (T ⊓ fixedInG A φ) inf_le_left hℓ3 with ⟨hXY, n, hn2, ⟨e⟩⟩ | ⟨hU, hL24, hAY⟩
    ·
      have e' : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
          projSL 2 (GaloisField 2 n) :=
        (MulEquiv.subgroupCongr (hPX.trans hXY)).trans e
      have := isSimpleGroup_projSL_two hn2
      have hK0 := Item222Proof.kZero_eq_perfectResidual hAF haA hXa hφX hφ.1.1 e'.isSimpleGroup
        (exists_not_commute_of_mulEquiv_projSL e') (three_dvd_card_of_mulEquiv_projSL e')
      have hU : ¬ StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
        rw [hK0]
        exact Item222Proof.not_statedClassicalModel_U34_of_mulEquiv (by omega) e'
      rw [kOf_eq_kZero hU, hK0, hPX, hXY]
    ·
      have hU' : StatedClassicalModel
          (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (fixedInG A φ : Set G)))
          .PSU 3 2 2 := by
        rw [hPX]
        exact hU
      have hSimp := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 2 hU').2
      have hcard : Nat.card
          (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer (fixedInG A φ : Set G))) =
            62400 := by
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hU').2.1 rfl]
        decide
      have hK0 := Item222Proof.kZero_eq_perfectResidual hAF haA hXa hφX hφ.1.1 hSimp
        (Item222Proof.exists_not_commute_of_isSimpleGroup (by rw [hcard]; norm_num)
          (by rw [hcard]; norm_num)) (by rw [hcard]; norm_num)
      have hU0 : StatedClassicalModel (kZero A φ) .PSU 3 2 2 := by
        rw [hK0]
        exact hU'
      obtain ⟨K, hKp, hKu⟩ := hK φ hφ hU0
      have hspec := kOf_spec hU0 ⟨K, hKp⟩
      have hYp : perfCent Y (T ⊓ fixedInG A φ) ≤ kZero A φ ∧
          StatedClassicalModel (perfCent Y (T ⊓ fixedInG A φ)) .PSL 2 2 2 ∧
          A ⊓ kZero A φ ≤ perfCent Y (T ⊓ fixedInG A φ) := by
        refine ⟨?_, hL24, ?_⟩
        · rw [hK0, hPX]
          exact Sec18.inSubgroup_perfectResidual_mono (inf_le_inf_right _ hYX)
        · rw [hK0, hPX]
          rintro x ⟨hxA, hxP⟩
          have hxX : x ∈ X := ((Subgroup.map_subtype_le _).trans inf_le_left) hxP
          exact hAY ⟨⟨hxA, hxX⟩, hxP⟩
      exact (hKu _ hspec).trans (hKu _ hYp).symm
  exact ⟨hℓ3, hfix, hKeq, hcA⟩

theorem not_le_of_U34 [Finite G] {P Q : Subgroup G} (hPQ : P ≤ Q)
    (hQ : StatedClassicalModel Q .PSU 3 2 2) (e : P ≃* projSL 2 (GaloisField 2 (2 * 2))) :
    False := by
  have hcard : Nat.card Q = 62400 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hQ).2.1 rfl]
    decide
  have hP : Nat.card P = 2 ^ (2 * 2) * ((2 ^ (2 * 2)) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_projSL_two (2 * 2) (by norm_num)]
  have hd := Subgroup.card_dvd_of_le hPQ
  rw [hcard, hP] at hd
  norm_num at hd

theorem insp228_of_U54 [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hU4 : U4EvenTorus) (hU5 : U54Torus) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) {X : Subgroup G} (hX : X ∈ lStar A)
    (hKX : kOf A φ ≤ X) (hJX : kOf A ψ ≤ X) (eX : X ≃* projSU 5 2 2) :
    Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ := by
  have hK := hKW G A E U c L hpair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hne' : φ ≠ ψ := fun h => hne h.symm
  have hD := innerData_of_U54 h45 h66 hpair hA27 hX eX
  set T := A ⊓ X with hTdef
  have hTe : IsElemAbelian 3 T := Sec5.isElemAbelian_of_le hAe inf_le_left
  obtain ⟨Y, hYX, hTY, ⟨eY⟩, hcmp⟩ := hU5 G X T ⟨eX⟩ inf_le_right hTe hD.card_inf
  obtain ⟨-, hlines, hpairs⟩ := hU4 G Y T 2 (by norm_num) even_two ⟨eY⟩ hTY hTe hD.card_inf
  have hS : ∀ ℓ : Subgroup G, ℓ ≤ T → Nat.card ℓ = 3 →
      (perfCent X ℓ = perfCent Y ℓ ∧ ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (perfCent Y ℓ ≃* projSL 2 (GaloisField 2 n))) ∨
      (StatedClassicalModel (perfCent X ℓ) .PSU 3 2 2 ∧
        StatedClassicalModel (perfCent Y ℓ) .PSL 2 2 2 ∧ A ⊓ X ⊓ perfCent X ℓ ≤ perfCent Y ℓ) := by
    intro ℓ hℓ h3
    rcases hcmp ℓ hℓ h3 with hXY | ⟨hU, hTP⟩
    · refine Or.inl ⟨hXY, ?_⟩
      rcases hlines ℓ hℓ h3 with h | h
      · exact ⟨2, le_rfl, h⟩
      · exact ⟨2 * 2, by norm_num, h⟩
    · refine Or.inr ⟨hU, ?_, hTP⟩
      have hYXℓ : perfCent Y ℓ ≤ perfCent X ℓ :=
        Sec18.inSubgroup_perfectResidual_mono (inf_le_inf_right _ hYX)
      rcases hlines ℓ hℓ h3 with h | h
      · obtain ⟨e⟩ := h
        exact statedClassicalModel_L24_of_mulEquiv e
      · obtain ⟨e⟩ := h
        exact (not_le_of_U34 hYXℓ hU e).elim
  obtain ⟨hℓ₁3, hfix₁, hK₁, hc₁T⟩ := root_facts_sub h222 hpair hK hD hYX hφ hKX hS
  obtain ⟨hℓ₂3, hfix₂, hK₂, hc₂T⟩ := root_facts_sub h222 hpair hK hD hYX hψ hJX hS
  have hc₁3 : Nat.card ((commOf φ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hφ.1.2
  have hc₂3 : Nat.card ((commOf ψ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hψ.1.2
  have hℓne : T ⊓ fixedInG A φ ≠ T ⊓ fixedInG A ψ := fun h =>
    fixedSubgroupOf_ne_of_ne h222 hpair hK hφ hψ hne' (Subgroup.map_injective
      A.subtype_injective (Item223PrintProof.fixedInG_eq_of_inf_eq hD.decomp
        (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hfix₁ hfix₂ h))
  have hc₁S : (commOf φ).map A.subtype ≤ perfCent Y (T ⊓ fixedInG A φ) :=
    hK₁ ▸ map_commOf_le_kOf h222 hpair hK hφ
  have hc₂S : (commOf ψ).map A.subtype ≤ perfCent Y (T ⊓ fixedInG A ψ) :=
    hK₂ ▸ map_commOf_le_kOf h222 hpair hK hψ
  obtain ⟨hL1, hL2⟩ := hpairs _ _ _ _ inf_le_left inf_le_left hc₁T hc₂T
    hℓ₁3 hℓ₂3 hc₁3 hc₂3 hℓne hc₁S hc₂S
  have hcℓ : ∀ {χ χ' : MulAut A}, (commOf χ).map A.subtype = T ⊓ fixedInG A χ' →
      commOf χ ≤ fixedSubgroupOf χ' := fun h =>
    (Subgroup.map_le_map_iff_of_injective A.subtype_injective).mp (h.le.trans inf_le_right)
  have hYle : ∀ {Z : Subgroup G}, Z = Y → Z ≤ X := fun h => h ▸ hYX
  refine ⟨fun hc => ?_, fun hnc => ?_⟩
  ·
    have h₂ : commOf φ ≤ fixedSubgroupOf ψ :=
      commOf_le_fixedSubgroupOf_of_commute hAc hA3 hψ.1 hφ.1 hc.symm hne
    have hc₁ℓ₂ : (commOf φ).map A.subtype = T ⊓ fixedInG A ψ :=
      Subgroup.eq_of_le_of_card_ge (le_inf hc₁T (Subgroup.map_mono h₂)) (by rw [hℓ₂3, hc₁3])
    obtain ⟨hc₂ℓ₁, h | ⟨hY, ⟨eK⟩, ⟨eJ⟩, g, hgY, hgT, hg₁, hg₂⟩⟩ := hL1 hc₁ℓ₂
    · left
      rw [hK₁, hK₂]
      exact h
    · have hKJ : kOf A φ ⊔ kOf A ψ = Y := by
        rw [hK₁, hK₂]
        exact hY
      refine Or.inr (Or.inr ⟨?_, ?_, ?_, ⟨X, hX, hYle hKJ, ⟨eX⟩⟩, ?_⟩)
      · rw [hK₁]
        exact ⟨eK⟩
      · rw [hK₂]
        exact ⟨eJ⟩
      · rw [hKJ]
        exact ⟨eY⟩
      · refine exists_wStar_conj_of_swap hD hAe hφ.1 hψ.1 hfix₁ hfix₂ (hYX hgY) hgT hg₁ ?_
        rw [hc₁ℓ₂, hg₂, hc₂ℓ₁]
  ·
    have hc₁ne : (commOf φ).map A.subtype ≠ T ⊓ fixedInG A ψ := by
      intro h
      obtain ⟨hc₂ℓ₁, -⟩ := hL1 h
      exact hnc (commute_of_commOf_le hAc hA3 hφ.1.1 (hcℓ h) (hcℓ hc₂ℓ₁))
    have hKJ : kOf A φ ⊔ kOf A ψ = Y := by
      rw [hK₁, hK₂]
      exact hL2 hc₁ne
    refine Or.inr ⟨?_, X, hX, hYle hKJ, ⟨eX⟩⟩
    rw [hKJ]
    exact ⟨eY⟩

end Item228InspProof

open Item228InspProof

theorem insp228U54_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hU4 : U4EvenTorus) (hU5 : U54Torus) : Insp228U54 := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam _
  obtain ⟨-, -, -, -, -, ⟨eX⟩⟩ := hfam
  exact insp228_of_U54 h45 h66 h222 hKW hU4 hU5 hpair hA27 hφ hψ hne hX hKX hJX eX

end CFSG.RankThree.PartTwo.Sec21

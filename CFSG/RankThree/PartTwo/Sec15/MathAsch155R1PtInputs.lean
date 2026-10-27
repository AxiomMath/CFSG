module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigChar
public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProof
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1PtInputs

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof15Res6
  CFSG.RankThree.PartTwo.Sec15.Proof15Res8 CFSG.RankThree.PartTwo.Sec15.Proof153Twin2
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]



theorem y4CoreMemExcl_at
    (h134 : Item134) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) (hHJ : ¬ AllPointsHJ A) :
    ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        J ∈ thetaComponentsIn M → J = delta A (lB A) J →
        (Nonempty (↥J ⧸ Sec4.oTwoFitting ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
          (∃ p : ℕ, p.Prime ∧ 3 < p ∧
            Nonempty (↥J ⧸ Sec4.oTwoP p ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
          (Nonempty (↥J ⧸ Sec4.oTwoP 3 ↥J ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) ∨
            Sec4.IsExtOf (↥J ⧸ Sec4.oTwoP 3 ↥J) (alternatingGroup (Fin 5)) Sec4.Q8D8)) →
          IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := by
  intro M _ _ J _ hAJ hJM hΔ hcase
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
  have hJq := isQuasisimple_theta_of_mem_thetaComponentsIn hJM
  rcases hcase with h2 | ⟨p, hp, hp3, he⟩ | h4
  · exfalso
    obtain ⟨e⟩ := h2
    have : (Sec4.oTwoFitting ↥J).Characteristic := oTwoFitting_characteristic
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ (p := 5) le_rfl (Sec4.oTwoFitting ↥J) e
  · have : Fact p.Prime := ⟨hp⟩
    have : (Sec4.oTwoP p ↥J).Characteristic := oTwoP_characteristic p
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h5 | h5
      · interval_cases p
        exact absurd hp (by norm_num)
      · exact h5
    exfalso
    obtain ⟨e⟩ := he
    exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ hp5 (Sec4.oTwoP p ↥J) e
  · exact isQuasisimple_of_case444 hJp hJq h4

theorem item152_at
    (h134 : Item134) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) (hHJ : ¬ AllPointsHJ A)
    (hcomp : Step152Comp A (lB A)) : Item152 A (lB A) := by
  intro Y hY M hM hYM hF
  obtain ⟨X, hX, hYX, hΔ⟩ := hcomp Y hY M hM hYM hF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  refine ⟨X, hX, hYX, mem_scriptY0_of_isQuasisimple hY hM hF hX hYX hAX hΔ ?_⟩
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h' => hM.1.1 (top_le_iff.mp (h' ▸ hXM))
  have hX1 : X ≠ ⊥ := fun h' => ne_bot_of_mem_scriptY4 hY (le_bot_iff.mp (h' ▸ hYX))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2 : CFSG.pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hX)
  have hS4 : SectionFourHyp ↥X := h.toTheoremFourHyp.sectionFourHyp hXtop
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X
  set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ)
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have hKsimp : IsSimpleGroup (↥X ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (↥X ⧸ θ))).isSimpleGroup
  have hex := y4CoreMemExcl_at h134 h48 h hHJ M hM hF X
    (mem_comp3In_of_le_delta hY hX hYX hΔ) hAX hX hΔ
  rcases Sec4.item4_4OTwo_holds ↥X hS4 hXp K hKs hKsimp hO2 with h1 | h2 | h3 | h4
  · exact h1
  · exact hex (Or.inl h2)
  · exact hex (Or.inr (Or.inl h3))
  · exact hex (Or.inr (Or.inr h4))

theorem item152_at_lThreePi
    (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) {m : ℕ}
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m) : Item152 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHJ : ¬ AllPointsHJ A :=
    not_allPointsHJ_of_isEmpty h.toSec14Std (isEmpty_j2_of_isoLThreePi hL)
  exact item152_at h134 h48 h hHJ
    (step152CompR_of' h149 h148 h134 h48 h415 hSz (step152CompJR_of_item148R h148 h134 h48 h415)
      G A c L h)


theorem claim153TwinTypes_at
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h7 : Claim153TwinCase7)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h152 : Item152 A (lB A)) :
    ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ¬ M ≤ Subgroup.normalizer (Y : Set G) →
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
            Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) := by
  intro Y hY hE M hM hMY
  have h := hR.toSec14Std
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hAN : A ≤ Subgroup.normalizer (M : Set G) := hM2.1.2
  let := ker148_normal hAN
  obtain ⟨U, V, hU, hV, hUp, hVp, hU1, hV1, hUV, hcard, ⟨eY⟩⟩ :=
    exists_pair_of_twin h (h149 G A c L h) h152 hY hM hMY hAN
  refine types_of_quot_equiv hY.prop.1 hE eY ?_
  have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA5Z : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hid : ∀ (X : Type) [Group X], (MonoidHom.id X).ker ≤ Subgroup.center X := fun X _ => by
    rw [MonoidHom.ker_id]
    exact bot_le
  rcases (h148 G A c L hR M hM2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    exfalso
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    apply hU1
    rw [eq_bot_iff]
    intro x _
    have hx : (x : ↥(M ⊔ A) ⧸ ker148 A M) ∈ (⊥ : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) := by
      rw [← hD]
      exact x.2
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp hx))
  ·
    exfalso
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact false_of_mulEquiv_quasisimple (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ
        hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · exact false_of_isTripleCover h6 hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, -, hU6, hV6⟩ |
        ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hU6, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · exfalso
      have := CFSG.Sporadic.ON.isSimpleGroup_ON
      exact false_of_isTripleCover hON hU hUp hVp hU1 hV1 hUV
    ·
      right
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      obtain ⟨hψ₂, hk₂⟩ := tripleCover_cover hV6.2.some
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id hψ₂ hk₂ (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, -⟩ | ⟨hUV₀, -⟩
      · exact exists_surjective_of_le_tripleCover hU6 hU hUp hU1 hUU
      · exact exists_surjective_of_le_tripleCover hV6 hU hUp hU1 hUV₀
    ·
      exfalso
      have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact Subgroup.commutator_le_inf U₀ V₀
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      have h360 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ U₀ → 360 ∣ Nat.card W := by
        intro W hW hWp hW1 hWU
        obtain ⟨g, hg, -, -⟩ := exists_surjective_of_le_tripleCover hU6 hW hWp hW1 hWU
        have := Subgroup.card_dvd_of_surjective hg
        rwa [card_alternatingGroup_six] at this
      have h60 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ V₀ → Nat.card W = 60 := by
        intro W hW hWp hW1 hWV
        rw [eq_of_le_simple_factor hA5Z eV hW hWp hW1 hWV, Nat.card_congr eV.toEquiv,
          card_alternatingGroup_five]
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id (ψ₂ := MonoidHom.id (alternatingGroup (Fin 5)))
          Function.surjective_id (hid _) (φ₂ := eV.symm.toMonoidHom) eV.symm.surjective hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, hVV⟩ | ⟨hUV₀, hVU⟩
      · have h1 := h360 hU hUp hU1 hUU
        rw [hcard, h60 hV hVp hV1 hVV] at h1
        norm_num at h1
      · have h1 := h360 hV hVp hV1 hVU
        rw [← hcard, h60 hU hUp hU1 hUV₀] at h1
        norm_num at h1
    ·
      left
      obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', -, -⟩ :=
        pair_map φ hU hV hUp hVp hU1 hV1 hUV
      rcases pair_prod hA5Z hA5Z hU' hV' hUp' hVp' hU1' hV1' hUV' with
        ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
    ·
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
    ·
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    exfalso
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 (3 * n))
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    exfalso
    obtain ⟨⟨φ⟩, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hJZ : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
    obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', hcU, hcV⟩ :=
      pair_map φ hU hV hUp hVp hU1 hV1 hUV
    rcases pair_prod hA5Z hJZ hU' hV' hUp' hVp' hU1' hV1' hUV' with
      ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩ | ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
  ·
    exact (h7 G A c L hR Y hY hE M hM hMY hAN h7').elim

theorem claim153Obs_at
    (h148 : Item148R) (h149 : Sec16.Item149S14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h152 : Item152 A (lB A)) : Claim153Obs A (lB A) := by
  intro Y hY S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hYX, -, hX2⟩ := facts153 hR.toSec14Std (h149 G A c L hR.toSec14Std) hY
  by_cases hE : HasFaithfulE9 Y
  · exact claim153ObsE9_of hR.toSec14Std (h149 G A c L hR.toSec14Std) h152 Y hY hE S hS
  by_cases hNY : n155 A Y ≤ Subgroup.normalizer (Y : Set G)
  · exact hS.prop.1.2.trans hNY
  have hSX : S ≤ n155 A Y := hS.prop.1.2
  set X := CFSG.GH74.GLS.oPrimeResidualOf 3
    (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hNXle : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_oPrimeResidualOf
      (CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta (Subgroup.normalizer (Y : Set G)))
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hYX.trans Subgroup.le_normalizer) hAX
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hNXle (hYA hx))⟩
  have hMY : ¬ M ≤ Subgroup.normalizer (Y : Set G) := fun hMY =>
    hNY ((hNXle.trans hle).trans hMY)
  have hdisj : ¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y)
        (alternatingGroup (Fin 6)) := by
    rcases claim153TwinTypes_at h148 h149 (claim153TwinCase7_of_item148R h148) hR h152
      Y hY hE M hMm hMY with ⟨⟨e⟩⟩ | h6
    · exact Or.inl (F153Obs.not_dvd_three_card_center_of_alt5 e)
    · exact Or.inr h6
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    ((CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_iff).mp hS.prop.1.1).2.1
  exact F153Obs.theoremA881 G A c L hR Y hY.prop hdisj S hSX hAS
    (F153Obs.coprime_card_three_of_isPi_two hS.prop.2)


theorem claim153Twin_at
    (h148 : Item148R) (h149 : Sec16.Item149S14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h152 : Item152 A (lB A)) : Claim153Twin A (lB A) := by
  have hS := hR.toSec14Std
  have hn := claim153TwinNorm_of hS (h148 G A c L hR) (h149 G A c L hS) h152
    (claim153TwinCase7_of_item148R h148 G A c L hR)
  have hnc : ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y → HasNonCentralThree Y :=
    fun _ hY _ => Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  exact claim153Twin_of_twinX hS (h149 G A c L hS) h152
    (claim153TwinX_of_twinN hS (h149 G A c L hS) h152 (claim153TwinN_of_norm hS h152 hn) hnc)

theorem item153Main_at
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h135 : Item135) (h137 : Item137) (h142 : Item142AllS14)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142c : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14) (h148HJ : Item148HJS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (h152 : Item152 A (lB A)) : Item153Main A (lB A) := by
  intro Y hY
  have h := hR.toSec14Std
  have htwin := claim153Twin_at h148 h149 hR h152
  have htw : Ronan153Big.TwinAt A Y := fun M hM hMY => htwin Y hY M hM hMY
  have hobs : Ronan153Big.ObsAt A Y := fun S hS => claim153Obs_at h148 h149 hR h152 Y hY S hS
  exact Ronan153Big.item153At_of_twinAt h (h149 G A c L h) hY htw
    (Ronan153Big.charAt_of h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146 h1444
      hbot h148HJ hR hY htw hobs)


theorem claim153Normal_at
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h1411 : Item1411_1R)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) : Claim153Normal A (lB A) := by
  have hS := hR.toSec14Std
  have hq : Claim156Q A (lB A) := claim156Q_of_item153Main h153
  intro Y hY M hM
  by_cases hE : HasFaithfulE9 Y
  · exact claim153NormalE9_of hS h152 Y hY hE M hM
  by_contra hMY
  have htype := claim153TwinTypes_at h148 h149 (claim153TwinCase7_of_item148R h148) hR h152
    Y hY hE M hM hMY
  obtain ⟨c₀, L₀, d, X₁, D⟩ := exists_data156_of_small' hS (h148 G A c L hR) h134 h48
    Sec4.Sporadic.rank3II_4_15 (step156DR_of h142 G A c L hR) hY htype
  have htype' : IsType156 Y := by
    rcases htype with he | h6
    · exact Or.inl he
    · exact Or.inr (Or.inl h6)
  have h₀ : Sec14Std G A c₀ L₀ := { hS with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hΩA : omegaA A = {Subgroup.zpowers c₀} := by
    have h1 : Subgroup.zpowers c₀ ∈ omegaA A := D.omega
    rw [hΩ, Set.mem_singleton_iff] at h1
    rw [hΩ, h1]
  obtain ⟨M', hM', S, hS', hSM⟩ := hq Y hY htype'
  exact Proof153Twin.false_of_omegaA_eq_of_le h142 h₀ h152 (h1411 G A c L hR) hY htype' D hΩA
    hM' hS' hSM


end CFSG.RankThree.PartTwo.Sec15.Res1PtInputs

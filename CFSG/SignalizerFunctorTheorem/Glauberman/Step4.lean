module

public import CFSG.SignalizerFunctorTheorem.Glauberman.External
public import CFSG.SignalizerFunctorTheorem.Glauberman.Step3
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Thompson

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem isSolvable_of_isPGroup_subgroup {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (hX : IsPGroup q X) : Group.IsSolvable X := by
  have : Fact q.Prime := ⟨hq⟩
  have := hX.isNilpotent
  infer_instance

omit [Finite G] in
theorem conjugateSubgroup_eq_bot_iff (g : G) (X : Subgroup G) :
    conjugateSubgroup g X = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj g).injective

theorem Setting.exists_not_normalizerFactors (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ S ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      ¬ NormalizerFactors p q A θ M Q := by
  classical
  have hqp : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  by_contra hcon
  push Not at hcon
  have hmem : q ∈ signalizerSpectrum p 1 A θ := by
    rw [h.spectrum]
    rcases hq with rfl | rfl <;> simp
  have hfact : signalizerNormalizerFactorization p 1 q A θ M := by
    intro W hW hWc hWq
    obtain ⟨S', hWS', hS'⟩ := Finite.exists_le_maximal
      (p := signalizerPrimeCompatible p 1 q A θ) (a := W) ⟨hWc.1, hWq⟩
    obtain ⟨c₀, hc₀⟩ := signalizer_prime_transitivity p 1 q h.prime hqp (h.p_ne hq) A h.elementary
      h.large θ h.conditions.coprime h.conditions.normalized h.conditions.balanced S S' hS hS'
    set g : G := c₀.val with hg
    have hgC : g ∈ signalizerCommonFixed p 1 A θ := c₀.property
    have hgA : g ∈ Subgroup.centralizer (A : Set G) := commonFixed_le_centralizer hgC
    have hgS : conjugateSubgroup g S = S' := hc₀
    set Q := conjugateSubgroup g⁻¹ W with hQ
    have hQW : conjugateSubgroup g Q = W := by
      rw [hQ, conjugate_subgroup_mul, mul_inv_cancel, conjugate_subgroup_one]
    have hQne : Q ≠ ⊥ := fun hQbot => hW (by
      rw [← hQW]
      exact (conjugateSubgroup_eq_bot_iff g Q).mpr hQbot)
    have hQS : Q ≤ S := by
      have hle : Q ≤ conjugateSubgroup g⁻¹ S' := Subgroup.map_mono (hWS')
      rwa [← hgS, conjugate_subgroup_inv_cancel] at hle
    have hQA : A ≤ Subgroup.normalizer (Q : Set G) :=
      le_normalizer_conj_of_mem_centralizer (Subgroup.inv_mem _ hgA) hWc.1.1
    have hQfactors := hcon Q hQne hQS hQA
    have hconj := (h.normalizerFactors_conj q M Q hgC).mpr hQfactors
    rw [hQW] at hconj
    exact ⟨c₀, hconj⟩
  exact h.incomplete (signalizer_normalizer_factorization_complete p 1 q h.prime hqp A M
    h.elementary h.large θ h.conditions h.locallyComplete hmem hM.prop hfact)


omit [Finite G] in
theorem conjugateSubgroup_inf (g : G) (X Y : Subgroup G) :
    conjugateSubgroup g (X ⊓ Y) = conjugateSubgroup g X ⊓ conjugateSubgroup g Y :=
  Subgroup.map_inf X Y _ (MulAut.conj g).injective

theorem Setting.exists_extremal (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M) (hSM : S ≤ M) :
    ∃ Q T : Subgroup G, Q ≠ ⊥ ∧ Q ≤ T ∧ T ≤ S ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      ¬ NormalizerFactors p q A θ M Q ∧
      IsSylowOf q T (signalizerNormalizerCompletion p 1 A θ Q ⊓ M) ∧
      A ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ Q' : Subgroup G, Q' ≠ ⊥ → Q' ≤ S → A ≤ Subgroup.normalizer (Q' : Set G) →
        ¬ NormalizerFactors p q A θ M Q' →
        ∀ P : Subgroup G, P ≤ signalizerNormalizerCompletion p 1 A θ Q' ⊓ M → IsPGroup q P →
          Nat.card P ≤ Nat.card T := by
  classical
  have hqp : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have hSc : signalizerCompatible p 1 A θ S := hS.prop.1
  have hSq : IsPGroup q S := hS.prop.2
  have hMc : signalizerCompatible p 1 A θ M := hM.prop.1
  have hSylS : IsSylowOf q S M := h.isSylowOf_of_maximal hqp hS hMc hSM
  have hbotA : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  have hbotq : IsPGroup q (⊥ : Subgroup G) := IsPGroup.of_bot
  let Good : Subgroup G → Prop := fun Q =>
    Q ≠ ⊥ ∧ Q ≤ S ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧ ¬ NormalizerFactors p q A θ M Q
  have hspec : ∀ Q : Subgroup G, Good Q →
      solvableSignalizerCompatible p 1 A θ (signalizerNormalizerCompletion p 1 A θ Q) ∧
        Q ≤ signalizerNormalizerCompletion p 1 A θ Q ∧
        signalizerNormalizerCompletion p 1 A θ Q ≤ Subgroup.normalizer (Q : Set G) ∧
        ∀ Y : Subgroup G, signalizerCompatible p 1 A θ Y → Y ≤ Subgroup.normalizer (Q : Set G) →
          Y ≤ signalizerNormalizerCompletion p 1 A θ Q := fun Q hQ =>
    h.normalizerCompletion_spec hQ.1
      ⟨signalizer_compatible_of_le p 1 A θ hSc hQ.2.1 hQ.2.2.1,
        isSolvable_of_isPGroup_subgroup hqp (hSq.to_le hQ.2.1)⟩
  obtain ⟨Q₀, hQ₀ne, hQ₀S, hQ₀A, hQ₀nf⟩ := h.exists_not_normalizerFactors hq hS hM
  have hPairs : Nonempty {x : Subgroup G × Subgroup G //
      Good x.1 ∧ IsSylowOf q x.2 (signalizerNormalizerCompletion p 1 A θ x.1 ⊓ M)} := by
    obtain ⟨T₀, -, hT₀⟩ := exists_isSylowOf_ge hqp
      (bot_le : (⊥ : Subgroup G) ≤ signalizerNormalizerCompletion p 1 A θ Q₀ ⊓ M) hbotq
    exact ⟨⟨(Q₀, T₀), ⟨hQ₀ne, hQ₀S, hQ₀A, hQ₀nf⟩, hT₀⟩⟩
  obtain ⟨⟨⟨Qs, Ts⟩, hQs, hTs⟩, hmax⟩ :=
    Finite.exists_max (fun x : {x : Subgroup G × Subgroup G //
      Good x.1 ∧ IsSylowOf q x.2 (signalizerNormalizerCompletion p 1 A θ x.1 ⊓ M)} =>
        Nat.card x.1.2)
  obtain ⟨hUsc, hQsU, hUsN, -⟩ := hspec Qs hQs
  have hUMc : signalizerCompatible p 1 A θ (signalizerNormalizerCompletion p 1 A θ Qs ⊓ M) :=
    signalizer_compatible_inf p 1 A θ _ M hUsc.1 hMc.1
  obtain ⟨T₀, -, hT₀, hT₀A⟩ := h.exists_invariant_sylow hqp hUMc hbotq bot_le hbotA
  have hcard : Nat.card T₀ = Nat.card Ts := hT₀.card_eq hqp hTs
  have hQsT₀ : Qs ≤ T₀ :=
    hT₀.le_of_normal (le_inf hQsU (hQs.2.1.trans hSM)) (hSq.to_le hQs.2.1)
      (inf_le_left.trans hUsN)
  obtain ⟨c, hcmem, hcle⟩ := h.exists_conj_le_sylow hqp hMc hSylS hSc.1 hT₀.isPGroup
    (hT₀.le.trans inf_le_right) hT₀A
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hcmem).1
  have hcA : c ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hcmem).2
  have hcC : c ∈ signalizerCommonFixed p 1 A θ := inf_centralizer_le_commonFixed hMc hcmem
  have hcM' : conjugateSubgroup c M = M := conjugate_subgroup_eq_of_mem c M hcM
  refine ⟨conjugateSubgroup c Qs, conjugateSubgroup c T₀, ?_, Subgroup.map_mono hQsT₀, hcle,
    le_normalizer_conj_of_mem_centralizer hcA hQs.2.2.1, ?_, ?_,
    le_normalizer_conj_of_mem_centralizer hcA hT₀A, ?_⟩
  · exact fun hb => hQs.1 ((conjugateSubgroup_eq_bot_iff c Qs).mp hb)
  · intro hnf
    apply hQs.2.2.2
    refine (h.normalizerFactors_conj q M Qs hcC).mp ?_
    rw [hcM']
    exact hnf
  · have hsyl := hT₀.conj c
    rw [conjugateSubgroup_inf, h.normalizerCompletion_conj Qs hcC, hcM'] at hsyl
    exact hsyl
  · intro Q' hQ'ne hQ'S hQ'A hQ'nf P hP hPq
    obtain ⟨T', hPT', hT'⟩ := exists_isSylowOf_ge hqp hP hPq
    have hle : Nat.card T' ≤ Nat.card Ts :=
      hmax ⟨(Q', T'), ⟨hQ'ne, hQ'S, hQ'A, hQ'nf⟩, hT'⟩
    calc Nat.card P ≤ Nat.card T' := Subgroup.card_le_of_le hPT'
      _ ≤ Nat.card Ts := hle
      _ = Nat.card T₀ := hcard.symm
      _ = Nat.card (conjugateSubgroup c T₀) := (conjugate_subgroup_card c T₀).symm

theorem Setting.step4 (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M) (hSM : S ≤ M) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ S ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (∃ T : Subgroup G, IsSylowOf q T (signalizerNormalizerCompletion p 1 A θ Q) ∧
        A ≤ Subgroup.normalizer (T : Set G) ∧
        ¬ ThompsonFactorizable q (signalizerNormalizerCompletion p 1 A θ Q) T) ∧
      ¬ signalizerNormalizerCompletion p 1 A θ Q ⊓ signalizerCommonFixed p 1 A θ ≤ M := by
  classical
  have hqp : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  obtain ⟨Q, T, hQne, hQT, hTS, hQA, hbad, hTsyl, hTA, hmax⟩ := h.exists_extremal hq hS hM hSM
  have hSc : signalizerCompatible p 1 A θ S := hS.prop.1
  have hSq : IsPGroup q S := hS.prop.2
  have hMc : signalizerCompatible p 1 A θ M := hM.prop.1
  have hQS : Q ≤ S := hQT.trans hTS
  have hTq : IsPGroup q T := hTsyl.isPGroup
  have hTne : T ≠ ⊥ := fun hb => hQne (le_bot_iff.mp (hb ▸ hQT))
  have hSne : S ≠ ⊥ := fun hb => hTne (le_bot_iff.mp (hb ▸ hTS))
  have hSA : A ≤ Subgroup.normalizer (S : Set G) := hSc.1
  have hQc : signalizerCompatible p 1 A θ Q := signalizer_compatible_of_le p 1 A θ hSc hQS hQA
  obtain ⟨hUsc, hQU, hUN, hUmax⟩ := h.normalizerCompletion_spec hQne
    ⟨hQc, isSolvable_of_isPGroup_subgroup hqp (hSq.to_le hQS)⟩
  set U := signalizerNormalizerCompletion p 1 A θ Q with hU
  have hTU : T ≤ U := hTsyl.le.trans inf_le_left
  have hTS_ne : T ≠ S := by
    intro heq
    have hSU : S ≤ U := heq ▸ hTU
    obtain ⟨M', hUM', hM'⟩ := Finite.exists_le_maximal
      (p := solvableSignalizerCompatible p 1 A θ) hUsc
    have hM'M : M' = M := h.step3 hq hS hM' hM (hSU.trans hUM') hSM
    exact hbad (normalizerFactors_of_le (hM'M ▸ hUM'))
  have hTlt : T < S := lt_of_le_of_ne hTS hTS_ne
  have hgrow : T < S ⊓ Subgroup.normalizer (T : Set G) :=
    pgroup_normalizer_strict_growth q hqp S T hSq hTlt
  set J := thompsonJ q T with hJ
  have hJT : J ≤ T := thompsonJ_le q T
  have hJS : J ≤ S := hJT.trans hTS
  have hJA : A ≤ Subgroup.normalizer (J : Set G) :=
    hTA.trans (normalizer_le_normalizer_thompsonJ q T)
  have hJq : IsPGroup q J := hTq.to_le hJT
  have hJne : J ≠ ⊥ := thompsonJ_ne_bot hqp hTq hTne
  have hJc : signalizerCompatible p 1 A θ J := signalizer_compatible_of_le p 1 A θ hSc hJS hJA
  obtain ⟨hU₁c, hJU₁, hU₁N, hU₁max⟩ := h.normalizerCompletion_spec hJne
    ⟨hJc, isSolvable_of_isPGroup_subgroup hqp hJq⟩
  set U₁ := signalizerNormalizerCompletion p 1 A θ J with hU₁
  have hNSTA : A ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) :=
    normalizer_inf_of_le A S _ hSA (normalizer_normalized A T hTA)
  have hNSTc : signalizerCompatible p 1 A θ (S ⊓ Subgroup.normalizer (T : Set G)) :=
    signalizer_compatible_of_le p 1 A θ hSc inf_le_left hNSTA
  have hNSTJ : S ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_thompsonJ q T)
  have hNSTU₁ : S ⊓ Subgroup.normalizer (T : Set G) ≤ U₁ := hU₁max _ hNSTc hNSTJ
  have hNF₁ : NormalizerFactors p q A θ M J := by
    by_contra hnf
    have hle := hmax J hJne hJS hJA hnf (S ⊓ Subgroup.normalizer (T : Set G))
      (le_inf hNSTU₁ (inf_le_left.trans hSM)) (hSq.to_le inf_le_left)
    exact absurd (subgroup_card_strict_mono hgrow) (not_lt.mpr hle)
  set Z := omegaCenter q S with hZ
  have hZS : Z ≤ S := omegaCenter_le q S
  have hZA : A ≤ Subgroup.normalizer (Z : Set G) :=
    hSA.trans (normalizer_le_normalizer_omegaCenter q S)
  have hZne : Z ≠ ⊥ := omegaCenter_ne_bot hqp hSq hSne
  have hZq : IsPGroup q Z := hSq.to_le hZS
  have hZc : signalizerCompatible p 1 A θ Z := signalizer_compatible_of_le p 1 A θ hSc hZS hZA
  have hZcentS : Z ≤ Subgroup.centralizer (S : Set G) := omegaCenter_le_centralizer q S
  have hZU : Z ≤ U := hUmax Z hZc
    (hZcentS.trans ((Subgroup.centralizer_le hQS).trans (Subgroup.centralizer_le_normalizer _)))
  have hZT : Z ≤ T := hTsyl.le_of_le_normalizer hqp (le_inf hZU (hZS.trans hSM)) hZq
    (hZcentS.trans ((Subgroup.centralizer_le hTS).trans (Subgroup.centralizer_le_normalizer _)))
  set ZT := omegaCenter q T with hZT'
  have hZZT : Z ≤ ZT := (le_inf le_rfl hZT).trans (omegaCenter_inf_le_omegaCenter hTS)
  have hZJ : Z ≤ J := hZZT.trans (omegaCenter_le_thompsonJ q T)
  have hOZ : primeCoreIn ({q}ᶜ : Set ℕ) U₁ ≤ Subgroup.centralizer (Z : Set G) :=
    (primeCoreIn_le_centralizer hqp hJU₁ hJq hU₁N).trans (Subgroup.centralizer_le hZJ)
  have hOA : A ≤ Subgroup.normalizer (primeCoreIn ({q}ᶜ : Set ℕ) U₁ : Set G) :=
    le_normalizer_primeCoreIn_of_le _ hU₁c.1.1
  have hOc : signalizerCompatible p 1 A θ (primeCoreIn ({q}ᶜ : Set ℕ) U₁) :=
    signalizer_compatible_of_le p 1 A θ hU₁c.1 (primeCoreIn_le _ _) hOA
  obtain ⟨hΘZc, hZΘ, hΘZN, hΘZmax⟩ := h.normalizerCompletion_spec hZne
    ⟨hZc, isSolvable_of_isPGroup_subgroup hqp hZq⟩
  have hCZA : A ≤ Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) :=
    le_normalizer_centralizer_of_le_normalizer hZA
  have hYc : signalizerCompatible p 1 A θ
      (signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G)) :=
    signalizer_compatible_inf p 1 A θ _ _ hΘZc.1 hCZA
  have hYsolv : Group.IsSolvable
      (signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G) :
        Subgroup G) := by
    have := hΘZc.2
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left :
        signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G) ≤
          signalizerNormalizerCompletion p 1 A θ Z))
  have hSZ : S ≤ Subgroup.centralizer (Z : Set G) := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZcentS hz) s hs).symm
  have hSY : S ≤ signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G) :=
    le_inf (hΘZmax S hSc (hSZ.trans (Subgroup.centralizer_le_normalizer _))) hSZ
  have hYM : signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G) ≤ M := by
    obtain ⟨M', hYM', hM'⟩ := Finite.exists_le_maximal
      (p := solvableSignalizerCompatible p 1 A θ) (⟨hYc, hYsolv⟩ :
        solvableSignalizerCompatible p 1 A θ
          (signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G)))
    have hM'M : M' = M := h.step3 hq hS hM' hM (hSY.trans hYM') hSM
    exact hM'M ▸ hYM'
  have hOY : primeCoreIn ({q}ᶜ : Set ℕ) U₁ ≤
      signalizerNormalizerCompletion p 1 A θ Z ⊓ Subgroup.centralizer (Z : Set G) :=
    le_inf (hΘZmax _ hOc (hOZ.trans (Subgroup.centralizer_le_normalizer _))) hOZ
  have hU₁M : U₁ ≤ M := hNF₁.le.trans (sup_le (hOY.trans hYM) inf_le_right)
  have hZTA : A ≤ Subgroup.normalizer (ZT : Set G) :=
    hTA.trans (normalizer_le_normalizer_omegaCenter q T)
  have hUNJ : U ⊓ Subgroup.normalizer (J : Set G) ≤ M := by
    have hA' : A ≤ Subgroup.normalizer ((U ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) :
        Set G) := normalizer_inf_of_le A U _ hUsc.1.1 (normalizer_normalized A J hJA)
    exact (hU₁max _ (signalizer_compatible_of_le p 1 A θ hUsc.1 inf_le_left hA')
      inf_le_right).trans hU₁M
  have hUCZT : U ⊓ Subgroup.centralizer (ZT : Set G) ≤ M := by
    have hA' : A ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (ZT : Set G) : Subgroup G) :
        Set G) := normalizer_inf_of_le A U _ hUsc.1.1
          (le_normalizer_centralizer_of_le_normalizer hZTA)
    have hcz : U ⊓ Subgroup.centralizer (ZT : Set G) ≤ Subgroup.centralizer (Z : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le hZZT)
    exact (le_inf (hΘZmax _ (signalizer_compatible_of_le p 1 A θ hUsc.1 inf_le_left hA')
      (hcz.trans (Subgroup.centralizer_le_normalizer _))) hcz).trans hYM
  have hTsylU : IsSylowOf q T U := by
    obtain ⟨T', hTT', hT'⟩ := exists_isSylowOf_ge hqp hTU hTq
    have hT'q : IsPGroup q T' := hT'.isPGroup
    have hmid : T' ⊓ Subgroup.normalizer (T : Set G) ≤ U ⊓ M := by
      have h1 : T' ⊓ Subgroup.normalizer (T : Set G) ≤ U := inf_le_left.trans hT'.le
      exact le_inf h1 ((le_inf h1 (inf_le_right.trans
        (normalizer_le_normalizer_thompsonJ q T))).trans hUNJ)
    have heq : T' ⊓ Subgroup.normalizer (T : Set G) = T :=
      hTsyl.eq_of_le (hT'q.to_le inf_le_left) (le_inf hTT' Subgroup.le_normalizer) hmid
    have hTT'eq : T = T' := by
      by_contra hne
      have hlt : T < T' := lt_of_le_of_ne hTT' hne
      have hgrow' := pgroup_normalizer_strict_growth q hqp T' T hT'q hlt
      rw [heq] at hgrow'
      exact lt_irrefl _ hgrow'
    rw [hTT'eq]
    exact hT'
  have hR : U ⊓ M ≤ primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) := le_sup_right
  have hO : primeCoreIn ({q}ᶜ : Set ℕ) U ≤ primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) := le_sup_left
  have hNJ' : U ⊓ Subgroup.normalizer (J : Set G) ≤
      primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) := (le_inf inf_le_left hUNJ).trans hR
  have hCZT' : U ⊓ Subgroup.centralizer (ZT : Set G) ≤
      primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) := (le_inf inf_le_left hUCZT).trans hR
  have hback : primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) ≤ U :=
    sup_le (primeCoreIn_le _ _) inf_le_left
  refine ⟨Q, hQne, hQS, hQA, ⟨T, hTsylU, hTA, ?_⟩, ?_⟩
  · intro hfact
    have hfact' : primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (J : Set G)) ⊔
        (U ⊓ Subgroup.centralizer (ZT : Set G)) = U := hfact
    apply hbad
    exact le_antisymm (hfact'.symm.le.trans (sup_le (sup_le hO hNJ') hCZT')) hback
  · intro hle
    apply hbad
    have hgen := thompson_generation hqp h.prime hUsc.2 h.elementary (h.coprime_card hUsc.1)
      hUsc.1.1 hTsylU hTA
    have hgen' : primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (J : Set G)) ⊔
        (U ⊓ Subgroup.centralizer (ZT : Set G)) ⊔ (U ⊓ Subgroup.centralizer (A : Set G)) = U :=
      hgen
    have hCA' : U ⊓ Subgroup.centralizer (A : Set G) ≤ primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ M) :=
      (le_inf inf_le_left ((le_inf inf_le_left
        (inf_centralizer_le_commonFixed hUsc.1)).trans hle)).trans hR
    exact le_antisymm
      (hgen'.symm.le.trans (sup_le (sup_le (sup_le hO hNJ') hCZT') hCA')) hback

end CFSG.SignalizerFunctorTheorem.Glauberman

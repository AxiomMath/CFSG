module

public import CFSG.Milestones.ASVolI.A2
public import CFSG.Quasithin.Background.RonanF615QTK
public import CFSG.Quasithin.Background.RonanF617

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6

structure HypF_6_2 {D : Type} [Group D] (G₁ G₂ D₁ D₂ : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  sylow₁ : D₁ ≤ G₁ ∧ IsPGroup 3 D₁ ∧ ¬ 3 ∣ D₁.relIndex G₁
  sylow₂ : D₂ ≤ G₂ ∧ IsPGroup 3 D₂ ∧ ¬ 3 ∣ D₂.relIndex G₂

@[expose] def IsQuotientOfSQTK (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E) (M : Subgroup E) (_ : M.Normal),
    CFSG.SectionRank.IsSQTKCat E ∧ Nonempty (X ≃* E ⧸ M)

@[expose] def IsQuotientOfQTK (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E) (M : Subgroup E) (_ : M.Normal),
    IsQuasithin E ∧ CFSG.SectionRank.IsKGroupCat E ∧ Nonempty (X ≃* E ⧸ M)

@[expose] def IsSQTKModOThreePrime (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E),
    CFSG.SectionRank.IsSQTKCat E ∧ Nonempty (X ≃* E ⧸ CFSG.pPrimeCore 3 E)

@[expose] def IsQTKModOThreePrime (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E),
    IsQuasithin E ∧ CFSG.SectionRank.IsKGroupCat E ∧ Nonempty (X ≃* E ⧸ CFSG.pPrimeCore 3 E)

structure HypF_1_1_abcd {G : Type} [Group G] (Li Lj S : Subgroup G) : Prop where
  finite : Finite ↥S
  pgroup : IsPGroup 2 S
  normalizes : S ≤ Subgroup.normalizer (Li : Set G)
  sylow : IsSylowTwoOf (S ⊓ Li) Li
  listed : IsRankOneListed (oTwoQuot ↥Li)
  borel_le : borelOf Lj S ≤ Subgroup.normalizer (Li : Set G)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.ASVolI.ChF

@[expose] def F_6_3 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsGreatest {N : Subgroup D | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₁).Normal ∧ (N.subgroupOf G₂).Normal}
      (CFSG.pCore 2 D)

private theorem amalgamIso_symm_aux {D E : Type*} [Group D] [Group E] {H₁ H₂ : Subgroup D}
    {K₁ K₂ : Subgroup E} (h : CFSG.Quasithin.F6.IsAmalgamIso H₁ H₂ K₁ K₂) :
    CFSG.Quasithin.F6.IsAmalgamIso K₁ K₂ H₁ H₂ := by
  obtain ⟨φ₁, φ₂, h1, h2⟩ := h
  exact ⟨φ₁.symm, φ₂.symm, h2, h1⟩

private theorem odd_card_oddCoreIn_top {D : Type} [Group D] [Finite D] :
    Odd (Nat.card ↥(CFSG.QuasithinUnique.oddCoreIn (⊤ : Subgroup D))) := by
  rw [CFSG.QuasithinUnique.oddCoreIn, Nat.card_congr ((CFSG.Open.fusionOddCore
    ↥(⊤ : Subgroup D)).equivMapOfInjective (⊤ : Subgroup D).subtype
    (⊤ : Subgroup D).subtype_injective).toEquiv.symm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

private theorem odd_card_oddCoreIn_of {D : Type} [Group D] [Finite D] (X : Subgroup D) :
    Odd (Nat.card ↥(CFSG.QuasithinUnique.oddCoreIn X)) := by
  rw [CFSG.QuasithinUnique.oddCoreIn, Nat.card_congr ((CFSG.Open.fusionOddCore
    ↥X).equivMapOfInjective X.subtype X.subtype_injective).toEquiv.symm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

theorem as_F_6_3 : F_6_3 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp
  have h := hyp.triple
  have hQT : CFSG.pCore 2 D ≤ G₁ ⊓ G₂ := h.pCore_le_inf
  refine ⟨?_, ?_⟩
  · rw [Set.mem_setOf_eq]
    exact ⟨hQT, inferInstance, inferInstance⟩
  · intro N hN
    rw [Set.mem_setOf_eq] at hN
    obtain ⟨hNT, hN₁, hN₂⟩ := hN
    have hG₁ : G₁ ≤ Subgroup.normalizer (N : Set D) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_left)).mp hN₁
    have hG₂ : G₂ ≤ Subgroup.normalizer (N : Set D) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_right)).mp hN₂
    have htop : (⊤ : Subgroup D) ≤ Subgroup.normalizer (N : Set D) := by
      rw [← h.gen]
      exact sup_le hG₁ hG₂
    have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
    exact h.le_pCore_of_normal_le_inf hNT

@[expose] def F_6_5 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ H₁ H₂ : Subgroup (D ⧸ CFSG.pCore 2 D),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      IsGoldschmidtAmalgam H₁ H₂ ∧
      IsGoldCaseCat H₁ H₂ ∧
      ((IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁) →
        CharTwo H₁ ∧ CharTwo H₂ ∧ IsWeakBNPair H₁ H₂) ∧
      ((IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
          IsGoldCaseV H₁ H₂ ∨ IsGoldCaseI H₂ H₁ ∨ IsGoldCaseII H₂ H₁ ∨ IsGoldCaseIII H₂ H₁ ∨
          IsGoldCaseIV H₂ H₁ ∨ IsGoldCaseV H₂ H₁) →
        ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₁) ∨ ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₂))

section F65Cert

theorem as_F_6_5 : F_6_5 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp H₁ H₂ hH₁ hH₂
  subst hH₁ hH₂
  have hA := hyp.triple.quotient_pCore
  refine ⟨hA, CFSG.Quasithin.F6.goldschmidtS3ListCat_holds.{0} _ _ _ hA, ?_,
    CFSG.Quasithin.RonanF65.not_isPGroup_of_isGoldCase_i_v⟩
  intro hvi
  obtain ⟨h₁, h₂⟩ := CFSG.Quasithin.RonanF65.charTwo_of_isGoldCaseVICat_or hA hvi
  exact ⟨h₁, h₂, CFSG.Quasithin.RonanF65.isWeakBNPair_of_charTwo hA h₁ h₂⟩

end F65Cert

@[expose] def F_6_6 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    twoResidual (⊤ : Subgroup D) = twoResidual G₁ ⊔ twoResidual G₂

theorem as_F_6_6 : F_6_6 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp
  exact CFSG.Quasithin.F6.twoResidual_top_eq hyp.triple

@[expose] def F_6_7 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ X : Subgroup D, X.IsSubnormal →
      List.TFAE [G₁ ⊓ X ≤ pCoreOf 2 G₁,
        G₁ ⊓ X = pCoreOf 2 G₁ ⊓ X ∧ pCoreOf 2 G₁ ⊓ X = G₁ ⊓ G₂ ⊓ X ∧
          IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X,
        ¬ twoResidual G₁ ≤ X] ∧
      List.TFAE [G₂ ⊓ X ≤ pCoreOf 2 G₂,
        G₂ ⊓ X = pCoreOf 2 G₂ ⊓ X ∧ pCoreOf 2 G₂ ⊓ X = G₁ ⊓ G₂ ⊓ X ∧
          IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X,
        ¬ twoResidual G₂ ≤ X]

theorem as_F_6_7 : F_6_7 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp X hX
  have hXc : CFSG.Open.IsSubnormal X ⊤ := CFSG.Open.IsSubnormal.of_mathlib hX
  refine ⟨CFSG.Quasithin.F6.tfae_inf_le_pCoreOf hyp.triple hXc, ?_⟩
  have h2 := CFSG.Quasithin.F6.tfae_inf_le_pCoreOf hyp.triple.symm hXc
  rw [inf_comm G₂ G₁] at h2
  exact h2

@[expose] def F_6_8 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ X : Subgroup D, X.Normal → G₁ ⊓ X ≤ pCoreOf 2 G₁ → G₂ ⊓ X ≤ pCoreOf 2 G₂ →
      G₁ ⊓ G₂ ⊓ X ≤ CFSG.pCore 2 D ∧
      Odd (Nat.card ↥(X.map (QuotientGroup.mk' (CFSG.pCore 2 D)))) ∧
      Group.IsSolvable ↥(X.map (QuotientGroup.mk' (CFSG.pCore 2 D)))

theorem as_F_6_8 : F_6_8 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp X hXn h₁ h₂
  exact ⟨CFSG.Quasithin.F6.inf_le_pCore_of_normal hyp.triple h₁ h₂,
    CFSG.Quasithin.F6.odd_card_map_of_normal hyp.triple h₁ h₂,
    CFSG.Quasithin.F6.isSolvable_map_of_normal hyp.triple h₁ h₂⟩

@[expose] def F_6_9 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    Group.IsSolvable D → IsQuotientOfSQTK D →
    (twoResidual G₁ ≤ Subgroup.centralizer (opResidual 3 (CFSG.fittingSubgroup D) : Set D) ∨
      twoResidual G₂ ≤ Subgroup.centralizer (opResidual 3 (CFSG.fittingSubgroup D) : Set D)) →
    ∀ q : ℕ, q.Prime → q ∣ Nat.card D → q = 2 ∨ q = 3

theorem as_F_6_9 : F_6_9 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hsolv hQ hL q hq hqd
  obtain ⟨E, hGE, hfin, M, hM, hsqt, ⟨e⟩⟩ := hQ
  obtain ⟨hsq, hK⟩ := hsqt
  have hD : ∃ (Ĝ : Type) (_ : Group Ĝ) (_ : Finite Ĝ) (φ : Ĝ →* D), Function.Surjective φ ∧
      CFSG.Open.SQTKTauCeti.StronglyQuasithin Ĝ ∧ CFSG.SectionRank.IsKGroupCat Ĝ :=
    ⟨E, hGE, hfin, e.symm.toMonoidHom.comp (QuotientGroup.mk' M),
      e.symm.surjective.comp (QuotientGroup.mk'_surjective M),
      CFSG.SectionRank.isStronglyQuasithin_iff.mp hsq, hK⟩
  exact CFSG.Quasithin.F6.prime_eq_two_or_three_of_sqtk hyp.triple hsolv hD hL hq hqd

@[expose] def F_6_10 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ¬ Group.IsSolvable D → IsQuotientOfQTK D →
    ∀ K : Subgroup D, CFSG.IsComponent K →
      ((twoResidual G₁ ≤ K ∧ K ⊔ G₂ = ⊤) ∨ (twoResidual G₂ ≤ K ∧ K ⊔ G₁ = ⊤)) ∧ K.Normal ∧
      ¬ K ≤ CFSG.pPrimeCore 3 D

section F610Cert

theorem as_F_6_10 : F_6_10 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp _ _ K hK
  obtain ⟨hn, hL, h3⟩ := CFSG.Quasithin.RonanF610.f6_10_of_list
    CFSG.Quasithin.F6.goldschmidtS3ListCat_holds.{0} hyp.triple hK
  exact ⟨hL, hn, h3⟩

end F610Cert

@[expose] def F_6_11 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    (IsSylowTwoOf (CFSG.pCore 2 D) (CFSG.pPrimeCore 3 D) ∧
      Group.IsSolvable ↥(CFSG.pPrimeCore 3 D)) ∧
    ∀ (H₁ H₂ : Subgroup (D ⧸ CFSG.pCore 2 D)) (G₁' G₂' : Subgroup (D ⧸ CFSG.pPrimeCore 3 D)),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      G₁' = G₁.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) →
      G₂' = G₂.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) →
        ((G₁' ⊓ G₂' = (G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) ∧
            IsGoldschmidtAmalgam G₁' G₂' ∧ IsAmalgamIso G₁' G₂' H₁ H₂) ∨
          (pCoreOf 2 G₁ = CFSG.pCore 2 D ∧ pCoreOf 2 G₂ = CFSG.pCore 2 D ∧
            Nonempty ((D ⧸ CFSG.pPrimeCore 3 D) ≃* Equiv.Perm (Fin 3)) ∧
            G₁ ⊔ CFSG.pPrimeCore 3 D = ⊤ ∧
            ¬ ∃ x ∈ CFSG.pPrimeCore 3 D, CFSG.pPrimeCore 3 D ≤ Subgroup.zpowers x ⊔ CFSG.pCore 2 D))

theorem as_F_6_11 : F_6_11 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp
  refine ⟨⟨CFSG.Quasithin.F6.isSylowTwoOf_pCore_pPrimeCore hyp.triple,
    CFSG.Quasithin.F6.isSolvable_pPrimeCore hyp.triple⟩, ?_⟩
  intro H₁ H₂ G₁' G₂' hH₁ hH₂ hG₁' hG₂'
  subst hH₁ hH₂ hG₁' hG₂'
  rcases CFSG.Quasithin.F6.goldschmidt_mod_pPrimeCore hyp.triple with
    ⟨e₁, e₂, e₃⟩ | ⟨p₁, p₂, p₃, p₄, p₅⟩
  · exact Or.inl ⟨e₁, e₂, amalgamIso_symm_aux e₃⟩
  · refine Or.inr ⟨p₁, p₂, p₃, p₄, ?_⟩
    rintro ⟨x, hxP, hle⟩
    apply p₅
    have h1 : (CFSG.pPrimeCore 3 D).map (QuotientGroup.mk' (CFSG.pCore 2 D)) ≤
        (Subgroup.zpowers x ⊔ CFSG.pCore 2 D).map (QuotientGroup.mk' (CFSG.pCore 2 D)) :=
      Subgroup.map_mono hle
    have hmap : (CFSG.pPrimeCore 3 D).map (QuotientGroup.mk' (CFSG.pCore 2 D)) ≤
        Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 D) x) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
      exact h1
    exact Subgroup.isCyclic_of_le hmap

@[expose] def F_6_12 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    CFSG.pCore 2 D = ⊥ →
    ((∀ S : Subgroup D, S ≤ pCoreOf 2 G₁ → S ≠ ⊥ → D₁ ≤ Subgroup.normalizer (S : Set D) →
        ¬ (pCoreOf 2 G₁ ⊔ twoResidual G₂ ≤ Subgroup.normalizer (S : Set D))) ∧
      (∀ S : Subgroup D, S ≤ pCoreOf 2 G₁ → S ≠ ⊥ → (S.subgroupOf (pCoreOf 2 G₁)).Characteristic →
        ¬ (pCoreOf 2 G₁ ⊔ twoResidual G₂ ≤ Subgroup.normalizer (S : Set D)))) ∧
    ((∀ S : Subgroup D, S ≤ pCoreOf 2 G₂ → S ≠ ⊥ → D₂ ≤ Subgroup.normalizer (S : Set D) →
        ¬ (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D))) ∧
      (∀ S : Subgroup D, S ≤ pCoreOf 2 G₂ → S ≠ ⊥ → (S.subgroupOf (pCoreOf 2 G₂)).Characteristic →
        ¬ (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D))))

theorem as_F_6_12 : F_6_12 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hQ
  have hQ' : Open.pCore 2 D = ⊥ := hQ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro S hS hS0 hSD hSn
    exact hS0 (CFSG.Quasithin.F6.eq_bot_of_le_pCoreOf_of_normalizes hyp.triple.symm hQ'
      (D₂ := D₁) hyp.sylow₁ hS hSD hSn)
  · intro S hS hS0 hchar hSn
    exact hS0 (CFSG.Quasithin.F6.eq_bot_of_characteristic hyp.triple.symm hQ' hS hchar hSn)
  · intro S hS hS0 hSD hSn
    exact hS0 (CFSG.Quasithin.F6.eq_bot_of_le_pCoreOf_of_normalizes hyp.triple hQ'
      (D₂ := D₂) hyp.sylow₂ hS hSD hSn)
  · intro S hS hS0 hchar hSn
    exact hS0 (CFSG.Quasithin.F6.eq_bot_of_characteristic hyp.triple hQ' hS hchar hSn)

@[expose] def F_6_13 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    CFSG.pCore 2 D = ⊥ →
    ∀ X : Subgroup D, twoResidual G₁ ≤ X → X.Normal → ¬ twoResidual G₂ ≤ X →
      (X ⊔ G₂ = ⊤ ∧ (X ⊔ pCoreOf 2 G₂).Normal ∧ IsSylowTwoOf (pCoreOf 2 G₂) (X ⊔ pCoreOf 2 G₂)) ∧
      Nonempty (↥(twoResidual G₁) ≃* Multiplicative (ZMod 3)) ∧
      ((IsElemAbelian 2 (pCoreOf 2 G₂) ∧ ∃ n : ℕ, n ≤ 3 ∧ Nat.card ↥(pCoreOf 2 G₂) = 2 ^ n) ∧
        (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) →
          pCoreOf 2 G₂ = ⊥) ∧
        (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤
            Subgroup.normalizer (pCoreOf 2 (twoResidual G₂) : Set D) →
          pCoreOf 2 (twoResidual G₂) = ⊥)) ∧
      (oddCoreIn X = X → ⁅pCoreOf 2 G₁, twoResidual G₁⁆ = ⊥)

section F613Cert

theorem as_F_6_13 : F_6_13 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hQ X hL₁ hXn hL₂
  have h := hyp.triple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.Quasithin.F6.F613Two.{0} :=
    CFSG.Quasithin.F6.f613Two_of_list CFSG.Quasithin.F6.goldschmidtS3ListCat_holds
  obtain ⟨⟨hEl, hcard⟩, h2, h3⟩ :=
    CFSG.Quasithin.F6.f6_13_three_of_F613Two hF h hQ hL₁ hL₂
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₂).exists_card_eq
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk ▸ hcard)
  refine ⟨⟨CFSG.Quasithin.F6.sup_eq_top_of_twoResidual_le h hL₁,
      CFSG.Quasithin.F6.normal_sup_pCoreOf h hL₁,
      CFSG.Quasithin.F6.isSylowTwoOf_pCoreOf_sup h hL₂⟩,
    hF D G₁ G₂ X h hQ hXn hL₁ hL₂,
    ⟨⟨hEl, k, hk3, hk⟩, fun hle => h2 (le_sup_right.trans hle), h3⟩, ?_⟩
  intro hodd
  have hO : Odd (Nat.card ↥X) := by
    have := odd_card_oddCoreIn_of X
    rw [hodd] at this
    exact this
  exact CFSG.Quasithin.F6.commutator_eq_bot_of_odd hL₁ hO

end F613Cert

@[expose] def F_6_14 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    twoResidual (⊤ : Subgroup D) = oddCoreIn (⊤ : Subgroup D) → CFSG.pCore 2 D = ⊥ →
      Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∨
      (Nonempty (↥(pCoreOf 2 G₁) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(pCoreOf 2 G₂) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

theorem as_F_6_14 : F_6_14 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp htw hQ
  refine CFSG.Quasithin.F6.f6_14 hyp.triple ?_ hQ
  rw [htw]
  exact odd_card_oddCoreIn_top

@[expose] def F_6_15 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    (IsSQTKModOThreePrime D ∨ IsQTKModOThreePrime D) →
      (CFSG.pPrimeCore 3 D = ⊥ ∧ CFSG.pCore 2 D = ⊥ ∧ IsGoldschmidtAmalgam G₁ G₂ ∧
        IsGoldCaseCat G₁ G₂) ∧
      (IsSQTKModOThreePrime D →
        ∀ K : Subgroup D, CFSG.IsComponent K → CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K)) ∧
      (IsQTKModOThreePrime D →
        ∀ K : Subgroup D, CFSG.IsComponent K → CFSG.ASVolI.ChA.TheoremBList (↥K ⧸ Subgroup.center ↥K))

open scoped commutatorElement in
private theorem f615_isQuasisimple_of_simple {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hc : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · obtain ⟨a, b, hab⟩ := hn
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

private theorem f615_map_bot_or_top {X S : Type} [Group X] [Group S] {A C : Subgroup X}
    (h : CFSG.Open.IsSubnormal A C) (hS : IsSimpleGroup S) (ρ : C →* S)
    (hρ : Function.Surjective ρ) :
    (A.subgroupOf C).map ρ = ⊥ ∨ (A.subgroupOf C).map ρ = ⊤ := by
  induction h with
  | refl =>
    refine Or.inr ?_
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hρ
  | @step A M C hAM hn _ ih =>
    rcases ih ρ hρ with h | h
    · refine Or.inl (eq_bot_iff.mpr (le_trans ?_ h.le))
      exact Subgroup.map_mono fun x hx => hAM hx
    · rw [Subgroup.normal_subgroupOf_iff hAM] at hn
      have hN : ((A.subgroupOf C).map ρ).Normal := by
        refine ⟨?_⟩
        rintro _ ⟨x, hx, rfl⟩ s
        obtain ⟨y, hy, rfl⟩ : s ∈ (M.subgroupOf C).map ρ := h ▸ Subgroup.mem_top s
        refine ⟨y * x * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy ⊢
        simpa using hn _ _ hx hy
      exact hS.eq_bot_or_eq_top_of_normal _

private theorem f615_isComponent_subgroupOf {E : Type} [Group E] {H L : Subgroup E}
    (h : CFSG.Open.IsComponentOf L H) : CFSG.IsComponent (L.subgroupOf H) := by
  rw [CFSG.isComponent_iff_open]
  exact ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem f615_center_statedSU {p f : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ∣ p ^ f + 1) :
    Subgroup.center ↥(CFSG.Open.StatedSU 3 (p ^ f) K) =
      (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 (p ^ f) K) := by
  have hle := CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ f)
    (F := K)
  have hc1 := CFSG.Open.StatedCenterThree.card_center_statedSU_three hK h3
  have hc2 := (CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2
  rw [Nat.gcd_eq_left h3] at hc2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

private theorem f615_evenRank_le_two {S : Type} [Group S] [Finite S]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.twoLocalPrimeRank p S ≤ 2) :
    CFSG.Open.evenRank S ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨p, Hs, hp, hp2, hTL, rfl⟩
  have hmem : CFSG.Open.pRank p Hs ∈
      {k | ∃ H : Subgroup S, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
    ⟨Hs, hTL, rfl⟩
  have hbdd : BddAbove
      {k | ∃ H : Subgroup S, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card S, ?_⟩
    rintro _ ⟨T, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt T
  exact (le_csSup hbdd hmem).trans (h p hp hp2)

private theorem f615_sqtk_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Milestones.SQTKSimpleList B) : CFSG.Milestones.SQTKSimpleList A := by
  unfold CFSG.Milestones.SQTKSimpleList at h ⊢
  rcases h with ⟨n, h1, h2, ⟨e'⟩⟩ | ⟨p, hp, hp2, h'⟩ | h' | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e'⟩⟩
  · exact Or.inl ⟨n, h1, h2, ⟨e.trans e'⟩⟩
  · refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    rcases h' with ⟨f, hf, hm⟩ | hm | hm
    · exact Or.inl ⟨f, hf, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
    · exact Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm))
    · exact Or.inr (Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm))
  · rcases h' with h' | h'
    · obtain ⟨f, hf⟩ := h'
      refine Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩)))
      rcases hf with ⟨h1, hm⟩ | ⟨h1, hm⟩ | ⟨h1, hm⟩ | ⟨h1, hm⟩ | ⟨h1, hm⟩ | ⟨h1, hm⟩ |
        ⟨h1, h2, hm⟩ | ⟨h1, h2, hm⟩
      · exact Or.inl ⟨h1, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
      · exact Or.inr (Or.inl ⟨h1, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h1, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h1, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h1, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h1, h2, CFSG.SectionRank.reeTitsModel_of_mulEquiv e hm⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨h1, h2, CFSG.SectionRank.suzukiModel_of_mulEquiv e hm⟩))))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (CFSG.SectionRank.reeTitsModel_of_mulEquiv e h'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, hn, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, ⟨e.trans e'⟩⟩)))

private noncomputable def f615Hom {E D : Type} [Group E] [Group D] (φ : E →* D) (K : Subgroup D) :
    ↥(K.comap φ) →* ↥K ⧸ Subgroup.center ↥K :=
  (QuotientGroup.mk' (Subgroup.center ↥K)).comp
    ((φ.comp (K.comap φ).subtype).codRestrict K (fun h => h.2))

private theorem f615Hom_surjective {E D : Type} [Group E] [Group D] {φ : E →* D}
    (hφ : Function.Surjective φ) (K : Subgroup D) : Function.Surjective (f615Hom φ K) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx⟩ := hφ (k : D)
  refine ⟨⟨x, ?_⟩, ?_⟩
  · show φ x ∈ K
    rw [hx]
    exact k.2
  · show QuotientGroup.mk (⟨φ x, _⟩ : ↥K) = QuotientGroup.mk k
    congr 1
    exact Subtype.ext hx

private theorem f615_isSectionOf {E D : Type} [Group E] [Group D] {φ : E →* D}
    (hφ : Function.Surjective φ) (K : Subgroup D) :
    CFSG.ASVolI.ChA.IsSectionOf (↥K ⧸ Subgroup.center ↥K) E := by
  set N := (f615Hom φ K).ker with hNdef
  have hsub : (N.map (K.comap φ).subtype).subgroupOf (K.comap φ) = N := by
    show Subgroup.comap (K.comap φ).subtype (N.map (K.comap φ).subtype) = N
    exact Subgroup.comap_map_eq_self_of_injective (K.comap φ).subtype_injective N
  have hn' : ((N.map (K.comap φ).subtype).subgroupOf (K.comap φ)).Normal := by
    rw [hsub]
    infer_instance
  refine ⟨K.comap φ, N.map (K.comap φ).subtype, hn', ?_⟩
  haveI : ((N.map (K.comap φ).subtype).subgroupOf (K.comap φ)).Normal := hn'
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (f615Hom_surjective hφ K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hsub).symm⟩

private theorem f615_commute_of_ne {E : Type} [Group E] [Finite E] {H H₁ H₂ : Subgroup E}
    (h₁ : CFSG.Open.IsComponentOf H₁ H) (h₂ : CFSG.Open.IsComponentOf H₂ H) (hne : H₁ ≠ H₂) :
    ∀ a ∈ H₁, ∀ b ∈ H₂, Commute a b := by
  intro a ha b hb
  have hne' : H₁.subgroupOf H ≠ H₂.subgroupOf H := by
    intro h
    apply hne
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr h₁.1, inf_eq_left.mpr h₂.1] at h'
  rcases CFSG.LocalCores.distinct_components_commute (f615_isComponent_subgroupOf h₁)
    (f615_isComponent_subgroupOf h₂) with h | h
  · exact absurd h hne'
  · have ha' : (⟨a, h₁.1 ha⟩ : ↥H) ∈ H₁.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    have hb' : (⟨b, h₂.1 hb⟩ : ↥H) ∈ H₂.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
    have hc := Subgroup.commutator_mem_commutator ha' hb'
    rw [h, Subgroup.mem_bot] at hc
    have hcomm : Commute (⟨a, h₁.1 ha⟩ : ↥H) ⟨b, h₂.1 hb⟩ :=
      commutatorElement_eq_one_iff_commute.mp hc
    exact hcomm.map H.subtype

private theorem f615_three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  omega

section F615Full

private theorem f615_sqtk_component
    {D E : Type} [Group D] [Group E] [Finite E]
    (hE : CFSG.SectionRank.IsSQTKCat E) (φ : E →* D) (hφ : Function.Surjective φ)
    (K : Subgroup D) (hK : CFSG.IsComponent K) :
    CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K) := by
  haveI hKs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  have hKn : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hK.1.2.2
  let hiso := QuotientGroup.quotientKerEquivOfSurjective (f615Hom φ K) (f615Hom_surjective hφ K)
  haveI hsimple : IsSimpleGroup (↥(K.comap φ) ⧸ (f615Hom φ K).ker) := hiso.isSimpleGroup
  have hnonab : ∃ a b : ↥(K.comap φ) ⧸ (f615Hom φ K).ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKn
    refine ⟨hiso.symm a, hiso.symm b, fun h => hab ?_⟩
    have := congrArg hiso h
    simpa using this
  have hSQ := CFSG.Milestones.cl_lit_sqtk_simple_list_section E hE (K.comap φ)
    (f615Hom φ K).ker hnonab
  exact f615_sqtk_of_mulEquiv hiso.symm hSQ

private theorem f615_theoremB
    {D E : Type} [Group D] [Finite D] [Group E] [Finite E]
    (hE : CFSG.Open.evenRank E ≤ 2) (hK : CFSG.SectionRank.IsKGroupCat E)
    (φ : E →* D) (hφ : Function.Surjective φ) (K : Subgroup D) (hKc : CFSG.IsComponent K) :
    CFSG.ASVolI.ChA.TheoremBList (↥K ⧸ Subgroup.center ↥K) := by
  haveI hKs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKc.1.2.1
  have hKn : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hKc.1.2.2
  have hsec := f615_isSectionOf hφ K
  have hgfl : CFSG.Open.genFittingLayer (↥K ⧸ Subgroup.center ↥K) = ⊤ := by
    have hQ : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
        (f615_isQuasisimple_of_simple hKs hKn)
    have hIC : CFSG.Open.IsComponentOf (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) ⊤ :=
      (CFSG.isComponent_iff_open _).mp ⟨hQ, Subgroup.IsSubnormal.top⟩
    refine le_antisymm le_top ?_
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    exact le_sSup hIC
  have hA := CFSG.ASVolI.as_A_2_1 E hE hK _ hsec hgfl
  have hKS : CFSG.SectionRank.IsKGroupCat (↥K ⧸ Subgroup.center ↥K) :=
    ((hK.subgroup (K.comap φ)).quotient (f615Hom φ K).ker).of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective (f615Hom φ K) (f615Hom_surjective hφ K)).symm
  obtain ⟨hAll, -⟩ := hA
  obtain ⟨hab, -⟩ := hAll 3 Nat.prime_three (by norm_num)
  rcases hab with ⟨h1, h2⟩ | ⟨-, H, H₁, H₂, n₁, n₂, ⟨eS⟩, -, hHH, hC1, hC2, hSU1, -, hn1, hodd1,
    -, -, -, -⟩
  ·
    have h3 : CFSG.Open.twoLocalPrimeRank 3 (↥K ⧸ Subgroup.center ↥K) ≤ 2 := h1.trans h2
    have hev : CFSG.Open.evenRank (↥K ⧸ Subgroup.center ↥K) ≤ 2 := by
      apply f615_evenRank_le_two
      intro p hp hp2
      by_cases hp3 : p = 3
      · subst hp3
        exact h3
      · obtain ⟨hab', -⟩ := hAll p hp hp2
        rcases hab' with ⟨g1, g2⟩ | ⟨g3, -⟩
        · exact g1.trans g2
        · exact absurd g3 hp3
    exact CFSG.ASVolI.as_A_2_2 _ hKs hKn hev hKS
  ·
    by_cases heq : H₁ = H₂
    ·
      subst heq
      have hHH' : H = H₁ := by rw [hHH, sup_idem]
      rw [hHH'] at eS
      obtain ⟨K₁, hfld, hfin, hcard, ⟨e₁⟩⟩ := hSU1
      have hcen₁ := f615_center_statedSU (p := 2) (f := n₁) Nat.prime_two hcard
        (f615_three_dvd_two_pow_add_one hodd1)
      let e₂ : ↥H₁ ⧸ Subgroup.center ↥H₁ ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n₁) K₁) :=
        QuotientGroup.congr (Subgroup.center ↥H₁)
          ((CFSG.Open.StatedScalars (Fin 3) K₁).subgroupOf (CFSG.Open.StatedSU 3 (2 ^ n₁) K₁))
          e₁ (by rw [Subgroup.map_center_eq e₁, hcen₁])
      have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 2 n₁ := by
        unfold CFSG.Open.StatedLieAdmissible
        refine ⟨Nat.prime_two, by omega, by norm_num, ?_⟩
        intro h
        have h2 : 2 ^ n₁ = 2 := (Prod.mk.inj h).2
        have : 2 ^ 3 ≤ 2 ^ n₁ := Nat.pow_le_pow_right (by norm_num) hn1
        omega
      have hPSU : CFSG.Open.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 n₁ := by
        unfold CFSG.Open.StatedClassicalModel
        exact ⟨hadm, K₁, hfld, hfin, hcard, ⟨eS.trans e₂⟩⟩
      unfold CFSG.ASVolI.ChA.TheoremBList
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      exact Or.inl ⟨n₁, Or.inr (Or.inr (Or.inl ⟨by omega, hPSU⟩))⟩
    ·
      exfalso
      let ρ : ↥H →* ↥H ⧸ Subgroup.center ↥H := QuotientGroup.mk' (Subgroup.center ↥H)
      haveI hS'simple : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := eS.symm.isSimpleGroup
      have himg : ∀ C : Subgroup E, CFSG.Open.IsComponentOf C H →
          (C.subgroupOf H).map ρ = ⊤ := by
        intro C hC
        rcases f615_map_bot_or_top hC.2.1 hS'simple ρ (QuotientGroup.mk'_surjective _) with h | h
        · exfalso
          have hcen : ∀ x : ↥C, x ∈ Subgroup.center ↥C := by
            intro x
            rw [Subgroup.mem_center_iff]
            intro g
            have hy : (⟨x.1, hC.1 x.2⟩ : ↥H) ∈ Subgroup.center ↥H := by
              rw [← QuotientGroup.eq_one_iff]
              have hmem : (⟨x.1, hC.1 x.2⟩ : ↥H) ∈ C.subgroupOf H :=
                Subgroup.mem_subgroupOf.mpr x.2
              have : ρ ⟨x.1, hC.1 x.2⟩ ∈ (C.subgroupOf H).map ρ :=
                Subgroup.mem_map_of_mem ρ hmem
              rw [h] at this
              exact Subgroup.mem_bot.mp this
            have hcg := Subgroup.mem_center_iff.mp hy ⟨g.1, hC.1 g.2⟩
            apply Subtype.ext
            have := congrArg Subtype.val hcg
            simpa using this
          have hsub : ∀ a b : ↥C ⧸ Subgroup.center ↥C, a = b := by
            intro a b
            obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
            obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
            exact QuotientGroup.eq.mpr (hcen _)
          haveI := hC.2.2.2
          obtain ⟨a, b, hab⟩ := exists_pair_ne (↥C ⧸ Subgroup.center ↥C)
          exact hab (hsub a b)
        · exact h
      have hcomm : ∀ s t : ↥H ⧸ Subgroup.center ↥H, s * t = t * s := by
        intro s t
        have hs : s ∈ (H₁.subgroupOf H).map ρ := by
          rw [himg H₁ hC1]
          exact Subgroup.mem_top s
        have ht : t ∈ (H₂.subgroupOf H).map ρ := by
          rw [himg H₂ hC2]
          exact Subgroup.mem_top t
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hs
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ht
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        have hc := f615_commute_of_ne hC1 hC2 heq (a : E) (Subgroup.mem_subgroupOf.mp ha)
          (b : E) (Subgroup.mem_subgroupOf.mp hb)
        exact hc.eq
      obtain ⟨a, b, hab⟩ := hKn
      apply hab
      apply eS.injective
      rw [map_mul, map_mul]
      exact hcomm _ _

theorem as_F_6_15
    : F_6_15 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hQ
  have hX : ∃ X : Type, ∃ _ : Group X, ∃ _ : Finite X,
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X) := by
    rcases hQ with ⟨X, hG, hF, -, ⟨e⟩⟩ | ⟨X, hG, hF, -, -, ⟨e⟩⟩
    · exact ⟨X, hG, hF, ⟨e⟩⟩
    · exact ⟨X, hG, hF, ⟨e⟩⟩
  obtain ⟨X, hXG, hXF, ⟨e⟩⟩ := hX
  obtain ⟨hp3, hp2⟩ := CFSG.Quasithin.F6.remark_f6_15 e
  obtain ⟨hA, hC⟩ := CFSG.Quasithin.F6.remark_f6_15_isGoldCaseCat
    CFSG.Quasithin.F6.goldschmidtS3ListCat_holds.{0} hyp.triple e
  refine ⟨⟨hp3, hp2, hA, hC⟩, ?_, ?_⟩
  · intro hSQ K hK
    obtain ⟨E, hEG, hEF, hE, ⟨e'⟩⟩ := hSQ
    exact f615_sqtk_component hE
      (e'.symm.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 E)))
      (e'.symm.surjective.comp (QuotientGroup.mk'_surjective _)) K hK
  · intro hQT K hK
    obtain ⟨E, hEG, hEF, hq, hKg, ⟨e'⟩⟩ := hQT
    exact f615_theoremB hq hKg (e'.symm.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 E)))
      (e'.symm.surjective.comp (QuotientGroup.mk'_surjective _)) K hK

end F615Full

@[expose] def F_6_16 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsSQTKModOThreePrime D → ¬ IsCyclic ↥(CFSG.pCore 3 D) →
      IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)) ∧
      ((Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∧ pCoreOf 2 G₁ = ⊥ ∧
          pCoreOf 2 G₂ = ⊥) ∨
        IsF618CaseTwo D)

theorem as_F_6_16 : F_6_16 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hX hnc
  obtain ⟨E, hGE, hfin, hsqt, ⟨e⟩⟩ := hX
  obtain ⟨hsq, -⟩ := hsqt
  exact CFSG.Quasithin.F6.f6_16_of_sqtk (X := E)
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsq) e hyp.triple hnc

@[expose] def F_6_17 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsQTKModOThreePrime D → IsCyclic ↥(CFSG.pCore 3 D) →
      (twoResidual (⊤ : Subgroup D) = CFSG.generalizedFitting D ∧
        CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) ∨
      (∃ (K Z : Subgroup D) (p e : ℕ),
        IsL2 p e ↥K ∧ (p ^ e % 24 = 11 ∨ p ^ e % 24 = 13) ∧
        Nat.card ↥Z = 3 ∧ K ⊔ Z = twoResidual (⊤ : Subgroup D) ∧ K ⊓ Z = ⊥ ∧
        (∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) ∧
        ((Nonempty (↥G₁ ≃* DihedralGroup 12) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4))) ∨
          (Nonempty (↥G₂ ≃* DihedralGroup 12) ∧ Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)))) ∧
        ∀ t ∈ G₁ ⊓ G₂, t ∉ K → InducesOuterAut t K ∧ InducesOuterAut t Z)

section F617Cert

private theorem f6_17_evenRank_le_two
    {D : Type} [Group D] [Finite D]
    (hD : IsQTKModOThreePrime D) (K : Subgroup D) (hK : CFSG.IsComponent K) :
    CFSG.Open.evenRank (↥K ⧸ Subgroup.center ↥K) ≤ 2 := by
  obtain ⟨E, _, _, hQT, hKE, ⟨e⟩⟩ := hD
  obtain ⟨H, N, hN, ⟨f⟩⟩ := CFSG.Quasithin.RonanF615.exists_isSection_mulEquiv
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 E)))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) K
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hK.1.2.2
  have hsec : ChA.IsSectionOf (↥K ⧸ Subgroup.center ↥K) E := ⟨H, N, hN, ⟨f⟩⟩
  obtain ⟨hA, -⟩ := as_A_2_1 E hQT hKE _ hsec
    (CFSG.Quasithin.RonanF615.genFittingLayer_eq_top hnab)
  refine CFSG.Quasithin.RonanF615.evenRank_le_two_of_forall fun q hq hq2 => ?_
  have hcq := hA q hq hq2
  unfold ChA.TheoremAConclusion at hcq
  obtain ⟨hcq1, -⟩ := hcq
  rcases hcq1 with ⟨ha, hb⟩ | ⟨-, H', H₁, H₂, n₁, n₂, ⟨e'⟩, hr3, hsup, hc1, hc2, hs1, -⟩
  · exact ha.trans hb
  · exact (CFSG.Quasithin.RonanF615.false_of_clauseB_simple hnab e' hr3 hsup hc1 hc2 hs1).elim

private theorem f6_17_of_walter
    (hW : CFSG.Quasithin.F6.WalterModelsStatement) : F_6_17 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp hD hcyc
  obtain ⟨E, _, _, -, -, ⟨e⟩⟩ := id hD
  obtain ⟨hO, hO2⟩ := CFSG.Quasithin.F6.remark_f6_15 e
  exact CFSG.Quasithin.RonanF617.f6_17_of hW hyp.triple hO hO2 hcyc
    (f6_17_evenRank_le_two hD)

theorem as_F_6_17
    : F_6_17 :=
  f6_17_of_walter CFSG.Quasithin.F6.walterModelsStatement

end F617Cert

@[expose] def F_6_4 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ H₁ H₂ T' : Subgroup (D ⧸ CFSG.pCore 2 D),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      T' = (G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      IsGoldschmidtAmalgam H₁ H₂ ∧
      (HypF_1_1_abcd G₁ G₂ (G₁ ⊓ G₂) ∧ HypF_1_1_abcd G₂ G₁ (G₁ ⊓ G₂)) ∧
      (HypF_1_1_abcd H₁ H₂ T' ∧ HypF_1_1_abcd H₂ H₁ T') ∧
      pCoreOf 2 (H₁ ⊔ H₂ ⊔ T') = ⊥ ∧
      ((CharTwo (H₁ ⊔ T' ⊔ borelOf H₂ T') ∧ CharTwo (H₂ ⊔ T' ⊔ borelOf H₁ T')) →
        IsWeakBNPair H₁ H₂ ∧ (IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁))

private theorem f64_perm3_centralizer :
    ∀ c t : Equiv.Perm (Fin 3), t * t = 1 → t ≠ 1 → c * t = t * c → c = 1 ∨ c = t := by
  decide

private theorem f64_normalizer_le {E : Type} [Group E] [Finite E] {A B : Subgroup E}
    (h : CFSG.Quasithin.IsGoldschmidtTriple A B) {x : E} (hxB : x ∈ B)
    (hxN : x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup E) : Set E)) : x ∈ A ⊓ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient₂
  set T : Subgroup E := A ⊓ B with hT
  set TB : Subgroup B := T.subgroupOf B with hTB
  set π : B →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 B)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ TB := by
    intro y hy
    have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 B) y) = 1 := hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 B) y = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : y ∈ CFSG.pCore 2 B := (QuotientGroup.eq_one_iff y).mp h2
    have h4 : (y : E) ∈ pCoreOf 2 B := (CFSG.Quasithin.F1.mem_pCore_iff_coe y).mp h3
    have h5 : (y : E) ∈ A ⊓ B := CFSG.Quasithin.F6.pCoreOf_le_inf_right h h4
    exact Subgroup.mem_subgroupOf.mpr h5
  have hTBidx : TB.index = 3 := h.relIndex_inf_right
  set P : Subgroup (Equiv.Perm (Fin 3)) := TB.map π with hP
  have hPidx : P.index = 3 := by
    rw [hP, Subgroup.index_map_eq (f := π) (H := TB) hπs hker, hTBidx]
  have hPcard : Nat.card P = 2 := by
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card]; rfl
    have hm := Subgroup.card_mul_index (H := P)
    rw [hPidx, h6] at hm
    omega
  obtain ⟨u, v, huv, huniv⟩ := Nat.card_eq_two_iff.mp hPcard
  have hall : ∀ z : P, z = u ∨ z = v := by
    intro z
    have hz : z ∈ ({u, v} : Set P) := by rw [huniv]; exact Set.mem_univ z
    simpa using hz
  have hall' : ∀ c ∈ P, c = u.1 ∨ c = v.1 := fun c hc => by
    rcases hall ⟨c, hc⟩ with h' | h'
    · exact Or.inl (congrArg Subtype.val h')
    · exact Or.inr (congrArg Subtype.val h')
  have hone : (1 : Equiv.Perm (Fin 3)) ∈ P := P.one_mem
  obtain ⟨t, htP, ht1, hcases⟩ : ∃ t ∈ P, t ≠ 1 ∧ ∀ c ∈ P, c = 1 ∨ c = t := by
    by_cases hu1 : u.1 = 1
    · refine ⟨v.1, v.2, fun hv => huv (Subtype.ext (hu1.trans hv.symm)), fun c hc => ?_⟩
      rcases hall' c hc with h' | h'
      · exact Or.inl (h'.trans hu1)
      · exact Or.inr h'
    · refine ⟨u.1, u.2, hu1, fun c hc => ?_⟩
      have hv1 : v.1 = 1 := by
        rcases hall' 1 hone with h' | h'
        · exact absurd h'.symm hu1
        · exact h'.symm
      rcases hall' c hc with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans hv1)
  have htt : t * t = 1 := by
    rcases hcases (t * t) (P.mul_mem htP htP) with h' | h'
    · exact h'
    · exact absurd (mul_left_cancel (h'.trans (mul_one t).symm)) ht1
  obtain ⟨t₀, ht₀TB, ht₀⟩ := Subgroup.mem_map.mp htP
  set y : B := ⟨x, hxB⟩ with hy
  have hconj : π y * t * (π y)⁻¹ = t := by
    have hmem : y * t₀ * y⁻¹ ∈ TB := by
      rw [hTB, Subgroup.mem_subgroupOf]
      have h1 : (t₀ : E) ∈ T := Subgroup.mem_subgroupOf.mp ht₀TB
      have h2 := (Subgroup.mem_normalizer_iff.mp hxN (t₀ : E)).mp h1
      simpa [hy] using h2
    have hPmem : π (y * t₀ * y⁻¹) ∈ P := Subgroup.mem_map_of_mem π hmem
    have hPmem' : π (y * t₀ * y⁻¹) = π y * t * (π y)⁻¹ := by
      rw [map_mul, map_mul, map_inv, ht₀]
    rw [hPmem'] at hPmem
    rcases hcases _ hPmem with h' | h'
    · exfalso
      apply ht1
      calc t = (π y)⁻¹ * (π y * t * (π y)⁻¹) * π y := by group
        _ = 1 := by rw [h']; group
    · exact h'
  have hcomm : π y * t = t * π y := mul_inv_eq_iff_eq_mul.mp hconj
  have hPy : π y ∈ P := by
    rcases f64_perm3_centralizer (π y) t htt ht1 hcomm with h' | h'
    · rw [h']; exact P.one_mem
    · rw [h']; exact htP
  obtain ⟨s, hsTB, hs⟩ := Subgroup.mem_map.mp hPy
  have hinv : s⁻¹ * y ∈ TB := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
  have hyTB : y ∈ TB := by
    have := TB.mul_mem hsTB hinv
    simpa using this
  exact Subgroup.mem_subgroupOf.mp hyTB

private theorem f64_borelOf_eq {E : Type} [Group E] [Finite E] {A B : Subgroup E}
    (h : CFSG.Quasithin.IsGoldschmidtTriple A B) :
    CFSG.Quasithin.borelOf B (A ⊓ B) = A ⊓ B := by
  have e : (A ⊓ B) ⊓ B = A ⊓ B := by rw [inf_assoc, inf_idem]
  apply le_antisymm
  · intro x hx
    unfold CFSG.Quasithin.borelOf at hx
    rw [e] at hx
    exact f64_normalizer_le h hx.1 hx.2
  · intro x hx
    unfold CFSG.Quasithin.borelOf
    rw [e]
    exact ⟨(Subgroup.mem_inf.mp hx).2, Subgroup.le_normalizer hx⟩

private theorem f64_hyp_abcd {E : Type} [Group E] [Finite E] {A B : Subgroup E}
    (h : CFSG.Quasithin.IsGoldschmidtTriple A B) : HypF_1_1_abcd A B (A ⊓ B) where
  finite := inferInstance
  pgroup := h.isPGroup_inf
  normalizes := inf_le_left.trans Subgroup.le_normalizer
  sylow := by
    rw [inf_eq_left.mpr inf_le_left]
    refine ⟨inf_le_left, h.isPGroup_inf, ?_⟩
    show ¬ 2 ∣ (A ⊓ B).relIndex A
    rw [h.relIndex_inf_left]
    norm_num
  listed := Or.inl ⟨1, le_rfl,
    CFSG.Quasithin.isL2Quot_one_iff_perm3.2 h.quotient₁⟩
  borel_le := by
    rw [f64_borelOf_eq h]
    exact inf_le_left.trans Subgroup.le_normalizer

section F64Cert

theorem as_F_6_4 : F_6_4 := by
  intro D _ _ G₁ G₂ D₁ D₂ hyp H₁ H₂ T' hH₁ hH₂ hT'
  subst hH₁ hH₂ hT'
  rw [hyp.triple.map_inf_of_pCore_le]
  have hA := hyp.triple.quotient_pCore
  set H₁ := G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) with hH₁
  set H₂ := G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) with hH₂
  have hT := hA.toIsGoldschmidtTriple
  have hab1 : HypF_1_1_abcd H₁ H₂ (H₁ ⊓ H₂) := f64_hyp_abcd hT
  have hab2 : HypF_1_1_abcd H₂ H₁ (H₁ ⊓ H₂) := by
    rw [inf_comm]
    exact f64_hyp_abcd hT.symm
  have hb2 : CFSG.Quasithin.borelOf H₂ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := f64_borelOf_eq hT
  have hb1 : CFSG.Quasithin.borelOf H₁ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := by
    have := f64_borelOf_eq hT.symm
    rw [inf_comm H₂ H₁] at this
    exact this
  have hDd : pCoreOf 2 (H₁ ⊔ H₂ ⊔ (H₁ ⊓ H₂)) = ⊥ := by
    rw [sup_eq_left.mpr (inf_le_left.trans le_sup_left), hA.gen,
      CFSG.QuasithinUnique.B113Lie.pCoreOf_top_eq_pCore']
    exact hA.pCore_eq_bot
  refine ⟨hA, ⟨f64_hyp_abcd hyp.triple, by rw [inf_comm]; exact f64_hyp_abcd hyp.triple.symm⟩,
    ⟨hab1, hab2⟩, hDd, ?_⟩
  rintro ⟨hC1, hC2⟩
  have e1 : H₁ ⊔ (H₁ ⊓ H₂) ⊔ (H₁ ⊓ H₂) = H₁ :=
    le_antisymm (sup_le (sup_le le_rfl inf_le_left) inf_le_left) (le_sup_left.trans le_sup_left)
  have e2 : H₂ ⊔ (H₁ ⊓ H₂) ⊔ (H₁ ⊓ H₂) = H₂ :=
    le_antisymm (sup_le (sup_le le_rfl inf_le_right) inf_le_right) (le_sup_left.trans le_sup_left)
  have hCT1 : CFSG.QuasithinUnique.CharTwo H₁ := by
    have := hC1
    rw [hb2, e1] at this
    exact this
  have hCT2 : CFSG.QuasithinUnique.CharTwo H₂ := by
    have := hC2
    rw [hb1, e2] at this
    exact this
  have hH : CFSG.Quasithin.Hyp111 H₁ H₂ (H₁ ⊓ H₂) :=
    ⟨⟨hab1.finite, hab1.pgroup, hab1.normalizes, hab1.sylow, hab1.listed, hab1.borel_le, hC1⟩,
      ⟨hab2.finite, hab2.pgroup, hab2.normalizes, hab2.sylow, hab2.listed, hab2.borel_le, hC2⟩,
      hDd⟩
  have hR : CFSG.Quasithin.Hyp111R H₁ H₂ (H₁ ⊓ H₂) :=
    CFSG.Quasithin.Hyp111R.of_hyp111 CFSG.Quasithin.rankOneListedFacts hH
  have hW := CFSG.Quasithin.F1.isWeakBNPair hR
  have hbig : CFSG.Quasithin.bigB H₁ H₂ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := by
    unfold CFSG.Quasithin.bigB
    rw [hb1, hb2, sup_idem, sup_idem]
  rw [hbig, sup_eq_left.mpr inf_le_left, sup_eq_left.mpr inf_le_right] at hW
  have hlist := CFSG.Quasithin.F6.goldschmidtS3ListCat_holds.{0} (D ⧸ CFSG.pCore 2 D) H₁ H₂ hA
  exact ⟨hW, CFSG.Quasithin.F6.isGoldCaseVICat_of_charTwo hlist hCT1 hCT2⟩

end F64Cert

end CFSG.ASVolI

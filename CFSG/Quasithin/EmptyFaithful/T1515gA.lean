module

public import CFSG.Quasithin.EmptyFaithful.T1515eB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def A7Str (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)) : Prop :=
  Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 7), (QuotientAddGroup.mk x : AltHeart 7) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) x) : AltHeart 7) =
          Multiplicative.toAdd (β v)

omit [Finite G] in
theorem isAltBlockTypeWith_iff_a7Str {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)} :
    IsAltBlockTypeWith L 7 α ↔ ∃ β, A7Str L α β := by
  constructor
  · rintro ⟨h1, h2, β, h3, h4, h5⟩
    exact ⟨β, h1, h2, h3, h4, h5⟩
  · rintro ⟨β, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, β, h3, h4, h5⟩

@[expose] def A7IsThreeSwaps (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∃ a b c d e f : Fin 7, [a, b, c, d, e, f].Nodup ∧
    σ = Equiv.swap a b * Equiv.swap c d * Equiv.swap e f

@[expose] def A7ActsOnU (L : Subgroup G) (β : ↥(blockU L) →* Multiplicative (AltHeart 7)) (s : G)
    (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ x y : ↥(blockU L), (y : G) = s * x * s⁻¹ → ∀ z : ↥(evenWeight 7),
    (QuotientAddGroup.mk z : AltHeart 7) = Multiplicative.toAdd (β x) →
      (QuotientAddGroup.mk (permWeight 7 σ z) : AltHeart 7) = Multiplicative.toAdd (β y)

@[expose] def a7ETheta (d : Fin 7) : ↥(evenWeight 7) :=
  ⟨fun i => if i = d then 0 else 1, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    fin_cases d <;> decide⟩

@[expose] def a7Y1Of (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (P : Finset (Finset (Fin 7))) : Subgroup G :=
  Subgroup.closure {x : G | ∃ hx : x ∈ L,
    StabilizesPartition (α ⟨x, hx⟩ : Equiv.Perm (Fin 7)) P ∧ ∃ k : ℕ, orderOf x = 3 ^ k}

@[expose] def a7BSub (S L : Subgroup G) (u : G) : Subgroup G :=
  (S ⊓ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers u

theorem false_of_a6_component1515g (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h6 : A318Exclusion (alternatingGroup (Fin 6)))
    {T Mc M Z₁ Z₂ V₁ V₂ L K : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h19 : Lemma15119Used T Mc M Z₁ V₂) (hL : IsL1519 Mc Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L)
    (hKc : K ∈ cComp (Subgroup.centralizer (V₁ : Set G)))
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 6)) : False := by
  have hS := hC.setting
  have hsmall := ce15Small_of_four_or_six h24.one
  have h7 := not_seven_of_four_or_six h24.one
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := lemma_15_1_25_six hS h24.one
    rw [Subgroup.relIndex_eq_one.mpr (fun x hx => hcon x hx)] at h1
    omega
  have hswap : conjByElt t V₂ = V₁ := hS.swap_small hsmall h7 t htT htS
  obtain ⟨⟨-, -, hcomm, hnorm⟩, -⟩ := hS.y_facts hsmall
  have hV2ne : V₂ ≠ ⊥ := by
    intro h
    apply (h19.seven L hL.comp hL.quasi hL.not_le).2
    rw [h]
    exact Subgroup.commutator_bot_right L
  obtain ⟨y, ⟨hyM, k, hyk⟩, hyC⟩ : ∃ y ∈ {x : G | x ∈ M ⊓ g1_1516 Z₁ ∧ ∃ k : ℕ, orderOf x = 3 ^ k},
      y ∉ Subgroup.centralizer (V₂ : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) ≤ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.closure_le _).mpr fun x hx => hcon x hx
    have h1 : ⁅oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁), V₂⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm, hcomm] at h1
    exact hV2ne h1
  have hyY : y ∈ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) := Subgroup.subset_closure ⟨hyM, k, hyk⟩
  obtain ⟨hxN, hxC⟩ := conj_normalizer_centralizer1515e hswap (hnorm hyY)
  have hx3 : orderOf (t * y * t⁻¹) = 3 ^ k := by
    rw [← hyk]
    exact orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective y
  set H' : Subgroup G := Subgroup.normalizer (V₁ : Set G) with hH'
  have hZ1V1 : Z₁ ≤ V₁ := h24.z1_le
  have hCH : Subgroup.centralizer (V₁ : Set G) ≤ H' := Subgroup.centralizer_le_normalizer _
  have hsub : IsSubnormal (Subgroup.centralizer (V₁ : Set G)) H' :=
    A3.subnormal_of_normal hCH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr
        (normalizer_le_normalizer_centralizer V₁))
  have hKcH : K ∈ cComp H' := cComp_mem_of_subnormal hsub hKc
  have hV1V : V₁ ≤ V154 T Mc M := (hS.decomp_other h7).1
  have hV1el : IsElemAbelian 2 V₁ :=
    isElemAbelian_mono151 hV1V (hS.V_isElemAbelian hC.qtfe hC.mf)
  have hV1ne : V₁ ≠ ⊥ := fun h => hS.z1_ne (le_bot_iff.mp (h ▸ hZ1V1))
  have hpc : pCoreOf 2 H' ≠ ⊥ := by
    intro h0
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : V₁ ≤ H') le_rfl (isPGroup_of_isElemAbelian hV1el)
    rw [h0] at this
    exact hV1ne (le_bot_iff.mp this)
  have hH : SQTKGroup ↥H' :=
    sqtkGroup_of_pCoreOf_ne_bot hC.qtfe.qtke hC.qtfe.simple hC.qtfe.nonabelian hpc
  have hKeq : K = oPrimeResidualOf 3 H' :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hKcH hKq e h6
  have hxK : t * y * t⁻¹ ∈ K := by
    rw [hKeq]
    exact Subgroup.subset_closure ⟨hxN, k, hx3⟩
  exact hyC (hxC (le_of_mem_cComp hKc hxK))

@[expose] def A7TypeStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → IsAltBlockType L 7 →
      (IsAltBlockType L 7 ∧ (M ⊓ L) ⊔ (mZ1516 Mc Z₁ ⊓ L) = L ∧ M ⊓ L < L) ∧
        ∃ α : ↥L →* alternatingGroup (Fin 7), IsAltBlockTypeWith L 7 α ∧
          ∃ P : Finset (Finset (Fin 7)), IsPartitionOfType P {2, 2, 2, 1} ∧
            (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ →
              StabilizesPartition (α x : Equiv.Perm (Fin 7)) P) ∧
            (∀ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P → (x : G) ∈ M)

@[expose] def A7ModuleStepA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    IsShort2 L → A7Str L α β → S ≤ Subgroup.normalizer (L : Set G) → blockU L ≤ S →
    ∀ (P : Finset (Finset (Fin 7))) (d : Fin 7), IsPartitionOfType P {2, 2, 2, 1} → {d} ∈ P →
    ∀ u : ↥(blockU L),
      (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u) →
      S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G) ≤ a7BSub S L (u : G) ∨
        ∃ s ∈ S, (∃ σ : Equiv.Perm (Fin 7), A7ActsOnU L β s σ ∧ A7IsThreeSwaps σ) ∧
          ∀ g ∈ S ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G),
            g ∈ a7BSub S L (u : G) ∨ ∃ b ∈ a7BSub S L (u : G), g = b * s

@[expose] def A7ModuleStepB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S V₁ : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    IsShort2 L → A7Str L α β → S ≤ Subgroup.normalizer (L : Set G) → blockU L ≤ S →
    ∀ u : ↥(blockU L), V₁ ≤ S → (Subgroup.centralizer (V₁ : Set G) ⊓ S).relIndex S = 2 →
    ∀ s ∈ S, ∀ σ : Equiv.Perm (Fin 7), A7ActsOnU L β s σ → A7IsThreeSwaps σ →
      (∀ g ∈ V₁, g ∈ a7BSub S L (u : G) ∨ ∃ b ∈ a7BSub S L (u : G), g = b * s) →
      V₁ ≤ a7BSub S L (u : G)

@[expose] def A7KStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S V₁ : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    IsShort2 L → A7Str L α β → S ≤ Subgroup.normalizer (L : Set G) → blockU L ≤ S →
    ∀ (d : Fin 7) (u : ↥(blockU L)),
      (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u) →
      V₁ ≤ a7BSub S L (u : G) → ¬ V₁ ≤ Subgroup.centralizer (L : Set G) →
      Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) →
      ∃ K : Subgroup G, K ∈ cComp (Subgroup.centralizer (V₁ : Set G)) ∧
        CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 6))

theorem lemma15125InputFive_of_named_inputs (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hK : KnownFacts15122Types) (n0 : A7TypeStep) (n1 : A7ModuleStepA)
    (n2 : A7ModuleStepB) (n3 : A7KStep) : Lemma15125InputFive := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 hA7
  have hS := hC.setting
  have hsmall := ce15Small_of_four_or_six h24.one
  have h7 := not_seven_of_four_or_six h24.one
  have hLeq : L = oPrimeResidualOf 3 (g1_1516 Z₁) :=
    lemma_15_1_25_one_of_a318 hF h36 h38 hK hC h19 hL h22 h24
  have hG1L : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_oPrimeResidualOf1516 3 _)
  have hSG1 : s1516 T Z₁ ≤ g1_1516 Z₁ := s1516_le_g1 T Z₁
  have hSL : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := hSG1.trans hG1L
  have hLG1 : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
  have hshort : IsShort2 L := hA7.1
  have hUS : blockU L ≤ s1516 T Z₁ := by
    have hQ : pCoreOf 2 L ≤ pCoreOf 2 (g1_1516 Z₁) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLG1)
        (hG1L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact (hshort.2.2.1.1.trans inf_le_left).trans (hQ.trans h18.four.pCoreOf_le)
  obtain ⟨_hCase, α, hα, P, hP, _hPS, hPM⟩ :=
    n0 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 hA7
  obtain ⟨β, hβ⟩ := isAltBlockTypeWith_iff_a7Str.mp hα
  obtain ⟨d, hd⟩ : ∃ d : Fin 7, {d} ∈ P := by
    have h1 : (1 : ℕ) ∈ P.val.map Finset.card := by
      rw [hP.2.2.2]
      decide
    obtain ⟨B, hB, hB1⟩ := Multiset.mem_map.mp h1
    obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hB1
    exact ⟨d, hB⟩
  obtain ⟨u, hu⟩ : ∃ u : ↥(blockU L),
      (QuotientAddGroup.mk (a7ETheta d) : AltHeart 7) = Multiplicative.toAdd (β u) := by
    obtain ⟨u, hu⟩ := hβ.2.2.1 (Multiplicative.ofAdd (QuotientAddGroup.mk (a7ETheta d)))
    exact ⟨u, by rw [hu]; rfl⟩
  have hY1le : a7Y1Of L α P ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) := by
    refine Subgroup.closure_mono ?_
    rintro x ⟨hx, hstab, k, hk⟩
    exact ⟨⟨hPM ⟨x, hx⟩ hstab, hLG1 hx⟩, k, hk⟩
  have hV1S1 : V₁ ≤ s1516 T Z₁ := (le_inf_iff.mp h24.four).1
  have hV1S : V₁ ≤ s1516 T Z₁ ⊓ Subgroup.centralizer (a7Y1Of L α P : Set G) :=
    le_inf hV1S1 ((le_inf_iff.mp h24.four).2.trans (Subgroup.centralizer_le hY1le))
  have hVB : V₁ ≤ a7BSub (s1516 T Z₁) L (u : G) := by
    rcases n1 G L (s1516 T Z₁) α β hshort hβ hSL hUS P d hP hd u hu with
      hB | ⟨s, hsS, ⟨σ, hσ, hcyc⟩, hall⟩
    · exact fun v hv => hB (hV1S hv)
    · exact n2 G L (s1516 T Z₁) V₁ α β hshort hβ hSL hUS u hV1S1 (hS.index_v1 hsmall h7) s hsS σ
        hσ hcyc (fun g hg => hall g (hV1S hg))
  have h3 : ¬ V₁ ≤ Subgroup.centralizer (L : Set G) :=
    lemma_15_1_25_three_of_a318 hF h36 h38 hK hC h19 hL h22 h24
  have hCN : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.centralizer_le (fun z hz => h24.z1_le hz) : Subgroup.centralizer (V₁ : Set G) ≤
      g1_1516 Z₁).trans hG1L
  obtain ⟨Kg, hKc, hKq, ⟨e⟩⟩ := n3 G L (s1516 T Z₁) V₁ α β hshort hβ hSL hUS d u hu hVB h3 hCN
  exact false_of_a6_component1515g hF h36 h38 hK.alt6 hC h19 hL h24 hKc hKq e

end CFSG.Quasithin

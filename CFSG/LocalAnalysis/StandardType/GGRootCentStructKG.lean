module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs
public import CFSG.LocalAnalysis.StandardType.GGSummandTwoGroup
public import CFSG.LocalAnalysis.StandardType.GGSummandStructAbstract

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

section ModSplit

variable {X : Type} [Group X]

@[expose] def ggCentMod (V Q A : Subgroup X) (hQV : Q ≤ V) (hQn : (Q.subgroupOf V).Normal) :
    Subgroup X where
  carrier := {t | t ∈ V ∧ ∀ a ∈ A, ⁅t, a⁆ ∈ Q}
  mul_mem' := by
    rintro t t' ⟨ht, htQ⟩ ⟨ht', ht'Q⟩
    refine ⟨V.mul_mem ht ht', fun a ha => ?_⟩
    have hconj := (Subgroup.normal_subgroupOf_iff hQV).mp hQn
    have h1 : ⁅t * t', a⁆ = t * ⁅t', a⁆ * t⁻¹ * ⁅t, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Q.mul_mem (hconj _ t (ht'Q a ha) ht) (htQ a ha)
  one_mem' := ⟨V.one_mem, fun a _ => by simpa using Q.one_mem⟩
  inv_mem' := by
    rintro t ⟨ht, htQ⟩
    refine ⟨V.inv_mem ht, fun a ha => ?_⟩
    have hconj := (Subgroup.normal_subgroupOf_iff hQV).mp hQn
    have h1 : ⁅t⁻¹, a⁆ = t⁻¹ * ⁅t, a⁆⁻¹ * t⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact hconj _ t⁻¹ (Q.inv_mem (htQ a ha)) (V.inv_mem ht)

theorem ggPerfect_le_of_split_mod {V Q A T₁ T₂ P : Subgroup X} (hQV : Q ≤ V)
    (hQn : (Q.subgroupOf V).Normal) (hQT₁ : Q ≤ T₁) (hT₁ : T₁ ≤ A) (hAV : A ≤ V)
    (hT₂ : T₂ ≤ ggCentMod V Q A hQV hQn) (hPA : P ≤ A) (hperf : ⁅P, P⁆ = P)
    (hP : P ≤ T₁ ⊔ T₂) : P ≤ T₁ := by
  have hT₂' : ∀ t ∈ T₂, ∀ a ∈ A, ⁅t, a⁆ ∈ Q := fun t ht a ha => (hT₂ ht).2 a ha
  have hnorm : ∀ t ∈ T₂, ∀ a ∈ T₁, t * a * t⁻¹ ∈ T₁ := by
    intro t ht a ha
    have h1 : ⁅t, a⁆ ∈ T₁ := hQT₁ (hT₂' t ht a (hT₁ ha))
    have h2 : t * a * t⁻¹ = ⁅t, a⁆ * a := by simp only [commutatorElement_def]; group
    rw [h2]; exact T₁.mul_mem h1 ha
  let B : Subgroup X :=
    { carrier := {y | ∃ a ∈ T₁, ∃ c ∈ T₂, y = a * c}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, c₁, hc₁, rfl⟩ ⟨a₂, ha₂, c₂, hc₂, rfl⟩
        refine ⟨a₁ * (c₁ * a₂ * c₁⁻¹), T₁.mul_mem ha₁ (hnorm c₁ hc₁ a₂ ha₂), c₁ * c₂,
          T₂.mul_mem hc₁ hc₂, ?_⟩
        group
      one_mem' := ⟨1, T₁.one_mem, 1, T₂.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        refine ⟨c⁻¹ * a⁻¹ * c⁻¹⁻¹, hnorm c⁻¹ (T₂.inv_mem hc) a⁻¹ (T₁.inv_mem ha), c⁻¹,
          T₂.inv_mem hc, ?_⟩
        group }
  have hle : T₁ ⊔ T₂ ≤ B := sup_le (fun t ht => ⟨t, ht, 1, T₂.one_mem, (mul_one t).symm⟩)
    (fun t ht => ⟨1, T₁.one_mem, t, ht, (one_mul t).symm⟩)
  have hdec : ∀ y ∈ P, ∃ a ∈ T₁, ∃ c ∈ T₂, c ∈ A ∧ y = a * c := by
    intro y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := hle (hP hy)
    refine ⟨a, ha, c, hc, ?_, rfl⟩
    have h1 : a⁻¹ * (a * c) ∈ A := A.mul_mem (A.inv_mem (hT₁ ha)) (hPA hy)
    simpa using h1
  let φ : ↥A →* ↥V ⧸ Q.subgroupOf V :=
    (QuotientGroup.mk' (Q.subgroupOf V)).comp (Subgroup.inclusion hAV)
  have hker : ∀ z : ↥A, φ z = 1 ↔ (z : X) ∈ Q := by
    intro z
    change QuotientGroup.mk' (Q.subgroupOf V) (Subgroup.inclusion hAV z) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hcomm : ∀ z w : ↥A, ⁅(z : X), (w : X)⁆ ∈ Q → Commute (φ z) (φ w) := by
    intro z w h
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hker]
    exact h
  have key : ∀ a ∈ T₁, ∀ a' ∈ T₁, ∀ c ∈ T₂, ∀ c' ∈ T₂, c ∈ A → c' ∈ A →
      ⁅a * c, a' * c'⁆ ∈ T₁ := by
    intro a ha a' ha' c hc c' hc' hcA hcA'
    let za : ↥A := ⟨a, hT₁ ha⟩
    let za' : ↥A := ⟨a', hT₁ ha'⟩
    let zc : ↥A := ⟨c, hcA⟩
    let zc' : ↥A := ⟨c', hcA'⟩
    have e : φ ⁅za * zc, za' * zc'⁆ = φ ⁅za, za'⁆ := by
      rw [map_commutatorElement, map_commutatorElement, map_mul, map_mul]
      exact commutator_mul_commute (hcomm zc za (hT₂' c hc a (hT₁ ha)))
        (hcomm zc za' (hT₂' c hc a' (hT₁ ha'))) (hcomm zc zc' (hT₂' c hc c' hcA'))
        (hcomm zc' za (hT₂' c' hc' a (hT₁ ha)))
    have h1 : φ (⁅za, za'⁆⁻¹ * ⁅za * zc, za' * zc'⁆) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 : ((⁅za, za'⁆⁻¹ * ⁅za * zc, za' * zc'⁆ : ↥A) : X) ∈ Q := (hker _).mp h1
    have h2' : (⁅a, a'⁆)⁻¹ * ⁅a * c, a' * c'⁆ ∈ Q := by
      have h2'' : ((⁅za, za'⁆⁻¹ * ⁅za * zc, za' * zc'⁆ : ↥A) : X) =
          (⁅a, a'⁆)⁻¹ * ⁅a * c, a' * c'⁆ := rfl
      rw [← h2'']; exact h2
    have h3 : (⁅a, a'⁆)⁻¹ * ⁅a * c, a' * c'⁆ ∈ T₁ := hQT₁ h2'
    have h4 : ⁅a, a'⁆ ∈ T₁ := by
      simp only [commutatorElement_def]
      exact T₁.mul_mem (T₁.mul_mem (T₁.mul_mem ha ha') (T₁.inv_mem ha)) (T₁.inv_mem ha')
    have h5 : ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ * ((⁅a, a'⁆)⁻¹ * ⁅a * c, a' * c'⁆) := by group
    rw [h5]
    exact T₁.mul_mem h4 h3
  rw [← hperf, Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨y, hy, y', hy', rfl⟩
  obtain ⟨a, ha, c, hc, hcA, rfl⟩ := hdec y hy
  obtain ⟨a', ha', c', hc', hcA', rfl⟩ := hdec y' hy'
  exact key a ha a' ha' c hc c' hc' hcA hcA'

end ModSplit

section Pieces

variable {X : Type} [Group X]

theorem pCoreOf_normal_subgroupOf (p : ℕ) (H : Subgroup X) :
    ((pCoreOf p H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (pCoreOf_le' p H)]
  intro q h hq hh
  exact conj_mem_pCoreOf' p hh hq

theorem ggPiece_le_or_commutator_le [Finite X] {V S Q U : Subgroup X} (hSV : S ≤ V)
    (hsn : IsSubnormal S V) (hQS : Q ≤ S) (hQn : (Q.subgroupOf V).Normal)
    (hq : ∀ [(Q.subgroupOf S).Normal], CFSG.IsQuasisimple (↥S ⧸ Q.subgroupOf S))
    (hUV : U ≤ V) (hU : IsSubnormal U V) : S ≤ U ⊔ Q ∨ ⁅S, U⁆ ≤ Q := by
  have hQSn : (Q.subgroupOf S).Normal := ggRCS_normal_subgroupOf hSV hQS hQn
  set π := QuotientGroup.mk' (Q.subgroupOf V) with hπ
  have hC := ggRCS_isComponent_of_isComponentOf_top
    (ggRCS_isComponentOf_map_quot hSV hsn (@hq hQSn))
  have hU' : ((U.subgroupOf V).map π).IsSubnormal := by
    have h1 : IsSubnormal (U.subgroupOf V) ⊤ := by
      have h := ggAssemblyIsSubnormal_subgroupOf hU V
      rwa [Subgroup.subgroupOf_self] at h
    have h2 := ggIsSubnormal_map π h1
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact ggRCS_isSubnormal_of_top h2 rfl
  have hπ1 : ∀ v : ↥V, π v = 1 ↔ (v : X) ∈ Q := fun v => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rcases CFSG.LocalCores.component_subnormal_subgroup hC hU' with hle | hc
  · left
    intro s hs
    obtain ⟨u, hu, hus⟩ := hle ⟨⟨s, hSV hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have h1 : π (u⁻¹ * ⟨s, hSV hs⟩) = 1 := by rw [map_mul, map_inv, hus, inv_mul_cancel]
    have hq' : (u : X)⁻¹ * s ∈ Q := by simpa using (hπ1 _).mp h1
    have hs' : s = (u : X) * ((u : X)⁻¹ * s) := by group
    rw [hs']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hu))
      (Subgroup.mem_sup_right hq')
  · right
    rw [Subgroup.commutator_le]
    intro s hs u hu
    have h1 : ⁅π ⟨s, hSV hs⟩, π ⟨u, hUV hu⟩⁆ ∈
        ⁅(S.subgroupOf V).map π, (U.subgroupOf V).map π⁆ :=
      Subgroup.commutator_mem_commutator ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hc, Subgroup.mem_bot, ← map_commutatorElement] at h1
    have h2 := (hπ1 _).mp h1
    simpa [commutatorElement_def] using h2

end Pieces

section Summands

variable {X : Type} [Group X] [Finite X]

theorem ggPerfect_not_dvd_of_isPGroup_two {p : ℕ} (hp : p.Prime) {A S : Subgroup X}
    (hA : IsPGroup 2 A) (hSA : S ≤ A) (hSp : ⁅S, S⁆ = S) (hpS : p ∣ Nat.card S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsol : Group.IsSolvable ↥A := by
    have : Group.IsNilpotent ↥A := hA.isNilpotent
    infer_instance
  have hbot : S = ⊥ := CFSG.SeitzReduction.perfect_eq_bot_of_le hsol hSp hSA
  subst hbot
  rw [Subgroup.card_bot] at hpS
  exact hp.not_dvd_one hpS

theorem ggQuasiPiece_pCore_le {p : ℕ} (hp : p.Prime) {V E S : Subgroup X}
    {𝒥 : Set (Subgroup X)} (hperf : ∀ P : Subgroup X, P ≤ V → ⁅P, P⁆ = P → P ≤ sSup 𝒥)
    (hJ : ∀ J ∈ 𝒥, GGRCSSummand V E J) (hS : GGRCSQuasiPiece p V S) :
    pCoreOf 2 V ≤ S := by
  obtain ⟨Q, hSV, hsn, hSp, hpS, -, hQS, hQ2, hQn, hq⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQV : Q ≤ V := hQS.trans hSV
  have hQbV : pCoreOf 2 V ≤ V := pCoreOf_le' 2 V
  have hQbn : ((pCoreOf 2 V).subgroupOf V).Normal := pCoreOf_normal_subgroupOf 2 V
  have hQQb : Q ≤ pCoreOf 2 V := by
    refine le_pCoreOf_of_normalized 2 hQV hQ2 ?_
    intro h hh q hq
    exact (Subgroup.normal_subgroupOf_iff hQV).mp hQn q h hq hh
  have hnot : ¬ S ≤ pCoreOf 2 V := fun h =>
    ggPerfect_not_dvd_of_isPGroup_two hp (isPGroup_pCoreOf' 2 V) h hSp hpS
  obtain ⟨J, hJ𝒥, hJnc⟩ : ∃ J ∈ 𝒥, ¬ J ≤ ggCentMod V Q S hQV hQn := by
    by_contra hcon
    push Not at hcon
    have hall : sSup 𝒥 ≤ ggCentMod V Q S hQV hQn := sSup_le hcon
    have hSQ : ⁅S, S⁆ ≤ Q := Subgroup.commutator_le.mpr fun a ha b hb =>
      (hall (hperf S hSV hSp ha)).2 b hb
    have hSQ' : S ≤ Q := by rwa [hSp] at hSQ
    exact hnot (hSQ'.trans hQQb)
  obtain ⟨hJV, hJsn, hJp, hQbJ, hJQ, hEJ, hJq⟩ := hJ J hJ𝒥
  have hq' : ∀ [((pCoreOf 2 V).subgroupOf J).Normal],
      CFSG.IsQuasisimple (↥J ⧸ (pCoreOf 2 V).subgroupOf J) := fun {hN} =>
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp (@hJq hN).1
  have hSJ : S ≤ J := by
    rcases ggPiece_le_or_commutator_le hSV hsn hQS hQn hq hJV hJsn with h | h
    · exact h.trans (sup_le le_rfl (hQQb.trans hQbJ))
    · refine absurd ?_ hJnc
      intro t ht
      refine ⟨hJV ht, fun a ha => ?_⟩
      have h1 : ⁅a, t⁆ ∈ Q := h (Subgroup.commutator_mem_commutator ha ht)
      simpa using Q.inv_mem h1
  have hJle : J ≤ S ⊔ pCoreOf 2 V := by
    rcases ggPiece_le_or_commutator_le hJV hJsn hQbJ hQbn hq' hSV hsn with h | h
    · exact h
    · have h2 : ⁅S, S⁆ ≤ pCoreOf 2 V := (Subgroup.commutator_mono hSJ le_rfl).trans h
      exact (hnot (by rwa [hSp] at h2)).elim
  have hJeq : S ⊔ pCoreOf 2 V = J := le_antisymm (sup_le hSJ hQbJ) hJle
  exact ggTwoGroup_le_of_subnormal_sup (ggIsSubnormal_of_le_of_le hsn hSJ hJV) hQbJ
    (isPGroup_pCoreOf' 2 V) hJeq hJQ

theorem ggSummandStruct_of_structKG {V E K : Subgroup X} (hK : CFSG.IsComponent K)
    (hQK : pCoreOf 2 V ≤ K) {𝒥 : Set (Subgroup X)}
    (hperf : ∀ P : Subgroup X, P ≤ V → ⁅P, P⁆ = P → P ≤ sSup 𝒥)
    (hJ : ∀ J ∈ 𝒥, GGRCSSummand V E J) :
    GGSummandStruct E K V (pCoreOf 2 V) {J | J ∈ 𝒥 ∧ J ≤ K} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQV : pCoreOf 2 V ≤ V := pCoreOf_le' 2 V
  have hQn : ((pCoreOf 2 V).subgroupOf V).Normal := pCoreOf_normal_subgroupOf 2 V
  have hQA : pCoreOf 2 V ≤ K ⊓ V := le_inf hQK hQV
  have hKV : IsSubnormal (K ⊓ V) V := by
    have h1 : IsSubnormal K ⊤ := (ggAssemblyIsSubnormal_iff le_top).mpr hK.2.subgroupOf
    have h2 := ggIsSubnormal_inf h1 V
    rwa [top_inf_eq] at h2
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm (pCoreOf_inf_le_of_isComponent hK 2) ?_
    refine le_pCoreOf_of_normalized 2 hQA (isPGroup_pCoreOf' 2 V) ?_
    intro h hh q hq
    exact conj_mem_pCoreOf' 2 (Subgroup.mem_inf.mp hh).2 hq
  · intro P hPA hperfP
    have hP𝒥 := hperf P (hPA.trans inf_le_right) hperfP
    have hT₁A : pCoreOf 2 V ⊔ sSup {J | J ∈ 𝒥 ∧ J ≤ K} ≤ K ⊓ V :=
      sup_le hQA (sSup_le fun J hJ' => le_inf hJ'.2 (hJ _ hJ'.1).1)
    have hT₂ : sSup {J | J ∈ 𝒥 ∧ ¬ J ≤ K} ≤ ggCentMod V (pCoreOf 2 V) (K ⊓ V) hQV hQn := by
      refine sSup_le fun J hJ' t ht => ?_
      obtain ⟨hJV, hJsn, -, hQJ, -, -, hJq⟩ := hJ J hJ'.1
      have hq : ∀ [((pCoreOf 2 V).subgroupOf J).Normal],
          CFSG.IsQuasisimple (↥J ⧸ (pCoreOf 2 V).subgroupOf J) := fun {hN} =>
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
          (@hJq hN).1
      rcases ggPiece_le_or_commutator_le hJV hJsn hQJ hQn hq inf_le_right hKV with h | h
      · exact absurd ((h.trans (sup_le le_rfl hQA)).trans inf_le_left) hJ'.2
      · exact ⟨hJV ht, fun a ha => h (Subgroup.commutator_mem_commutator ht ha)⟩
    have hPT : P ≤ (pCoreOf 2 V ⊔ sSup {J | J ∈ 𝒥 ∧ J ≤ K}) ⊔
        sSup {J | J ∈ 𝒥 ∧ ¬ J ≤ K} := by
      refine hP𝒥.trans (sSup_le fun J hJ' => ?_)
      by_cases h : J ≤ K
      · exact le_sup_of_le_left (le_sup_of_le_right (le_sSup ⟨hJ', h⟩))
      · exact le_sup_of_le_right (le_sSup ⟨hJ', h⟩)
    have hPT₁ := ggPerfect_le_of_split_mod hQV hQn le_sup_left hT₁A inf_le_right hT₂ hPA
      hperfP hPT
    by_cases hne : {J | J ∈ 𝒥 ∧ J ≤ K}.Nonempty
    · obtain ⟨J₀, hJ₀⟩ := hne
      exact hPT₁.trans (sup_le ((hJ _ hJ₀.1).2.2.2.1.trans (le_sSup hJ₀)) le_rfl)
    · have hemp : {J | J ∈ 𝒥 ∧ J ≤ K} = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hemp, sSup_empty, sup_bot_eq] at hPT₁
      rw [hemp, sSup_empty]
      have hsol : Group.IsSolvable ↥(pCoreOf 2 V) := by
        have : Group.IsNilpotent ↥(pCoreOf 2 V) := (isPGroup_pCoreOf' 2 V).isNilpotent
        infer_instance
      exact (CFSG.SeitzReduction.perfect_eq_bot_of_le hsol hperfP hPT₁).le
  · intro J hJ'
    obtain ⟨hJ𝒥, hJK⟩ := hJ'
    obtain ⟨hJV, hJsn, hJp, hQJ, -, hEJ, hJq⟩ := hJ J hJ𝒥
    refine ⟨le_inf hJK hJV, hQJ, ggIsSubnormal_of_le_of_le hJsn (le_inf hJK hJV) inf_le_right,
      hJp, hEJ, ?_⟩
    exact hJq

end Summands

section Inputs

theorem ggRootCentAutKIIIFlatInput_of_known (hKG : GGRootCentStructKGInput) :
    GGRootCentAutKIIIFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset
  obtain ⟨hK, hKV, hEK, hSK, hQ⟩ := hset
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  obtain ⟨hEel, -⟩ := ggBarE_elem_card hp hp2 hch.le_centralizer hch.2.1
  obtain ⟨𝒥, hperf, hJ⟩ := hKG G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have hQK : pCoreOf 2 (ggRCSImg r (ggM p B x L D J)) ≤ K :=
    (ggQuasiPiece_pCore_le hp hperf hJ hQ).trans hSK
  intro hN
  exact ggRCSAutKIIIFlat_of_summandStruct hp hp2 hEel hfus.1 hEK
    (ggSummandStruct_of_structKG hK hQK hperf hJ)

end Inputs

end CFSG.StandardType

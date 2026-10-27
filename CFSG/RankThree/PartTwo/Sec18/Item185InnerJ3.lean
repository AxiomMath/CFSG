module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27Classes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutLocal
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutElemJ3
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Holt.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Normalizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.H13.L32NKGSp6Search
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerK
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec18.SylowFiveTwo
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Descent
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofChoiceY
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofTools
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofE27

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction (j3_e27_class_split centralizer_structure_J3Plain)

private theorem ncard_compl_E27 {Q : Type} [Group Q] [Finite Q] {A B₁ : Subgroup Q}
    (hB₁ : B₁ ≤ A) (h27 : Nat.card A = 27) (h9 : Nat.card B₁ = 9) :
    ((A : Set Q) \ (B₁ : Set Q)).ncard = 18 := by
  have hsub : (B₁ : Set Q) ⊆ (A : Set Q) := fun g hg => hB₁ hg
  have h1 : (A : Set Q).ncard = 27 := by rw [← Nat.card_coe_set_eq]; exact h27
  have h2 : (B₁ : Set Q).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact h9
  have h3 := Set.ncard_diff hsub (Set.toFinite _)
  omega

section J3


private theorem card_centralizer_iso_J3 {Q : Type} [Group Q] (e : Q ≃* NativeSporadic.J3)
    (x : Q) :
    Nat.card (Subgroup.centralizer ({x} : Set Q)) =
      Nat.card (Subgroup.centralizer ({e x} : Set NativeSporadic.J3)) := by
  have hcard1 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv (e x)
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    (e.trans CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv) x
  exact hcard2.trans hcard1.symm

private theorem card_automizer_J3 {Q : Type} [Group Q] (e : Q ≃* NativeSporadic.J3)
    {A : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    Nat.card (CFSG.RankThree.Asc83Table.Automizer A) = 72 := by
  have ψ : Q ≃* CFSG.Sporadic.J3.J CFSG.RankThree.Asc83Table.J3.D :=
    e.trans CFSG.RankThree.Asc83Table.J3.φ
  obtain ⟨h72, -⟩ := (@CFSG.RankThree.Asc83Table.e27_transport
    (CFSG.Sporadic.J3.J CFSG.RankThree.Asc83Table.J3.D)
    (inferInstance : Group (CFSG.Sporadic.J3.J CFSG.RankThree.Asc83Table.J3.D)) Q
    (inferInstance : Group Q) ψ
    CFSG.RankThree.Asc83Table.J3.pRank_J CFSG.RankThree.Asc83Table.J3.automizer_J).2 A hA h27
  exact h72

private theorem card_normalizer_eq_J3 {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.J3) {A : Subgroup Q} (hA : IsElementaryAbelian 3 A)
    (h27 : Nat.card A = 27) :
    Nat.card (Subgroup.normalizer (A : Set Q)) =
      72 * Nat.card (Subgroup.centralizer (A : Set Q)) := by
  have h72 := card_automizer_J3 e hA h27
  have hcen : Nat.card ↥((Subgroup.centralizer (A : Set Q)).subgroupOf
      (Subgroup.normalizer (A : Set Q))) = Nat.card ↥(Subgroup.centralizer (A : Set Q)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv
  have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.centralizer (A : Set Q)).subgroupOf (Subgroup.normalizer (A : Set Q)))
  rw [hcen, h72] at hdecomp
  exact hdecomp

theorem j3_centralizer_E27 {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    Subgroup.centralizer (A : Set Q) = A := by
  have hN := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.j3_e27_card_normalizer e hA h27
  have hq := card_normalizer_eq_J3 e hA h27
  have hcomm := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hA).1
  have hAC : A ≤ Subgroup.centralizer (A : Set Q) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb a ha
  exact (Subgroup.eq_of_le_of_card_ge hAC (by omega)).symm

theorem j3_card_normalizer_E27 {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    Nat.card (Subgroup.normalizer (A : Set Q)) = 1944 := by
  have hq := card_normalizer_eq_J3 e hA h27
  rw [j3_centralizer_E27 e hA h27, h27] at hq
  omega

private theorem j3_plane_classes {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A B₁ : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) (hB₁ : B₁ ≤ A)
    (h9 : Nat.card B₁ = 9)
    (hcl : ∀ x ∈ A, x ∉ B₁ → Nat.card (Subgroup.centralizer ({x} : Set Q)) = 1080) :
    ∀ z ∈ B₁, z ≠ 1 → Nat.card (Subgroup.centralizer ({z} : Set Q)) = 243 := by
  obtain ⟨B₁', hB₁'A, hB₁'9, h243, -⟩ := j3_e27_class_split e hA h27
  have hle : B₁' ≤ B₁ := by
    intro z hz
    by_contra hzB
    have hz1 : z ≠ 1 := fun h => hzB (h ▸ B₁.one_mem)
    have h1 := hcl z (hB₁'A hz) hzB
    have h2 := h243 z hz hz1
    omega
  have heq : B₁' = B₁ := Subgroup.eq_of_le_of_card_ge hle (by omega)
  intro z hz hz1
  exact h243 z (by rw [heq]; exact hz) hz1

private theorem j3_stab_le {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27)
    {x : Q} (hxA : x ∈ A) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set Q)) = 1080) :
    Nat.card ↥(Subgroup.normalizer (A : Set Q) ⊓ Subgroup.centralizer ({x} : Set Q)) ≤ 108 := by
  have hcomm := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hA).1
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({e x} : Set NativeSporadic.J3)) := by
    rw [← card_centralizer_iso_J3 e x, hC]
    norm_num
  obtain ⟨I, hIC, -, ⟨eI⟩, -, -, hD3, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Plain e hx3 hx1 h5
  have hDcomm' : ∀ d ∈ Subgroup.zpowers x, ∀ y ∈ I, d * y = y * d :=
    fun d hd y hy => hDcomm d hd y (hIC hy)
  have hAC : A ≤ Subgroup.zpowers x ⊔ I := by
    intro a ha
    rw [hCeq, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm a ha x hxA
  obtain ⟨-, hAcard⟩ := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_eq_mul_card_inf_of_le
    hDcomm' hDI (Subgroup.zpowers_le.2 hxA) hAC
  have hAI : Nat.card ↥(A ⊓ I) = 9 := by
    rw [hD3, h27] at hAcard
    omega
  have hM₀ : Nat.card ↥(I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)) ≤ 36 := by
    have hE₀I : A ⊓ I ≤ I := inf_le_right
    have hE'card : Nat.card ((A ⊓ I).subgroupOf I) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀I).toEquiv]
      exact hAI
    have h36 := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_normalizer_le_of_A6 eI hE'card
    have hle : (I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)).subgroupOf I ≤
        Subgroup.normalizer (((A ⊓ I).subgroupOf I : Subgroup ↥I) : Set ↥I) := by
      intro g hg
      have hg' := Subgroup.mem_subgroupOf.1 hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.1 hg'.2 (h : Q)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this
    calc Nat.card ↥(I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q))
        = Nat.card ↥((I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)).subgroupOf I) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ ≤ Nat.card ↥(Subgroup.normalizer (((A ⊓ I).subgroupOf I : Subgroup ↥I) : Set ↥I)) :=
          Subgroup.card_le_of_le hle
      _ ≤ 36 := h36
  have hCN : Nat.card ↥(Subgroup.normalizer (A : Set Q) ⊓ Subgroup.centralizer ({x} : Set Q))
      ≤ 108 := by
    have hle : Subgroup.normalizer (A : Set Q) ⊓ Subgroup.centralizer ({x} : Set Q) ≤
        Subgroup.zpowers x ⊔ (I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)) := by
      intro g hg
      have hgC : g ∈ Subgroup.zpowers x ⊔ I := by
        rw [hCeq]
        exact hg.2
      obtain ⟨d, hd, i, hi, rfl⟩ :=
        (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.mem_sup_of_commute hDcomm').1 hgC
      have hdN : d ∈ Subgroup.normalizer (A : Set Q) :=
        Subgroup.le_normalizer ((Subgroup.zpowers_le.2 hxA) hd)
      have hiN : i ∈ Subgroup.normalizer (A : Set Q) := by
        have := (Subgroup.normalizer (A : Set Q)).mul_mem
          ((Subgroup.normalizer (A : Set Q)).inv_mem hdN) hg.1
        simpa using this
      have hi' : i ∈ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q) :=
        CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.mem_normalizer_inf_out hiN
          (Subgroup.le_normalizer hi)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right ⟨hi, hi'⟩)
    have hM₀N : I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q) ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Q) : Set Q) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hDcomm' d hd g hg.1
    have hdisj : Disjoint (Subgroup.zpowers x)
        (I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)) :=
      hDI.mono_right inf_le_left
    have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers x) (I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)) hM₀N hdisj
    calc Nat.card ↥(Subgroup.normalizer (A : Set Q) ⊓ Subgroup.centralizer ({x} : Set Q))
        ≤ Nat.card ↥(Subgroup.zpowers x ⊔
            (I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q))) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥(Subgroup.zpowers x) *
          Nat.card ↥(I ⊓ Subgroup.normalizer ((A ⊓ I : Subgroup Q) : Set Q)) := hsup
      _ ≤ 108 := by
          rw [hD3]
          omega
  exact hCN

theorem j3_normalizer_transitive {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A B₁ : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) (hB₁ : B₁ ≤ A)
    (h9 : Nat.card B₁ = 9)
    (hcl : ∀ x ∈ A, x ∉ B₁ → Nat.card (Subgroup.centralizer ({x} : Set Q)) = 1080) :
    ∀ x ∈ A, x ∉ B₁ → ∀ y ∈ A, y ∉ B₁ → ∃ g ∈ Subgroup.normalizer (A : Set Q), g * x * g⁻¹ = y := by
  intro x hxA hxB y hyA hyB
  have h3B := j3_plane_classes e hA h27 hB₁ h9 hcl
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ B₁.one_mem)
  have hx3 : x ^ 3 = 1 := (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.1 hA).2 x hxA
  have hC : Nat.card (Subgroup.centralizer ({x} : Set Q)) = 1080 := hcl x hxA hxB
  have hN := j3_card_normalizer_E27 e hA h27
  have hH := j3_stab_le e hA h27 hxA hx3 hx1 hC
  have hT := ncard_compl_E27 hB₁ h27 h9
  set N : Subgroup Q := Subgroup.normalizer (A : Set Q) with hNdef
  set H : Subgroup ↥N := (N ⊓ Subgroup.centralizer ({x} : Set Q)).subgroupOf N with hHdef
  have hHcard : Nat.card ↥H = Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set Q)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmemT : ∀ n : ↥N, (n : Q) * x * (n : Q)⁻¹ ∈ (A : Set Q) \ (B₁ : Set Q) := by
    intro n
    refine ⟨(Subgroup.mem_normalizer_iff.1 n.2 x).1 hxA, fun hB => ?_⟩
    have hne : (n : Q) * x * (n : Q)⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.1 h1)
    have h1 := h3B _ hB hne
    rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_cent_conj] at h1
    omega
  let φ : ↥N ⧸ H → Q :=
    Quotient.lift (fun n : ↥N => (n : Q) * x * (n : Q)⁻¹) (by
      intro n n' hnn'
      have hmem := QuotientGroup.leftRel_apply.1 hnn'
      have hc : ((n⁻¹ * n' : ↥N) : Q) ∈ Subgroup.centralizer ({x} : Set Q) :=
        (Subgroup.mem_subgroupOf.1 hmem).2
      have hk := Subgroup.mem_centralizer_singleton_iff.1 hc
      have hk' : ((n : Q)⁻¹ * (n' : Q)) * x = x * ((n : Q)⁻¹ * (n' : Q)) := by
        simpa using hk
      show (n : Q) * x * (n : Q)⁻¹ = (n' : Q) * x * (n' : Q)⁻¹
      calc (n : Q) * x * (n : Q)⁻¹
          = (n : Q) * (x * ((n : Q)⁻¹ * (n' : Q))) * ((n : Q)⁻¹ * (n' : Q))⁻¹ * (n : Q)⁻¹ := by
            group
        _ = (n : Q) * (((n : Q)⁻¹ * (n' : Q)) * x) * ((n : Q)⁻¹ * (n' : Q))⁻¹ * (n : Q)⁻¹ := by
            rw [hk']
        _ = (n' : Q) * x * (n' : Q)⁻¹ := by group)
  have hφmk : ∀ n : ↥N, φ (QuotientGroup.mk n) = (n : Q) * x * (n : Q)⁻¹ := fun n => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective b
    rw [hφmk, hφmk] at hab
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.2 ⟨N.mul_mem (N.inv_mem n.2) n'.2, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show ((n : Q)⁻¹ * (n' : Q)) * x = x * ((n : Q)⁻¹ * (n' : Q))
    calc ((n : Q)⁻¹ * (n' : Q)) * x
        = (n : Q)⁻¹ * ((n' : Q) * x * (n' : Q)⁻¹) * (n' : Q) := by group
      _ = (n : Q)⁻¹ * ((n : Q) * x * (n : Q)⁻¹) * (n' : Q) := by rw [hab]
      _ = x * ((n : Q)⁻¹ * (n' : Q)) := by group
  have hrange : Set.range φ ⊆ (A : Set Q) \ (B₁ : Set Q) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
    exact hmemT n
  have hidx : Nat.card (↥N ⧸ H) ≤ 18 := by
    calc Nat.card (↥N ⧸ H) = Nat.card (Set.range φ) :=
          (Nat.card_range_of_injective hφinj).symm
      _ = (Set.range φ).ncard := Nat.card_coe_set_eq _
      _ ≤ ((A : Set Q) \ (B₁ : Set Q)).ncard := Set.ncard_le_ncard hrange (Set.toFinite _)
      _ = 18 := hT
  have hq18 : Nat.card (↥N ⧸ H) = 18 := by
    have hNcard := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [hHcard, hN] at hNcard
    by_contra hne
    have hlt : Nat.card (↥N ⧸ H) ≤ 17 := by omega
    have hle := Nat.mul_le_mul hlt hH
    omega
  have hTeq : Set.range φ = (A : Set Q) \ (B₁ : Set Q) := by
    refine Set.eq_of_subset_of_ncard_le hrange ?_ (Set.toFinite _)
    have hr : (Set.range φ).ncard = Nat.card (↥N ⧸ H) := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hφinj]
    omega
  have hyT : y ∈ (A : Set Q) \ (B₁ : Set Q) := ⟨hyA, hyB⟩
  rw [← hTeq] at hyT
  obtain ⟨a, ha⟩ := hyT
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective a
  rw [hφmk] at ha
  exact ⟨(n₀ : Q), n₀.2, ha⟩

theorem j3_invariant_plane_eq {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {A B₁ B : Subgroup Q} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) (hB₁ : B₁ ≤ A)
    (h9 : Nat.card B₁ = 9)
    (hcl : ∀ x ∈ A, x ∉ B₁ → Nat.card (Subgroup.centralizer ({x} : Set Q)) = 1080)
    (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hN : Subgroup.normalizer (A : Set Q) ≤ Subgroup.normalizer (B : Set Q)) : B = B₁ := by
  by_contra hne
  have hex : ∃ x ∈ B, x ∉ B₁ := by
    by_contra hall
    push Not at hall
    exact hne (Subgroup.eq_of_le_of_card_ge (fun g hg => hall g hg) (by omega))
  obtain ⟨x, hxB, hxB₁⟩ := hex
  have hxA : x ∈ A := hBA hxB
  have hsub : (A : Set Q) \ (B₁ : Set Q) ⊆ (B : Set Q) := by
    rintro g ⟨hgA, hgB₁⟩
    obtain ⟨n, hn, hng⟩ := j3_normalizer_transitive e hA h27 hB₁ h9 hcl x hxA hxB₁ g hgA hgB₁
    have hnB : n ∈ Subgroup.normalizer (B : Set Q) := hN hn
    rw [← hng]
    exact (Subgroup.mem_normalizer_iff.1 hnB x).1 hxB
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (B : Set Q).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hB9
  rw [ncard_compl_E27 hB₁ h27 h9, h2] at h1
  omega

theorem j3_oTwoThree_small {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3) {c : Q}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hC : Nat.card (Subgroup.centralizer ({c} : Set Q)) = 1080) :
    Nat.card (Sec4.oTwoP 3 (Subgroup.centralizer ({c} : Set Q))) ≤ 3 := by
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({e c} : Set NativeSporadic.J3)) := by
    rw [← card_centralizer_iso_J3 e c, hC]
    norm_num
  obtain ⟨I, hIC, -, ⟨eI⟩, -, -, hD3, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Plain e hc3 hc1 h5
  have hDcomm' : ∀ d ∈ Subgroup.zpowers c, ∀ y ∈ I, d * y = y * d :=
    fun d hd y hy => hDcomm d hd y (hIC hy)
  set H : Subgroup Q := Subgroup.centralizer ({c} : Set Q) with hHdef
  have hconjI : ∀ g ∈ H, ∀ i ∈ I, g * i * g⁻¹ ∈ I := by
    intro g hg i hi
    have hg' : g ∈ Subgroup.zpowers c ⊔ I := by
      rw [hCeq]
      exact hg
    obtain ⟨d, hd, j, hj, rfl⟩ :=
      (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.mem_sup_of_commute hDcomm').1 hg'
    have hk : j * i * j⁻¹ ∈ I := I.mul_mem (I.mul_mem hj hi) (I.inv_mem hj)
    have hdk : d * (j * i * j⁻¹) = j * i * j⁻¹ * d := hDcomm d hd _ (hIC hk)
    have e1 : d * j * i * (d * j)⁻¹ = j * i * j⁻¹ := by
      calc d * j * i * (d * j)⁻¹ = d * (j * i * j⁻¹) * d⁻¹ := by group
        _ = j * i * j⁻¹ * d * d⁻¹ := by rw [hdk]
        _ = j * i * j⁻¹ := by group
    rw [e1]
    exact hk
  haveI hN'normal : (I.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hconjI (g : Q) g.2 (n : Q) hn
    simpa using this⟩
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have eN : ↥(I.subgroupOf H) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.subgroupOfEquivOfLe hIC).trans eI
  have hsimple : IsSimpleGroup ↥(I.subgroupOf H) := eN.isSimpleGroup
  have hcard : Nat.card ↥(I.subgroupOf H) = 360 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hna : ¬ ∀ x y : ↥(I.subgroupOf H), x * y = y * x := by
    intro hcomm
    letI : CommGroup ↥(I.subgroupOf H) :=
      { (inferInstance : Group ↥(I.subgroupOf H)) with mul_comm := hcomm }
    have hp : (Nat.card ↥(I.subgroupOf H)).Prime := CommGroup.is_simple_iff_prime_card.1 hsimple
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  have hO := oTwoP_le_centralizer_of_simple_normal (I.subgroupOf H) hsimple hna
  have hle : (Sec4.oTwoP 3 ↥H).map H.subtype ≤ Subgroup.zpowers c := by
    rintro _ ⟨g, hg, rfl⟩
    show (g : Q) ∈ Subgroup.zpowers c
    have hgc := hO hg
    have hg' : (g : Q) ∈ Subgroup.zpowers c ⊔ I := by
      rw [hCeq]
      exact g.2
    obtain ⟨d, hd, j, hj, hdj⟩ :=
      (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.mem_sup_of_commute hDcomm').1 hg'
    have hcomm : ∀ i ∈ I, (g : Q) * i = i * (g : Q) := by
      intro i hi
      have hmem : (⟨i, hIC hi⟩ : ↥H) ∈ (I.subgroupOf H : Set ↥H) :=
        Subgroup.mem_subgroupOf.2 hi
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hgc _ hmem)
      simpa using h1.symm
    have hji : ∀ i ∈ I, j * i = i * j := by
      intro i hi
      have h1 := hcomm i hi
      rw [← hdj] at h1
      have h2 : d * i = i * d := hDcomm' d hd i hi
      have h3 : d * (j * i) = d * (i * j) := by
        calc d * (j * i) = d * j * i := by group
          _ = i * (d * j) := h1
          _ = i * d * j := by group
          _ = d * i * j := by rw [h2]
          _ = d * (i * j) := by group
      exact mul_left_cancel h3
    have hjc : (⟨j, hj⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro i
      apply Subtype.ext
      exact (hji i.1 i.2).symm
    rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.center_eq_bot_of_equiv_alt6 I eI,
      Subgroup.mem_bot] at hjc
    have hj1 : j = 1 := congrArg Subtype.val hjc
    rw [hj1, mul_one] at hdj
    rw [← hdj]
    exact hd
  calc Nat.card (Sec4.oTwoP 3 ↥H)
      = Nat.card ↥((Sec4.oTwoP 3 ↥H).map H.subtype) :=
        (Subgroup.card_map_of_injective (f := H.subtype) (Subgroup.subtype_injective H)).symm
    _ ≤ Nat.card ↥(Subgroup.zpowers c) := Subgroup.card_le_of_le hle
    _ = 3 := hD3

theorem noInnerData_J3 : NoInnerData (Sec4.Spor .J3) := by
  intro A B c hd
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let e : Sec4.Spor .J3 ≃* NativeSporadic.J3 := b.symm
  haveI : Finite (Sec4.Spor .J3) := Finite.of_equiv _ b.toEquiv
  have hAe : IsElementaryAbelian 3 A :=
    Sec4.Item434Spor.isElementaryAbelian_of_isElemAbelian hd.isElemAbelian
  obtain ⟨B₁, hB₁A, hB₁9, -, hB₁3A⟩ := j3_e27_class_split e hAe hd.card_A
  have hBB₁ : B = B₁ := j3_invariant_plane_eq e hAe hd.card_A hB₁A hB₁9 hB₁3A hd.le_B hd.card_B
    hd.normalizer_le
  have hcA : c ∈ A := by rw [hd.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcB₁ : c ∉ B₁ := hBB₁ ▸ hd.not_mem
  have hc3 : c ^ 3 = 1 := hd.isElemAbelian.2 c hcA
  have hc1 : c ≠ 1 := fun h => hd.not_mem (h ▸ B.one_mem)
  have hsmall := j3_oTwoThree_small e hc3 hc1 (hB₁3A c hcA hcB₁)
  have h1 := Subgroup.card_le_of_le hd.omega
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
  have := hd.card_B
  omega

end J3

end CFSG.RankThree.PartTwo.Sec18.Item185Proof

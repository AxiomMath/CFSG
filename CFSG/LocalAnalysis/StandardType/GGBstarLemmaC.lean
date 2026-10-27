module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDichotomy
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGInnerDiagBound2L (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eb Eh : Subgroup (MulAut R), (Eb : Set (MulAut R)) ⊆ I → IsElemAbelian p Eb →
    p ^ r ≤ Nat.card Eb → p ^ 3 ≤ Nat.card Eb → Eb ≤ Eh → IsElemAbelian p Eh →
    Nat.card Eh ≤ p * Nat.card Eb → ¬ (Eh : Set (MulAut R)) ⊆ I →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ Eb, ∀ u ∈ U, φ u ∈ U) →
    ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ Eh, ∀ u ∈ U, φ u ∈ U

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.innLocal_of_ne {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hne : B ≠ Bs) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hC.1
  rcases ggInnLocal_or_delta hβ.1 hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hU | hδ
  · exact hU
  · exact absurd (bstar_eq_of_moved hC hnc hδ).symm hne

theorem GGConfig.beta_twoLocal_of_ne {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hne : B ≠ Bs) :
    ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ φ ∈ (ggBeta L θ hBN).range, ∀ v ∈ V, φ v ∈ V := by
  obtain ⟨U, hUL, hU1, hU2, hBU⟩ := hC.innLocal_of_ne hnc hL θ hBN h3 hOD hne
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hC.1.2.2.2.2.2.2.1.2.2.2.1.1
  set UL : Subgroup L := U.subgroupOf L with hUL'
  have hUL2 : IsPGroup 2 UL := hU2.comap_subtype
  refine ⟨UL.map (ggQuotHom θ), fun h => hU1 ?_, hUL2.map _, ?_⟩
  ·
    have hZ : UL ≤ Subgroup.center L := by
      rw [← ker_ggQuotHom θ, ← Subgroup.map_eq_bot_iff]
      exact h
    refine hC.twoSub_centralizer_eq_bot hnc hne (fun u hu => ?_) (fun u hu => hLx (hUL hu)) hU2
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hz := Subgroup.mem_center_iff.mp (hZ (show (⟨u, hUL hu⟩ : L) ∈ UL from hu)) ⟨l, hl⟩
    exact (congrArg Subtype.val hz)
  · rintro _ ⟨b, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨ggGamma L hBN b l, ?_, (ggBeta_ggQuotHom L hBN θ b l).symm⟩
    show ((ggGamma L hBN b l : L) : G) ∈ U
    rw [ggGamma_coe]
    have hb := hBU b.2
    exact (Subgroup.mem_normalizer_iff.mp hb (l : G)).mp hl

theorem bstar_innerDiag_of_bound2L {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hbound : GGInnerDiagBound2L p r R I)
    (hOD : GGOutdiagOdd p R I) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  have hBsN := hC.bstar_le_normalizer hnc
  obtain ⟨hcard, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  have hEhI : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I := by
    by_contra hnot
    have hne : B ≠ Bs := by
      rintro rfl
      apply hnot
      rintro _ ⟨b, rfl⟩
      exact ggBeta_mem L θ hBsN h3 b
    have hV := hC.beta_twoLocal_of_ne hnc hL θ hBN h3 hOD hne
    obtain ⟨hT, hBs, -⟩ := hC
    obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
    have hp : p.Prime := hβ.1
    have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨b, rfl⟩
      exact ggBeta_mem L θ hBN h3 b
    obtain ⟨U, hU, hU2, hEU⟩ := hbound _ _ hEbI (isElemAbelian_range_ggBeta θ hS.1.1 hBN)
      (pow_le_card_range_ggBeta hp hS hL θ hBN hlift) h3' (range_ggBeta_le θ hBs.1 hBN hBsN)
      (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) hcard hnot hV
    obtain ⟨T, hTne, hT2, hBsT⟩ := exists_twoSubgroup_of_normalizes θ hBsN hU hU2
      (fun e he u hu => hEU _ ⟨⟨e, he⟩, rfl⟩ u hu)
    have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hBsT hBs.2.1
    rw [← hS.1.2.1] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hBs.1 hc)
  refine ⟨hBsN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv L θ (hBsN (Bs.inv_mem hb))⟩⟩
  exact hEhI ⟨⟨b⁻¹, Bs.inv_mem hb⟩, rfl⟩

theorem ggBstarInnerDiagLInputOn_of_labels2L {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound2L p r R I ∧ GGOutdiagOdd p R I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hnc := ha₀ G p B x L hC.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, hBN, h3⟩, r, hlift, hbound, hOD⟩
  exact ⟨hs, hna, θ, hSl, hsplit, bstar_innerDiag_of_bound2L hC hnc hL θ hBN h3 hlift hbound hOD⟩

end CFSG.StandardType

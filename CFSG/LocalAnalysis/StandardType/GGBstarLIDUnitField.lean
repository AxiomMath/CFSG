module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldR
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_two_subgroup_of_center {L E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) {U : Subgroup L} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hUZ : U ≤ Subgroup.center L) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  set Z₂ : Subgroup L := TableBU.twoPartOf (Subgroup.center L) le_rfl (Nat.card L) with hZ₂
  refine ⟨Z₂.map L.subtype, ?_, (TableBU.isPGroup_twoPartOf _ _ _).map _, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := TableBU.mem_twoPartOf_of_pow le_rfl (hUZ hu) hk'
    rw [← hZ₂, hbot] at h1
    exact h1
  · apply le_normalizer_of_map_conj_le
    intro e he
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨e, hEN he⟩ z, ⟨?_, ?_⟩, ?_⟩
    · exact BstarDesc.mulAut_mem_center _ hz.1
    · rw [← map_pow, hz.2, map_one]
    · rfl

theorem bstar_innerDiag_of_fieldInn {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hfield : GGFieldInnR p r R I)
    (hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  have hBsN := hC.bstar_le_normalizer hnc
  obtain ⟨hcard, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN h3 b
  have hEhI : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I := by
    by_contra hnot
    obtain ⟨f, ⟨b₁, rfl⟩, hfI⟩ := Set.not_subset.mp hnot
    have hb₁ : (b₁ : G) ∉ B := fun hb => hfI (ggBeta_mem L θ hBN h3 ⟨b₁, hb⟩)
    have hBlt : B < Bs := lt_of_le_of_ne hBs.1 fun he => hb₁ (he ▸ b₁.2)
    obtain ⟨U, hUL, hU1, hU2, hBU⟩ := hinn
    have hU'1 : U.subgroupOf L ≠ ⊥ := by
      intro hbot
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have h1 : (⟨u, hUL hu⟩ : L) ∈ U.subgroupOf L := hu
      rw [hbot, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    have hU'2 : IsPGroup 2 (U.subgroupOf L) :=
      hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm
    by_cases hUZ : U.subgroupOf L ≤ Subgroup.center L
    · obtain ⟨T, hT1, hT2, hBsT⟩ := exists_two_subgroup_of_center hBsN hU'1 hU'2 hUZ
      have hc := card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hBsT hBs.2.1
      rw [← hS.1.2.1] at hc
      exact hBlt.ne (Subgroup.eq_of_le_of_card_ge hBs.1 hc)
    · set V : Subgroup R := (U.subgroupOf L).map (ggQuotHom θ) with hV
      have hV1 : V ≠ ⊥ := by
        intro hbot
        apply hUZ
        intro u hu
        rw [← ker_ggQuotHom θ, MonoidHom.mem_ker]
        have h1 : ggQuotHom θ u ∈ V := ⟨u, hu, rfl⟩
        rw [hbot] at h1
        exact Subgroup.mem_bot.mp h1
      have hV2 : IsPGroup 2 V := hU'2.map _
      have hEbV : ∀ φ ∈ (ggBeta L θ hBN).range, ∀ v ∈ V, φ v ∈ V := by
        rintro _ ⟨b, rfl⟩ _ ⟨u, hu, rfl⟩
        rw [ggBeta_ggQuotHom L hBN θ b u]
        refine ⟨ggGamma L hBN b u, ?_, rfl⟩
        show ((ggGamma L hBN b u : L) : G) ∈ U
        rw [ggGamma_coe]
        exact (Subgroup.mem_normalizer_iff.mp (hBU b.2) u).mp hu
      obtain ⟨E', hlt, hle, V', hV'1, hV'2, hE'V⟩ := hfield _ _ hEbI
        (isElemAbelian_range_ggBeta θ hS.1.1 hBN)
        (pow_le_card_range_ggBeta hp hS hL θ hBN hlift) h3' ⟨V, hV1, hV2, hEbV⟩
        (range_ggBeta_le θ hBs.1 hBN hBsN) (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN)
        ⟨_, ⟨b₁, rfl⟩, hfI⟩
      set E₂ : Subgroup G := (E'.comap (ggBeta L θ hBsN)).map Bs.subtype with hE₂
      have hE₂E : E₂ ≤ Bs := Subgroup.map_subtype_le _
      have hBE₂ : B ≤ E₂ := by
        intro b hb
        exact ⟨⟨b, hBs.1 hb⟩, hlt.le ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      have hBne : B ≠ E₂ := by
        intro heq
        obtain ⟨φ, hφE', hφB⟩ := IsConcreteLE.exists_of_lt hlt
        obtain ⟨e₀, rfl⟩ := hle hφE'
        apply hφB
        have he₂ : (e₀ : G) ∈ E₂ := ⟨e₀, hφE', rfl⟩
        rw [← heq] at he₂
        exact ⟨⟨e₀, he₂⟩, rfl⟩
      have hE₂ab : IsElemAbelian p E₂ := isElemAbelian_mono hBs.2.1 hE₂E
      have hE₂N : E₂ ≤ Subgroup.normalizer (L : Set G) := hE₂E.trans hBsN
      obtain ⟨T, hT1, hT2, hE₂T⟩ := exists_twoSubgroup_of_normalizes θ hE₂N hV'1 hV'2
        (fun e he u hu => by
          obtain ⟨e', he', rfl⟩ := he
          exact hE'V _ he' u hu)
      have hc := card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hE₂T hE₂ab
      rw [← hS.1.2.1] at hc
      exact hBne (Subgroup.eq_of_le_of_card_ge hBE₂ hc)
  refine ⟨hBsN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv L θ (hBsN (Bs.inv_mem hb))⟩⟩
  exact hEhI ⟨⟨b⁻¹, Bs.inv_mem hb⟩, rfl⟩

theorem ggInnerDiagOnLab_bstar_of_fieldInn {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLab S p B L)
    (hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)) : GGInnerDiagOnLab S p Bs L := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, hBN, h3⟩, r, hr2, hlift, hfield⟩
  have hnc := UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift
  exact ⟨hs, hna, θ, hSl, hsplit,
    bstar_innerDiag_of_fieldInn hC hnc hL θ hBN h3 hlift hfield hinn⟩

end Config

section Unitary

theorem largeEvenLabelAll_unitDvdField_fieldInn {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab h.1
  obtain ⟨⟨⟨ht, -, -, -⟩, -⟩, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
    omega
  refine ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hr2,
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq, ?_⟩⟩
  simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  exact TableBUD.ggFieldInnR_unitary_dvd hK hn hd5 hp hpq h63

theorem largeEvenLabelAll_unitDvdField_torus_outdiag {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab h.1
  obtain ⟨⟨⟨ht, -, -, -⟩, -⟩, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
    omega
  exact ⟨K, i1, i2, hK, ⟨hQ', ⟨ggUnitaryTorusRank p (l + 1), hr2,
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq⟩,
    InndiagSU.ggOutdiagOdd_unitary hK hn (by omega) (fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])) p⟩⟩

end Unitary

end CFSG.StandardType

end

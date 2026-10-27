module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Cfg
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Mod

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LineU

@[expose] def GGUnitDvd63CoprimeNLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvd63Label p lab ∧ ¬ p ∣ lab.n

@[expose] def GGUnitDvd63FieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvd63Label p lab ∧ p ∣ lab.n

theorem ggUnitDvd63Label_iff (p : ℕ) (lab : LargeEvenLabel) :
    GGUnitDvd63Label p lab ↔ GGUnitDvd63CoprimeNLabel p lab ∨ GGUnitDvd63FieldLabel p lab := by
  unfold GGUnitDvd63CoprimeNLabel GGUnitDvd63FieldLabel
  by_cases h : p ∣ lab.n
  · simp [h]
  · simp [h]

section PerLabel

theorem largeEvenLabelAll_unitDvd63_lift {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (5 + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank 3 (5 + 1), by norm_num [ggUnitaryTorusRank],
    ggTorusLift_unitary hK hn (by omega) hdq Nat.prime_three hpn⟩⟩

theorem largeEvenLabelAll_unitDvd63_nbr {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => U63TB.GGTorusNbrSCrK p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', U63TB.ggTorusNbrSCrK_unitary63 hK hn hpn⟩⟩

theorem largeEvenLabelAll_unitDvd63_module {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTableBModuleSCr p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', U63TB.ggTableBModuleSCr_unitary63 hK hn hpn⟩⟩

end PerLabel

section LID

theorem ggBstarInnerDiagLInputOn_unitDvd63_of_coprimeN {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvd63CoprimeNLabel p lab) : GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab)
    (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
    (fun lab hlab hs => largeEvenLabelAll_unitDvd63_lift hlab (hS p lab hs).1)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, -, r, hr2, hlift⟩ := largeEvenRawDatum_exists hraw
  exact CorFourTwoOpen.ggInnerDiagOnLab_bstar_of_pow
    (fun p lab hp hlab hs => largeEvenLabelAll_pow_mem_vac hp hlab
      ⟨TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 (hS p lab hs).1.1.2.2.1,
        Or.inr (Or.inr ⟨Or.inl (hS p lab hs).1.1.1, (hS p lab hs).2⟩)⟩)
    hC (UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift) hM

theorem ggBstarInnerDiagLInputOn_unitDvd63_coprimeN :
    GGBstarInnerDiagLInputOn GGUnitDvd63CoprimeNLabel :=
  ggBstarInnerDiagLInputOn_unitDvd63_of_coprimeN fun _ _ h => h

theorem ggBstarInnerDiagLInputOn_unitDvd63 (hF : GGBstarInnerDiagLInputOn GGUnitDvd63FieldLabel) :
    GGBstarInnerDiagLInputOn GGUnitDvd63Label := by
  have h' := ggBstarInnerDiagLInputOn_unitDvd63_coprimeN.or hF
  have e : (fun p lab => GGUnitDvd63CoprimeNLabel p lab ∨ GGUnitDvd63FieldLabel p lab) =
      GGUnitDvd63Label :=
    funext fun p => funext fun lab => propext (ggUnitDvd63Label_iff p lab).symm
  rwa [e] at h'

end LID

section Results

theorem card_range_ggGamma_unitDvd63 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLab GGUnitDvd63Label p Bs L) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    p ^ 4 ≤ Nat.card (ggGamma L hBsN).range ∧ p ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by
  have h5 := Line63.H5.ggUnitDvd63BstarRankInput_holds G p B Bs x L D J hcfg hM
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hBsN
  have h4' : p ^ 4 ≤ Nat.card (ggGamma L hBsN).range := by
    rw [← hmul, pow_succ] at h5
    exact Nat.le_of_mul_le_mul_right h5 hp.pos
  exact ⟨h4', (Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4'⟩

theorem ggTableBCxInputOn_unitDvd63_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvd63Label p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBCxInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hMs := hD G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (P' := fun R _ I _ => (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ U63TB.GGTorusNbrSCrK p 4 R I)
    (fun lab hlab hs => largeEvenLabelAll_and (largeEvenLabelAll_unitDvd63_lift hlab (hS p lab hs))
      (largeEvenLabelAll_unitDvd63_nbr hlab (hS p lab hs)))
    (fun _ _ _ _ _ _ hP => hP.1) hMs
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, ⟨r, hr2, hlift⟩, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨h4', h3'⟩ := card_range_ggGamma_unitDvd63 hcfg (hMs.mono hS) hBsN
  exact U63TB.ggTableBCx_of_card hcfg (UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift) hL θ
    hBsN (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4' h3' hT hYx hYN hYn hYp

theorem ggTableBModuleInputOn_unitDvd63_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvd63Label p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBModuleInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hMs := hD G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (P' := fun R _ I _ => GGTableBModuleSCr p 4 R I)
    (fun lab hlab hs => largeEvenLabelAll_unitDvd63_module hlab (hS p lab hs))
    (fun _ _ _ _ _ _ hP => hP.1) hMs
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨h4', h3'⟩ := card_range_ggGamma_unitDvd63 hcfg (hMs.mono hS) hBsN
  exact U63TB.ggTableBModule_of_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4' h3' hT

theorem ggTableBCxInputOn_unitDvd63 (hD : GGBstarInnerDiagLInputOn GGUnitDvd63Label) :
    GGTableBCxInputOn GGUnitDvd63Label :=
  ggTableBCxInputOn_unitDvd63_of_lid (fun _ _ h => h) hD

theorem ggTableBModuleInputOn_unitDvd63 (hD : GGBstarInnerDiagLInputOn GGUnitDvd63Label) :
    GGTableBModuleInputOn GGUnitDvd63Label :=
  ggTableBModuleInputOn_unitDvd63_of_lid (fun _ _ h => h) hD

theorem ggTableBCxInputOn_unitDvd63CoprimeN_holds :
    GGTableBCxInputOn GGUnitDvd63CoprimeNLabel :=
  ggTableBCxInputOn_unitDvd63_of_lid (fun _ _ h => h.1)
    ggBstarInnerDiagLInputOn_unitDvd63_coprimeN

theorem ggTableBModuleInputOn_unitDvd63CoprimeN_holds :
    GGTableBModuleInputOn GGUnitDvd63CoprimeNLabel :=
  ggTableBModuleInputOn_unitDvd63_of_lid (fun _ _ h => h.1)
    ggBstarInnerDiagLInputOn_unitDvd63_coprimeN

theorem ggTableBCxInputOn_of_not_unitDvd63CoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_unitDvd63CoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvd63CoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_unitDvd63CoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_unitDvd63CoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvd63CoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBCxInputOn_of_not_unitDvd63 (hF : GGBstarInnerDiagLInputOn GGUnitDvd63FieldLabel)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_unitDvd63 (ggBstarInnerDiagLInputOn_unitDvd63 hF)).or h).mono
    fun p lab hlab => by
      by_cases hl : GGUnitDvd63Label p lab
      · exact Or.inl hl
      · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_unitDvd63
    (hF : GGBstarInnerDiagLInputOn GGUnitDvd63FieldLabel) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_unitDvd63 (ggBstarInnerDiagLInputOn_unitDvd63 hF)).or h).mono
    fun p lab hlab => by
      by_cases hl : GGUnitDvd63Label p lab
      · exact Or.inl hl
      · exact Or.inr ⟨hlab, hl⟩

end Results

end CFSG.StandardType

end

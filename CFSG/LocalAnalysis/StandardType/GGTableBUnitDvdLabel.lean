module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdMod
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUDvd
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLMod
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LineU

@[expose] def GGUnitDvdCoprimeNLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvdLabelNo63 p lab ∧ ¬ p ∣ lab.n

@[expose] def GGUnitDvdFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvdLabelNo63 p lab ∧ p ∣ lab.n

theorem ggUnitDvdLabelNo63_iff (p : ℕ) (lab : LargeEvenLabel) :
    GGUnitDvdLabelNo63 p lab ↔ GGUnitDvdCoprimeNLabel p lab ∨ GGUnitDvdFieldLabel p lab := by
  unfold GGUnitDvdCoprimeNLabel GGUnitDvdFieldLabel
  by_cases h : p ∣ lab.n
  · simp [h]
  · simp [h]

section PerLabel

theorem unitDvdLabel_arith {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdLabelNo63 p lab) :
    1 ≤ lab.n ∧ 5 ≤ lab.rank + 1 ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1 ∧
      ¬ (lab.rank + 1 = 6 ∧ p = 3) ∧ (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, hl, hpn, hpd⟩, hno⟩ := h
  dsimp only at ht hl hpn hpd hno ⊢
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hd5 : 5 ≤ l + 1 := by
    by_contra hlt
    have hl3 : l = 3 := by omega
    subst hl3
    have h4 : p ∣ 2 ^ 2 := by simpa using hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
  refine ⟨hn, hd5, hpd, hpn, fun ⟨h6, h3⟩ => hno ⟨by omega, h3⟩, fun heq => ?_⟩
  have := congrArg Prod.fst heq
  simp only at this
  omega

theorem largeEvenLabelAll_unitDvd_torusNbrSCr {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGTorusNbrSCr p r R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab h
  obtain ⟨⟨ht, -, -, -⟩, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
    omega
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hr2,
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq,
    UnitTB.ggTorusNbrSCr_unitary hK hn hd5 hp hpq hpd h63⟩⟩

theorem largeEvenLabelAll_unitDvd_module {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTableBModuleSCr p r R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab h
  obtain ⟨⟨ht, -, -, -⟩, -⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1),
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq,
    UnitTB.ggTableBModuleSCr_unitary hK hn hd5 hp hpq hpd h63⟩⟩

end PerLabel

namespace UnitTB

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_of_torusLift {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) {L : Subgroup G}
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hlift : GGTorusLift p r R) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker⟩ := hlift L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  have hEG : IsElemAbelian p (E.map L.subtype) := isElemAbelian_map hE L.subtype
  have hcard : Nat.card (E.map L.subtype) = p ^ r := by
    rw [← Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv, hEcard]
  exact ⟨E.map L.subtype, Subgroup.map_subtype_le E, isPGroup_of_isElemAbelian hEG,
    not_isCyclic_of_card hp.one_lt hEG.2 (by rw [hcard]; exact Nat.pow_le_pow_right hp.pos hr)⟩

theorem ggTableBCxInputOn_of_labelsSCr_two {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGTorusNbrSCr p r R I) :
    GGTableBCxInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1)
    (hD G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hr2, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact ggTableBCx_of_ggTorusNbrSCr hcfg (exists_noncyclic_of_torusLift hp hr2 hL θ hlift) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift hT hYx hYN hYn hYp

end Config

end UnitTB

section LID

theorem ggBstarInnerDiagLInputOn_unitDvd_coprimeN :
    GGBstarInnerDiagLInputOn GGUnitDvdCoprimeNLabel := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGUnitDvdCoprimeNLabel p lab)
    (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
    (fun lab hlab hs => by
      intro Q hQ
      obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab hs.1
      obtain ⟨⟨⟨ht, -, -, -⟩, -⟩, -⟩ := hs
      obtain ⟨t, l, n⟩ := lab
      dsimp only at ht hn hd5 hpd hpq h63 hdq
      subst ht
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
      have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
        simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
        omega
      exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hr2,
        ggTorusLift_unitary hK hn (by omega) hdq hp hpq⟩⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, -, r, hr2, hlift⟩ := largeEvenRawDatum_exists hraw
  exact CorFourTwoOpen.ggInnerDiagOnLab_bstar_of_pow
    (fun p lab hp hlab hs => largeEvenLabelAll_pow_mem_vac hp hlab
      ⟨TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 hs.1.1.2.2.1,
        Or.inr (Or.inr ⟨Or.inl hs.1.1.1, hs.2⟩)⟩)
    hC (UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift) hM

theorem ggBstarInnerDiagLInputOn_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel) :
    GGBstarInnerDiagLInputOn GGUnitDvdLabelNo63 := by
  have h' := ggBstarInnerDiagLInputOn_unitDvd_coprimeN.or hF
  have e : (fun p lab => GGUnitDvdCoprimeNLabel p lab ∨ GGUnitDvdFieldLabel p lab) =
      GGUnitDvdLabelNo63 :=
    funext fun p => funext fun lab => propext (ggUnitDvdLabelNo63_iff p lab).symm
  rwa [e] at h'

end LID

section Results

theorem ggTableBCxInputOn_unitDvd_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvdLabelNo63 p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBCxInputOn S :=
  UnitTB.ggTableBCxInputOn_of_labelsSCr_two hD
    fun _ _ hp hlab h => largeEvenLabelAll_unitDvd_torusNbrSCr hp hlab (hS _ _ h)

theorem ggTableBModuleInputOn_unitDvd_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvdLabelNo63 p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBModuleInputOn S :=
  ggTableBModuleInputOn_of_labelsSCr hD
    fun _ _ hp hlab h => largeEvenLabelAll_unitDvd_module hp hlab (hS _ _ h)

theorem ggTableBCxInputOn_unitDvdCoprimeN_holds : GGTableBCxInputOn GGUnitDvdCoprimeNLabel :=
  ggTableBCxInputOn_unitDvd_of_lid (fun _ _ h => h.1) ggBstarInnerDiagLInputOn_unitDvd_coprimeN

theorem ggTableBModuleInputOn_unitDvdCoprimeN_holds :
    GGTableBModuleInputOn GGUnitDvdCoprimeNLabel :=
  ggTableBModuleInputOn_unitDvd_of_lid (fun _ _ h => h.1)
    ggBstarInnerDiagLInputOn_unitDvd_coprimeN

theorem ggTableBCxInputOn_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel) :
    GGTableBCxInputOn GGUnitDvdLabelNo63 :=
  ggTableBCxInputOn_unitDvd_of_lid (fun _ _ h => h) (ggBstarInnerDiagLInputOn_unitDvdNo63 hF)

theorem ggTableBModuleInputOn_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel) :
    GGTableBModuleInputOn GGUnitDvdLabelNo63 :=
  ggTableBModuleInputOn_unitDvd_of_lid (fun _ _ h => h) (ggBstarInnerDiagLInputOn_unitDvdNo63 hF)

theorem ggTableBCxInputOn_of_not_unitDvdCoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_unitDvdCoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdCoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_unitDvdCoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_unitDvdCoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdCoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBCxInputOn_of_not_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_unitDvdNo63 hF).or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdLabelNo63 p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_unitDvdNo63 (hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_unitDvdNo63 hF).or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvdLabelNo63 p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

end Results

end CFSG.StandardType

end

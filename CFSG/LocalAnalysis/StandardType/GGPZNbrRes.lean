module

public import CFSG.LocalAnalysis.StandardType.GGPZNbrDatum
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomy
public import CFSG.LocalAnalysis.StandardType.GGPZNotSevenA8
public import CFSG.LocalAnalysis.StandardType.GGPZNotSevenE6
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZNbrResDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y →
      GGInnerDiagOnLabel GGTBWeylRowRes p Bs Y → GGResXDatumSurj p Bs Y

theorem ggPZ_nbr_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {z : G} {Y : Subgroup G}
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J z Y) (h : GGInnerDiagOnLabel GGTBTorCov p Bs Y) :
    ∃ (m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N))
      (hN : Bs ≤ Subgroup.normalizer (Y : Set G)),
      Odd m ∧ p ∣ m ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        GGTorusTorData m N C M ↥Y (ggGamma Y hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨_lab, _r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hBsI, hlift, hT⟩ :=
    l05nPlQ_marking hW hLift hp2 h
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift
  have hTor := hT ↥Y (ggQuotHom θ) (ggGamma Y hN).range hTB
  obtain ⟨hom, hpm, hM, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩

theorem ggPZ_resXDatum_of_tbTor_nbr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {z : G} {Y : Subgroup G}
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hcfg : GGConfig p B Bs x L D J)
    (hnb : GGNbr p B x D J z Y) (h : GGInnerDiagOnLabel GGTBTorCov p Bs Y) :
    GGResXDatum p Bs Y := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩ :=
    ggPZ_nbr_core (ggTBTorWRows_of_all hT) hLift hcfg hnb h
  exact ggResXDatum_of_torData hp2 hom hpm hM hMC hBs hS hN hTor

private theorem ggPZNbr_three_dvd_of_seven_dvd {n : ℕ} (h : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ^ n % 7 = 1 := by omega
  have h3 : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h4 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 3 <;> simp at h3 <;> omega

private theorem ggPZNbr_not_seven_dvd_two_pow_add_one (n : ℕ) : ¬ 7 ∣ 2 ^ n + 1 := by
  intro h
  have h3 : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h4 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 3 <;> simp at h3 <;> omega

private theorem ggPZNbr_labJ_seven {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z) (hp7 : p = 7) :
    ∃ a : ℕ, 1 ≤ a ∧ GGHasLabel ⟨.A, 4, 3 * a⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨-, -, hΛJ, -, hJlab, -, hrow, -⟩ := h
  have hn1 : 1 ≤ labJ.n := hΛJ.1
  obtain ⟨hrowTN, hxr⟩ := hrow
  subst hp7
  rcases hrowTN with ⟨hJt, hpq, hpl, hXe⟩ | ⟨hJt, hpq, hpl, hXe⟩ | ⟨hJe, hp3, hpq, hXe⟩ |
      ⟨hJe, hp3, hpq, hXe⟩
  · rw [hXe] at hxr
    have hr4 : labJ.rank = 4 := by
      obtain ⟨k, hk⟩ := hpl
      simp only at hxr
      omega
    obtain ⟨a, ha⟩ := ggPZNbr_three_dvd_of_seven_dvd hpq
    refine ⟨a, by omega, ?_⟩
    cases labJ
    simp only at hJt hr4 ha hJlab ⊢
    subst hJt
    subst hr4
    subst ha
    exact hJlab
  · exact absurd hpq (ggPZNbr_not_seven_dvd_two_pow_add_one _)
  · omega
  · omega

private theorem ggPZNbr_not_rowSeven
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs} {Y : Subgroup G}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z)
    (hY : LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y) (hJY : J ≤ Y)
    {labK : LargeEvenLabel} (hlabK : LargeEvenInLambda2 labK)
    (hhasK : GGHasLabel labK (↥Y ⧸ Subgroup.center ↥Y))
    (hHalf : LargeEvenHalfSplit p labK True) (hrow : ggRowSeven p labK labK) : False := by
  obtain ⟨hp7, hlab5⟩ := hrow
  obtain ⟨a, ha, hJ⟩ := ggPZNbr_labJ_seven h hp7
  have hYperf : commutator ↥Y = ⊤ := by
    have hperf : Group.IsPerfect ↥(Y.subgroupOf (Subgroup.centralizer ({(z : G)} : Set G))) :=
      CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect
        ((ggLargeEvenPComponent_iff p _ _).1 hY).2
    let e := Subgroup.subgroupOfEquivOfLe hY.1
    have h1 : (commutator ↥(Y.subgroupOf (Subgroup.centralizer ({(z : G)} : Set G)))).map
        e.toMonoidHom = commutator ↥Y := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h1, hperf.commutator_eq_top, Subgroup.map_top_of_surjective _ e.surjective]
  have hd := largeEvenHalfSplit_dvd hlabK hHalf
  subst hp7
  rcases hlab5 with rfl | rfl | rfl | rfl | rfl
  · exact ggPZ_not_halfSplit_seven_A8 ha hYperf hJY hJ hhasK
  · rcases hd with hd | ⟨-, hd⟩
    · norm_num at hd
    · simp at hd
  · exact ggPZ_not_halfSplit_seven_E6 ha hYperf hJY hJ hhasK
  · rcases hd with hd | ⟨-, hd⟩
    · norm_num at hd
    · simp at hd
  · rcases hd with hd | ⟨-, hd⟩
    · norm_num at hd
    · simp at hd

theorem ggPZNbr_cov_or_res
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs} {Y : Subgroup G}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z)
    (hY : LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y) (hJY : J ≤ Y)
    (hnb : GGNbr p B x D J (z : G) Y) :
    GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs Y := by
  have hcfg : GGConfig p B Bs x L D J := h.1.1
  have hInnY : GGInnerDiagOn Bs Y := h.1.2.2.1.2 (z : G) Y hnb
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hcfg hnb hInnY
  obtain ⟨labK, hlabK, hhasK, R, _, I, F, θ, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hmarkK := ggInnerDiagOn_relabel hRig hInnY hlabK hhasK
  have hHalfK : LargeEvenHalfSplit p labK True := largeEvenHalfSplit_true hHSlab
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hS1 : GGTBTorCov p labK ∨ GGTBWeylRowRes p labK := by
    by_contra hnot
    have hnotTor : ¬ GGTBTorCov p labK := fun h' => hnot (Or.inl h')
    have hnotRes : ¬ GGTBWeylRowRes p labK := fun h' => hnot (Or.inr h')
    have hcases : ggRowSeven p labK labK ∨ labK.tag = .twF4 ∨ labK.tag = .twF4der := by
      by_contra h'
      push Not at h'
      exact hnotRes ⟨hnotTor, hHalfK, h'.1, h'.2.1, h'.2.2⟩
    rcases hcases with hrow | htag | htag
    · exact ggPZNbr_not_rowSeven h hY hJY hlabK hhasK hHalfK hrow
    · have hdvd : p ∣ 2 ^ labK.n - 1 ∨ p ∣ 2 ^ labK.n + 1 := by
        rcases hHSlab with h1 | h1 | h1 | h1 | h1 | h1
        · exact Or.inr (TableBExcSmallRest.dvd_of_largeEvenSplit_twF4 htag hlabK h1)
        · exfalso; rcases h1.1 with h2 | h2 | h2 | h2 | h2 <;> simp [htag] at h2
        · exfalso; rcases h1.1 with ⟨h2, -⟩ | h2 <;> simp [htag] at h2
        · exfalso; exact (by simp [htag] at h1)
        · exfalso; exact (by simp [htag] at h1)
        · exfalso; exact (by simp [htag] at h1)
      have hrank := ggInnerDiagOnLabel_nbr_pRank_ge_three (S := fun _ lab' => lab' = labK)
        hcfg hnb hmarkK
      have hbad : LargeEvenMarking ↥Y (fun lab' R _ I _ _ =>
          (lab'.tag = .twF4 ∧ (p ∣ 2 ^ lab'.n - 1 ∨ p ∣ 2 ^ lab'.n + 1)) ∧
            ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
              p ^ 3 ≤ Nat.card E) := by
        refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
        rw [hP'.1]
        exact ⟨⟨htag, hdvd⟩, hP'.2⟩
      exact absurd hbad (ggInndiag_pRank_le_two_twF4 (X := ↥Y) hp hp2)
    · have hrank := ggInnerDiagOnLabel_nbr_pRank_ge_three (S := fun _ lab' => lab' = labK)
        hcfg hnb hmarkK
      have hbad : LargeEvenMarking ↥Y (fun lab' R _ I _ _ =>
          lab'.tag = .twF4der ∧
            ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
              p ^ 3 ≤ Nat.card E) := by
        refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hrank
        rw [hP'.1]
        exact ⟨htag, hP'.2⟩
      exact absurd hbad (ggInndiag_pRank_le_two_twF4der (X := ↥Y) hp hp2)
  refine largeEvenMarking_mono (fun lab' R _ I _ θ hP' => ?_) hmarkK
  exact ⟨hP'.1 ▸ hS1, hP'.2⟩

theorem ggPZNbrDatum_of_res
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hR : GGPZNbrResDatum) : GGPZNbrDatum := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY hnb
  have hcov := ggPZNbr_cov_or_res hRig hraw hiso h hY hJY hnb
  rcases GGInnerDiagOnLabel.elim_or hcov with hTor | hRes
  · exact (ggPZ_resXDatum_of_tbTor_nbr hT hLift h.1.1 hnb hTor).toSurj
  · exact hR G p B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY hnb hRes

end CFSG.StandardType

end

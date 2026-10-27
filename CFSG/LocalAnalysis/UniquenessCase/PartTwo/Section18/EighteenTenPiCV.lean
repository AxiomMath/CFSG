module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShapeCong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PRankSurvivor
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2Rank
public import CFSG.Quasithin.Background.QuasisimpleSp4G2Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenG2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenSp
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.Ch4Sec3L436
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31HSCases
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem no_pElement_centMbar (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {f : ℕ}
    (hnat : NatSpn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f ∨
      CFSG.Quasithin.G2Natural
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) f ∨
      CFSG.Quasithin.BinaryNaturalSL
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 2 f ∨
      (Even f ∧ NatOmegaMinus
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 (f / 2)))
    (hcopf : Nat.Coprime p (2 ^ f - 1))
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    ∀ c ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, orderOf c = p →
      (∀ x ∈ barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L), c * x = x * c) →
      False := by
  have hcomm := @k_18_10_commutant
  set hV := h.hyp125.isElemAbelian with hVdef
  set Xbar := barSub V₀ V hV (conjClosure D.M L) with hXbardef
  intro c hcM hcord hcX
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hfix : ∀ w : Vtil V₀ V hV, c w * w⁻¹ ∈ CFSG.Quasithin.fixV Xbar := by
    intro w
    exact hcomm hW Xbar f hnat c hcX (by rw [hcord]; exact hcopf) w
  let δ : Vtil V₀ V hV →* Vtil V₀ V hV :=
    { toFun := fun w => c w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hδfix : ∀ v : Vtil V₀ V hV, δ v ∈ CFSG.Quasithin.fixV Xbar := hfix
  have hδgen : ∀ x ∈ Xbar, ∀ v : Vtil V₀ V hV, δ (x v * v⁻¹) = 1 := by
    intro x hx v
    have hxc : c (x v) = x (c v) := by
      have := congrArg (fun q : MulAut (Vtil V₀ V hV) => q v) (hcX x hx)
      simpa [MulAut.mul_apply] using this
    have hδv : x (c v * v⁻¹) = c v * v⁻¹ := hδfix v x hx
    have hδv' : x (c v) * (x v)⁻¹ = c v * v⁻¹ := by
      simpa [map_mul, map_inv] using hδv
    show c (x v * v⁻¹) * (x v * v⁻¹)⁻¹ = 1
    rw [map_mul, map_inv, hxc, mul_inv_rev, inv_inv]
    calc x (c v) * (c v)⁻¹ * (v * (x v)⁻¹)
        = (x (c v) * (x v)⁻¹) * ((c v)⁻¹ * v) := by ac_rfl
      _ = (c v * v⁻¹) * ((c v)⁻¹ * v) := by rw [hδv']
      _ = 1 := by
        rw [mul_comm ((c v)⁻¹) v]
        group
  have hδ1 : ∀ w : Vtil V₀ V hV, δ w = 1 := by
    intro w
    have htop : CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V hV)) Xbar = ⊤ :=
      commSub_top_barSub_conjClosure_eq_top hx h61 h127 h1214 h hX1
    have hmem : w ∈ CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V hV)) Xbar := by
      rw [htop]
      exact Subgroup.mem_top w
    have hker : CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V hV)) Xbar ≤
        (⊥ : Subgroup (Vtil V₀ V hV)).comap δ := by
      rw [CFSG.Quasithin.commSub]
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨x, hx, v, -, rfl⟩
      exact hδgen x hx v
    exact Subgroup.mem_bot.mp (hker hmem)
  have hc1 : c = 1 := by
    refine MulEquiv.ext fun v => ?_
    exact mul_inv_eq_one.mp (hδ1 v)
  have h1 : orderOf c = 1 := by rw [hc1]; exact orderOf_one
  have : p = 1 := by rw [← hcord, h1]
  exact h.p_prime.ne_one this

theorem pRank_centVec_ge (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {f : ℕ}
    (hnat : NatSpn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f ∨
      CFSG.Quasithin.G2Natural
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) f ∨
      CFSG.Quasithin.BinaryNaturalSL
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 2 f ∨
      (Even f ∧ NatOmegaMinus
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 (f / 2)))
    (hcopf : Nat.Coprime p (2 ^ f - 1))
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥)
    {m : ℕ} (hC : m ≤ CFSG.Open.pRank p (F08.CentOverO2 D.M (conjClosure D.M L))) :
    m ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (V : Set G)) := by
  classical
  have hp : p.Prime := h.p_prime
  haveI : Fact p.Prime := ⟨hp⟩
  set hV := h.hyp125.isElemAbelian with hVdef
  set X := conjClosure D.M L with hXdef
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMN : D.M ≤ normalizer (X : Set G) := TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hMst : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hO2M : barSub V₀ V hV (pCoreOf 2 D.M) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_hyp125 (V₀ := V₀) (V := V) h.hyp125
  have hO2X : barSub V₀ V hV (pCoreOf 2 X) = ⊥ := by
    refine le_bot_iff.1 (hO2M ▸ barSub_mono V₀ V hV ?_)
    exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hXM hMN
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) (H := F08.CentOverO2 D.M X) hp.one_lt
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p (n := m) (by
    rw [hEcard]
    exact pow_dvd_pow p hC)
  let Lsub : Subgroup G := K.map E.subtype
  have hLsub_le : Lsub ≤ F08.CentOverO2 D.M X := (Subgroup.map_subtype_le K).trans hE
  have hLsub_ea : IsElemAbelian p Lsub := hEel.mono (Subgroup.map_subtype_le K)
  have hLsub_card : Nat.card Lsub = p ^ m := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hKcard
  have hcard : Nat.card V₀ ≤ 2 :=
    (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
  have hpodd : Odd p := hp.odd_of_ne_two h.p_ne_two
  have hLsub_inf : Lsub ≤ D.M ⊓ centralizer (V : Set G) := by
    intro e he
    obtain ⟨eE, heE, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨heM, heact⟩ := mem_centOverO2_iff.mp (hLsub_le he)
    refine ⟨heM, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    by_cases he1 : (eE : G) = 1
    · simp [he1]
    · have hepow : (eE : G) ^ p = 1 := hEel.2 (eE : G) eE.2
      have heord : orderOf (eE : G) = p := orderOf_eq_prime hepow he1
      have hMs : (eE : G) ∈ stabTil V₀ V := hMst heM
      let c : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨(eE : G), hMs⟩
      have hcM : c ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV heM hMs
      have hcX : ∀ x ∈ barSub V₀ V hV X, c * x = x * c := by
        intro xbar hxbar
        obtain ⟨x, hxX, hxeq⟩ := (mem_barSub V₀ V hV X xbar).1 hxbar
        rw [← hxeq]
        have hxM : (x : G) ∈ D.M := hXM hxX
        have hqX : (eE : G) * (x : G) * (eE : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 X :=
          heact (x : G) hxX
        have hqst : (eE : G) * (x : G) * (eE : G)⁻¹ * (x : G)⁻¹ ∈ stabTil V₀ V :=
          hMst (D.M.mul_mem (D.M.mul_mem (D.M.mul_mem heM hxM) (D.M.inv_mem heM))
            (D.M.inv_mem hxM))
        have hqbar : actTil V₀ V hV
            ⟨(eE : G) * x * (eE : G)⁻¹ * x⁻¹, hqst⟩ = 1 := by
          have hmem : actTil V₀ V hV
              ⟨(eE : G) * x * (eE : G)⁻¹ * x⁻¹, hqst⟩ ∈
              barSub V₀ V hV (pCoreOf 2 X) :=
            actTil_mem_barSub V₀ V hV hqX hqst
          rwa [hO2X, Subgroup.mem_bot] at hmem
        have hexst : (eE : G) * x * (eE : G)⁻¹ ∈ stabTil V₀ V :=
          hMst (D.M.mul_mem (D.M.mul_mem heM hxM) (D.M.inv_mem heM))
        have hmul : c * actTil V₀ V hV x * c⁻¹ =
            actTil V₀ V hV ⟨(eE : G) * (x : G) * (eE : G)⁻¹, hexst⟩ := by
          have h1 : (⟨(eE : G), hMs⟩ : stabTil V₀ V) * x *
              (⟨(eE : G), hMs⟩ : stabTil V₀ V)⁻¹ =
              ⟨(eE : G) * (x : G) * (eE : G)⁻¹, hexst⟩ := Subtype.ext (by simp)
          have h2 : actTil V₀ V hV ((⟨(eE : G), hMs⟩ : stabTil V₀ V) * x *
              (⟨(eE : G), hMs⟩ : stabTil V₀ V)⁻¹) =
              c * actTil V₀ V hV x * c⁻¹ := by
            simp only [c, map_mul, map_inv]
          rw [← h2, h1]
        have hconj : c * actTil V₀ V hV x * c⁻¹ = actTil V₀ V hV x := by
          rw [hmul]
          have hq_eq : (⟨(eE : G) * (x : G) * (eE : G)⁻¹, hexst⟩ : stabTil V₀ V) =
              (⟨(eE : G) * (x : G) * (eE : G)⁻¹ * (x : G)⁻¹, hqst⟩ : stabTil V₀ V) * x :=
            Subtype.ext (by simp)
          rw [hq_eq, map_mul]
          have hstep : actTil V₀ V hV
                ⟨(eE : G) * (x : G) * (eE : G)⁻¹ * (x : G)⁻¹, hqst⟩ *
              actTil V₀ V hV x = 1 * actTil V₀ V hV x :=
            congrArg (fun y => y * actTil V₀ V hV x) hqbar
          simpa using hstep
        exact mul_inv_eq_iff_eq_mul.mp hconj
      have hcpow : c ^ p = 1 := by
        change actTil V₀ V hV ⟨(eE : G), hMs⟩ ^ p = 1
        rw [← map_pow]
        have h1 : (⟨(eE : G), hMs⟩ : stabTil V₀ V) ^ p = 1 := Subtype.ext hepow
        rw [h1, map_one]
      have hc1 : c = 1 := by
        by_contra hcne
        have hcordvd : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcpow
        have hcord : orderOf c = p := by
          rcases (Nat.dvd_prime hp).1 hcordvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.mp h1) hcne
          · exact h1
        exact no_pElement_centMbar D h hx h61 h127 h1214 hnat hcopf hX1
          c hcM hcord hcX
      have hact : actTil V₀ V hV ⟨(eE : G), hMs⟩ = 1 := hc1
      have hfix : actTil V₀ V hV ⟨(eE : G), hMs⟩ (tilOf V₀ V hV v hv) =
          tilOf V₀ V hV v hv := by rw [hact, MulAut.one_apply]
      have hcommv : (eE : G) * v * (eE : G)⁻¹ = v :=
        fixes_of_actTil_tilOf_eq_of_odd hV h.hyp125.pairFacts.le hcard hMs hv hfix
          (by rw [heord]; exact hpodd)
      calc v * (eE : G) = ((eE : G) * v * (eE : G)⁻¹) * (eE : G) := by rw [hcommv]
        _ = (eE : G) * v := by group
  exact CFSG.SectionRank.le_pRank hp.one_lt hLsub_inf hLsub_ea hLsub_card

theorem barSub_ne_bot_of_natRealizes {W : Type} [CommGroup W] [Finite W]
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)}
    {π : ↥Γ →* ↥H} (h : (CFSG.Quasithin.FFModel.nat Γ).RealizesVia H ⊤
      (CFSG.Quasithin.fixV H) π) : H ≠ ⊥ := by
  intro hH
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  let i : ι := Classical.arbitrary ι
  let v : ι → K := Pi.single i 1
  have hv : v ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp [v] at this
  let q : (CFSG.Quasithin.FFModel.nat Γ).Sec :=
    QuotientGroup.mk ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩
  have hq : q ≠ 1 := by
    intro hq1
    have hmem : (⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ :
        ↥(CFSG.Quasithin.FFModel.nat Γ).sec) ∈
        ((CFSG.Quasithin.FFModel.nat Γ).ker.subgroupOf
          (CFSG.Quasithin.FFModel.nat Γ).sec) :=
      (QuotientGroup.eq_one_iff _).1 hq1
    rw [Subgroup.mem_subgroupOf] at hmem
    change Multiplicative.ofAdd v ∈ (⊥ : Subgroup (Multiplicative (ι → K))) at hmem
    rw [Subgroup.mem_bot] at hmem
    have h1 : Multiplicative.ofAdd v = (1 : Multiplicative (ι → K)) := hmem
    apply hv
    simpa using congrArg Multiplicative.toAdd h1
  obtain ⟨u, hu⟩ := hβs q
  have htop : CFSG.Quasithin.fixV H = ⊤ := by
    ext w
    simp [CFSG.Quasithin.mem_fixV, hH]
  have h1 : β u = 1 := (hβk u).2 (by rw [htop]; exact Subgroup.mem_top _)
  exact hq (hu ▸ h1)

section Certified


theorem cong_of_isL2_barSub (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) {f : ℕ}
    (hL2 : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f) :
    (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set Xbar := barSub V₀ V hV (conjClosure D.M L) with hXbardef
  have hsimple : IsSimpleGroup Xbar :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  have hL2L : IsL2 ↥(barSub V₀ V hV L) f := by
    rw [← hXL, ← hXbardef]
    exact hL2
  have hL2Bar : IsL2 (Bar2 L) f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2L
  have hthin : F08.Thin8 L := S17.thin8_of_isL2 hL2Bar
  have hL0 : L ∈ S17.calL0Star D p := by
    rw [← hXL]
    exact h.hX
  have h54 : S17.Hyp1754 D p :=
    S17.hyp1754_of_thin_mem_calL0Star D h1742 h.hp h.hL hL0 hthin
  obtain ⟨m, -, hP, -, hL2m⟩ :=
    S17.exists_p1642_isL2_of_self (V₀ := V₀) (V := V) h1742 h641 h642 h643 h.hp h.hL hL0 hthin
  have hmf : m = f := S17.isL2_field_unique hL2m hL2Bar
  subst hmf
  exact (h643 p h54 m hP).2

theorem exists_adjoint_of_isG2 {X : Type} [Group X] {f : ℕ} (hG2 : IsG2 X f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
  have hcheb : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  have hU : CFSG.Blueprint.UntwistedChevalleyModel X .G2 (2 ^ f) := by
    simpa [CFSG.Blueprint.ChevalleyExceptionalModel] using hcheb.2
  exact CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) (q := 2 ^ f) hU

theorem center_eq_bot_of_isG2 {X : Type} [Group X] {f : ℕ} (hG2 : IsG2 X f) :
    Subgroup.center X = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_of_isG2 hG2
  letI := hKf
  letI := hKfin
  exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

theorem pRank_le_two_of_isG2 {X : Type} [Group X] [Finite X] {f p : ℕ} (hf2 : 2 ≤ f)
    (hG2 : IsG2 X f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_of_isG2 hG2
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hp1 : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  have hdvd : p ∣ (2 ^ f) ^ 2 - 1 := by
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [hfac]
    exact dvd_mul_of_dvd_left (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong) _
  have hES : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ f) p = 1 :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_one_iff hp1).2 hdvd
  have hKcard' : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hKcard' hf2 hp hp2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e, hrank, hKcard',
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_rkG2_of_eS hES]

end Certified

theorem coprime_of_cong {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) :
    Nat.Coprime p (2 ^ f - 1) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_not_dvd_pred hp hp2 hcong)

theorem pRank_centOverO2_ge_of_rank_bound (D : Data G) {X : Subgroup G} {p r k : ℕ}
    (hXM : X ≤ D.M) (hMN : D.M ≤ normalizer (X : Set G))
    (hcenter : Subgroup.center (Bar2 X) = ⊥)
    (hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 X)))
    (hp : p.Prime) (hp2 : p ≠ 2) (hOp : UC22.F10.OpRes p D.M = D.M)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) ≤ r)
    (hMr : k + r ≤ CFSG.Open.pRank p D.M) :
    k ≤ CFSG.Open.pRank p (F08.CentOverO2 D.M X) := by
  have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hXM hMN hcenter hcyc hp hp2 hOp
  omega

theorem barSub_ne_bot_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {f : ℕ}
    (h : CFSG.Quasithin.BinaryNaturalSL H ⊤ (CFSG.Quasithin.fixV H) 2 f) : H ≠ ⊥ := by
  obtain ⟨K, hKf, hKfin, -, hR⟩ := h
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨π, hπ⟩ := hR
  exact barSub_ne_bot_of_natRealizes (ι := Fin 2) (K := K) hπ

theorem barSub_ne_bot_of_natOmegaMinus4 {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {f : ℕ}
    (h : NatOmegaMinus H ⊤ (CFSG.Quasithin.fixV H) 4 (f / 2)) : H ≠ ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, -, -, hR⟩ := h
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨π, hπ⟩ := hR
  exact barSub_ne_bot_of_natRealizes (ι := Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2) hπ

section CertifiedL2


theorem piCV_L2_ge_two (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) {f : ℕ}
    (hL2 : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f)
    (hnat : CFSG.Quasithin.BinaryNaturalSL
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 2 f ∨
      (Even f ∧ NatOmegaMinus
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 (f / 2)))
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (V : Set G)) := by
  classical
  have hp : p.Prime := h.p_prime
  have hp2 : p ≠ 2 := h.p_ne_two
  set hV := h.hyp125.isElemAbelian with hVdef
  set X := conjClosure D.M L with hXdef
  set Xbar := barSub V₀ V hV X with hXbardef
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMN : D.M ≤ normalizer (X : Set G) := TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hsimple : IsSimpleGroup Xbar :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsimple
  have hXL' : X = L := by rw [hXdef]; exact hXL
  have hL2L : IsL2 ↥(barSub V₀ V hV L) f := by
    rw [← hXL', ← hXbardef]
    exact hL2
  have hL2Ev : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2Ev Xbar f :=
    (CFSG.LocalAnalysis.UniquenessCase.UC22.P22fin.isL2Ev_of_isL2 hL2).1
  have hcenterXbar : Subgroup.center Xbar = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.center_eq_bot_of_isL2Ev hL2Ev
  have hcenterBar : Subgroup.center ↥(barSub V₀ V hV L) = ⊥ := by
    rw [← hXL', ← hXbardef]
    exact hcenterXbar
  have hcenter : Subgroup.center (Bar2 X) = ⊥ := by
    rw [hXL']
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e hcenterBar
  have hcycXbar : IsCyclic (Outer Xbar) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.isCyclic_outer_of_isL2Ev hL2Ev
  have hcycBar : IsCyclic (Outer ↥(barSub V₀ V hV L)) := by
    rw [← hXL', ← hXbardef]
    exact hcycXbar
  have hcyc : IsCyclic (Outer (Bar2 X)) := by
    rw [hXL']
    exact isCyclic_of_surjective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.toMonoidHom
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.surjective
  have hrankXbar : CFSG.Open.pRank p (⊤ : Subgroup ↥(barSub V₀ V hV L)) ≤ 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz (Or.inl hL2L) hp hp2
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) ≤ 1 := by
    rw [hXL']
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact hrankXbar
  have hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] :=
    cong_of_isL2_barSub D h h1742 h641 h642 h643 hL2
  have hcopf : Nat.Coprime p (2 ^ f - 1) := coprime_of_cong hp hp2 hcong
  have hnatFull : NatSpn Xbar ⊤ (CFSG.Quasithin.fixV Xbar) 4 f ∨
      CFSG.Quasithin.G2Natural Xbar ⊤ (CFSG.Quasithin.fixV Xbar) f ∨
      CFSG.Quasithin.BinaryNaturalSL Xbar ⊤ (CFSG.Quasithin.fixV Xbar) 2 f ∨
      (Even f ∧ NatOmegaMinus Xbar ⊤ (CFSG.Quasithin.fixV Xbar) 4 (f / 2)) := by
    rcases hnat with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hMr : 2 + 1 ≤ CFSG.Open.pRank p D.M := by
    have h3 := hx.three_le p h.hp
    omega
  have hC := pRank_centOverO2_ge_of_rank_bound D (X := X) (p := p) (r := 1) (k := 2)
    hXM hMN hcenter hcyc hp hp2 (h638 p hp hp2 (Or.inl h.hp)) hrk hMr
  exact pRank_centVec_ge D h hx h61 h127 h1214 hnatFull hcopf hX1 hC

theorem cong_of_isSp4_or_isG2 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {f : ℕ}
    (hS : IsSp4 (Bar2 (conjClosure D.M L)) f ∨ IsG2 (Bar2 (conjClosure D.M L)) f) :
    (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] :=
  (isSp4_or_isG2_bar2_cong_more h h1742 hS).2.2.2.2.1

theorem piCV_a_18_10
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) :
    Gap_18_10_piCV_a D V₀ V p L h := by
  classical
  intro h62 hnot
  have hp : p.Prime := h.p_prime
  have hp2 : p ≠ 2 := h.p_ne_two
  set hV := h.hyp125.isElemAbelian with hVdef
  set X := conjClosure D.M L with hXdef
  set Xbar := barSub V₀ V hV X with hXbardef
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMN : D.M ≤ normalizer (X : Set G) := TwelveTwentyThree.le_normalizer_conjClosure D.M L
  obtain ⟨f, hcases⟩ := h62
  rcases hcases with hsp | hg2 | hsUn | hOm6 | hOp4 | hOm4 | hL2
  ·
    obtain ⟨hSp4, hnatSpn⟩ := hsp
    have hcong := cong_of_isSp4_or_isG2 h h1742 (Or.inl hSp4)
    have hcopf := coprime_of_cong hp hp2 hcong
    have hX1 : Xbar ≠ ⊥ := barSub_ne_bot_of_natSpn hnatSpn
    have hcenter : Subgroup.center (Bar2 X) = ⊥ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218d_center_eq_bot_sp4 hSp4
    have hcyc : IsCyclic (Outer (Bar2 X)) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isCyclic_outer_of_lieModel_PSp4 hSp4
    have hrk : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) ≤ 2 :=
      CFSG.Quasithin.B69K.pRank_le_two_of_psp2
        (hSp4.statedClassicalModel (by decide)) hp hp2
    have hMr : 1 + 2 ≤ CFSG.Open.pRank p D.M := by
      have h3 := hx.three_le p h.hp
      omega
    have hC := pRank_centOverO2_ge_of_rank_bound D (X := X) (p := p) (r := 2) (k := 1)
      hXM hMN hcenter hcyc hp hp2 (h638 p hp hp2 (Or.inl h.hp)) hrk hMr
    have hnat : NatSpn Xbar ⊤ (CFSG.Quasithin.fixV Xbar) 4 f := hnatSpn
    have hle := pRank_centVec_ge D h hx h61 h127 h1214 (Or.inl hnat) hcopf hX1 hC
    exact ⟨hp, CFSG.GroupTheory.dvd_card_of_one_le_pRank hp hle⟩
  ·
    obtain ⟨hG2, hnatG2⟩ := hg2
    have hcong := cong_of_isSp4_or_isG2 h h1742 (Or.inr hG2)
    have hcopf := coprime_of_cong hp hp2 hcong
    have hX1 : Xbar ≠ ⊥ := barSub_ne_bot_of_g2Natural hnatG2
    have hadm := CFSG.Blueprint.LieModel.admissible hG2
    have h3 : 3 ≤ 2 ^ f := hadm.2.2.2
    have hf2 : 2 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hfpos
      · norm_num at h3
      · have hf1' : f ≠ 1 := by
          rintro rfl
          norm_num at h3
        omega
    have hcenter : Subgroup.center (Bar2 X) = ⊥ := center_eq_bot_of_isG2 hG2
    have hcyc : IsCyclic (Outer (Bar2 X)) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isCyclic_outer_of_lieModel_G2 hG2
    have hrk : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) ≤ 2 :=
      pRank_le_two_of_isG2 hf2 hG2 hp hp2 hcong
    have hMr : 1 + 2 ≤ CFSG.Open.pRank p D.M := by
      have h3 := hx.three_le p h.hp
      omega
    have hC := pRank_centOverO2_ge_of_rank_bound D (X := X) (p := p) (r := 2) (k := 1)
      hXM hMN hcenter hcyc hp hp2 (h638 p hp hp2 (Or.inl h.hp)) hrk hMr
    have hnat : CFSG.Quasithin.G2Natural Xbar ⊤ (CFSG.Quasithin.fixV Xbar) f := hnatG2
    have hle := pRank_centVec_ge D h hx h61 h127 h1214
      (Or.inr (Or.inl hnat)) hcopf hX1 hC
    exact ⟨hp, CFSG.GroupTheory.dvd_card_of_one_le_pRank hp hle⟩
  ·
    exact False.elim (hnot ⟨f, Or.inl hsUn.1⟩)
  ·
    exact False.elim (hnot ⟨f, Or.inr (Or.inl hOm6.1)⟩)
  ·
    exact False.elim (hnot ⟨f, Or.inr (Or.inr hOp4.1)⟩)
  ·
    obtain ⟨hEven, hOm, hNat⟩ := hOm4
    have hk : 1 ≤ f / 2 := by
      obtain ⟨-, K, hKf, hKfin, b, c, hKcard, -, -⟩ := hOm
      exact CFSG.ComponentClassification.CatLeafProof.one_le_of_card_eq_pow hKcard
    have hL2' : IsL2 Xbar (2 * (f / 2)) := isL2_of_isOmegaMinus_four hk hOm
    have h2f : 2 * (f / 2) = f := by
      obtain ⟨m, hm⟩ := hEven
      omega
    have hL2f : IsL2 Xbar f := by simpa [h2f] using hL2'
    have hX1 : Xbar ≠ ⊥ := barSub_ne_bot_of_natOmegaMinus4 hNat
    have hle := piCV_L2_ge_two D h hx h61 h127 h1214 h638 h1742 h641 h642 h643
      hL2f (Or.inr ⟨hEven, hNat⟩) hX1
    exact ⟨hp, CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (by omega)⟩
  ·
    obtain ⟨hL2f, hNat⟩ := hL2
    have hX1 : Xbar ≠ ⊥ := barSub_ne_bot_of_binaryNaturalSL hNat
    have hle := piCV_L2_ge_two D h hx h61 h127 h1214 h638 h1742 h641 h642 h643
      hL2f (Or.inl hNat) hX1
    exact ⟨hp, CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (by omega)⟩

theorem piCV_b_18_10
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) :
    Gap_18_10_piCV_b D V₀ V p L h := by
  classical
  intro _h62 hb
  rcases hb with ⟨f, hEven, hOm, hNat⟩ | ⟨f, hL2, hNat⟩
  ·
    have hk : 1 ≤ f / 2 := by
      obtain ⟨-, K, hKf, hKfin, b, c, hKcard, -, -⟩ := hOm
      exact CFSG.ComponentClassification.CatLeafProof.one_le_of_card_eq_pow hKcard
    have hL2' : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))
        (2 * (f / 2)) := isL2_of_isOmegaMinus_four hk hOm
    have h2f : 2 * (f / 2) = f := by
      obtain ⟨m, hm⟩ := hEven
      omega
    have hL2f : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f := by
      simpa [h2f] using hL2'
    have hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ :=
      barSub_ne_bot_of_natOmegaMinus4 hNat
    exact piCV_L2_ge_two D h hx h61 h127 h1214 h638 h1742 h641 h642 h643
      hL2f (Or.inr ⟨hEven, hNat⟩) hX1
  ·
    have hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ :=
      barSub_ne_bot_of_binaryNaturalSL hNat
    exact piCV_L2_ge_two D h hx h61 h127 h1214 h638 h1742 h641 h642 h643
      hL2 (Or.inl hNat) hX1

theorem eighteen_ten_of_inputs (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) :
    R18_10At D V₀ V p L h :=
  eighteen_ten D h h127 h61 h1742 k_18_10_Sp_holds k_18_10_G2_holds
    (piCV_a_18_10 D h hx h61 h127 h1214 h638 h1742 h641 h642 h643)
    (piCV_b_18_10 D h hx h61 h127 h1214 h638 h1742 h641 h642 h643)

end CertifiedL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

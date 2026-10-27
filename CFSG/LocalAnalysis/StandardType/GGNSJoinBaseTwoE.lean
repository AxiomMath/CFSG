module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitary
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGIsWeylMatrixE.of_not_typeA_not_typeD {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hA : ¬ GGIsWeylMatrixA M)
    (hD : ¬ NSJoin.NSTypeD M) : GGIsWeylMatrixE M := by
  rcases SecFiveL1Odd.weyl_ad_or_e_or_small hM h3 with (⟨n, σ, hn, hM'⟩ | hD') | hE |
    ⟨n, σ, hn, -, hM'⟩
  · exact absurd ⟨n, σ, by omega, hM'⟩ hA
  · exact absurd hD' hD
  · exact hE
  · exact absurd ⟨n, σ, hn, hM'⟩ hA

theorem NSJoin.eq_three_of_innerDiagOnLabel_n_one {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop} (hp : p.Prime)
    (hP : ∀ lab, P p lab → lab.n = 1 ∧ p ∣ 2 ^ lab.n + 1) (h : GGInnerDiagOnLabel P p Bs X) :
    p = 3 := by
  obtain ⟨lab, -, -, -, -, -, -, -, hl, -⟩ := largeEvenMarking_exists_hasLabel h
  obtain ⟨hn, hdvd⟩ := hP lab hl
  have h3 : p ∣ 3 := by
    rw [hn] at hdvd
    simpa using hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3

theorem NSJoin.eq_three_of_innerDiagOnLabel_resGenRestTwo {G : Type} [Group G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (h : GGInnerDiagOnLabel ggRowP_ResGenRestTwo p Bs X) :
    p = 3 :=
  NSJoin.eq_three_of_innerDiagOnLabel_n_one hp (fun _ ⟨hn, hrow⟩ => ⟨hn, by
    rcases hrow with ⟨⟨-, hd⟩, -⟩ | ⟨-, -, -, hd⟩ | ⟨-, -, -, hd⟩ <;> exact hd⟩) h

theorem NSJoin.not_innerDiagOnLabel_qFour_of_n_one {G : Type} [Group G] {p : ℕ}
    {Bs X : Subgroup G} {P : ℕ → LargeEvenLabel → Prop} (hRig : GGLabelRigidInput)
    (hP : ∀ lab, P p lab → lab.n = 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2))
    (h : GGInnerDiagOnLabel P p Bs X) : ¬ GGInnerDiagOnLabel GGLabQFour p Bs X := by
  intro hq
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, hl, -⟩ := largeEvenMarking_exists_hasLabel h
  obtain ⟨lab', hΛ', hhas', -, -, -, -, -, hq', -⟩ := largeEvenMarking_exists_hasLabel hq
  obtain ⟨hn, hA, hD⟩ := hP lab hl
  have hn' := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') hA hD
  have h2 : 2 ≤ lab'.n := hq'
  omega

theorem NSJoin.not_innerDiagOnLabel_qFour_of_resGenRestTwo {G : Type} [Group G] {p : ℕ}
    {Bs X : Subgroup G} (hRig : GGLabelRigidInput)
    (h : GGInnerDiagOnLabel ggRowP_ResGenRestTwo p Bs X) :
    ¬ GGInnerDiagOnLabel GGLabQFour p Bs X := by
  refine NSJoin.not_innerDiagOnLabel_qFour_of_n_one hRig (fun lab hl => ?_) h
  obtain ⟨hn, hrow⟩ := hl
  refine ⟨hn, ?_⟩
  rcases hrow with ⟨⟨⟨ht, -⟩ | ⟨ht, hr⟩, -⟩, -⟩ | ⟨ht, -, -, -⟩ | ⟨ht, hr, -, -⟩ <;>
    refine ⟨by rw [ht]; decide, fun ht' => ?_⟩ <;> rw [ht] at ht' <;>
    first | omega | exact absurd ht' (by decide)

section


theorem NSJoin.false_of_orthTwo_L {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6)
    (h : GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab))
      p Bs L) :
    False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hOrth : ∀ P : ℕ → LargeEvenLabel → Prop,
      (∀ lab, P p lab → ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) → (∀ lab, P p lab → lab.n = 1) →
      GGInnerDiagOnLabel P p Bs L →
      (∀ lab, P p lab → GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → Subgroup.center ↥L = ⊥) →
      False := by
    intro P hProw hPn hmark hZK
    obtain ⟨lab, hPlab, -, Φ, -, hcard, -⟩ :=
      OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hBs hSC hProw hmark hZK
        (ggGamma_L_exists_ne_one hconf)
    have hK : Nat.card Φ.F = 2 := by rw [hcard, hPn lab hPlab, pow_one]
    obtain ⟨a, ha, hrefl, h6⟩ := Φ.exists_refl_card_six hK
    exact hsix a ha (ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha) hrefl) h6
  have h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1 ∧ ¬ (lab.tag = .D ∧ lab.rank = 4)))
      p Bs L :=
    h.mono' fun lab hl => by
      obtain ⟨hn, hrow⟩ := hl
      by_cases h4 : lab.tag = .D ∧ lab.rank = 4
      · refine Or.inl ⟨?_, hn, h4.2⟩
        rcases hrow with hrow | ⟨ht, -⟩
        · exact hrow
        · rw [h4.1] at ht
          exact absurd ht (by decide)
      · exact Or.inr ⟨hrow, hn, h4⟩
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  ·
    exact hOrth _ (fun _ hl => Or.inl hl.1) (fun _ hl => hl.2.1) h
      (fun _ _ _ => GGConfig.center_eq_bot_of_D4two hRig hconf h)
  ·
    have : Group.IsPerfect ↥L := Group.IsPerfect.mk h.1
    refine hOrth _ (fun _ hl => hl.1) (fun _ hl => hl.2.1) h fun lab hl hhas => ?_
    obtain ⟨hrow, hn, h4⟩ := hl
    refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
    rcases hrow with ⟨ht, hr, -, -⟩ | ⟨ht, hr, -, -⟩
    · have h4' : lab.rank ≠ 4 := fun h => h4 ⟨ht, h⟩
      exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr ⟨ht, by omega⟩

private theorem ggCard_eq_three_pow_six_or_center_eq_bot_of_twA5_E6 {G : Type}
    [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {σ : Fin 6 ≃ ι}
    (hM : M = CoxeterMatrix.E₆.reindex σ)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L)
    (hle : Nat.card Bs ≤ 3 ^ 6) :
    Nat.card ↥Bs = 3 ^ 6 ∨ Subgroup.center ↥L = ⊥ := by
  classical
  have hBs : IsElemAbelian 3 Bs := ggRouteCfg_isElemAbelian hcfg
  have hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hge : 3 ^ 5 ≤ Nat.card Bs := E6QTwo.three_pow_five_le_card hBs hcfg.1.2.2.2.1
    (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hφ)) hW
  obtain ⟨k, hk⟩ := hBs.isPGroup.exists_card_eq
  rw [hk] at hge hle ⊢
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  have hk6 : k ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  interval_cases k
  · refine Or.inr (hcfg.center_eq_bot_of_twA5_E6 hpres ⟨σ, hM⟩ ?_ hk)
    refine h.mono' fun lab hl => ?_
    obtain ⟨hesu, hn, hr⟩ := hl
    refine ⟨?_, hr, hn⟩
    rcases hesu with ⟨⟨ht, -⟩ | ⟨-, hr3⟩, -⟩
    · exact ht
    · omega
  · exact Or.inl rfl

theorem GGSecFiveRouteCfg.card_eq_three_pow_six_or_center_eq_bot_of_twA5_typeE {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hTB : GGTBFixInput) (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ (∃ σ : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex σ) ∧
      (Nat.card ↥Bs = 3 ^ 6 ∨ Subgroup.center ↥L = ⊥) := by
  classical
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
      (b : G) ∈ Subgroup.zpowers x := by
    obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
    intro b hb
    exact hTB G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN
      (hcfg.2.1 y K' hN) (Or.inr hcfg.2.1) b hb
  obtain ⟨rfl, -, hle⟩ := nsQ2U62_weyl hconf hFix h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨rfl, ?_⟩
  rcases hE with ⟨σ, hM⟩ | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · exact ⟨⟨σ, hM⟩, ggCard_eq_three_pow_six_or_center_eq_bot_of_twA5_E6 hcfg hpres hM h hle⟩
  · exfalso
    have hW : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h7 : 3 ^ 7 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) (ggRouteCfg_isElemAbelian hcfg) hW
      FrameRoute.exists_elemAbelian_two_coxeterE7
    have := h7.trans hle
    norm_num at this
  · exfalso
    have hW : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h8 : 3 ^ 8 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) (ggRouteCfg_isElemAbelian hcfg) hW
      FrameRoute.exists_elemAbelian_two_coxeterE8
    have := h8.trans hle
    norm_num at this

theorem GGSecFiveRouteCfg.exists_rankOne_card_six_of_twA5_typeE {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card ↥(ggRankOneIn L Bs r) = 6 := by
  classical
  obtain ⟨rfl, -, hZor⟩ :=
    GGSecFiveRouteCfg.card_eq_three_pow_six_or_center_eq_bot_of_twA5_typeE hTB hcfg hpres hE h
  obtain ⟨K, _hf, _hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn, hr5⟩ := hSide
  change n = 1 at hn
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  obtain ⟨r, hrA, hrefl, hr6⟩ :=
    ggNsq2_exists_rankOne_of_or hU62 hTB hcfg hK hdvd θ hperf hBsN hbs
      (fun _ => hZor.imp (fun h => Nat.le_of_eq h.symm) id)
  exact ⟨r, hrA, ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hE.le_three
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrefl, hr6⟩

theorem NSJoin.false_of_twA5_two_L_typeE {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    False := by
  obtain ⟨r, hrA, hrC, hr6⟩ := hcfg.exists_rankOne_card_six_of_twA5_typeE hTB hU62 hpres hE h
  exact hsix r hrA hrC hr6

theorem NSJoin.not_innerDiagOnLabel_resGenRestTwo_L_typeE {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6) :
    ¬ GGInnerDiagOnLabel ggRowP_ResGenRestTwo p Bs L := by
  intro h
  have h' : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
      (lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab))) p Bs L :=
    h.mono' fun lab hl => by
      obtain ⟨hn, hrow⟩ := hl
      rcases hrow with ⟨hesu, h35 | h35⟩ | hrow | hrow
      · refine Or.inl ⟨?_, h35, hesu.2⟩
        rcases hesu with ⟨⟨ht, -⟩ | ⟨ht, -⟩, -⟩
        · exact Or.inl ht
        · exact Or.inr ht
      · exact Or.inr (Or.inl ⟨hesu, hn, h35⟩)
      · exact Or.inr (Or.inr ⟨hn, Or.inl hrow⟩)
      · exact Or.inr (Or.inr ⟨hn, Or.inr hrow⟩)
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  ·
    exact not_ggInnerDiagOnLabel_unitary_four hcfg.1.1 h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact NSJoin.false_of_twA5_two_L_typeE hTB hU62 hcfg hpres hE hsix h
  ·
    exact NSJoin.false_of_orthTwo_L hcfg hpres hE.le_three hsix h

theorem NSJoin.innerDiagOnLabel_qFour_of_nbrQFour_E {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hNbrQ4 : NSJoin.NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M))
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hns : ¬ GGSplitLie 3 L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G} (hX : X ∈ 𝒦 ∨ GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X) :
    GGInnerDiagOnLabel GGLabQFour 3 Bs X := by
  obtain ⟨y, hnb⟩ : ∃ y : G, GGNbr 3 B x D J y X := by
    rcases hX with hXK | hw
    · exact hcfg.2.2.2.1.2 X hXK
    · exact hw.1
  exact hNbrQ4 G B Bs x L D J 𝒦 ⟨hcfg, hns, ι, M, e, hpres, hE, hsix⟩ y X hnb

end

end CFSG.StandardType

end

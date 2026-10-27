module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct

public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrder
public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public import CFSG.LocalAnalysis.StandardType.GGResJLinearCubeAutomizer
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryCubicBlock
public import CFSG.LocalAnalysis.StandardType.GGResJPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge

public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTBWNormSmall

public import CFSG.LocalAnalysis.StandardType.GGCRNOrthNs

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsRows

public import CFSG.LocalAnalysis.StandardType.GGTBTorD

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Holds

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL

public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_range_ggGamma_mul_prime_le {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) :
    Nat.card (ggGamma X hN).range * p ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hzord : orderOf z = p := orderOf_eq_prime (hBs.2 z hzBs) hz1
  have hzp : Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hzBs, hzC⟩
  have hcard : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← hzord, ← Nat.card_zpowers]
    exact Subgroup.card_le_of_le hzp
  exact (Nat.mul_le_mul_left _ hcard).trans_eq
    (NbrU63.card_range_ggGamma_mul_card_inf hN)

theorem GGResHyp.pow_three_le_card_range {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    p ^ 3 ≤ Nat.card (ggGamma X hN).range := by
  rcases hX with hX | hX
  · subst X
    have hc := NbrU63.card_range_ggGamma_mul_card_inf hN
    have hle := hH.1.card_bstar_centralizer_le
    have h4 := hH.1.tableB_facts.2.2.2.2
    have hm := Nat.mul_le_mul_left (Nat.card (ggGamma L hN).range) hle
    have hp : p.Prime := hH.1.tableB_facts.1
    have hf : p ^ 4 = p ^ 3 * p := by rw [show 4 = 3 + 1 from rfl, pow_succ]
    rw [hf] at h4
    exact Nat.le_of_mul_le_mul_right (h4.trans (hc.symm.le.trans hm)) hp.pos
  · subst X
    exact pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN

theorem inf_center_eq_bot_of_isElemAbelian_of_not_dvd {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hcp : ¬ p ∣ Nat.card (Subgroup.center X)) :
    Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  by_contra hg1
  have hgc : (⟨g, hg.1.2⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg.2 k k.2)
  let c : Subgroup.center X := ⟨⟨g, hg.1.2⟩, hgc⟩
  have hc1 : c ≠ 1 := fun h => hg1 (congrArg (fun a : Subgroup.center X => ((a : X) : G)) h)
  have hcpow : c ^ p = 1 := Subtype.ext (Subtype.ext (hBs.2 g hg.1.1))
  have hcorder : orderOf c = p := orderOf_eq_prime hcpow hc1
  exact hcp (hcorder ▸ orderOf_dvd_natCard c)

theorem seven_le_card_range_ggGamma_of_autCardSC
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs) (hX : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I)
    {r : ℕ} (hRank : GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial))
    (hCp : GGCenterPrime 3 R) (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hcard : Nat.card (ggAutomizer X Bs) = 51840) :
    3 ^ 7 ≤ Nat.card (ggGamma X hN).range := by
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hX θ hN hBsI h3 h3
  obtain ⟨hr, horder⟩ := hRank X (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hX (ggGamma X hN).range hTB.2.2.2.1 hTB.2.2.2.2.1 h3
    hTB.2.2.2.2.2.2.2
  have hcp : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
    hCp X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd Nat.prime_three hBs hcp, Subgroup.card_bot]
    norm_num
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN hZ
  rw [hcard, horder] at hdvd
  have hr7 : 7 ≤ r := by
    by_contra h
    have hr6 : r ≤ 6 := by omega
    have hle : 2 ^ r * r.factorial ≤ 2 ^ 6 * (6 : ℕ).factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hr6) (Nat.factorial_le hr6)
    have hgt := Nat.le_of_dvd (by positivity : 0 < 2 ^ r * r.factorial) hdvd
    norm_num at hle
    omega
  exact (Nat.pow_le_pow_right (by norm_num) hr7).trans hr

theorem six_le_card_range_ggGamma_of_autCardSC
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs) (hX : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I)
    {r : ℕ} (hRank : GGTorusAutCardSC 3 R I r (2 ^ r * r.factorial))
    (hCp : GGCenterPrime 3 R) (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hcard : Nat.card (ggAutomizer X Bs) = 51840) :
    3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
  exact (by norm_num : 3 ^ 6 ≤ 3 ^ 7).trans
    (seven_le_card_range_ggGamma_of_autCardSC hBs hSC hNoTr hX θ hN hBsI hRank hCp h3 hcard)

theorem seven_le_card_range_ggGamma_of_symplectic_automizer
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    {m f : ℕ} (hm : 1 ≤ m)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.C, m, f⟩) 3 Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hcard : Nat.card (ggAutomizer X Bs) = 51840) :
    3 ^ 7 ≤ Nat.card (ggGamma X hN).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hX, lab, hΛ, hraw⟩ := hmark
  have hEq : lab = ⟨.C, m, f⟩ := by
    obtain ⟨R, _, I, F, -, -, θ, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
    exact hEq
  subst hEq
  have hq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have hmod : (2 ^ f) ^ 2 % 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm f 2, pow_mul]
      simp [Nat.pow_mod]
    omega
  have hKGA := KGA.kga_label_of_pos Nat.prime_three (by norm_num) hm hq
  have hCenter : LargeEvenLabelAll ⟨.C, m, f⟩ fun R _ _ _ => GGCenterPrime 3 R := by
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have := charP_two_of_card hK
    have : NeZero m := ⟨by omega⟩
    exact ⟨K, inferInstance, inferInstance, hK, hQ, ggCenterPrime_sp Nat.prime_three (by norm_num)⟩
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, hN', hind⟩, hP, hCenter⟩ := largeEvenRawDatum_exists
    ((largeEvenLabelAll_and hKGA hCenter) _ hraw)
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    exact ggLAut_mem_of_induces X θ hN' hind hb
  exact seven_le_card_range_ggGamma_of_autCardSC hBs hSC hNoTr hX θ hN hBsI hP hCenter h3 hcard

theorem six_le_card_range_ggGamma_of_symplectic_automizer
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    {m f : ℕ} (hm : 1 ≤ m)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.C, m, f⟩) 3 Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range)
    (hcard : Nat.card (ggAutomizer X Bs) = 51840) :
    3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
  exact (by norm_num : 3 ^ 6 ≤ 3 ^ 7).trans
    (seven_le_card_range_ggGamma_of_symplectic_automizer hBs hSC hNoTr hm hmark hN h3 hcard)

theorem GGResHyp.not_symplectic_of_card_automizer_E6_upto_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs X) :
    False := by
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with hX | hX
    · rw [hX]; exact hH.2.2.1.1
    · rw [hX]; exact hH.2.2.1.2 y K hH.2.2.2.2.1
  let hN : Bs ≤ Subgroup.normalizer (X : Set G) := hInn.le_normalizer
  have horder : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  have hXfacts : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range := by
    exact hH.pow_three_le_card_range hX hN
  obtain ⟨_, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -⟩ := largeEvenRawDatum_exists hraw
  have hm : 1 ≤ lab.rank := by
    rcases htag with ht | ht <;> simp only [LargeEvenInLambda2, ht] at hΛ <;> omega
  have hMarkC : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨.C, lab.rank, lab.n⟩) 3 Bs X := by
    refine ⟨hInn.1, ⟨.C, lab.rank, lab.n⟩, ?_, ?_⟩
    · rcases htag with ht | ht <;> simpa only [LargeEvenInLambda2, ht] using hΛ
    · have hrawC : LargeEvenRawDatum ⟨.C, lab.rank, lab.n⟩
          (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
            ∃ θ : X ⧸ Subgroup.center X ≃* R, Bs ≤ Subgroup.normalizer (X : Set G) ∧
              ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
        have hraw' : LargeEvenRawDatum lab
            (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
              ∃ θ : X ⧸ Subgroup.center X ≃* R, Bs ≤ Subgroup.normalizer (X : Set G) ∧
                ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
          largeEvenRawDatum_mono
          (fun R _ I F h => ⟨h.1, h.2.1, h.2.2.choose,
            h.2.2.choose_spec.2⟩) hraw
        rcases htag with ht | ht
        all_goals simpa only [LargeEvenRawDatum, ht] using hraw'
      exact largeEvenRawDatum_mono
        (fun R _ I F h => ⟨h.1, h.2.1, h.2.2.choose, rfl, h.2.2.choose_spec⟩) hrawC
  have h7 := seven_le_card_range_ggGamma_of_symplectic_automizer hBs hSC hH.2.2.2.1 hm
    hMarkC hN h3 horder
  obtain ⟨z, hzBs, hz1, hzC⟩ := hXfacts
  have hmul := card_range_ggGamma_mul_prime_le Nat.prime_three hBs hN hzBs hz1 hzC
  norm_num at h7 hmul hcardBs
  omega

theorem GGResHyp.not_symplectic_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs X) :
    False := by
  exact GGResHyp.not_symplectic_of_card_automizer_E6_upto_seven
    hH hX (by rw [hcardBs]; norm_num) hcard hMark

theorem GGResE6DepShape.not_symplectic
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    {X : Subgroup G} (hX : X = L ∨ X = K) :
    ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) p Bs X := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hcard : Nat.card (ggAutomizer X Bs) = 51840 := by
    rcases hX with hX | hX
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).1
    · rw [hX]; exact (ggResE6DepShape_card_automizer hS).2
  exact hH.not_symplectic_of_card_automizer_E6 hX hS.2.1 hcard

theorem ggResE6Dep_labels
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hT1 : GGTBE6OrderInput) (hH : GGResHyp p B Bs x L D J y K)
    (hS : GGResE6DepShape p Bs L J K) :
    ∃ labL labK : LargeEvenLabel, LargeEvenInLambda2 labL ∧ LargeEvenInLambda2 labK ∧
      GGE6DepLabel labL ∧ GGE6DepLabel labK ∧
      GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧ GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hcardL, hcardK⟩ := ggResE6DepShape_card_automizer hS
  obtain ⟨hp, -, -⟩ := hS
  obtain ⟨labL, hinL, hE6L, hlL⟩ :=
    hT1 G p B Bs x L D J hH.1 hH.2.2.1 hH.2.2.2.1 hp L (Or.inl rfl) hcardL
  obtain ⟨labK, hinK, hE6K, hlK⟩ :=
    hT1 G p B Bs x L D J hH.1 hH.2.2.1 hH.2.2.2.1 hp K
      (Or.inr ⟨y, K, hH.2.2.2.2.1, rfl⟩) hcardK
  exact ⟨labL, labK, hinL, hinK, hE6L, hE6K, hlL, hlK⟩

section OriginalE6ComponentTable


open TablePThreeKG

theorem GGResHyp.exists_e6_two_original_J_label_table
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs L) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
      E6TwoCompLabelW labJ ∧ (labJ = ⟨.A, 2, 2⟩ → Subgroup.center ↥J ≠ ⊥) := by
  have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨δ, hdat, huniq⟩ :=
    exists_ggTorsionDatum_unique_of_innerDiagOnLabel
      (fun lab => lab.tag = .E6 ∧ lab.n = 1) hH.1.1 hH.1.2.2 hH.1.2.1.1 hMark
  obtain ⟨-, -, hδ3, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, labL, hΛL, hraw⟩ := hmark
  have hL : labL.tag = .E6 ∧ labL.n = 1 :=
    GGDichotomy.rawDatum_elim_const (lab := labL)
      (Q := labL.tag = .E6 ∧ labL.n = 1)
      (largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨-, -, θ, hP, -⟩ := h
        exact hP) hraw)
  have hrawMM : LargeEvenRawDatumLegacy labL
      (fun R _ I F => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          (labL.tag = .E6 ∧ labL.n = 1) ∧ ggInducedAut θ δ ∈ I) ∧ MarkedModel labL R) :=
    largeEvenRawDatum_markedModel hΛL (fun R _ I F h => h.2.1) hraw
  have hinndiag : LargeEvenLabelAll labL (LargeEvenSimpleGuard GGInndiagCommEq) :=
    largeEvenLabelAll_inndiagComm_E6 hL.1
  obtain ⟨R, hR, I, F, hbase, hGuard⟩ :=
    largeEvenRawDatum_exists (hinndiag _ hrawMM)
  obtain ⟨⟨hs, hna, θ, -, hδI⟩, hm⟩ := hbase
  have hEq : GGInndiagCommEq R I F := hGuard hs hna
  have ht_mem : markTag labL ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, hL.1]
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag labL) 2 labL.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag labL) (markRank labL)
        (markChar labL) (markDeg labL) := hm
    have h := hm0.chevalleyExceptionalModel ht_mem
    simpa [markChar, markDeg, hL.1] using h
  obtain ⟨d, hdchar, hk, huntw, he⟩ :=
    e6TwoLeaf_index_E6 (p := 2) (f := labL.n) (e6TwoLeaf_chevE6 hchev hL.1)
  obtain ⟨e⟩ := he
  have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
    rw [hk, hL.2, pow_one]
  obtain ⟨labJ, hΛJ, hHasSub, hpairW, -⟩ :=
    e6TwoLeaf_component (X := ↥L) (δ := δ) (J := J.subgroupOf L)
      θ hXc hδ3 hδ1 hcomp huniq hδI hEq d hdchar hdfield (Or.inl huntw) e
  obtain ⟨hW, hcentW⟩ := hpairW huntw
  have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hHasSub
  have hcentJ : labJ = ⟨.A, 2, 2⟩ → Subgroup.center ↥J ≠ ⊥ := by
    intro hA hbot
    apply hcentW hA
    let eJ := Subgroup.subgroupOfEquivOfLe hJL
    have hmap : Subgroup.map (eJ : ↥(J.subgroupOf L) →* ↥J)
        (Subgroup.center ↥(J.subgroupOf L)) = ⊥ := by
      rw [Subgroup.map_center_eq eJ, hbot]
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : eJ z ∈ Subgroup.map (eJ : ↥(J.subgroupOf L) →* ↥J)
        (Subgroup.center ↥(J.subgroupOf L)) := ⟨z, hz, rfl⟩
    rw [hmap] at hz'
    have hz1 : eJ z = 1 := by simpa using hz'
    exact eJ.injective (by simpa using hz1)
  exact ⟨labJ, hΛJ, hHasJ, hW, hcentJ⟩

theorem GGResHyp.exists_e6_original_J_marking_table
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L) :
    ∃ labL labJ : LargeEvenLabel,
      GGE6DepLabel labL ∧ LargeEvenInLambda2 labL ∧
      GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labL) 3 Bs L ∧
      LargeEvenInLambda2 labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J ∧
      (2 ≤ labL.n → E6CompLabel (2 ^ labL.n) labJ) ∧
      (labL.n = 1 → labL.tag = .E6 → E6TwoCompLabelW labJ ∧
        (labJ = ⟨.A, 2, 2⟩ → Subgroup.center ↥J ≠ ⊥)) ∧
      (labL.n = 1 → labL.tag = .twE6 → E6TwoCompLabelT labJ) := by
  have hI : GGThmIHyp 3 B x L := hH.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hH.1.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨δ, hdat, huniq⟩ :=
    exists_ggTorsionDatum_unique_of_innerDiagOnLabel
      (fun lab => GGE6DepLabel lab) hI hDJ hBBs hMark
  obtain ⟨-, -, hδ3, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, labL, hlabL, hraw⟩ := hmark
  have hL : GGE6DepLabel labL :=
    GGDichotomy.rawDatum_elim_const (lab := labL) (Q := GGE6DepLabel labL)
      (largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨-, -, θ, hP, -⟩ := h
        exact hP) hraw)
  have htagL : labL.tag = .E6 ∨ labL.tag = .twE6 := by
    rcases hL with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  have hHasL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have hML : GGInnerDiagOnLabel (fun _ lab => lab = labL) 3 Bs L :=
    ggInnerDiagOn_relabel hrigid
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hMark) hlabL hHasL
  have hInnerJ : GGInnerDiagOn Bs J := by
    rcases GGInnerDiagOnLabel.elim_or hMark with hME | hMT
    · exact q1E6Three_holds G 3 B Bs x L D J hH.1
        (hME.mono_label fun _ h => ⟨h.1, rfl, h.2⟩)
    · exact q1TwE6Three_holds G 3 B Bs x L D J hH.1
        (hMT.mono_label fun _ h => ⟨h.1, rfl, h.2⟩)
  have markedJ (labJ : LargeEvenLabel) (hΛJ : LargeEvenInLambda2 labJ)
      (hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
      GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J :=
    ggInnerDiagOn_relabel hrigid hInnerJ hΛJ hHasJ
  by_cases h2 : 2 ≤ labL.n
  ·
    have hdatTag : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 δ
        (J.subgroupOf L) := by
      refine ⟨Nat.prime_three, by norm_num, hδ3, hδ1, hcomp, ?_⟩
      have hmark0 : LargeEvenMarking ↥L (fun lab _ _ I _ θ =>
          GGE6DepLabel lab ∧ ggInducedAut θ δ ∈ I) := ⟨hXc, labL, hlabL, hraw⟩
      refine largeEvenMarking_mono ?_ hmark0
      rintro lab R _ I F θ ⟨hP, hδI⟩
      exact ⟨(by rcases hP with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]), hδI⟩
    have hq : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => 2 ≤ lab.n) :=
      ⟨hXc, labL, hlabL, largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, -⟩ := h
        exact ⟨hs, hna, θ, h2⟩) hraw⟩
    have hE6mark := TablePThreeKG.ggTorsion_E6eps_unique_label
      (X := ↥L) (δ := δ) (J := J.subgroupOf L) hdatTag hq huniq
    obtain ⟨-, labOut, hlabOut, hrawOut⟩ := hE6mark
    have hExistsJ : ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
        GGHasLabel labJ
          (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) ∧
        E6CompLabel (2 ^ labOut.n) labJ :=
      GGDichotomy.rawDatum_elim_const (lab := labOut)
        (Q := ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
          GGHasLabel labJ
            (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) ∧
          E6CompLabel (2 ^ labOut.n) labJ)
        (largeEvenRawDatum_mono (fun R _ I F h => by
          obtain ⟨-, -, hJ⟩ := h.2.2
          exact hJ) hrawOut)
    obtain ⟨labJ, hlabJ, hhasSub, hE6⟩ := hExistsJ
    have hHasOut : GGHasLabel labOut (↥L ⧸ Subgroup.center ↥L) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawOut
    have hiso : GGLabelIso labL labOut :=
      hrigid labL labOut (↥L ⧸ Subgroup.center ↥L) hlabL hlabOut hHasL hHasOut
    have heq : labL = labOut := eq_of_ggLabelIso_of_e6Tag hiso htagL
    have hE6' : E6CompLabel (2 ^ labL.n) labJ := by
      rw [← heq] at hE6
      exact hE6
    have hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      ggHasLabel_of_mulEquiv
        (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hhasSub
    refine ⟨labL, labJ, hL, hlabL, hHasL, hML, hlabJ, hhasJ,
      markedJ labJ hlabJ hhasJ, fun _ => hE6', ?_, ?_⟩
    · intro h1
      omega
    · intro h1
      omega
  ·
    have h1le : 1 ≤ labL.n := hlabL.1
    have h1 : labL.n = 1 := by omega
    have hrawMM : LargeEvenRawDatumLegacy labL
        (fun R _ I F => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
            GGE6DepLabel labL ∧ ggInducedAut θ δ ∈ I) ∧ MarkedModel labL R) :=
      largeEvenRawDatum_markedModel hlabL (fun R _ I F h => h.2.1) hraw
    have hinndiag : LargeEvenLabelAll labL (LargeEvenSimpleGuard GGInndiagCommEq) := by
      rcases htagL with h | h
      · exact largeEvenLabelAll_inndiagComm_E6 h
      · exact largeEvenLabelAll_inndiagComm_twE6 hlabL h
    have hrawAll := hinndiag _ hrawMM
    obtain ⟨R, hR, I, F', hbase, hGuard⟩ := largeEvenRawDatum_exists hrawAll
    obtain ⟨⟨hs, hna, θ, hP, hδI⟩, hm⟩ := hbase
    have hEq : GGInndiagCommEq R I F' := hGuard hs hna
    have ht_mem : markTag labL ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
      rcases htagL with h | h <;>
        simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]
    have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag labL) 2 labL.n := by
      have hm0 : CFSG.Blueprint.LieModel R (markTag labL) (markRank labL)
          (markChar labL) (markDeg labL) := hm
      have h := hm0.chevalleyExceptionalModel ht_mem
      have hchar : markChar labL = 2 := by
        rcases htagL with h | h <;> simp [markChar, h]
      have hdeg : markDeg labL = labL.n := by
        rcases htagL with h | h <;> simp [markDeg, h]
      rw [hchar, hdeg] at h
      exact h
    rcases htagL with htagE | htagT
    ·
      have hchevE6 : CFSG.Blueprint.ChevalleyExceptionalModel R .E6 2 labL.n :=
        e6TwoLeaf_chevE6 hchev htagE
      obtain ⟨d, hdchar, hk, huntw, he⟩ :=
        e6TwoLeaf_index_E6 (p := 2) (f := labL.n) hchevE6
      obtain ⟨e⟩ := he
      have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
        rw [hk, h1, pow_one]
      obtain ⟨labJ, hlabJ, hhasSub, hpairW, hcentSub⟩ :=
        e6TwoLeaf_component (X := ↥L) (δ := δ) (J := J.subgroupOf L)
          θ hXc hδ3 hδ1 hcomp huniq hδI hEq d hdchar hdfield (Or.inl huntw) e
      obtain ⟨hW, hcentW⟩ := hpairW huntw
      have hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
        ggHasLabel_of_mulEquiv
          (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hhasSub
      have hcentJ : labJ = ⟨.A, 2, 2⟩ → Subgroup.center ↥J ≠ ⊥ := by
        intro hA hbot
        apply hcentW hA
        let eJ := Subgroup.subgroupOfEquivOfLe hJL
        have hmap : Subgroup.map (eJ : ↥(J.subgroupOf L) →* ↥J)
            (Subgroup.center ↥(J.subgroupOf L)) = ⊥ := by
          rw [Subgroup.map_center_eq eJ, hbot]
        rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        have hz' : eJ z ∈ Subgroup.map (eJ : ↥(J.subgroupOf L) →* ↥J)
            (Subgroup.center ↥(J.subgroupOf L)) :=
          ⟨z, hz, rfl⟩
        rw [hmap] at hz'
        have hz1 : eJ z = 1 := by simpa using hz'
        exact eJ.injective (by simpa using hz1)
      refine ⟨labL, labJ, hL, hlabL, hHasL, hML, hlabJ, hhasJ,
        markedJ labJ hlabJ hhasJ, ?_, ?_, ?_⟩
      · intro h2'
        omega
      · intro h1' _
        exact ⟨hW, hcentJ⟩
      · intro h1' htag
        rw [htagE] at htag
        exact absurd htag (by decide)
    ·
      have hchevT : CFSG.Blueprint.ChevalleyExceptionalModel R .twistedE6 2 labL.n :=
        e6TwoLeaf_chevTwE6 hchev htagT
      obtain ⟨d, hdchar, hk, huntw, he⟩ :=
        e6TwoLeaf_index_twE6 (p := 2) (f := labL.n) hchevT
      obtain ⟨e⟩ := he
      have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
        rw [hk, h1, pow_one]
      have hnotE6 : ¬ (∃ q : TauCeti.PrimePower, d.1 = .E6 q) := by
        rintro ⟨q1, hq1⟩
        obtain ⟨q2, hq2⟩ := huntw
        rw [hq1] at hq2
        cases hq2
      obtain ⟨labJ, hlabJ, hhasSub, -, hpairT⟩ :=
        e6TwoLeaf_component (X := ↥L) (δ := δ) (J := J.subgroupOf L)
          θ hXc hδ3 hδ1 hcomp huniq hδI hEq d hdchar hdfield (Or.inr huntw) e
      have hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
        ggHasLabel_of_mulEquiv
          (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hhasSub
      refine ⟨labL, labJ, hL, hlabL, hHasL, hML, hlabJ, hhasJ,
        markedJ labJ hlabJ hhasJ, ?_, ?_, ?_⟩
      · intro h2'
        omega
      · intro h1' htag
        rw [htag] at htagT
        exact absurd htagT (by decide)
      · intro h1' htag
        exact hpairT hnotE6

end OriginalE6ComponentTable

section ExactThreeE6ComponentTable

open CFSG.StandardType.TablePThreeKG
open CFSG.StandardType.ResJCubicBlock


private theorem e6Three_mark_data {G : Type} [Group G] {Bs J : Subgroup G}
    {lab : LargeEvenLabel}
    (h : GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs J) :
    LargeEvenInLambda2 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  obtain ⟨-, lab', hΛ', hraw⟩ := h
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, θ, hP⟩ := hQ
  have hlab : lab' = lab := hP.1
  subst lab'
  refine ⟨hΛ', ?_⟩
  unfold GGHasLabel
  refine largeEvenRawDatum_mono ?_ hraw
  intro R' _ I' F' hQ'
  obtain ⟨_, _, θ', _⟩ := hQ'
  exact ⟨θ'⟩

private theorem e6Three_mark_mono {G : Type} [Group G] {Bs J : Subgroup G}
    {lab : LargeEvenLabel}
    (h : GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs J)
    {P : LargeEvenLabel → Prop} (hP : P lab) :
    GGInnerDiagOnLabel (fun _ l => P l) 3 Bs J :=
  GGInnerDiagOnLabel.mono_label (fun l hl => by rw [hl]; exact hP) h

theorem e6CompLabel_false_of_not_twA_five
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    {q : ℕ} {lab : LargeEvenLabel}
    (hMark : GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs J)
    (hE6 : E6CompLabel q lab)
    (hres : ¬ (lab.tag = .twA ∧ lab.rank = 5)) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΛ, hHas⟩ := e6Three_mark_data hMark
  rcases hE6 with ⟨htag, hrk, _hn⟩ | ⟨htagD, hrk4, _hn⟩ | ⟨htri, _hn⟩ |
    ⟨hrk2, _hn3, hsign⟩
  ·
    rcases htag with hDtag | hTwDtag | hAtag | hTwAtag
    ·
      rcases ggThree_dvd_two_pow_sub_or_add lab.n with hminus | hplus
      · exact GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hminus, Or.inl ⟨hDtag, by omega⟩⟩)
      · exact GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hplus, Or.inl ⟨hDtag, by omega⟩⟩)
    ·
      rcases ggThree_dvd_two_pow_sub_or_add lab.n with hminus | hplus
      · exact GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hminus, Or.inr ⟨hTwDtag, by omega⟩⟩)
      · exact GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hplus, Or.inr ⟨hTwDtag, by omega⟩⟩)
    ·
      rcases ggThree_dvd_two_pow_sub_or_add lab.n with hminus | hplus
      ·
        obtain ⟨lab3, hΛ3, hLine3, hHas3⟩ :=
          GGResHyp.exists_lineJLabel_A3_of_compatible_splitLinear_marking hH hD
            (e6Three_mark_mono hMark ⟨hAtag, hminus⟩)
        have hLine := ggResLineJLabel_of_iso hLine3
          (ggLabelRigidInput_holds lab3 lab _ hΛ3 hΛ hHas3 hHas)
        rcases hLine with ⟨-, hr, -⟩ | ⟨-, hr, -⟩ <;> omega
      ·
        exact GGResHyp.actual_J_not_oppositeLinear_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hAtag, hplus⟩)
    ·
      exact absurd ⟨hTwAtag, hrk⟩ hres
  ·
    rcases htagD with hDtag | hTwDtag
    · rcases ggThree_dvd_two_pow_sub_or_add lab.n with hminus | hplus
      · exact GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hminus, Or.inl ⟨hDtag, by omega⟩⟩)
      · exact GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hplus, Or.inl ⟨hDtag, by omega⟩⟩)
    · rcases ggThree_dvd_two_pow_sub_or_add lab.n with hminus | hplus
      · exact GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hminus, Or.inr ⟨hTwDtag, by omega⟩⟩)
      · exact GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
          (e6Three_mark_mono hMark ⟨hplus, Or.inr ⟨hTwDtag, by omega⟩⟩)
  ·
    exact GGResHyp.not_small_J_label_of_A3 hH hD hΛ hHas (Or.inr (Or.inl htri))
  ·
    rcases hsign with ⟨-, hAtag⟩ | ⟨-, hTwAtag⟩
    · exact absurd (GGResHyp.rank_ge_three_of_A3_label hH hD hΛ hHas (Or.inl hAtag))
        (by omega)
    · exact absurd (GGResHyp.rank_ge_three_of_A3_label hH hD hΛ hHas (Or.inr hTwAtag))
        (by omega)


theorem e6Three_J_A2_four_false
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ l => l = (⟨.A, 2, 2⟩ : LargeEvenLabel)) 3 Bs J) :
    False := by
  obtain ⟨hΛ, hHas⟩ := e6Three_mark_data hMark
  have h3 := GGResHyp.rank_ge_three_of_A3_label hH hD hΛ hHas (Or.inl rfl)
  exact absurd h3 (by norm_num)

theorem e6Three_J_twA2_eight_false
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ l => l = (⟨.twA, 2, 3⟩ : LargeEvenLabel)) 3 Bs J) :
    False := by
  obtain ⟨hΛ, hHas⟩ := e6Three_mark_data hMark
  have h3 := GGResHyp.rank_ge_three_of_A3_label hH hD hΛ hHas (Or.inr rfl)
  exact absurd h3 (by norm_num)

theorem e6Three_J_twA4_two_false
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ l => l = (⟨.twA, 4, 1⟩ : LargeEvenLabel)) 3 Bs J) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΛ, hHas⟩ := e6Three_mark_data hMark
  obtain ⟨lab3, hΛ3, hLine3, hHas3⟩ :=
    GGResHyp.exists_lineJLabel_A3_of_compatible_unitary_marking_coprime hH hD
      (e6Three_mark_mono hMark ⟨rfl, by norm_num, by norm_num⟩)
  have hLine := ggResLineJLabel_of_iso hLine3
    (ggLabelRigidInput_holds lab3 _ _ hΛ3 hΛ hHas3 hHas)
  rcases hLine with ⟨-, hr, -⟩ | ⟨-, hr, -⟩ <;> norm_num at hr

theorem e6TwoCompLabel_false_of_not_twA_five
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    {lab : LargeEvenLabel}
    (hMark : GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs J)
    (hW : E6TwoCompLabelW lab ∨ E6TwoCompLabelT lab)
    (hres : ¬ (lab.tag = .twA ∧ lab.rank = 5)) : False := by
  rcases hW with hW | hT
  · unfold E6TwoCompLabelW at hW
    rcases hW with rfl | rfl | rfl
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inl ⟨?_, ?_, ?_⟩
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rfl
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inr (Or.inl ⟨Or.inr rfl, rfl, ?_⟩)
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)
    · exact e6Three_J_A2_four_false hH hD hMark
  · unfold E6TwoCompLabelT at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hres
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inr (Or.inl ⟨Or.inl rfl, rfl, ?_⟩)
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inl ⟨Or.inr (Or.inl rfl), rfl, ?_⟩
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)
    · exact e6Three_J_twA4_two_false hH hD hMark
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inr (Or.inr (Or.inr ⟨by norm_num, by norm_num, ?_⟩))
        · norm_num) (by rintro ⟨-, hr⟩; norm_num at hr)
    · exact e6CompLabel_false_of_not_twA_five (q := 2) hH hD hMark (by
        refine Or.inr (Or.inl ⟨Or.inr rfl, rfl, ?_⟩)
        · norm_num) (by rintro ⟨ht, -⟩; simp at ht)




theorem GGResHyp.relativeA5_J_card_automizer_of_A3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (hD : GGResLineJDatum p Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun p lab => lab.rank = 5 ∧
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) p Bs J) :
    Nat.card ↥(ggAutomizer J Bs) = 48 := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, _, _, θ₀, ⟨hrank, hrow⟩, _, _⟩ :=
    largeEvenRawDatum_exists hraw
  have hTorW := ggTBTorRelA5_holds 3 hp hp2 lab hΛ hrank hrow
  let Qmark : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : J ⧸ Subgroup.center J ≃* R,
        (lab.rank = 5 ∧ ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1))) ∧
          Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hraw' : LargeEvenRawDatum lab Qmark := hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, hpred, hN, hInd⟩, hTorGen⟩ :=
    largeEvenRawDatum_exists (hTorW Qmark hraw')
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces J θ hN hInd (b := b) hb
  have h3 : 3 ^ 3 ≤ Nat.card ↥(ggGamma J hN).range :=
    by
      have hEq : ggGamma J hN = ggGamma J (GGResHyp.Bs_le_normalizer_J hH) := by
        ext b; rfl
      rw [hEq]
      exact hH.cube_le_card_gamma_of_A3 hD
  have hTB : GGTorusTBGroup 3 3 R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN hBsI h3 h3
  have hTor : GGTorusTorData (ggTorMpm 3 lab) 3 (CartanMatrix.C 3)
      (CoxeterMatrix.B 3) J (ggGamma J hN).range :=
    hTorGen J (ggQuotHom θ) (ggGamma J hN).range hTB
  have hm : Odd (ggTorMpm 3 lab) := by
    unfold ggTorMpm
    split_ifs
    · exact ggHLT_odd_two_pow_sub_one hΛ.1
    · exact ggHLT_odd_two_pow_add_one hΛ.1
  have hpm : 3 ∣ ggTorMpm 3 lab := by
    unfold ggTorMpm
    split_ifs with hsub
    · exact hsub
    · rcases hrow with hrow | hrow
      · exact hrow.2
      · exact (hsub hrow.2).elim
  obtain ⟨φ, e, hφ, he⟩ := ggTBWeyl_of_torW hp2 hm hpm hBs hSC hN hTor
  rw [← Nat.card_congr e.toEquiv, ggCoxeterB_card 3 (by norm_num)]
  norm_num


theorem GGResHyp.exists_e6_exactThree_twisted_J_unitary_five
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L)
    (h3 : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) :
    ∃ labL labJ : LargeEvenLabel,
      LargeEvenInLambda2 labL ∧ GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labL) 3 Bs L ∧
      labL.tag = .twE6 ∧ 3 ∣ 2 ^ labL.n + 1 ∧
      LargeEvenInLambda2 labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J ∧
      labJ.tag = .twA ∧ labJ.rank = 5 ∧ labJ.n = labL.n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : GGResLineJDatum 3 Bs J .A3 := by
    rcases h3 with h3 | h3 <;> exact e6_exactThree_GGResLineJDatum_A3 h3
  obtain ⟨labL, labJ, hEL, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ,
    hTable, hW, hT⟩ := hH.exists_e6_original_J_marking_table hMark
  have hres : labJ.tag = .twA ∧ labJ.rank = 5 := by
    by_contra hn
    by_cases h2 : 2 ≤ labL.n
    · exact e6CompLabel_false_of_not_twA_five hH hD hMJ (hTable h2) hn
    · have h1 : labL.n = 1 := by have := hΛL.1; omega
      rcases hEL with ⟨he, -⟩ | ⟨ht, -⟩
      · exact e6TwoCompLabel_false_of_not_twA_five hH hD hMJ
          (Or.inl (hW h1 he).1) hn
      · exact e6TwoCompLabel_false_of_not_twA_five hH hD hMJ
          (Or.inr (hT h1 ht)) hn
  have field_same (h2 : 2 ≤ labL.n) : labJ.n = labL.n := by
    rcases hTable h2 with ⟨-, -, hpow⟩ | ⟨-, hr, -⟩ | ⟨ht, -⟩ | ⟨hr, -⟩
    · exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    · have := hres.2; omega
    · rw [hres.1] at ht; cases ht
    · have := hres.2; omega
  have hTw : labL.tag = .twE6 ∧ 3 ∣ 2 ^ labL.n + 1 := by
    rcases hEL with ⟨he, hsub⟩ | hTw
    · exfalso
      by_cases h2 : 2 ≤ labL.n
      · have hsubJ : 3 ∣ 2 ^ labJ.n - 1 := by rw [field_same h2]; exact hsub
        have hRel : GGInnerDiagOnLabel (fun p lab => lab.rank = 5 ∧
            ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
              (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) 3 Bs J :=
          GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = labJ)
            (fun _ h => h ▸ ⟨hres.2, Or.inr ⟨hres.1, hsubJ⟩⟩) hMJ
        have h48 := hH.relativeA5_J_card_automizer_of_A3 rfl hD hRel
        have h24 := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
        rw [h24] at h48
        norm_num at h48
      · have h1 : labL.n = 1 := by have := hΛL.1; omega
        rw [h1] at hsub
        norm_num at hsub
    · exact hTw
  have hn : labJ.n = labL.n := by
    by_cases h2 : 2 ≤ labL.n
    · exact field_same h2
    · have h1 : labL.n = 1 := by have := hΛL.1; omega
      have ht := hT h1 hTw.1
      rcases ht with heq | heq | heq | heq | heq | heq | heq
      all_goals rw [heq] at hres ⊢; simp_all
  exact ⟨labL, labJ, hΛL, hHasL, hML, hTw.1, hTw.2,
    hΛJ, hHasJ, hMJ, hres.1, hres.2, hn⟩
theorem GGResHyp.not_e6_exactThree_either_of_splitE6_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L) :
    ¬ (GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) := by
  intro h3
  have hME : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label
      (S := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) (fun _ h => Or.inl h) hMark
  obtain ⟨labL, labJ, hΛL, hHasL, hML, hTw, -⟩ :=
    hH.exists_e6_exactThree_twisted_J_unitary_five hME h3
  obtain ⟨-, lab0, hΛ0, hraw⟩ := hMark
  have hP0 : lab0.tag = .E6 ∧ 3 ∣ 2 ^ lab0.n - 1 :=
    GGDichotomy.rawDatum_elim_const
      (Q := lab0.tag = .E6 ∧ 3 ∣ 2 ^ lab0.n - 1)
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.choose_spec.1) hraw)
  have hHas0 : GGHasLabel lab0 (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have heq := eq_of_ggLabelIso_of_e6Tag
    (ggLabelRigidInput_holds lab0 labL _ hΛ0 hΛL hHas0 hHasL) (Or.inl hP0.1)
  rw [← heq, hP0.1] at hTw
  cases hTw


theorem GGResHyp.not_e6_exactThree_either_of_e6_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L) :
    ¬ (GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) := by
  intro h3
  have hD : GGResLineJDatum 3 Bs J .A3 := by
    rcases h3 with h3 | h3 <;> exact e6_exactThree_GGResLineJDatum_A3 h3
  obtain ⟨labL, labJ, hΛL, hHasL, hML, hTw, hplus,
    hΛJ, hHasJ, hMJ, hJtag, hJrank, hfield⟩ :=
    hH.exists_e6_exactThree_twisted_J_unitary_five hMark h3
  have hplusJ : 3 ∣ 2 ^ labJ.n + 1 := by rw [hfield]; exact hplus
  by_cases h1 : labJ.n = 1
  · have heq : labJ = ⟨.twA, 5, 1⟩ := by
      cases labJ
      simp_all
    exact hH.actual_J_not_unitary_six_two_for_A3 hD
      (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = labJ)
        (fun _ h => h.trans heq) hMJ)
  · exact hH.actual_J_not_unitary_six_for_A3_qplus_large hD
      (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = labJ)
        (fun _ h => h ▸ ⟨hJtag, hJrank, hplusJ, h1⟩) hMJ)

end ExactThreeE6ComponentTable


namespace E6ExactTwo

open CFSG CFSG.Monster.B.Geometry CFSG.StandardType.TablePThreeKG

private theorem e6_exact_two_survivor_det_ne_zero_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e)
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS ML S) :
    (Matrix.of fun i j : {i : Λ // i ∉ S} => (CL i.1 j.1 : ZMod 3)).det ≠ 0 := by
  classical
  let S0 : Finset (Fin 6) := S.map e.symm.toEmbedding
  have hS0 : S0.card = 2 := by simpa [S0] using hS
  let T : Type := {i : Fin 6 // i ∉ S0}
  let T' : Type := {i : Λ // i ∉ S}
  let eT : T ≃ T' :=
    { toFun := fun i => ⟨e i.1, by simpa [S0] using i.2⟩
      invFun := fun i => ⟨e.symm i.1, by simpa [S0] using i.2⟩
      left_inv := fun i => by apply Subtype.ext; simp
      right_inv := fun i => by apply Subtype.ext; simp }
  have hc0 : GGDeletedConnectedS CoxeterMatrix.E₆ S0 := by
    intro i j
    have hp := l05nBL_rtg_map
      (r := fun u v : T' => u ≠ v ∧ ML.M u.1 v.1 ≠ 2)
      (p := fun u v : T => u ≠ v ∧ CoxeterMatrix.E₆.M u.1 v.1 ≠ 2)
      eT.symm (fun u v huv => by
        refine ⟨fun h => huv.1 (eT.symm.injective h), ?_⟩
        simpa [hML, CoxeterMatrix.reindex_apply, eT, S0] using huv.2)
      (hc (eT i) (eT j))
    simpa using hp
  have hCLstd : ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j :=
    ggIntCartan_E6_entries_of_type hCL e hML
  have hsub : (Matrix.of fun i j : T' => (CL i.1 j.1 : ZMod 3)) =
      (Matrix.of fun i j : T =>
        (CartanMatrix.E 6 i.1 j.1 : ZMod 3)).submatrix eT.symm eT.symm := by
    ext i j
    change (CL i.1 j.1 : ZMod 3) =
      (CartanMatrix.E 6 (e.symm i.1) (e.symm j.1) : ZMod 3)
    rw [← hCLstd (e.symm i.1) (e.symm j.1)]
    simp
  have hdet : (Matrix.of fun i j : T' => (CL i.1 j.1 : ZMod 3)).det =
      (Matrix.of fun i j : T => (CartanMatrix.E 6 i.1 j.1 : ZMod 3)).det := by
    rw [hsub, Matrix.det_submatrix_equiv_self]
  rw [hdet]
  exact e6_exact_two_survivor_det_ne_zero hS0 hc0

private theorem e6_exact_two_gamma_card_ge_pow_four {G : Type} [Group G] [Finite G]
    {B Bs L D J K X Y : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs X J Y ggSelAny ggTypLE6) :
    3 ^ 4 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, htyp, hlin, hrefl, hpair, -, -, -, -, -, -, hconn, hclosJ⟩
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  let T : Type := {i : Λ // i ∉ S}
  let C : Matrix T T ℤ := CL.submatrix (Subtype.val : T → Λ) (Subtype.val : T → Λ)
  let M : CoxeterMatrix T := parMatrix ML {i | i ∉ S}
  have hC : GGIntCartan M C := by
    constructor
    · intro i
      simpa [M, C, Matrix.submatrix_apply] using hCL.1 i.1
    · intro i j hij
      have hij' : (i : Λ) ≠ j := fun hh => hij (Subtype.ext hh)
      simpa [M, C, parMatrix_apply, Matrix.submatrix_apply] using hCL.2 i.1 j.1 hij'
  obtain ⟨e, he⟩ := htyp
  have hdetMap : (C.map (Int.castRingHom (ZMod 3))).det ≠ 0 := by
    have h := e6_exact_two_survivor_det_ne_zero_reindex hCL e he hS hconn
    rw [show C.map (Int.castRingHom (ZMod 3)) =
      Matrix.of (fun i j : T => ((CL i.1 j.1 : ℤ) : ZMod 3)) from rfl]
    exact h
  have hdet : ((C.det : ℤ) : ZMod 3) ≠ 0 := by
    rwa [Int.cast_det]
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using (Fintype.card_congr e).symm
  have hcardT : Fintype.card T = 4 := by
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    change Fintype.card {i : Λ // i ∉ S} = 4
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub, hS, hcardΛ]
  have hrank : Matrix.rank (C.map (Int.castRingHom (ZMod 3))) = 4 := by
    rw [rank_map_eq_card_of_det_ne_zero hdet]
    exact hcardT
  have hbound := ggGamma_card_ge_cartan_rank (p := 3) (by norm_num)
    hH.1.2.1.2.1 (GGResHyp.Bs_le_normalizer_J hH) hC ι
    (fun i : T => φ (Sum.inl i.1)) (fun i : T => h (Sum.inl i.1))
    (fun i : T => α (Sum.inl i.1))
    (fun i v => hlin (Sum.inl i.1) v)
    (fun i j => by simpa [C, Matrix.submatrix_apply] using hpair i.1 j.1)
    (fun i => by
      rw [hclosJ]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  rw [hrank] at hbound
  simpa using hbound

private theorem actual_card_of_torW {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I)
    {m Mval N : ℕ} (hm3 : 3 ≤ m) (hodd : Odd Mval) (hpm : 3 ∣ Mval)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hTorW : GGTorusTorW 3 m Mval N C M R I)
    (hγ : 3 ^ m ≤ Nat.card (ggGamma J hN).range) :
    Nat.card ↥(ggAutomizer J Bs) = Nat.card M.Group := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 3) hm3).trans hγ
  have hTB : GGTorusTBGroup 3 m R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hγ h3
  obtain ⟨w, hw⟩ := hTorW ↥J (ggQuotHom θ) (ggGamma J hN).range hTB
  obtain ⟨hnk, _, _, _, _, _, _, _⟩ := ggTD_core hodd hpm hBs hSC hN w hw
  obtain ⟨e, _⟩ := ggTD_weyl hN hw (by norm_num) hBs hnk
  exact Nat.card_congr e.symm.toEquiv

private theorem gamma_card_eq_ggLAut_range {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {R : Type} [Group R]
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range =
      Nat.card ((ggLAut J θ).comp (Subgroup.inclusion hN)).range := by
  let ψ : ↥Bs →* MulAut R := (ggLAut J θ).comp (Subgroup.inclusion hN)
  have hker : ψ.ker = (ggGamma J hN).ker := by
    ext b
    constructor
    · intro h
      exact (ggGamma_eq_one_iff J hN b).mpr
        (mem_centralizer_of_ggLAut_eq_one J θ hJperf h)
    · intro h
      exact ggLAut_eq_one_of_mem_centralizer J θ ((ggGamma_eq_one_iff J hN b).mp h)
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := Subgroup.card_ker_mul_card_range (ggGamma J hN)
  rw [hker] at h1
  haveI : Finite ↥(ggGamma J hN).ker := Subtype.finite
  haveI : Finite ↥ψ.ker := Subtype.finite
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)).symm

private theorem false_of_actor_autR_bound {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I)
    (hBs : IsElemAbelian 3 Bs)
    (hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range)
    (hbound : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 X → Nat.card X < 3 ^ 3) : False := by
  let ψ : ↥Bs →* MulAut R := (ggLAut J θ).comp (Subgroup.inclusion hN)
  have hXsub : ((ψ.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact hBI b b.2
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hXab : IsElemAbelian 3 ψ.range := isElemAbelian_range hBc hBp ψ
  have hlt := hbound ψ.range hXsub hXab
  have hEq : Nat.card (ggGamma J hN).range = Nat.card ψ.range := by
    simpa [ψ] using gamma_card_eq_ggLAut_range hJperf θ hN
  rw [hEq] at hγ4
  omega

private theorem false_of_actor_lift_bound {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I)
    (hBs : IsElemAbelian 3 Bs)
    (hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range)
    (hbound : ∀ (L' : Type) [Group L'] [Finite L'],
      ∀ (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ →
        ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < 3 ^ 3) : False := by
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hAab : IsElemAbelian 3 A := isElemAbelian_range hBc hBp (ggGamma J hN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggLAut J θ ⟨b, hN b.2⟩, hBI b b.2, fun l => by
      simpa [ggBeta_eq] using ggBeta_ggQuotHom J hN θ b l⟩
  have hlt : Nat.card ↥(ggGamma J hN).range < 3 ^ 3 := by
    simpa [A] using hbound ↥J (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hJperf A hAab hAI
  have hlt4 : Nat.card ↥(ggGamma J hN).range < 3 ^ 4 := by omega
  exact (not_lt_of_ge hγ4) hlt4


private theorem exists_labelAll_markJ {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {labJ : LargeEvenLabel}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J)
    {P : LargeEvenRawCont}
    (hAll : LargeEvenLabelAll labJ P) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : ↥J ⧸ Subgroup.center ↥J ≃* R),
      P R I F ∧ (∀ b (hb : b ∈ Bs),
        ggLAut J θ ⟨b, hH.Bs_le_normalizer_J hb⟩ ∈ I) := by
  obtain ⟨hJperf, lab0, hΛ0, hraw0⟩ := hMark
  obtain ⟨R0, hR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw0
  obtain ⟨hs0, hna0, θ0, hP0⟩ := hQ0
  have hlab0 : lab0 = labJ := hP0.1
  subst hlab0
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists (hAll _ hraw0)
  obtain ⟨⟨hs, hna, θ, hP⟩, hPall⟩ := hQ
  exact ⟨R, hR, I, F, θ, hPall, fun b hb =>
    ggLAut_mem_of_induces J θ hP.2.1 hP.2.2 hb⟩

end E6ExactTwo

open E6ExactTwo CFSG.Monster.B.Geometry CFSG.StandardType.TablePThreeKG
@[expose] def GGTwE6ExactTwoPSU5Residual {G : Type} [Group G] [Finite G]
    (Bs L J : Subgroup G) : Prop :=
  ∃ labL labJ : LargeEvenLabel,
    labL = ⟨.twE6, 0, 1⟩ ∧ labJ = ⟨.twA, 4, 1⟩ ∧
    LargeEvenInLambda2 labL ∧ GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧
    GGInnerDiagOnLabel (fun _ lab => lab = labL) 3 Bs L ∧
    LargeEvenInLambda2 labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
    GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J

section ExactTwoTableConsumeCertificates


theorem GGResHyp.not_e6_exactTwo_either_of_splitE6_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L) :
    ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6) := by
  intro hD
  have hMarkGGE6 : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hMark
  obtain ⟨labL, labJ, hGL, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ, hTable, -, -⟩ :=
    GGResHyp.exists_e6_original_J_marking_table hH hMarkGGE6
  obtain ⟨hperf0, lab0, hΛ0, hraw0⟩ := hMark
  obtain ⟨R0, hR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw0
  obtain ⟨-, -, θ0, hP0⟩ := hQ0
  have hGL0 : GGE6DepLabel lab0 := hP0.1.1
  have hspl0 : 3 ∣ 2 ^ lab0.n - 1 := hP0.1.2
  have hHas0 : GGHasLabel lab0 (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
  have hiso : GGLabelIso labL lab0 :=
    ggLabelRigidInput_holds labL lab0 _ hΛL hΛ0 hHasL hHas0
  have hEq : labL = lab0 := eq_of_ggLabelIso_of_e6Tag hiso (by
    rcases hGL with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h)
  have hsplL : 3 ∣ 2 ^ labL.n - 1 := by rw [hEq]; exact hspl0
  obtain ⟨tL, rL, nL⟩ := labL
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  have htagL : tL = .E6 := by
    rcases hGL with ⟨h, -⟩ | ⟨h, hplus⟩
    · exact h
    · exfalso
      have hplus' : 3 ∣ 2 ^ nL + 1 := by simpa using hplus
      have hspl' : 3 ∣ 2 ^ nL - 1 := by simpa using hsplL
      exact (not_dvd_two_pow_add_one_of_dvd_sub_one Nat.prime_three (by norm_num) hspl') hplus'
  subst htagL
  have hΛL' := hΛL
  simp only [LargeEvenInLambda2] at hΛL'
  have hrL : rL = 0 := hΛL'.2
  have hnL1 : 1 ≤ nL := hΛL'.1
  have hnL2 : 2 ≤ nL := by
    by_contra h
    have h1 : nL = 1 := by omega
    subst h1
    norm_num at hsplL
  subst hrL
  have hE6 := hTable hnL2
  have hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    rcases hD with hDL | hDK
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDL
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDK
  have hAJ : Nat.card ↥(ggAutomizer J Bs) = 120 ∨ Nat.card ↥(ggAutomizer J Bs) = 192 := by
    rcases hD with hDL | hDK
    · exact ggResLeviDatumExact2_E6_automizerJ_card hDL
    · exact ggResLeviDatumExact2_E6_automizerJ_card hDK
  have hN := GGResHyp.Bs_le_normalizer_J hH
  have hJperf : commutator ↥J = ⊤ := hMJ.1
  have hnJ1 : 1 ≤ nJ := hΛJ.1
  have hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
    have h34 : 3 ^ 3 ≤ 3 ^ 4 := by norm_num
    exact h34.trans hγ4
  rcases hE6 with ⟨htags5, hrank5, hq5⟩ | ⟨htags4, hrank4, hq4⟩ |
    ⟨htri, hqTri⟩ | ⟨hrank2, hqA2, hmods⟩
  ·
    rcases htags5 with ht | ht | ht | ht
    ·
      subst ht
      subst hrank5
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := by rw [hnEq]; exact hsplL
      have hplusJ : ¬ 3 ∣ 2 ^ nJ + 1 :=
        not_dvd_two_pow_add_one_of_dvd_sub_one Nat.prime_three (by norm_num) hminusJ
      have hLiftAll := largeEvenLabelAll_torusLift_D (lab := ⟨.D, 5, nJ⟩) rfl hΛJ
        (by norm_num) (by norm_num) hminusJ
      have hTorAll := ggTBTorDHigh_split (p := 3) (lab := ⟨.D, 5, nJ⟩)
        Nat.prime_three (by norm_num) hΛJ (by norm_num) rfl hminusJ
      have hAll := largeEvenLabelAll_and hLiftAll hTorAll
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      obtain ⟨hLift, hTorW⟩ := hP
      have hγ : 3 ^ 5 ≤ Nat.card (ggGamma J hN).range := by
        simpa using GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
      have hTorW' : GGTorusTorW 3 5 (2 ^ nJ - 1) 5 (CartanMatrix.D 5)
          (ggCoxeterMatrixD 5) R I := by
        simpa [ggTorEnn, ggTorMpm, hminusJ, hplusJ] using hTorW
      have hcard := actual_card_of_torW (m := 5) (Mval := 2 ^ nJ - 1)
        hH hJperf θ hN hBI (by norm_num) (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
        hminusJ hTorW' hγ
      have hMcard : Nat.card (ggCoxeterMatrixD 5).Group = 1920 := by
        rw [OrthF3.card_coxeterD_eq 5 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 1920 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
    ·
      subst ht
      subst hrank5
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := by rw [hnEq]; exact hsplL
      have hTorAll := largeEvenLabelAll_relD_twD_split (p := 3) (n := nJ) (ℓ := 5)
        Nat.prime_three (by norm_num) hnJ1 (by norm_num) hminusJ
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 4 (2 ^ nJ - 1) 4 (CartanMatrix.B 4)
          (CoxeterMatrix.B 4) R I := by
        simpa [ggTorMpm, hminusJ] using hP
      have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ nJ - 1)
        hH hJperf θ hN hBI (by norm_num) (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
        hminusJ hTorW' hγ4
      have hMcard : Nat.card (CoxeterMatrix.B 4).Group = 384 := by
        rw [ggCoxeterB_card 4 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 384 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
    ·
      subst ht
      subst hrank5
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := by rw [hnEq]; exact hsplL
      have hplusJ : ¬ 3 ∣ 2 ^ nJ + 1 :=
        not_dvd_two_pow_add_one_of_dvd_sub_one Nat.prime_three (by norm_num) hminusJ
      have hTorAll := ggTorusTorW_lin_label (p := 3) (n := nJ) (l := 5)
        Nat.prime_three (by norm_num) (by norm_num) (by simpa [ggTorM] using hminusJ)
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 4 (2 ^ nJ - 1) 5 (CartanMatrix.A 5)
          (CoxeterMatrix.A 5) R I := by
        simpa [ggTorM, ggTorEnn, hminusJ, hplusJ] using hP
      have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ nJ - 1)
        hH hJperf θ hN hBI (by norm_num) (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
        hminusJ hTorW' hγ4
      have hMcard : Nat.card (CoxeterMatrix.A 5).Group = 720 := by
        rw [l05nK3a_card_coxeterA 5]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 720 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
    ·
      subst ht
      subst hrank5
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := by rw [hnEq]; exact hsplL
      have hTorAll := ggTBTorRelA5_holds (p := 3) Nat.prime_three (by norm_num)
        ⟨.twA, 5, nJ⟩ hΛJ rfl (Or.inr ⟨rfl, hminusJ⟩)
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 3 (2 ^ nJ - 1) 3 (CartanMatrix.C 3)
          (CoxeterMatrix.B 3) R I := by
        simpa [ggTorMpm, hminusJ] using hP
      have hcard := actual_card_of_torW (m := 3) (Mval := 2 ^ nJ - 1)
        hH hJperf θ hN hBI (by norm_num) (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
        hminusJ hTorW' hγ3
      have hMcard : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
        rw [ggCoxeterB_card 3 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 48 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
  ·
    rcases htags4 with ht | ht
    ·
      subst ht
      subst hrank4
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq4
      subst nL
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := hsplL
      have hrow : GGResRowAt ggRowTwoNode 3 J L := by
        refine ⟨⟨.D, 4, nJ⟩, ⟨.E6, 0, nJ⟩, hΛJ, hΛL, hHasJ, hHasL, ?_⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hminusJ, rfl⟩))
      exact hnoRowL hrow
    ·
      subst ht
      subst hrank4
      have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq4
      have hminusJ : 3 ∣ 2 ^ nJ - 1 := by rw [hnEq]; exact hsplL
      have hTorAll := largeEvenLabelAll_relD_twD_split (p := 3) (n := nJ) (ℓ := 4)
        Nat.prime_three (by norm_num) hnJ1 (by norm_num) hminusJ
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 3 (2 ^ nJ - 1) 3 (CartanMatrix.B 3)
          (CoxeterMatrix.B 3) R I := by
        simpa [ggTorMpm, hminusJ] using hP
      have hcard := actual_card_of_torW (m := 3) (Mval := 2 ^ nJ - 1)
        hH hJperf θ hN hBI (by norm_num) (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
        hminusJ hTorW' hγ3
      have hMcard : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
        rw [ggCoxeterB_card 3 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 48 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
  ·
    have hAll := NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all (p := 3)
      Nat.prime_three (by norm_num) hΛJ htri
    obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
    exact false_of_actor_autR_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
  ·
    rcases hmods with ⟨-, htA⟩ | ⟨-, htTwA⟩
    · subst htA
      subst hrank2
      have hAll := largeEvenLabelAll_card_lt_A2_all (p := 3) Nat.prime_three (by norm_num)
        (lab := ⟨.A, 2, nJ⟩) rfl rfl
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      exact false_of_actor_autR_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
    · subst htTwA
      subst hrank2
      have hAll := largeEvenLabelAll_lift_card_lt_unitaryThree_all (p := 3)
        Nat.prime_three (by norm_num) hΛJ rfl rfl
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      exact false_of_actor_lift_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP


theorem GGResHyp.rowTwoNode_of_e6_exactTwo_either_of_splitE6_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6) :
    GGResRowAt ggRowTwoNode 3 J L := by
  classical
  by_contra hnoRowL
  exact hH.not_e6_exactTwo_either_of_splitE6_L hMark hnoRowL hD

theorem GGResHyp.twE6_component_table_of_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L) :
    ∃ labL labJ : LargeEvenLabel,
      labL.tag = .twE6 ∧ 3 ∣ 2 ^ labL.n + 1 ∧
      LargeEvenInLambda2 labL ∧ GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labL) 3 Bs L ∧
      LargeEvenInLambda2 labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labJ) 3 Bs J ∧
      (2 ≤ labL.n → E6CompLabel (2 ^ labL.n) labJ) ∧
      (labL.n = 1 → E6TwoCompLabelT labJ) := by
  classical
  have hMarkGGE6 : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hMark
  obtain ⟨labL, labJ, hGL, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ, hTable, hW, hT⟩ :=
    GGResHyp.exists_e6_original_J_marking_table hH hMarkGGE6
  obtain ⟨hperf0, lab0, hΛ0, hraw0⟩ := hMark
  obtain ⟨R0, hR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw0
  obtain ⟨-, -, θ0, hP0⟩ := hQ0
  have hGL0 : GGE6DepLabel lab0 := hP0.1.1
  have htag0 : lab0.tag = .twE6 := hP0.1.2.1
  have hplus0 : 3 ∣ 2 ^ lab0.n + 1 := hP0.1.2.2
  have hHas0 : GGHasLabel lab0 (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
  have hiso : GGLabelIso labL lab0 :=
    ggLabelRigidInput_holds labL lab0 _ hΛL hΛ0 hHasL hHas0
  have hEq : labL = lab0 := eq_of_ggLabelIso_of_e6Tag hiso (by
    rcases hGL with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h)
  have htagL : labL.tag = .twE6 := by rw [hEq]; exact htag0
  have hplusL : 3 ∣ 2 ^ labL.n + 1 := by rw [hEq]; exact hplus0
  exact ⟨labL, labJ, htagL, hplusL, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ,
    hTable, fun h1 => hT h1 htagL⟩


theorem GGResHyp.twE6_exactTwo_either_classification
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L) :
    GGTwE6ExactTwoPSU5Residual (G := G) Bs L J := by
  classical
  obtain ⟨labL, labJ, htagL, hplusL, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ, hTable, hT⟩ :=
    GGResHyp.twE6_component_table_of_marking hH hMark
  have hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    rcases hD with hDL | hDK
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDL
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDK
  have hAJ : Nat.card ↥(ggAutomizer J Bs) = 120 ∨
      Nat.card ↥(ggAutomizer J Bs) = 192 := by
    rcases hD with hDL | hDK
    · exact ggResLeviDatumExact2_E6_automizerJ_card hDL
    · exact ggResLeviDatumExact2_E6_automizerJ_card hDK
  have hN := GGResHyp.Bs_le_normalizer_J hH
  have hJperf : commutator ↥J = ⊤ := hMJ.1
  have hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
    have h34 : 3 ^ 3 ≤ 3 ^ 4 := by norm_num
    exact h34.trans hγ4
  obtain ⟨tL, rL, nL⟩ := labL
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  have htagLt : tL = .twE6 := htagL
  have hplusLn : 3 ∣ 2 ^ nL + 1 := hplusL
  subst tL
  have hΛLn := hΛL
  simp only [LargeEvenInLambda2] at hΛLn
  have hrL : rL = 0 := hΛLn.2
  have hnL1 : 1 ≤ nL := hΛLn.1
  subst hrL
  by_cases h2 : 2 ≤ nL
  ·
    have hE6 := hTable h2
    exfalso
    rcases hE6 with ⟨htags5, hrank5, hq5⟩ | ⟨htags4, hrank4, hq4⟩ |
      ⟨htri, hqTri⟩ | ⟨hrank2, hqA2, hmods⟩
    ·
      rcases htags5 with ht | ht | ht | ht
      ·
        subst ht
        subst hrank5
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
        have hplusJ : 3 ∣ 2 ^ nJ + 1 := by rw [hnEq]; exact hplusLn
        have hminusJ : ¬ 3 ∣ 2 ^ nJ - 1 :=
          not_dvd_two_pow_sub_one_of_dvd_add_one Nat.prime_three (by norm_num) hplusJ
        have hoddJ : Odd (2 ^ nJ + 1) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : nJ ≠ 0)
          rw [hk, pow_succ]
          exact ⟨2 ^ k, by omega⟩
        have hLiftAll := largeEvenLabelAll_torusLift_D_nonsplit
          (lab := ⟨.D, 5, nJ⟩) rfl (by norm_num) Nat.prime_three (by norm_num) hplusJ
        have hTorAll := largeEvenLabelAll_relD_D_ns (p := 3) (n := nJ) (ℓ := 5)
          Nat.prime_three (by norm_num) (by omega) (by norm_num) ⟨2, by norm_num⟩ hplusJ
        have hAll := largeEvenLabelAll_and hLiftAll hTorAll
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
        obtain ⟨hLift, hTorW⟩ := hP
        have hTorW' : GGTorusTorW 3 4 (2 ^ nJ + 1) 4 (CartanMatrix.B 4)
            (CoxeterMatrix.B 4) R I := by
          simpa [ggTorMpm, hminusJ] using hTorW
        have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ nJ + 1)
          hH hJperf θ hN hBI (by norm_num) hoddJ hplusJ hTorW' hγ4
        have hMcard : Nat.card (CoxeterMatrix.B 4).Group = 384 := by
          rw [ggCoxeterB_card 4 (by norm_num)]
          norm_num [Nat.factorial]
        have hcard' : Nat.card ↥(ggAutomizer J Bs) = 384 := by
          simpa [hMcard] using hcard
        rw [hcard'] at hAJ
        rcases hAJ with h | h <;> omega
      ·
        subst ht
        subst hrank5
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
        have hplusJ : 3 ∣ 2 ^ nJ + 1 := by rw [hnEq]; exact hplusLn
        have hminusJ : ¬ 3 ∣ 2 ^ nJ - 1 :=
          not_dvd_two_pow_sub_one_of_dvd_add_one Nat.prime_three (by norm_num) hplusJ
        have hoddJ : Odd (2 ^ nJ + 1) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : nJ ≠ 0)
          rw [hk, pow_succ]
          exact ⟨2 ^ k, by omega⟩
        have hTorAll := ggTBTorD_holds 3 Nat.prime_three (by norm_num) ⟨.twD, 5, nJ⟩ hΛJ
          (Or.inr ⟨rfl, hplusJ, ⟨2, by norm_num⟩⟩)
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
        have hTorW' : GGTorusTorW 3 4 (2 ^ nJ + 1) 5 (CartanMatrix.D 5)
            (ggCoxeterMatrixD 5) R I := by
          simpa [ggTorEnn, ggTorMpm, hplusJ, hminusJ] using hP
        have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ nJ + 1)
          hH hJperf θ hN hBI (by norm_num) hoddJ hplusJ hTorW' hγ4
        have hMcard : Nat.card (ggCoxeterMatrixD 5).Group = 1920 := by
          rw [OrthF3.card_coxeterD_eq 5 (by norm_num)]
          norm_num [Nat.factorial]
        have hcard' : Nat.card ↥(ggAutomizer J Bs) = 1920 := by
          simpa [hMcard] using hcard
        rw [hcard'] at hAJ
        rcases hAJ with h | h <;> omega
      ·
        subst ht
        subst hrank5
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
        have hplusJ : 3 ∣ 2 ^ nJ + 1 := by rw [hnEq]; exact hplusLn
        have hminusJ : ¬ 3 ∣ 2 ^ nJ - 1 :=
          not_dvd_two_pow_sub_one_of_dvd_add_one Nat.prime_three (by norm_num) hplusJ
        have hTorAll := ggTBTorRelA5_holds (p := 3) Nat.prime_three (by norm_num)
          ⟨.A, 5, nJ⟩ hΛJ (by norm_num) (Or.inl ⟨rfl, hplusJ⟩)
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
        have hTorW' : GGTorusTorW 3 3 (2 ^ nJ + 1) 3 (CartanMatrix.C 3)
            (CoxeterMatrix.B 3) R I := by
          simpa [ggTorMpm, hminusJ] using hP
        have hcard := actual_card_of_torW (m := 3) (Mval := 2 ^ nJ + 1)
          hH hJperf θ hN hBI (by norm_num)
          (by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : nJ ≠ 0)
            rw [hk, pow_succ]
            exact ⟨2 ^ k, by omega⟩)
          hplusJ hTorW' hγ3
        have hMcard : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
          rw [ggCoxeterB_card 3 (by norm_num)]
          norm_num [Nat.factorial]
        have hcard' : Nat.card ↥(ggAutomizer J Bs) = 48 := by
          simpa [hMcard] using hcard
        rw [hcard'] at hAJ
        rcases hAJ with h | h <;> omega
      ·
        subst ht
        subst hrank5
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq5
        have hplusJ : 3 ∣ 2 ^ nJ + 1 := by rw [hnEq]; exact hplusLn
        have hTorAll := ggTorusTorW_uni_six_three_label_all (f := nJ) (by omega) hplusJ
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
        have hTorW' : GGTorusTorW 3 4 (2 ^ nJ + 1) 5 (CartanMatrix.A 5)
            (CoxeterMatrix.A 5) R I := hP
        have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ nJ + 1)
          hH hJperf θ hN hBI (by norm_num)
          (by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : nJ ≠ 0)
            rw [hk, pow_succ]
            exact ⟨2 ^ k, by omega⟩)
          hplusJ hTorW' hγ4
        have hMcard : Nat.card (CoxeterMatrix.A 5).Group = 720 := by
          rw [l05nK3a_card_coxeterA 5]
          norm_num [Nat.factorial]
        have hcard' : Nat.card ↥(ggAutomizer J Bs) = 720 := by
          simpa [hMcard] using hcard
        rw [hcard'] at hAJ
        rcases hAJ with h | h <;> omega
    ·
      rcases htags4 with ht | ht
      ·
        subst ht
        subst hrank4
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq4
        subst nL
        have hrow : GGResRowAt ggRowTwoNode 3 J L := by
          refine ⟨⟨.D, 4, nJ⟩, ⟨.twE6, 0, nJ⟩, hΛJ, hΛL, hHasJ, hHasL, ?_⟩
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hplusLn, rfl⟩))
        exact hnoRowL hrow
      ·
        subst ht
        subst hrank4
        have hnEq : nJ = nL := Nat.pow_right_injective le_rfl hq4
        have hplusJ : 3 ∣ 2 ^ nJ + 1 := by rw [hnEq]; exact hplusLn
        have hminusJ : ¬ 3 ∣ 2 ^ nJ - 1 :=
          not_dvd_two_pow_sub_one_of_dvd_add_one Nat.prime_three (by norm_num) hplusJ
        have hTorAll := largeEvenLabelAll_relD_twD_ns (p := 3) (n := nJ) (ℓ := 4)
          Nat.prime_three (by norm_num) (by omega) (by norm_num) ⟨2, by norm_num⟩ hplusJ
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
        have hTorW' : GGTorusTorW 3 3 (2 ^ nJ + 1) 3 (CartanMatrix.B 3)
            (CoxeterMatrix.B 3) R I := by
          simpa [ggTorMpm, hminusJ] using hP
        have hcard := actual_card_of_torW (m := 3) (Mval := 2 ^ nJ + 1)
          hH hJperf θ hN hBI (by norm_num)
          (by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : nJ ≠ 0)
            rw [hk, pow_succ]
            exact ⟨2 ^ k, by omega⟩)
          hplusJ hTorW' hγ3
        have hMcard : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
          rw [ggCoxeterB_card 3 (by norm_num)]
          norm_num [Nat.factorial]
        have hcard' : Nat.card ↥(ggAutomizer J Bs) = 48 := by
          simpa [hMcard] using hcard
        rw [hcard'] at hAJ
        rcases hAJ with h | h <;> omega
    ·
      subst htri
      have hAll := NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all (p := 3)
        Nat.prime_three (by norm_num) hΛJ rfl
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      exact false_of_actor_autR_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
    ·
      rcases hmods with ⟨-, htA⟩ | ⟨-, htTwA⟩
      · subst htA
        subst hrank2
        have hAll := largeEvenLabelAll_card_lt_A2_all (p := 3) Nat.prime_three (by norm_num)
          (lab := ⟨.A, 2, nJ⟩) rfl rfl
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
        exact false_of_actor_autR_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
      · subst htTwA
        subst hrank2
        have hAll := largeEvenLabelAll_lift_card_lt_unitaryThree_all (p := 3)
          Nat.prime_three (by norm_num) hΛJ rfl rfl
        obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
        exact false_of_actor_lift_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
  ·
    have hn1 : nL = 1 := by omega
    subst nL
    have hT2 := hT rfl
    unfold E6TwoCompLabelT at hT2
    rcases hT2 with hlab | hlab | hlab | hlab | hlab | hlab | hlab
    ·
      cases hlab
      exfalso
      have hTorAll := ggTorusTorW_uni_six_three_label_all (f := 1) (by norm_num) (by norm_num)
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 4 (2 ^ 1 + 1) 5 (CartanMatrix.A 5)
          (CoxeterMatrix.A 5) R I := hP
      have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ 1 + 1)
        hH hJperf θ hN hBI (by norm_num) (by norm_num) (by norm_num) hTorW' hγ4
      have hMcard : Nat.card (CoxeterMatrix.A 5).Group = 720 := by
        rw [l05nK3a_card_coxeterA 5]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 720 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
    ·
      cases hlab
      exfalso
      have hrow : GGResRowAt ggRowTwoNode 3 J L := by
        refine ⟨⟨.D, 4, 1⟩, ⟨.twE6, 0, 1⟩, hΛJ, hΛL, hHasJ, hHasL, ?_⟩
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by norm_num, rfl⟩))
      exact hnoRowL hrow
    ·
      cases hlab
      exfalso
      have hAll := NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all (p := 3)
        Nat.prime_three (by norm_num) hΛJ rfl
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      exact false_of_actor_autR_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
    ·
      cases hlab
      exfalso
      have hTorAll := ggTBTorD_holds 3 Nat.prime_three (by norm_num) ⟨.twD, 5, 1⟩ hΛJ
        (Or.inr ⟨rfl, by norm_num, ⟨2, by norm_num⟩⟩)
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 4 (2 ^ 1 + 1) 5 (CartanMatrix.D 5)
          (ggCoxeterMatrixD 5) R I := by
        simpa [ggTorEnn, ggTorMpm] using hP
      have hcard := actual_card_of_torW (m := 4) (Mval := 2 ^ 1 + 1)
        hH hJperf θ hN hBI (by norm_num) (by norm_num) (by norm_num) hTorW' hγ4
      have hMcard : Nat.card (ggCoxeterMatrixD 5).Group = 1920 := by
        rw [OrthF3.card_coxeterD_eq 5 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 1920 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega
    ·
      cases hlab
      exact ⟨⟨.twE6, 0, 1⟩, ⟨.twA, 4, 1⟩, rfl, rfl, hΛL, hHasL, hML,
        hΛJ, hHasJ, hMJ⟩
    ·
      cases hlab
      exfalso
      have hAll := largeEvenLabelAll_lift_card_lt_unitaryThree_all (p := 3)
        Nat.prime_three (by norm_num) hΛJ rfl rfl
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hAll
      exact false_of_actor_lift_bound hJperf θ hN hBI hH.1.2.1.2.1 hγ4 hP
    ·
      cases hlab
      exfalso
      have hTorAll := largeEvenLabelAll_relD_twD_ns (p := 3) (n := 1) (ℓ := 4)
        Nat.prime_three (by norm_num) (by norm_num) (by norm_num) ⟨2, by norm_num⟩
        (by norm_num)
      obtain ⟨R, hR, I, F, θ, hP, hBI⟩ := exists_labelAll_markJ hH hMJ hTorAll
      have hTorW' : GGTorusTorW 3 3 (2 ^ 1 + 1) 3 (CartanMatrix.B 3)
          (CoxeterMatrix.B 3) R I := by
        simpa [ggTorMpm] using hP
      have hcard := actual_card_of_torW (m := 3) (Mval := 2 ^ 1 + 1)
        hH hJperf θ hN hBI (by norm_num) (by norm_num) (by norm_num) hTorW' hγ3
      have hMcard : Nat.card (CoxeterMatrix.B 3).Group = 48 := by
        rw [ggCoxeterB_card 3 (by norm_num)]
        norm_num [Nat.factorial]
      have hcard' : Nat.card ↥(ggAutomizer J Bs) = 48 := by
        simpa [hMcard] using hcard
      rw [hcard'] at hAJ
      rcases hAJ with h | h <;> omega

open CFSG.ClassicalGroups.UnitaryFlag

theorem GGResHyp.actual_gamma_J_card_le_three_four
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) 3 Bs J) :
    Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range ≤ 3 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple₀, _hnonab₀, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS, hN, hBsI⟩ := hP₀
  have htag : tag = .twA := hS.1
  have hrank : rank = 4 := hS.2.1
  have hn : n = 1 := hS.2.2
  subst htag
  subst hrank
  subst hn
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨_hS, hN', hBsI'⟩ := hP
  let d : ℕ := 5
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ 1)))
      (LargeEvenGUSet (Fin d) F (2 ^ 1))
  have hf1 : 1 ≤ 1 := by norm_num
  have hd3 : 3 ≤ d := by norm_num [d]
  have hp : Nat.Prime 3 := by norm_num
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hcop_d : ¬ 3 ∣ d := by norm_num [d]
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN' = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    refine ⟨ggBeta J θ hN' b, ggBeta_mem J θ hN' hBsI' b, fun l => ?_⟩
    rw [ggBeta_ggQuotHom J hN' θ b l, hgamma]
  have hcov : LineU.UnitaryCoverAt 1 d F :=
    LineU.unitaryUniversalCover_holds 1 d F hFcard (by norm_num [d])
      (by norm_num [d])
  obtain ⟨φ, hφs, hφker, hdiagA⟩ :=
    LineU.exists_diagModel_coprime (L' := ↥J) (K := F) (n := 1) (d := d) (p := 3)
      (hK := hFcard) (hn := hf1) (hd := hd3) (hp := hp) (hpq := hpq) (hpd := hcop_d)
      (hcov := hcov) (ψ := ggQuotHom θ) (hψ := ggQuotHom_surjective θ)
      (hker := le_of_eq (ker_ggQuotHom θ)) (hperf := hperfJ) (hA := hAe) (hAI := hAI)
  have hdiag : ∀ a ∈ A, ∃ t : Fin d → F, LineU.ActsDiagU φ a t := by
    simpa [A] using hdiagA
  let hUfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hFcard hf1
  have hM : UnitTB.Model φ := ⟨hUfield, hφs, hφker⟩
  have hcard : Nat.card A ≤ 3 ^ (d - 1) :=
    UnitTB.card_diagonal_pow_le (φ := φ) hM hd3 hp hAe.2 hdiag
  simpa [A, d] using hcard


theorem GGResHyp.gamma_J_card_eq_three_four_of_e6_exactTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J) :
    Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range = 3 ^ 4 := by
  have hMJ' : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) 3 Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
      ⟨by simpa only [hP.1] using (show
        (⟨.twA, 4, 1⟩ : LargeEvenLabel).tag = .twA ∧
        (⟨.twA, 4, 1⟩ : LargeEvenLabel).rank = 4 ∧
        (⟨.twA, 4, 1⟩ : LargeEvenLabel).n = 1 from ⟨rfl, rfl, rfl⟩), hP.2⟩) hMJ
  refine le_antisymm (hH.actual_gamma_J_card_le_three_four hMJ') ?_
  rcases hD with hDL | hDK
  · exact e6_exact_two_gamma_card_ge_pow_four hH hDL
  · exact e6_exact_two_gamma_card_ge_pow_four hH hDK

theorem GGResHyp.card_Bs_six_or_seven_of_e6_exactTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J) :
    Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hCpow : ∃ k, Nat.card C = 3 ^ k :=
    IsPGroup.iff_card.mp ((CFSG.Open.IsElemAbelian.isPGroup hH.1.2.1.2.1).to_le
      (show C ≤ Bs from inf_le_left))
  obtain ⟨k, hk⟩ := hCpow
  have hCge : 3 ^ 2 ≤ Nat.card C := by
    have hDle : D ≤ C := by
      rw [hH.1.2.2.1.2.2.2.2.2.2]
      exact inf_le_inf hH.1.2.1.1 le_rfl
    have h := Subgroup.card_le_of_le hDle
    rwa [hH.1.2.2.1.2.2.1] at h
  have hCle : Nat.card C ≤ 3 ^ 3 := GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hk ▸ hCge)
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hk ▸ hCle)
  have hker : (ggGamma J hH.Bs_le_normalizer_J).ker =
      (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card (ggGamma J hH.Bs_le_normalizer_J).ker = Nat.card C := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard : Nat.card Bs = 3 ^ 4 * Nat.card C := by
    have hc := TableB.card_range_mul_card_ker (ggGamma J hH.Bs_le_normalizer_J)
    rw [hH.gamma_J_card_eq_three_four_of_e6_exactTwo hD hMJ, hkerCard] at hc
    exact hc.symm
  have hcases : k = 2 ∨ k = 3 := by omega
  rw [hcard, hk]
  rcases hcases with rfl | rfl
  · left; norm_num
  · right; norm_num

theorem GGResHyp.twE6_exactTwo_either_card_classification
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L) :
    GGTwE6ExactTwoPSU5Residual (G := G) Bs L J ∧
      Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range = 3 ^ 4 ∧
      (Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7) := by
  have hres := hH.twE6_exactTwo_either_classification hMark hD hnoRowL
  obtain ⟨labL, labJ, heL, heJ, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ⟩ :=
    hH.twE6_exactTwo_either_classification hMark hD hnoRowL
  have hMJ' : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J := by simpa only [heJ] using hMJ
  exact ⟨hres, hH.gamma_J_card_eq_three_four_of_e6_exactTwo hD hMJ',
    hH.card_Bs_six_or_seven_of_e6_exactTwo hD hMJ'⟩

private theorem largeEvenRawDatumLegacy_twA4_torW {Q : CFSG.Assembly.LargeEvenRawCont}
    (hQ : CFSG.Assembly.LargeEvenRawDatumLegacy (⟨.twA, 4, 1⟩ : LargeEvenLabel) Q) :
    CFSG.Assembly.LargeEvenRawDatumLegacy (⟨.twA, 4, 1⟩ : LargeEvenLabel)
      (fun R _ I F => Q R I F ∧
        GGTorusTorW 3 3 3 4 (CartanMatrix.A 4) (CoxeterMatrix.A 4) R I) := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ',
    ggTorusTorW_unitary_liftTwo (K := K) (n := 1) (N := 4) hK le_rfl (by norm_num)
      Nat.prime_three (by norm_num) (by norm_num)⟩

theorem GGResHyp.twA_four_two_J_automizer_card_of_e6_exactTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J) :
    Nat.card ↥(ggAutomizer J Bs) = 120 := by
  classical
  have hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    rcases hD with hDL | hDK
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDL
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDK
  have hN := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMJ
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ :=
    CFSG.StandardType.Legacy.largeEvenRawDatum_exists
      ((largeEvenRawDatum_legacy _ _).2 hraw)
  obtain ⟨hs₀, hna₀, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hlab_eq, -, -⟩ := hP₀
  subst lab
  have hTorRaw := largeEvenRawDatumLegacy_twA4_torW hraw
  obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.Legacy.largeEvenRawDatum_exists
    ((largeEvenRawDatum_legacy _ _).mpr hTorRaw)
  obtain ⟨hQ0, hTorW⟩ := hQ
  obtain ⟨hs, hna, θ, hP⟩ := hQ0
  obtain ⟨-, hNraw, hBIraw⟩ := hP
  have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    exact ggLAut_mem_of_induces J θ hN hBIraw hb
  have hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    (by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans hγ4
  have hcard := actual_card_of_torW (m := 3) (Mval := 3) (N := 4)
    hH hJperf θ hN hBI (by norm_num) (by norm_num) (by norm_num) hTorW hγ3
  simpa [l05nK3a_card_coxeterA, Nat.factorial] using hcard

private theorem twA_four_two_J_torData_of_e6_exactTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J) :
    GGTorusTorData 3 4 (CartanMatrix.A 4) (CoxeterMatrix.A 4) ↥J
      (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
  classical
  have hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    rcases hD with hDL | hDK
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDL
    · exact e6_exact_two_gamma_card_ge_pow_four hH hDK
  have hN := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMJ
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ :=
    CFSG.StandardType.Legacy.largeEvenRawDatum_exists
      ((largeEvenRawDatum_legacy _ _).2 hraw)
  obtain ⟨hs₀, hna₀, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hlab_eq, -, -⟩ := hP₀
  subst lab
  have hTorRaw := largeEvenRawDatumLegacy_twA4_torW hraw
  obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.Legacy.largeEvenRawDatum_exists
    ((largeEvenRawDatum_legacy _ _).mpr hTorRaw)
  obtain ⟨hQ0, hTorW⟩ := hQ
  obtain ⟨hs, hna, θ, hP⟩ := hQ0
  obtain ⟨-, hNraw, hBIraw⟩ := hP
  have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    exact ggLAut_mem_of_induces J θ hN hBIraw hb
  have hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    (by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans hγ4
  have hTB : GGTorusTBGroup 3 3 R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hH.1.2.1.2.1 hH.1.2.1.2.2.2
      hJperf θ hN hBI hγ3 hγ3
  exact hTorW ↥J (ggQuotHom θ) (ggGamma J hN).range hTB

theorem GGResHyp.twA_four_two_J_weyl_of_e6_exactTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J) :
    GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer J Bs) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨w, hw⟩ := twA_four_two_J_torData_of_e6_exactTwo hH hD hMJ
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ :=
    exists_ggLinData (p := 3) (G := G) (Bs := Bs) hH.1.2.1.2.1
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ :=
    ggTD_linearData (by norm_num : Odd (3 : ℕ)) (dvd_refl 3)
      hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw (by norm_num : (3 : ℕ) ≠ 2)
    hH.1.2.1.2.1 hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A 4).1 i]
    norm_num
  refine ⟨e, fun i => ?_⟩
  rw [he i]
  exact ggIsReflection_of_eq_reflection (by norm_num : (3 : ℕ) ≠ 2)
    ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))



@[expose] def GGTwE6KTypeCases {Idx : Type} (MK : CoxeterMatrix Idx) : Prop :=
  (∃ e : Fin 5 ≃ Idx, MK = (CoxeterMatrix.A 5).reindex e) ∨
  (∃ e : Fin 5 ≃ Idx, MK = (CoxeterMatrix.B 5).reindex e) ∨
  (∃ e : Fin 5 ≃ Idx, MK = (ggCoxeterMatrixD 5).reindex e) ∨
  (∃ e : Fin 6 ≃ Idx, MK = (CoxeterMatrix.A 6).reindex e) ∨
  (∃ e : Fin 6 ≃ Idx, MK = (CoxeterMatrix.B 6).reindex e) ∨
  (∃ e : Fin 6 ≃ Idx, MK = (ggCoxeterMatrixD 6).reindex e) ∨
  (∃ e : Fin 6 ≃ Idx, MK = CoxeterMatrix.E₆.reindex e)

private theorem ggTwE6KTypeCases_of_card {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} (hMK : GGIsWeylMatrix MK)
    (hcard : Fintype.card Idx = 5 ∨ Fintype.card Idx = 6) :
    GGTwE6KTypeCases MK := by
  rcases hMK with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ |
    ⟨e6, hE6⟩ | ⟨e7, hE7⟩ | ⟨e8, hE8⟩ | ⟨e4, hF4⟩ | ⟨e2, hG2⟩
  · have hncard : n = Fintype.card Idx := by simpa using Fintype.card_congr e
    rcases hcard with h5 | h6
    · have hn5 : n = 5 := by omega
      subst hn5
      exact Or.inl ⟨e, hA⟩
    · have hn6 : n = 6 := by omega
      subst hn6
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hA⟩)))
  · have hncard : n = Fintype.card Idx := by simpa using Fintype.card_congr e
    rcases hcard with h5 | h6
    · have hn5 : n = 5 := by omega
      subst hn5
      exact Or.inr (Or.inl ⟨e, hB⟩)
    · have hn6 : n = 6 := by omega
      subst hn6
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hB⟩))))
  · have hncard : n = Fintype.card Idx := by simpa using Fintype.card_congr e
    rcases hcard with h5 | h6
    · have hn5 : n = 5 := by omega
      subst hn5
      exact Or.inr (Or.inr (Or.inl ⟨e, hD⟩))
    · have hn6 : n = 6 := by omega
      subst hn6
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hD⟩)))))
  · have h6 : Fintype.card Idx = 6 := by simpa using (Fintype.card_congr e6).symm
    have h65 : Fintype.card Idx = 5 ∨ Fintype.card Idx = 6 := hcard
    rcases h65 with h5 | h6'
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e6, hE6⟩)))))
  · have h7 : Fintype.card Idx = 7 := by simpa using (Fintype.card_congr e7).symm
    omega
  · have h8 : Fintype.card Idx = 8 := by simpa using (Fintype.card_congr e8).symm
    omega
  · have h4 : Fintype.card Idx = 4 := by simpa using (Fintype.card_congr e4).symm
    omega
  · have h2 : Fintype.card Idx = 2 := by simpa using (Fintype.card_congr e2).symm
    omega

@[expose] def GGTwE6KDiagramClassified {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
    (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
    GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
    ggTypLE6 ML MK ∧
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    (∀ o, GGIsReflection p (φ o)) ∧
    (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
    (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
    ggSelAny (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i))
      (LinearIndependent (ZMod p) h) ∧
    (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
    (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
    ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
    ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)) ∧
    GGDeletedConnectedS ML S ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∧
    (Nat.card Λa = 1 ∨ Nat.card Λa = 2) ∧
    GGTwE6KTypeCases MK

theorem ggTwE6KDiagramClassified_of_witness
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hS2 : S.card = 2) (hA1 : 1 ≤ Nat.card Λa) (hA3 : Nat.card Λa ≤ 3)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (htyp : ggTypLE6 ML MK)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hsel : ggSelAny (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i))
      (LinearIndependent (ZMod p) h))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hdel : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)))
    (hAa : Nat.card Λa = 1 ∨ Nat.card Λa = 2)
    (hCases : GGTwE6KTypeCases MK) :
    GGTwE6KDiagramClassified (G := G) p Bs L J K :=
  ⟨Λ, inferInstance, inferInstance, S, Λa, inferInstance, inferInstance, ML, CL, MK, CK, V,
    inferInstance, inferInstance, ι, φ, h, α, hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp,
    hlin, hrefl, hpairL, hpairK, hsel, hfL, hfK, hclosL, hclosK, hdel, hclosJ, hAa, hCases⟩

theorem GGTwE6KDiagramClassified.toDatum {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (h : GGTwE6KDiagramClassified (G := G) p Bs L J K) :
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypLE6 := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ, hAa, hCases⟩ := h
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩

theorem ggParabolic_E6_exact_two_actual_A4
    {Λ H : Type} [DecidableEq Λ] [Group H] {M : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS M S)
    {X J : Subgroup H} (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i))
    (hcard : Nat.card ↥J = 120) :
    ∃ (a : Fin 4 ≃ {i : Λ // i ∉ S})
      (g : (CoxeterMatrix.A 4).Group ≃* ↥J),
      ∀ i, (g ((CoxeterMatrix.A 4).simple i) : H) = φ (a i) := by
  rcases ggParabolic_E6_exact_two_actual e hM hS hc f φ hf hJ with
      ⟨a, g, hg⟩ | ⟨a, g, hg⟩
  · exact ⟨a, g, hg⟩
  · exfalso
    have h192 : Nat.card ↥J = 192 := by
      rw [← Nat.card_congr g.toEquiv, OrthF3.card_coxeterD_eq 4 (by omega)]
      norm_num
    omega

theorem GGResHyp.e6_exactTwo_other_diagram_of_twA_four_two_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {X Y : Subgroup G}
    (hXY : (X = L ∧ Y = K) ∨ (X = K ∧ Y = L))
    (hD : GGResLeviDatumExact2 3 Bs X J Y ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J)
    (hno3 : ¬ GGResLeviDatumExact3 3 Bs Y J X ggSelAny ggTypAny) :
    GGTwE6KDiagramClassified (G := G) 3 Bs X J Y := by
  classical
  have hDE : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6 := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hD
    · exact Or.inr hD
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let T : Type := {i : Λ // i ∉ S}
  have htypD := htyp
  obtain ⟨e6, -⟩ := htyp
  have hΛ6 : Fintype.card Λ = 6 := by simpa using Fintype.card_congr e6.symm
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]; simp
  have hcomp : Fintype.card T = Fintype.card Λ - S.card := by
    change Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hT4 : Fintype.card T = 4 := by omega
  obtain ⟨eJ, -⟩ := GGResHyp.twA_four_two_J_weyl_of_e6_exactTwo hH hDE hMJ
  have hA4W : GGIsWeylMatrix (CoxeterMatrix.A 4) := ggHLT_weyl_A (n := 4) (by norm_num)
  have hA4T := ggWeylTypeData_of_isWeylMatrix hA4W
  have hJType : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    rw [← Nat.card_congr eJ.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr eJ).toEquiv]
    simpa using hA4T
  obtain ⟨fK, hfK⟩ := hfKx
  have hKType : GGWeylTypeData (Fintype.card (T ⊕ Λa))
      (Nat.card ↥(ggAutomizer Y Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer Y Bs))) := by
    have h := ggWeylTypeData_of_isWeylMatrix hWMK
    rw [← Nat.card_congr fK.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fK).toEquiv]
    exact h
  have h120 := GGResHyp.twA_four_two_J_automizer_card_of_e6_exactTwo hH hDE hMJ
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by rw [hbot]; simp
    omega
  have h2any : GGResLeviDatumExact2 3 Bs X J Y ggSelAny ggTypAny :=
    ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, trivial, hlin, hrefl,
      hpairL, hpairK, hsel, hfLx, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  have hrev :=
    ggResLeviDatumExact2_reverse_card_one_two_of_not_exact3 h2any hno3
  have hIdx : Fintype.card (T ⊕ Λa) = 5 ∨ Fintype.card (T ⊕ Λa) = 6 := by
    rcases hrev with hrev1 | hrev2
    · obtain ⟨r, hr, hJrev⟩ :=
        ggResLeviDatumCard_rank_eq_of_weylTypeData (hD := hrev1) hJne hKType
      have hr4 : r = 4 := ggWeylTypeData_rank_eq hJrev hJType
      left; omega
    · obtain ⟨r, hr, hJrev⟩ :=
        ggResLeviDatumCard_rank_eq_of_weylTypeData (hD := hrev2) hJne hKType
      have hr4 : r = 4 := ggWeylTypeData_rank_eq hJrev hJType
      right; omega
  have hsum : Fintype.card (T ⊕ Λa) = Fintype.card T + Fintype.card Λa := Fintype.card_sum
  have hAa : Nat.card Λa = 1 ∨ Nat.card Λa = 2 := by
    have hf : Nat.card Λa = Fintype.card Λa := Nat.card_eq_fintype_card
    rcases hIdx with h5 | h6
    · left; omega
    · right; omega
  have hCases := ggTwE6KTypeCases_of_card hWMK hIdx
  exact ggTwE6KDiagramClassified_of_witness (p := 3) hS2 hA1 hA3 hWML hCLL hWMK hCKK
    htypD hlin hrefl hpairL hpairK hsel hfLx ⟨fK, hfK⟩ hclosL hclosK hdel hclosJ hAa hCases

theorem GGResHyp.e6_exactTwo_K_diagram_of_twA_four_two_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6)
    (hMJ : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J)
    (hno3 : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    GGTwE6KDiagramClassified (G := G) 3 Bs L J K :=
  hH.e6_exactTwo_other_diagram_of_twA_four_two_J (Or.inl ⟨rfl, rfl⟩) hD hMJ hno3


end ExactTwoTableConsumeCertificates


open CFSG CFSG.Assembly


theorem rank_six_CK_E6_of_witness
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hK6 : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 6)
    (hBs6 : Nat.card Bs = 3 ^ 6) :
    ∃ e : Fin 6 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
      ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let φK : {i : Λ // i ∉ S} ⊕ Λa → MulAut ↥Bs :=
    fun o => φ (o.map Subtype.val id)
  have hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    rw [hclosK]
    congr 1
    ext z
    constructor
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
  have hlinK : ∀ o w, ggLin (p := 3) ι (φK o) w =
      w - α (o.map Subtype.val id) w • h (o.map Subtype.val id) :=
    fun o w => hlin (o.map Subtype.val id) w
  have hdiag : ∀ o, CK o o = 2 := fun o => hCKK.1 o
  have hrank_core : Matrix.rank (CK.map (Int.castRingHom (ZMod 3))) + 1 ≤
      Module.finrank (ZMod 3) V :=
    ggResK_rank_core_add_one hH hlinK hpairK hdiag hgen
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hVcard : Nat.card V = 3 ^ 6 := by
    have hcard_add : Nat.card (Additive ↥Bs) = Nat.card ↥Bs :=
      (Nat.card_congr (Additive.ofMul : ↥Bs ≃ Additive ↥Bs)).symm
    rw [← Nat.card_congr ι.toEquiv, hcard_add, hBs6]
  haveI : Fintype V := Fintype.ofFinite V
  have hVdim : Module.finrank (ZMod 3) V = 6 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := V)
    have hVcardF : Fintype.card V = 3 ^ 6 := by
      rw [← Nat.card_eq_fintype_card]
      exact hVcard
    rw [hVcardF, show Fintype.card (ZMod 3) = 3 by simp [ZMod.card]] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < 3) h).symm
  have hrank_le : Matrix.rank (CK.map (Int.castRingHom (ZMod 3))) ≤ 5 := by
    omega
  have hr : Matrix.rank (CK.map (Int.castRingHom (ZMod 3))) <
      Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) := by
    rw [hK6]
    omega
  rcases ggIntCartan_A_or_E6_of_rank_lt hWMK hCKK (by norm_num : (3 : ℕ) ≠ 2) hr with
    ⟨n, e, hn1, hpd, he⟩ | ⟨hp3, e, he⟩
  · exfalso
    have hn : n = 6 := by
      have hcard : Fintype.card (Fin n) = Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) :=
        Fintype.card_congr e
      rw [hK6] at hcard
      simpa using hcard
    subst hn
    norm_num at hpd
  · exact ⟨e, he⟩

@[expose] def GGTwE6KDiagramClassifiedRefinement {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
    (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
    GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
    ggTypLE6 ML MK ∧
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    (∀ o, GGIsReflection p (φ o)) ∧
    (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
    (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
    ggSelAny (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i))
      (LinearIndependent (ZMod p) h) ∧
    (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
    (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
    ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
    ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)) ∧
    GGDeletedConnectedS ML S ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∧
    (Nat.card Λa = 1 ∨ Nat.card Λa = 2) ∧
    GGTwE6KTypeCases MK ∧
    (Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7) ∧
    (Nat.card Bs = 3 ^ 6 → Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 6 →
      ∃ e : Fin 6 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
        ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j)

section TwE6KRankSixCertificates


theorem GGResHyp.twE6_exactTwo_K_diagram_and_Bs_count
    [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hno3K : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    GGTwE6KDiagramClassified (G := G) 3 Bs L J K ∧
      (Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7) := by
  obtain ⟨labL, labJ, heL, heJ, hΛL, hHasL, hML, hΛJ, hHasJ, hMJ⟩ :=
    hH.twE6_exactTwo_either_classification hMark (Or.inl hD) hnoRowL
  have hMJ' : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel))
      3 Bs J := by simpa only [heJ] using hMJ
  exact ⟨hH.e6_exactTwo_K_diagram_of_twA_four_two_J hD hMJ' hno3K,
    hH.card_Bs_six_or_seven_of_e6_exactTwo (Or.inl hD) hMJ'⟩

theorem GGResHyp.twE6_exactTwo_K_refinement
    [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hno3K : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    GGTwE6KDiagramClassifiedRefinement (G := G) 3 Bs L J K := by
  obtain ⟨hK, hBs⟩ :=
    hH.twE6_exactTwo_K_diagram_and_Bs_count hMark hD hnoRowL hno3K
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ, hAa, hCases⟩ := hK
  refine ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ, hAa, hCases, hBs, ?_⟩
  intro h6 hK6
  exact rank_six_CK_E6_of_witness (ML := ML) (CL := CL)
    hH hWMK hCKK hlin hpairK hclosK hK6 h6

end TwE6KRankSixCertificates

end CFSG.StandardType

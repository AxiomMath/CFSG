module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPlus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOne
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenLabels
import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusForcing
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOnePlus
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem oppSup_ggFixG_eq_ggHyperplane (Bs : Subgroup G) (r : MulAut ↥Bs) :
    ggFixG Bs r = ggHyperplane Bs r := by
  have h : ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
    ext b; rfl
  rw [ggFixG, ggHyperplane, h]

theorem ggRootCompGenAvoiding_nbr_of_avoidOn_cfg {S : ℕ → LargeEvenLabel → Prop}
    (hKG : GGRootGenKGAvoidOn S) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK : GGInnerDiagOnLabel S p Bs K) : GGRootCompGenAvoiding p Bs K := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hKc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := S p)
    (fun lab hlab hs => hKG p lab hp hp2 hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hyBs hKy.2.1 hKc θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
    (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hKc θ hBsN hlift)
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

section LabelRigid

theorem ggInnerDiagOnLabel_linPhiTwo_of_a5 {p : ℕ} {Bs A : Subgroup G}
    (hInn : GGInnerDiagOn Bs A) (hlab : GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A))
    (hp : p ∣ 2 ^ 2 + 1) : GGInnerDiagOnLabel GGRootGenLinPhiTwoLabel p Bs A := by
  obtain ⟨hcomm, labA, hlabA, hraw⟩ := hInn
  have hhas : GGHasLabel labA (↥A ⧸ Subgroup.center ↥A) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨θ⟩
  have hΛ : LargeEvenInLambda2 (⟨.A, 5, 2⟩ : LargeEvenLabel) :=
    ⟨by norm_num, by norm_num, fun _ => by norm_num⟩
  have hEq : labA = ⟨.A, 5, 2⟩ :=
    ggLabelIso_a5_right (ggLabelRigidInput_holds labA _ _ hlabA hΛ hhas hlab)
  refine ⟨hcomm, labA, hlabA, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP⟩
  refine ⟨hs, hna, θ, ⟨?_, hP⟩⟩
  rw [hEq]
  exact ⟨hp, le_rfl, Or.inl rfl⟩

end LabelRigid

theorem ggRealized_le_sup_of_rankOneFamily {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L K : Subgroup G} (hBs : IsElemAbelian p Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hfam : GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e))
    {t : MulAut ↥Bs} (htR : t ∈ ggCoxRefl CoxeterMatrix.F₄ e) (hr : GGIsReflection p t)
    {Jt : Subgroup G} (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G)))) :
    Jt ≤ L ⊔ K := by
  obtain ⟨hSH, hSC, hBS, htS, -⟩ := hfam.1 t htR
  set S := ggRankOneFrom p L (L ⊔ K) Bs t with hSdef
  set C := Subgroup.centralizer (ggFixG Bs t : Set G) with hCdef
  rw [← oppSup_ggFixG_eq_ggHyperplane] at hSC
  have htJ : t ∈ ggAutomizer Jt Bs := by
    obtain ⟨g, hgJ, hgN, hg⟩ := hind
    exact mem_ggAutomizer_iff.mpr ⟨g, hgJ, hgN, hg⟩
  have hpS : p ∣ Nat.card S := by
    obtain ⟨g, hgS, hgN, hg⟩ := mem_ggAutomizer_iff.mp htS
    obtain ⟨b, hb⟩ : ∃ b : ↥Bs, t b ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hr.ne_one Fact.out (MulEquiv.ext hcon)
    have hdS : g * (b : G) * g⁻¹ * (b : G)⁻¹ ∈ S := by
      have h : (b : G) * g⁻¹ * (b : G)⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hBS b.2) g⁻¹).mp (S.inv_mem hgS)
      have h' := S.mul_mem hgS h
      rwa [← mul_assoc, ← mul_assoc] at h'
    have hdBs : g * (b : G) * g⁻¹ * (b : G)⁻¹ ∈ Bs :=
      Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN b).mp b.2) (Bs.inv_mem b.2)
    have hd1 : g * (b : G) * g⁻¹ * (b : G)⁻¹ ≠ 1 := by
      intro h1
      apply hb
      apply Subtype.ext
      rw [hg b]
      exact mul_inv_eq_one.mp h1
    have hord : orderOf (g * (b : G) * g⁻¹ * (b : G)⁻¹) = p :=
      orderOf_eq_prime (hBs.2 _ hdBs) hd1
    have hordS : orderOf (⟨_, hdS⟩ : ↥S) = p := by
      rw [Subgroup.orderOf_mk]
      exact hord
    rw [← hordS]
    exact orderOf_dvd_natCard _
  have hSO : ¬ S ≤ CFSG.Open.lBalancePrimeCore p C := not_le_lBalancePrimeCore_of_dvd hpS
  have hJt' : CFSG.Open.lBalanceIsPComponent p C Jt :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p C Jt
      hJC).mp hpc
  rcases lBalanceIsPComponent_eq_or_commute hSC hSO hJt' with h | h
  · rw [h]
    exact hSH
  · exfalso
    have hcomm : ∀ g ∈ S, ∀ k ∈ Jt, g * k = k * g := by
      intro g hg k hk
      have h1 : k * g * k⁻¹ * g⁻¹ = 1 := by
        have hmem : ⁅k, g⁆ ∈ ⁅Jt, S⁆ := Subgroup.commutator_mem_commutator hk hg
        rw [h, Subgroup.mem_bot] at hmem
        rw [commutatorElement_def] at hmem
        exact hmem
      have h2 : k * g = g * k := by
        have := mul_inv_eq_one.mp h1
        calc k * g = k * g * k⁻¹ * k := by group
          _ = g * k := by rw [this]
      exact h2.symm
    have hBs2 : ∀ b ∈ Bs, b * b = 1 → b = 1 := fun b hb h =>
      eq_one_of_mul_self_eq_one_of_isElemAbelian (Nat.Prime.odd_of_ne_two Fact.out hp2) hBs hb h
    exact hr.ne_one Fact.out (ggAutomizer_eq_one_of_commute hBs2 hBS hcomm htS htJ hr.1)

theorem ggOppPlus_le_sup_of_rankOneFamily {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D' J' K : Subgroup G} (hc' : GGConfig p B Bs x L D' J') (hNT : GGNoTransvection p Bs)
    {d : G} {A : Subgroup G} (hnbr : GGNbr p B x D' J' d A)
    (hInn : GGInnerDiagOnLabel GGRootGenLinPhiTwoLabel p Bs A)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    (hfam : GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e))
    (hAAW : ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    A ≤ L ⊔ K := by
  obtain ⟨hpp, hEl, -, -, -⟩ := hc'.tableB_facts
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := hc'.1.2.2.2.2.2.1.2.1
  have hAind : (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    have h := Fintype.card_congr e'
    simp at h
  have hgen := ggRootCompGenAvoiding_nbr_of_avoidOn_cfg ggRootGenKGAvoidOn_linPhiTwo hc' hnbr hInn
  rw [hgen 1]
  refine iSup_le fun t => iSup_le fun Jt => iSup_le fun hJt => ?_
  obtain ⟨-, hr, hind, hJA, hJC, hpc⟩ := hJt
  have htA : t ∈ ggAutomizer A Bs := by
    obtain ⟨g, hgJ, hgN, hg⟩ := hind
    exact mem_ggAutomizer_iff.mpr ⟨g, hJA hgJ, hgN, hg⟩
  have htW := hAAW htA
  obtain ⟨i, g, hig⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hpp hp2 hEl hNT _
    hAind (Fin 4) CoxeterMatrix.F₄ hpres.1 hG2 e hpres.2 ⟨t, htW⟩ hr
  have htR : t ∈ ggCoxRefl CoxeterMatrix.F₄ e :=
    ⟨g, i, by rw [← hig]⟩
  exact ggRealized_le_sup_of_rankOneFamily hp2 hEl hfam htR hr hind hJC hpc

section Assembled

theorem ggF4QGeFourOppPlus_plane_le_sup_at (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K)
    (hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hLim : GGCentralImage .POmegaMinus 4 f L)
    (hεL : ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs), ∀ i, GGIsReflection p
      ((ε ((CoxeterMatrix.B 3).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hfam : ∀ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' →
        GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e')) :
    p = 5 ∧ f = 2 ∧ ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
      (w : CoxeterMatrix.F₄.Group) (n : G),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' ∧ n ∈ L ⊔ K ∧
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((((e' (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs
        ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) : Set G) ∧
      ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
      D' = ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∧
      J' = LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) ∧
      D' = Subgroup.closure {x, d} ∧ LargeEvenStdSub p B x L D' J' ∧
      GGConfig p B Bs x L D' J' ∧ GGNbr p B x D' J' d A ∧
      A = ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J' ∧
      A.map (MulAut.conj n).toMonoidHom = A ∧ J' ≤ A ∧
      GGHasLabel ⟨.A, 3, f⟩ (↥J' ⧸ Subgroup.center ↥J') ∧ Subgroup.center ↥J' = ⊥ ∧
      GGInnerDiagOn Bs A ∧ GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A) ∧
      GGCentralImage .PSL 6 2 A ∧
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) d A ∧
      ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
      A ≤ L ⊔ K := by
  obtain ⟨hp5, hf2, e', w, n, hpres, hnLK, hnN, hn, hnc, D', J', d, A, hD', hJ', hD'x, hStd, hc',
    hnbr, hAdef, hAn, hJA, hhJ, hZJ, hInnA, hhA, hAimg, hEnd, hLA⟩ :=
    ggF4QGeFourOppPlus_plane_at hLB hB3 hNPLA hR hW hq hNb hWF4 hf hpq hLim hεL hfam
  have hNT : GGNoTransvection p Bs := hR.2.2.2.1
  have hInnLab : GGInnerDiagOnLabel GGRootGenLinPhiTwoLabel p Bs A :=
    ggInnerDiagOnLabel_linPhiTwo_of_a5 hInnA hhA (by rw [hp5]; norm_num)
  have hle : A ≤ L ⊔ K :=
    ggOppPlus_le_sup_of_rankOneFamily hc' hNT hnbr hInnLab hpres (hfam e' hpres) hEnd.2.2.2.1
  exact ⟨hp5, hf2, e', w, n, hpres, hnLK, hnN, hn, hnc, D', J', d, A, hD', hJ', hD'x, hStd, hc',
    hnbr, hAdef, hAn, hJA, hhJ, hZJ, hInnA, hhA, hAimg, hEnd, hLA, hle⟩

theorem ggF4N2OmegaK_altPlane (hLB : GGLBalanceInput) (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 5 B Bs x L D J) (hW : GGSecFiveWeylCase' 5 B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo 5 Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr 5 B x D J y K)
    (hWF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
      (w : CoxeterMatrix.F₄.Group) (n : G),
      GGCoxeterPres 5 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' ∧ n ∈ L ⊔ K ∧
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((((e' (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs
        ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) : Set G) ∧
      ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
      D' = ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∧
      J' = LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) ∧
      D' = Subgroup.closure {x, d} ∧ LargeEvenStdSub 5 B x L D' J' ∧
      GGConfig 5 B Bs x L D' J' ∧ GGNbr 5 B x D' J' d A ∧
      A = ggLayerClosure 5 (Subgroup.centralizer ({d} : Set G)) J' ∧
      A.map (MulAut.conj n).toMonoidHom = A ∧ J' ≤ A ∧
      GGHasLabel ⟨.A, 3, 2⟩ (↥J' ⧸ Subgroup.center ↥J') ∧ Subgroup.center ↥J' = ⊥ ∧
      GGInnerDiagOn Bs A ∧ GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A) ∧
      GGCentralImage .PSL 6 2 A ∧
      GGF4QGeFourOppEnd 5 Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) d A ∧
      ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧ A ≤ L ⊔ K := by
  have hcfg : GGF4QGeFourCfg 5 B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hf : 2 ≤ 2 := le_rfl
  have hpq : 5 ∣ 2 ^ 2 + 1 := by norm_num
  obtain ⟨-, -, hrest⟩ := ggF4QGeFourOppPlus_plane_le_sup_at hLB GGK0ExcB3Prod.ggK0ExcB3_holds
    hNPLA hR hW hq hNb hWF4 hf hpq hL (ggF4Plus_original_b3_of_cfg hcfg hf hpq hL)
    (fun _ hpres' => ggF4OriginalRankOneFamily_plus hcfg hpres' hf hpq hL)
  exact hrest

end Assembled

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeNineTB
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixLin
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBTwA3Row
import CFSG.LocalAnalysis.StandardType.GGQTwoReduction
import CFSG.LocalAnalysis.StandardType.GGQ2GammaOfShape
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXOffI1Holds
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumMovesLine
import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreRefl
import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
import CFSG.LocalAnalysis.StandardType.GGQTwoTBDerive
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2TwAHeartDatumSixInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {X : Subgroup G} {u : G}, (X = L ∧ u = x) ∨ GGNbr p B x D J u X →
      GGQ2S08RowTwA p 6 X J → u ∉ X →
        ∃ M : GGQ2LDatum p Bs X u, ∃ e : Fin 5 ≃ M.Λ,
          (∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 5 i j) ∧ M.ShapeB

private theorem ggQ2tn6_not_mem_zpowers_of_movesLine {G : Type} [Group G] {Bs : Subgroup G}
    {u : G} (hu : u ∈ Bs) {φ : MulAut ↥Bs} (h : GGQ2MovesLine Bs u φ) :
    φ ⟨u, hu⟩ ∉ Subgroup.zpowers (⟨u, hu⟩ : ↥Bs) := by
  obtain ⟨b, hb, hφb⟩ := h
  intro hmem
  apply hφb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hbk : b = (⟨u, hu⟩ : ↥Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  rw [hbk, map_zpow, ← hm, ← zpow_mul]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m * k, by simp⟩

theorem ggQ2_nbr_not_mem_zpowers_pair {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnbr : GGNbr p B x D J y K) :
    y ∉ Subgroup.zpowers x ∧ x ∉ Subgroup.zpowers y := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcyc : ∀ z ∈ D, ¬ D ≤ Subgroup.zpowers z := by
    intro z hz hle
    have hD_eq : D = Subgroup.zpowers z := le_antisymm hle (Subgroup.zpowers_le.mpr hz)
    have hdvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one (hDab.2 z hz)
    have horder : orderOf z = p ^ 2 := by
      rw [← Nat.card_zpowers, ← hD_eq, hDcard]
    have hp2le : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (horder ▸ hdvd)
    nlinarith [hp.two_le]
  refine ⟨fun hy => hcyc x hxD ?_, fun hx => hcyc y hyD ?_⟩
  · rw [hnbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hy
  · rw [hnbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hx
    · exact Subgroup.mem_zpowers _

theorem GGQ2LDatum.simple_isReflection {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (i : M.Λ) : GGIsReflection 3 (M.simple i) := by
  have hfx : M.root i (M.coroot i) = 2 := GGQ2LDatum.root_coroot_two M i
  exact ggIsReflection_of_eq_reflection (p := 3) (by decide) M.model hfx
    (ggLin_eq_reflection (p := 3) M.model hfx (M.simple_apply i))

theorem ggQ2_tn6_automizer_le (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (hNT : GGNoTransvection 3 Bs) (M : GGQ2LDatum 3 Bs X u)
    (e : Fin 5 ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 5 i j) (hB : M.ShapeB)
    (𝓜 : Subgroup (MulAut ↥Bs)) (h𝓜 : 𝓜 ≤ ggAutomizer ⊤ Bs) (hX : ggAutomizer X Bs ≤ 𝓜)
    (hΓ : ∀ φ ∈ ggAutomizer ⊤ Bs, φ ⟨u, M.hx⟩ = ⟨u, M.hx⟩ → φ ∈ 𝓜) {t : MulAut ↥Bs}
    (ht : t ∈ 𝓜) (htR : GGIsReflection 3 t)
    (htu : t ⟨u, M.hx⟩ ∉ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs)) :
    ggAutomizer ⊤ Bs ≤ 𝓜 := by
  classical
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) := (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  let 𝓜V : Subgroup (M.V ≃ₗ[ZMod 3] M.V) := 𝓜.map (ggLin (p := 3) M.model)
  let c : Fin 5 → M.V := fun i => M.coroot (e i)
  let α : Fin 5 → Module.Dual (ZMod 3) M.V := fun i => M.root (e i)
  let s : Fin 5 → (M.V ≃ₗ[ZMod 3] M.V) := fun i => ggLin (p := 3) M.model (M.simple (e i))
  have hcoSpan : M.coSpan = Submodule.span (ZMod 3) (Set.range c) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by
        change M.coroot (e (e.symm j)) = M.coroot j
        rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hxH : M.xV ∉ Submodule.span (ZMod 3) (Set.range c) := by
    rw [← hcoSpan]
    exact hB.2.2.1
  have hdim : Module.finrank (ZMod 3) M.V = 5 := by
    rw [ggQ2LD_dim_heart M (Or.inl hB), ← Fintype.card_congr e, Fintype.card_fin]
  have hpair : ∀ i j : Fin 5, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3) := by
    intro i j
    rw [M.pairing (e i) (e j), hC i j]
  have hs : ∀ i : Fin 5, ∀ v, s i v = v - α i v • c i := fun i => M.simple_apply (e i)
  have hs𝓜 : ∀ i : Fin 5, s i ∈ 𝓜V := fun i => Subgroup.mem_map_of_mem _
    (hX (by rw [M.automizer_L]; exact Subgroup.subset_closure ⟨e i, rfl⟩))
  have hxfix : ∀ i : Fin 5, α i M.xV = 0 := fun i => GGQ2LDatum.root_xV M (e i)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hlin : ∀ ψ : MulAut ↥Bs, ggLin (p := 3) M.model ψ M.xV =
      M.model (Additive.ofMul (ψ ⟨u, M.hx⟩)) := fun ψ =>
    ggLin_apply_ofMul (p := 3) M.model ψ _
  have hΓV : ∀ g ∈ A, g M.xV = M.xV → g ∈ 𝓜V := by
    rintro _ ⟨φ, hφ, rfl⟩ hfix
    refine Subgroup.mem_map_of_mem _ (hΓ φ hφ ?_)
    rw [hlin] at hfix
    exact Additive.ofMul.injective (M.model.injective hfix)
  have htV : IsReflLin (ggLin (p := 3) M.model t) :=
    (ggLinRefl_iff_isReflLin _).mp ((ggRC_isReflection_iff_linRefl M.model t).mp htR)
  have htx : ggLin (p := 3) M.model t M.xV ∉ Submodule.span (ZMod 3) {M.xV} := by
    intro hmem
    rw [hlin] at hmem
    have hfx : M.model (Additive.ofMul (t ⟨u, M.hx⟩)) ∈
        ggFixedSubmodule (p := 3) M.model (ggAutomizer X Bs) := by
      rw [M.fixed_x]
      exact hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((M.model_mem_fixed_iff _).mp hfx)
    exact htu (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
  have hle := ggQ2TN6_le hK A 𝓜V (Subgroup.map_mono h𝓜) hTF hdim c α hpair s hs hs𝓜 M.xV hxH
    hxfix hΓV _ (Subgroup.mem_map_of_mem _ ht) htV htx
  intro φ hφ
  obtain ⟨ψ, hψ, hψeq⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem _ hφ))
  rwa [ggLin_injective M.model hψeq] at hψ

theorem ggQ2s08_tn6L_of_tpLine
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (hK : GGReflClassOmegaInput) (hCavH : GGQ2CavOfTBHeartInner)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) (hD6 : GGQ2TwAHeartDatumSixInput) :
    GGQ2S08TNCellL (GGQ2S08PosTwA 6) := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow hx
  subst hp
  have hrow' : GGQ2S08RowTwA 3 6 L J := hrow
  obtain ⟨M, e, hC, hB⟩ := hD6 rfl hS hI1 (Or.inl ⟨rfl, rfl⟩) hrow' hx
  have hdim : finrank (ZMod 3) M.V = 5 := by
    rw [ggQ2LD_dim_heart M (Or.inl hB), ← Fintype.card_congr e, Fintype.card_fin]
  have hcard : Nat.card Bs = 3 ^ 5 := by
    rw [M.card_eq_pow_finrank, hdim]
  have hCav : 4 ∣ Nat.card (ggAutomizer J Bs) := by
    obtain ⟨labX, labJ, hmX, -, -, htX, hrk, -, -, -, hNJ⟩ := hrow'
    have hTBH : GGQ2TBHeart 3 Bs L := by
      refine ⟨labX, ggQ2_labQTwo_of_marking_twA hRig hS htX hmX, hmX,
        Or.inl ⟨htX, by rw [hrk]; omega⟩, ?_⟩
      rw [M.index_centralizer_of_setting hS, hdim]
      simp only [GGQ2LieRank, htX]
      congr 1
      omega
    exact ggQ2_cav_of_tbHeart hCavH hS rfl hTBH M (Or.inl hB)
  have hΓ : GGGammaAt 3 B Bs x L D J ⟨x, M.hx⟩ :=
    ggQ2_gammaAt_of_gammaX (ggQ2_gammaX_of_heartA hLB hP hS hCav M e hC (by norm_num) hB) rfl
  obtain ⟨labX, labJ, hmX, hmJ, htJ, htX, -, hn, -, hpq, hNJ⟩ := hrow'
  obtain ⟨lJ, hΛJ, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEJ
  have hXq : labX.n < 2 := ggQ2_labQTwo_of_marking_twA hRig hS htX hmX
  obtain ⟨N, hsh⟩ := ggQ2_nbrDatum_twA3_of_tpLine hRig hLB hP hTP hS hI1 hnb hcard hΛJ
    (Or.inr ⟨Or.inl htJ, by omega, hpq⟩) (by have := hΛJ.1; omega) hhasJ
  have hdimN : finrank (ZMod 3) N.V = 5 := by
    have h := N.card_eq_pow_finrank
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hΛN := ggQ2LD_finrank_le_card_succ N hsh
  obtain ⟨j, hj⟩ := N.exists_simple_movesLine (by omega) M.hx
    (ggQ2_nbr_not_mem_zpowers_pair hS.1.1 hnb).2
  have hG0 : ∀ {Y : Subgroup G}, Y ≤ ggG0 3 B x L D J → ggAutomizer Y Bs ≤
      ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs :=
    fun hY => ggAutomizer_mono Bs (hY.trans Subgroup.le_normalizer)
  have hAM := ggQ2_tn6_automizer_le hK hS.1.2.2.2.1 M e hC hB _ (ggAutomizer_mono Bs le_top)
    (hG0 (le_ggG0_left 3 B x L D J))
    (fun φ hφ hφx => hΓ φ hφ (by rw [hφx]; exact Subgroup.mem_zpowers _))
    (hG0 (le_ggG0_of_ggNbr hnb) (by rw [N.automizer_L]; exact Subgroup.subset_closure ⟨j, rfl⟩))
    (N.simple_isReflection j) (ggQ2tn6_not_mem_zpowers_of_movesLine M.hx hj)
  exact ggQ2_normalizer_le_of_automizer_le (ggQ2_centralizer_le_normalizer_ggG0 hNC hS) hAM

theorem ggQ2s08_tn6K_of_tablePAtL
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hPL : GGQ2TablePAtLTwA3) (hD6 : GGQ2TwAHeartDatumSixInput) :
    GGQ2S08TNCellK (GGQ2S08PosTwA 6) := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow hy
  subst hp
  have hrow' : GGQ2S08RowTwA 3 6 K J := hrow
  obtain ⟨MK, eK, hCK, hBK⟩ := hD6 rfl hS hI1 (Or.inr hnb) hrow' hy
  have hdim : finrank (ZMod 3) MK.V = 5 := by
    rw [ggQ2LD_dim_heart MK (Or.inl hBK), ← Fintype.card_congr eK, Fintype.card_fin]
  have hcard : Nat.card Bs = 3 ^ 5 := by
    rw [MK.card_eq_pow_finrank, hdim]
  have hΓ : GGGammaAt 3 B Bs x L D J ⟨y, MK.hx⟩ :=
    ggQ2_gammaNbr_of_tableBShape hLB hP h5 hS hI1 hnb MK (Or.inr (Or.inr (Or.inl hBK)))
      (fun hF _ => absurd (finrank_span_eq_card hF.2.1) (by
        have := hBK.2.1
        change Module.finrank (ZMod 3) MK.coSpan ≠ Fintype.card MK.Λ
        omega))
      (fun _ => ⟨5, by norm_num, eK, hCK⟩) rfl
  obtain ⟨_, labJ, -, hmJ, htJ, -, -, -, -, hpq, hNJ⟩ := hrow'
  obtain ⟨lJ, hΛJ, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEJ
  obtain ⟨ML, hsh⟩ := ggQ2_LDatum_twA3_of_tablePAtL hRig hPL hS hI1 hnb hcard hΛJ htJ (by omega)
    hpq hhasJ
  have hdimL : finrank (ZMod 3) ML.V = 5 := by
    have h := ML.card_eq_pow_finrank
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hΛL := ggQ2LD_finrank_le_card_succ ML hsh
  obtain ⟨j, hj⟩ := ML.exists_simple_movesLine (by omega) MK.hx
    (ggQ2_nbr_not_mem_zpowers_pair hS.1.1 hnb).1
  have hG0 : ∀ {Y : Subgroup G}, Y ≤ ggG0 3 B x L D J → ggAutomizer Y Bs ≤
      ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs :=
    fun hY => ggAutomizer_mono Bs (hY.trans Subgroup.le_normalizer)
  have hAM := ggQ2_tn6_automizer_le hK hS.1.2.2.2.1 MK eK hCK hBK _ (ggAutomizer_mono Bs le_top)
    (hG0 (le_ggG0_of_ggNbr hnb))
    (fun φ hφ hφy => hΓ φ hφ (by rw [hφy]; exact Subgroup.mem_zpowers _))
    (hG0 (le_ggG0_left 3 B x L D J)
      (by rw [ML.automizer_L]; exact Subgroup.subset_closure ⟨j, rfl⟩))
    (ML.simple_isReflection j) (ggQ2tn6_not_mem_zpowers_of_movesLine MK.hx hj)
  exact ggQ2_normalizer_le_of_automizer_le (ggQ2_centralizer_le_normalizer_ggG0 hNC hS) hAM

theorem ggQ2s08_tn6_of_tableP
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hCavH : GGQ2CavOfTBHeartInner) (hTP : GGNbrTablePNbrInputI1On GGRegimeLine)
    (hPL : GGQ2TablePAtLTwA3) (hD6 : GGQ2TwAHeartDatumSixInput) :
    GGQ2S08TNCell (GGQ2S08PosTwA 6) :=
  ggQ2s08_tnCell_of_LK (ggQ2s08_tn6L_of_tpLine hRig hLB hP hNC hK hCavH hTP hD6)
    (ggQ2s08_tn6K_of_tablePAtL hRig hLB hP hNC h5 hK hPL hD6)

end CFSG.StandardType

end

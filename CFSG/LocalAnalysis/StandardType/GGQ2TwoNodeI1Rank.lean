module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNodeBasics
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeRestDefs
import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_card_bstar_eq_of_I1 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range * p ^ 2 = Nat.card Bs := by
  have hD : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
    have hDdef : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
    refine le_antisymm (fun b hb => hI1 b hb.1 fun j hj => ?_) ?_
    · exact ((Subgroup.mem_centralizer_iff.mp hb.2) j hj).symm
    · rw [hDdef]
      exact inf_le_inf_right _ hcfg.2.1.1
  rw [← hcfg.2.2.1.2.2.1, ← hD]
  exact NbrU63.card_range_ggGamma_mul_card_inf hN

theorem ggQ2_card_bstar_le_of_I1_twA
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    {N : ℕ} (h7 : 7 ≤ N) (hrow : GGQ2S08RowTwA p N X J) :
    Nat.card Bs ≤ p ^ (N - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨labX, labJ, hmX, hmJ, hJt, hXt, hrk, hn, hpd, hpq, hNJ⟩ := hrow
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  obtain ⟨lJ, -, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEX hEJ
  obtain ⟨tX, rX, nX⟩ := lX
  obtain ⟨tJ, rJ, nJ⟩ := lJ
  dsimp only at hJt hXt hrk hn hpd hpq hNJ hΛX hhasX hhasJ
  subst hJt hXt hrk hn
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub
      (fun a ha b hb => congrArg Subtype.val
        (hcfg.tableB_facts.2.1.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩))
      hcfg.2.1.1 hcfg.2.2.1 (GGDichotomy.le_normalizer_of_innerDiagOn hIDA.1)
  have hpd' : p ∣ rJ + 2 + 1 := by simpa only [Nat.add_assoc] using hpd
  have hJLab : GGHasLabel ⟨.twA, rJ + 2 - 2, nX⟩ (J ⧸ Subgroup.center J) := by
    simpa only [Nat.add_sub_cancel] using hhasJ
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := fun b hb => hcfg.tableB_facts.2.1.2 b hb
  have hcap : Nat.card (ggGamma J hBsJ).range ≤ p ^ (rJ + 2 - 1 - 1) := by
    rcases hX with rfl | ⟨y, hnb⟩
    · obtain ⟨F, hField, hFinite, -, hN, φ, S, -, hM, hJ, hS, hdiag⟩ :=
        exists_corank_two_block_of_large_unitary_L_of_cfg hRig hcfg hIDA (by omega) (by omega) hpq
          hpd' hhasX hΛX hJLab
      let : Field F := hField
      let : Finite F := hFinite
      rw [← hS]
      exact card_range_ggGamma_le hM hN hdiag le_rfl S (by omega) hJ hBsJ hp hBsp
    · obtain ⟨F, hField, hFinite, -, hN, φ, S, -, hM, hJ, hS, hdiag⟩ :=
        exists_corank_two_block_of_large_unitary_K_of_cfg hRig hLB hcfg hIDA hnb (by omega)
          (by omega) hpq hpd' hhasX hΛX hJLab
      let : Field F := hField
      let : Finite F := hFinite
      rw [← hS]
      exact card_range_ggGamma_le hM hN hdiag le_rfl S (by omega) hJ hBsJ hp hBsp
  calc Nat.card Bs = Nat.card (ggGamma J hBsJ).range * p ^ 2 :=
        (ggQ2_card_bstar_eq_of_I1 hcfg hI1 hBsJ).symm
    _ ≤ p ^ (rJ + 2 - 1 - 1) * p ^ 2 := Nat.mul_le_mul_right _ hcap
    _ = p ^ (N - 1) := by
      rw [← pow_add]
      congr 1
      omega

theorem GGQ2LDatum.card_eq_pow_finrank {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u) :
    Nat.card Bs = p ^ Module.finrank (ZMod p) M.V := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
    _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
    _ = p ^ Module.finrank (ZMod p) M.V := (FiniteField.pow_finrank_eq_natCard p M.V).symm

theorem GGQ2LDatum.card_of_shapeC {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u) (hC : M.ShapeC) :
    Nat.card Bs = p ^ (Fintype.card M.Λ + 1) := by
  rw [M.card_eq_pow_finrank, hC.2.2.2.1]

theorem ggQ2_not_shapeC_twA_of_I1
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    {N : ℕ} (h7 : 7 ≤ N) (hrow : GGQ2S08RowTwA p N X J) {u : G} (M : GGQ2LDatum p Bs X u)
    (hΛ : Fintype.card M.Λ = N - 1) : ¬ M.ShapeC := by
  intro hC
  have hle := ggQ2_card_bstar_le_of_I1_twA hRig hLB hcfg hIDA hI1 hX h7 hrow
  rw [M.card_of_shapeC hC, hΛ] at hle
  have := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle
  omega

theorem ggQ2_shapeB_twA_of_I1
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    {N : ℕ} (h7 : 7 ≤ N) (hrow : GGQ2S08RowTwA p N X J) {u : G} (M : GGQ2LDatum p Bs X u)
    (hΛ : Fintype.card M.Λ = N - 1) (hBC : M.ShapeB ∨ M.ShapeC) : M.ShapeB :=
  hBC.resolve_right (ggQ2_not_shapeC_twA_of_I1 hRig hLB hcfg hIDA hI1 hX h7 hrow M hΛ)

theorem ggQ2_tnBigSel_of_shapeBC
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    {N : ℕ} (h12 : 12 ≤ N) (hrow : GGQ2S08RowTwA p N X J) {u : G} (M : GGQ2LDatum p Bs X u)
    (e : Fin (N - 1) ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A (N - 1) i j)
    (hBC : M.ShapeB ∨ M.ShapeC) : GGQ2TNBigSel p Bs X u := by
  have hΛ : Fintype.card M.Λ = N - 1 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hB := ggQ2_shapeB_twA_of_I1 hRig hLB hcfg hIDA hI1 hX (by omega) hrow M hΛ hBC
  have h3 : 3 ∣ N - 1 + 1 := by
    obtain ⟨-, labJ, -, -, -, -, -, -, hpd, -, hN⟩ := hrow
    rw [← hp, show N - 1 + 1 = N by omega, ← hN]
    exact hpd
  exact ⟨M, N - 1, by omega, h3, e, hC, hB⟩

theorem ggQ2_inf_centralizer_nbr_eq_of_I1 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)
  refine le_antisymm (fun c hc => ?_) ?_
  · refine ggQ2_K1_of_I1 hLB hP hHyp hI1 y K hnb c hc.1 ?_
    have h1 : Subgroup.zpowers c ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hc.2
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1]
    exact bot_le
  · rw [Subgroup.zpowers_le]
    exact ⟨hHyp.1.2.1.1 hnb.1.2.1, hyK⟩

end CFSG.StandardType

end

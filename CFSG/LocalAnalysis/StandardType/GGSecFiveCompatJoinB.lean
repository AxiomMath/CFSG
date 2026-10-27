module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixAD
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpCartan
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSpMember
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBGuarded
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE6
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE8
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPSL
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberTwistedE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedF4
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedPSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSelectedE7Guarded
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
import CFSG.LieType.Universal.SpinClause0
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem GGSecFiveRouteCfg.bstar_le_ggG0_of_B
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hB : GGIsWeylMatrixB M) :
    Bs ≤ ggG0 p B x L D J := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, σ, hm, rfl⟩ := hB
  have hW : GGWeylOfType p (CoxeterMatrix.B m) (ggAutomizerJoin L Bs 𝒦) :=
    GGWeylOfType.of_reindex ⟨e, hP.2⟩
  let root : Fin m := ⟨0, by omega⟩
  obtain ⟨hno6, hpar, hdepth⟩ := ggCartanC_pathTree root rfl
  refine hcfg.bstar_le_ggG0_of_cartan hp2 (ggIntCartan_C m) hno6
    (ggPathPar m) root (fun i => i.1) hpar hdepth hW
    (card_le_pow_rank_of_isUnit_det ?_ hW fun b hb =>
      hcfg.eq_one_of_forall_join_fix hTBF hWI b hb)
  rw [CartanMatrix.C_det (by omega : 0 < m)]
  have h := (ZMod.isUnit_iff_coprime 2 p).mpr
    (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2))
  simpa using h

section RegularLinearCells

open CFSG.LieType CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

private theorem guarded_marking_of_selected_hasLabel
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hRig : GGLabelRigidInput)
    {K : Subgroup G} (hK : K ∈ 𝒦) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hguard : GuardedLargeEvenLabel lab) :
    ∃ y : G, GGNbr p B x D J y K ∧
      LargeEvenMarking ↥K (fun lab' _ _ _ _ _ => GuardedLargeEvenLabel lab') := by
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK
  have hmark := ggInnerDiagOn_relabel hRig (hR.1.2.2.1.2 y K hy) hlab hhas
  refine ⟨y, hy, largeEvenMarking_mono ?_ hmark⟩
  intro lab' _ _ _ _ _ h
  exact h.1.symm ▸ hguard

theorem GGSecFiveRouteCfg.exists_guarded_nbr_of_bPermLin_regularCell
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hcell : (∃ q K i, GGSecFiveBPermSpCell p Bs L 𝒦 n eta q K i) ∨
      (∃ q K i, GGSecFiveBPermOmCell p Bs L 𝒦 n eta q K i) ∨
      (∃ m K i, GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i)) :
    ∃ (y : G) (K : Subgroup G), K ∈ 𝒦 ∧ GGNbr p B x D J y K ∧
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := by
  rcases hcell with hSp | hOm | hQ
  · obtain ⟨q, K, i, hf, hK, _, ⟨e⟩, _⟩ := hSp
    have hlab : LargeEvenInLambda2 (⟨.C, n - 1, q⟩ : LargeEvenLabel) :=
      ⟨by change 1 ≤ q; omega, by change 2 ≤ n - 1; omega, fun _ => hf⟩
    have hhas := ggHasLabel_C_of_mulEquiv_statedSp (by omega : 2 ≤ n - 1) hf e
    have hg : GuardedLargeEvenLabel (⟨.C, n - 1, q⟩ : LargeEvenLabel) :=
      Or.inl ⟨Or.inr rfl, by change 3 ≤ n - 1; omega⟩
    obtain ⟨y, hy, hmark⟩ := guarded_marking_of_selected_hasLabel hR hRig hK hlab hhas hg
    exact ⟨y, K, hK, hy, hmark⟩
  · obtain ⟨q, K, i, hf, hK, _, ⟨e⟩, _⟩ := hOm
    let U := spinGroup (quadMinus n (GaloisField 2 q)
      (minusCoeffs 2 q).1 (minusCoeffs 2 q).2)
    have hmodel : CFSG.Open.StatedClassicalModel (U ⧸ Subgroup.center U) .POmegaMinus n 2 q :=
      CFSG.LieType.Universal.Spin.statedClassicalModel_spin_quadMinus
        ⟨Nat.prime_two, by omega, hn⟩ (GaloisField.card 2 q (by omega))
        (minusCoeffs_irr 2 q)
    have hU : GGHasLabel (⟨.twD, n, q⟩ : LargeEvenLabel) (U ⧸ Subgroup.center U) := by
      change if n = 2 then _ else if n = 3 then _ else _
      simp only [show n ≠ 2 from by omega, show n ≠ 3 from by omega, ↓reduceIte]
      exact recipeOmegaMinus_of_statedClassicalModel hmodel
    have hhas : GGHasLabel (⟨.twD, n, q⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) :=
      ggHasLabel_quotCenter_of_mulEquiv e.symm hU
    have hlab : LargeEvenInLambda2 (⟨.twD, n, q⟩ : LargeEvenLabel) :=
      ⟨by change 1 ≤ q; omega, by change 2 ≤ n; omega⟩
    have hg : GuardedLargeEvenLabel (⟨.twD, n, q⟩ : LargeEvenLabel) :=
      Or.inr (Or.inl ⟨Or.inr rfl, hn⟩)
    obtain ⟨y, hy, hmark⟩ := guarded_marking_of_selected_hasLabel hR hRig hK hlab hhas hg
    exact ⟨y, K, hK, hy, hmark⟩
  · obtain ⟨m, K, i, _, hm, hK, _, ⟨e⟩, _⟩ := hQ
    have hm6 : 6 ≤ m := by omega
    have hhas : GGHasLabel (⟨.A, m - 1, 1⟩ : LargeEvenLabel)
        (↥K ⧸ Subgroup.center ↥K) :=
      ggHasLabel_of_mulEquiv_specialLinear (by omega : 2 ≤ m) (by simp)
        (fun h => by have := congrArg Prod.fst h; omega)
        (fun h => by have := congrArg Prod.fst h; omega) e.symm
    have hlab : LargeEvenInLambda2 (⟨.A, m - 1, 1⟩ : LargeEvenLabel) :=
      ⟨by change 1 ≤ 1; decide, by change 1 ≤ m - 1; omega,
        by change m - 1 = 1 → 2 ≤ 1; omega⟩
    have hg : GuardedLargeEvenLabel (⟨.A, m - 1, 1⟩ : LargeEvenLabel) :=
      Or.inr (Or.inr (Or.inr ⟨rfl, by change 5 ≤ m - 1; omega, rfl⟩))
    obtain ⟨y, hy, hmark⟩ := guarded_marking_of_selected_hasLabel hR hRig hK hlab hhas hg
    exact ⟨y, K, hK, hy, hmark⟩

end RegularLinearCells

theorem ggSecFiveCompatJoinB_of_guarded
    (hKnown : KnownActualMemberSelectedInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hB : GGIsWeylMatrixB M)
    {t : StatedLieTag} {n f : ℕ} (ψ : (ggU t n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    GGSecFiveCompat p B x L D J := by
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  have hBs : Bs ≤ ggG0 p B x L D J := hcfg.bstar_le_ggG0_of_B hTBF hWI hP hB
  have horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J := by
    rcases hX with hXL | ⟨y, hN⟩
    · exact Or.inl ⟨hXL, hBs hc.tableB_facts.2.2.1⟩
    · exact Or.inr ⟨y, hN, hBs (hc.2.1.1 hN.1.2.1)⟩
  obtain ⟨S, hmember, hpresented⟩ :=
    hKnown G p B Bs x L D J hc t n f ψ hpres X horigin hmark
  exact ggCompat_of_selected_packages hpres hX hmember hpresented

theorem GGSecFiveRouteCfg.compat_of_bPermLin_regularCell
    (hRig : GGLabelRigidInput) (hKnown : KnownActualMemberSelectedInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hB : GGIsWeylMatrixB M)
    {t : StatedLieTag} {d f : ℕ} (ψ : (ggU t d f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t d f).D t d f ψ)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hcell : (∃ q K i, GGSecFiveBPermSpCell p Bs L 𝒦 n eta q K i) ∨
      (∃ q K i, GGSecFiveBPermOmCell p Bs L 𝒦 n eta q K i) ∨
      (∃ m K i, GGSecFiveBPermQTwoCell p Bs L 𝒦 n eta m K i)) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨y, K, _, hy, hmark⟩ := hR.exists_guarded_nbr_of_bPermLin_regularCell hRig hn eta hcell
  exact ggSecFiveCompatJoinB_of_guarded hKnown hR hTBF hWI hP hB ψ hpres
    (Or.inr ⟨y, hy⟩) hmark

end CFSG.StandardType

end

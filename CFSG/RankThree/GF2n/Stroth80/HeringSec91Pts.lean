module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData
public import CFSG.RankThree.GF2n.Stroth80.Sec91
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Pts91 (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K]
    (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (u : Fin 2 ⊕ Fin 2 → K) : Prop where
  card : Nat.card K = Nat.card Z
  range : φ.range = StatedOmega (StatedQuadPlus 2 K)
  ker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)
  act : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
    (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  sing : quadPlus 2 K u = 0
  ne_zero : u ≠ 0
  point : ∀ x : Fin 2 ⊕ Fin 2 → K,
    (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u
  perp : ∀ x : Fin 2 ⊕ Fin 2 → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
    (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔
    polar (quadPlus 2 K) u x = 0
  root : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u

theorem exists_pts91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 2 ⊕ Fin 2 → K))
      (u : Fin 2 ⊕ Fin 2 → K), Pts91 hc t E φ ψ u := by
  classical
  have hs5 := hs.toSec5
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  let E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)) :=
    ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)
  obtain ⟨u, hQu, hu0, hBiff, hW, hLeq⟩ := hc.omega_points_flag h34 hs5 hnotQB hK E hQ h3
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
  exact ⟨K, fK, finK, ‹CharP K 2›, E, hn, φ, ψ, u,
    ⟨hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, hLeq⟩⟩

theorem card_Vt_inf_QB_plus4 {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ 4 := by
  classical
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B :=
    le_inf (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hc.Z_le_QB.1
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left
    {x | polar (quadPlus 2 K) u x = 0} (fun x => P.perp x)
  have h2 : Nat.card {x : Fin 2 ⊕ Fin 2 → K // polar (quadPlus 2 K) u x = 0} =
      Nat.card K ^ (Fintype.card (Fin 2 ⊕ Fin 2) - 1) := card_polar_perp (quadPlus 2 K) hQ P.ne_zero
  have hι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
  have h3 : Nat.card ↥{x : Fin 2 ⊕ Fin 2 → K | polar (quadPlus 2 K) u x = 0} =
      Nat.card K ^ 3 := by
    have := h2
    rw [hι] at this
    exact this
  rw [h1, h3, P.card]
  ring

end HS9


theorem step91OrderVQB_of (h34 : Stroth34Statement) : Step91OrderVQBStatement := by
  intro G _ _ M Q Z B hc n t hs V hV
  subst hV
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  exact HS9.card_Vt_inf_QB_plus4 P

end CFSG.RankThree.GF2n.Stroth80

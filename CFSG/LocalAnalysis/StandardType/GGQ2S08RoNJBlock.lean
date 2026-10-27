module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNAut
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB6C27
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6S21
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecKGC27b
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.Walter.J1Props
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.E6QTwo

open CFSG CFSG.Assembly
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}

theorem exists_jBlock (c : GGQ2S08RoN n Bs L x) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) :
    ∃ I : Finset (Fin (n + 1)), 4 ≤ I.card ∧
      (J.subgroupOf L).map c.piL =
        (TableBUE.blockSU (K := c.K) (n := 1) I).map
          (InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ) := by
  classical
  let h := USixTwo.fieldDataFour c.hK
  let R := LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) c.K (2 ^ 1))
  let cnj : R →* MulAut R := MulAut.conj
  let ψ : ↥(unitarySU 2 1 c.K (n + 1)) →* MulAut R :=
    cnj.comp (InndiagSU.frameMk h c.Q c.hQ)
  let Kq : Subgroup R := (J.subgroupOf L).map c.piL
  have hL : commutator ↥L = ⊤ := c.hperf
  have hperfL : Group.IsPerfect ↥L := ⟨hL⟩
  have hZq : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot ↥L _ hperfL
  have hZR : Subgroup.center R = ⊥ := by
    apply le_antisymm
    · intro r hr
      have hpre : c.θ.symm r ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
        rw [Subgroup.mem_center_iff] at hr ⊢
        intro q
        apply c.θ.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hr (c.θ q)
      have hpre1 : c.θ.symm r = 1 := by simpa [hZq] using hpre
      have hr1 : r = 1 := by simpa using congrArg c.θ hpre1
      simp [hr1]
    · exact bot_le
  have hc : Function.Injective cnj := CFSG.mulAutConj_injective_of_center_eq_bot hZR
  have hconj : ∀ (β : MulAut R) (r : R), cnj (β r) = β * cnj r * β⁻¹ := by
    intro β r
    ext y
    simp [cnj, MulAut.mul_apply, MulAut.conj_apply]
  have hψrange : ψ.range = cnj.range := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (InndiagSU.frameMk_surjective h c.Q c.hQ),
      Subgroup.map_top]
  have hψker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 c.K (n + 1)) := by
    intro u hu
    apply TableBUI.ker_frameMk_le_center h c.Q c.hQ
    rw [MonoidHom.mem_ker] at hu ⊢
    apply hc
    simpa [ψ] using hu
  let hDL : D ≤ Subgroup.normalizer (L : Set G) := QTwoCav.d_le_normalizer hS c.hNL
  have hstd : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  obtain ⟨-, -, -, -, -, hJcomp, -⟩ := hstd.1
  have hJq : IsComponentOf Kq (⨅ d : D, ggFix (ggBeta L c.θ hDL d)) :=
    QTwoCav.isComponentOf_quotient_image (hDL := hDL) (θ := c.θ) hJcomp
  obtain ⟨d, hd1, hdgen, hdiInf⟩ :=
    QTwoCav.exists_beta_d_generator (θ := c.θ) Nat.prime_three hS c.hNL
  let β : MulAut R := ggBeta L c.θ hDL d
  have hJfix : IsComponentOf Kq (ggFix β) := by
    rw [hdiInf] at hJq
    exact hJq
  have hDle : D ≤ Bs := hstd.1.1.trans hS.1.1.2.1.1
  have hβE : β ∈ (ggBeta L c.θ c.hNL).range :=
    range_ggBeta_le c.θ hDle hDL c.hNL (MonoidHom.mem_range.mpr ⟨d, rfl⟩)
  have hβact : ggBeta L c.θ hDL d = c.act ⟨(d : G), hDle d.2⟩ := by
    apply MulEquiv.ext
    intro r
    obtain ⟨q, rfl⟩ := c.θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [ggBeta_eq, ggLAut_apply]
      change c.piL ((L.normalizerMonoidHom ⟨(d : G), hDL d.2⟩) l) =
        (c.act ⟨(d : G), hDle d.2⟩) (c.piL l)
      rw [← c.piL_conjB ⟨(d : G), hDle d.2⟩ l]
      apply congrArg c.piL
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, e6QTwoBstarConjAction_apply]
  have hpair : (β, diagHom (n + 1) (c.diag ⟨(d : G), hDle d.2⟩)) ∈
      SUTorus.suPairs ψ := by
    refine ⟨?_, ?_⟩
    · exact SUTorus.mem_normalizer_of_mem_primeFormUnitary h
        (TableBUD.diagHom_mem_primeFormUnitary h (c.norm_one _))
    · intro u v hv
      change (ggBeta L c.θ hDL d) * cnj (InndiagSU.frameMk h c.Q c.hQ u) *
          (ggBeta L c.θ hDL d)⁻¹ = cnj (InndiagSU.frameMk h c.Q c.hQ v)
      rw [hβact, ← hconj (c.act ⟨(d : G), hDle d.2⟩)
        (InndiagSU.frameMk h c.Q c.hQ u)]
      exact congrArg cnj ((c.frameDiag_diag ⟨(d : G), hDle d.2⟩).apply u v hv)
  have hfixMap : (ggFix β).map cnj =
      cnj.range ⊓ Subgroup.centralizer ({β} : Set (MulAut R)) := by
    have h := map_fixSubgroup_eq_of_conj cnj hc β β (hconj β)
    have hgg : ggFix β = fixSubgroup β := by ext r; rfl
    rwa [← hgg] at h
  have hJopen : CFSG.Open.IsComponentOf Kq (ggFix β) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hJfix
  have hJmap := isComponentOf_map_inj hJopen cnj hc
  rw [hfixMap, ← hψrange] at hJmap
  have hJblock : IsComponentOf (Kq.map cnj) (ψ.range ⊓ Subgroup.centralizer {β}) :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr hJmap
  obtain ⟨I, hI4, hconst, hblock⟩ :=
    SUTorus.exists_blockSU_of_isComponentOf_two (m := n) h hψker hpair hJblock
  have hmap : Kq.map cnj =
      ((TableBUE.blockSU (K := c.K) (n := 1) I).map
        (InndiagSU.frameMk h c.Q c.hQ)).map cnj := by
    rw [hblock, Subgroup.map_map]
  have hKqeq : Kq = (TableBUE.blockSU (K := c.K) (n := 1) I).map
      (InndiagSU.frameMk h c.Q c.hQ) :=
    Subgroup.map_injective (f := cnj) hc hmap
  exact ⟨I, hI4, hKqeq⟩

theorem centralizes_iff_diag (c : GGQ2S08RoN n Bs L x)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L))) (heven : Even n) {J : Subgroup G}
    (hJL : J ≤ L) {I : Finset (Fin (n + 1))}
    (hJ : (J.subgroupOf L).map c.piL =
      (TableBUE.blockSU (K := c.K) (n := 1) I).map
        (InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ)) (b : ↥Bs) :
    (b : G) ∈ Subgroup.centralizer (J : Set G) ↔ ∀ i ∈ I, ∀ i' ∈ I, c.diag b i = c.diag b i' := by
  classical
  let h := USixTwo.fieldDataFour c.hK
  constructor
  · intro hb i hi i' hi'
    by_cases hii : i = i'
    · rw [hii]
    obtain ⟨k, -, hkpair⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, i'} : Finset (Fin (n + 1)))) (t := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hii]
        have := c.hn
        omega)
    have hki : k ≠ i := fun hk => hkpair (by simp [hk])
    have hki' : k ≠ i' := fun hk => hkpair (by simp [hk])
    let Pmat : GL (Fin (n + 1)) c.K := CFSG.RankThree.Classical.permGL (Equiv.swap i i')
    let P : ↥(unitarySU 2 1 c.K (n + 1)) := ⟨Pmat, TableBUE.permGL_swap_mem h i i'⟩
    have hPmem : P ∈ TableBUE.blockSU (K := c.K) (n := 1)
        ({i, i'} : Finset (Fin (n + 1))) := by
      rw [TableBUE.mem_blockSU]
      exact TableBUE.isBlockOn_permGL_swap (S := ({i, i'} : Finset (Fin (n + 1))))
        (by simp) (by simp)
    have hPblock : P ∈ TableBUE.blockSU (K := c.K) (n := 1) I := by
      refine (SUTorus.blockSU_mono (I := ({i, i'} : Finset (Fin (n + 1)))) (J := I) ?_) hPmem
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hi'
    have hmem : InndiagSU.frameMk h c.Q c.hQ P ∈
        (TableBUE.blockSU (K := c.K) (n := 1) I).map (InndiagSU.frameMk h c.Q c.hQ) :=
      ⟨P, hPblock, rfl⟩
    rw [← hJ] at hmem
    obtain ⟨j, hj, hPj⟩ := hmem
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hcomm : (j : G) * (b : G) = (b : G) * (j : G) :=
      Subgroup.mem_centralizer_iff.mp hb (j : G) hjJ
    have hcomm' : (b : G) * (j : G) = (j : G) * (b : G) := hcomm.symm
    have hconjj : c.conjB b j = j := by
      apply Subtype.ext
      rw [e6QTwoBstarConjAction_apply]
      rw [hcomm', mul_inv_cancel_right]
    have hact : c.act b (InndiagSU.frameMk h c.Q c.hQ P) =
        InndiagSU.frameMk h c.Q c.hQ P := by
      rw [← hPj, ← c.piL_conjB b j, hconjj]
    let w : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2) := (suCongrN c.K).symm P
    have hw : (w : GL (Fin (n + 1)) c.K) = Pmat := rfl
    have hfrw : c.fr w = InndiagSU.frameMk h c.Q c.hQ P := by
      rw [fr_apply, MulEquiv.apply_symm_apply]
    have hactw : c.act b (c.fr w) = c.fr w := by
      rw [hfrw]
      exact hact
    have hfr_eq : c.fr (c.diagConj (c.diag b) w) = c.fr w := by
      rw [← c.act_fr b w]
      exact hactw
    obtain ⟨μ, hμ⟩ := c.exists_scalar_of_fr_eq hfr_eq.symm
    let D : GL (Fin (n + 1)) c.K := diagHom (n + 1) (c.diag b)
    have hcoe := c.coe_diagConj (c.diag b) w
    have hmat : D * Pmat * D⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * Pmat := by
      calc D * Pmat * D⁻¹ = diagHom (n + 1) (c.diag b) * Pmat *
            (diagHom (n + 1) (c.diag b))⁻¹ := by rfl
        _ = diagHom (n + 1) (c.diag b) * (w : GL (Fin (n + 1)) c.K) *
              (diagHom (n + 1) (c.diag b))⁻¹ := by rw [hw]
        _ = (c.diagConj (c.diag b) w : GL (Fin (n + 1)) c.K) := hcoe.symm
        _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
              (w : GL (Fin (n + 1)) c.K) := hμ
        _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * Pmat := by rw [hw]
    have hDP : D * Pmat =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * (Pmat * D) := by
      calc D * Pmat = (D * Pmat * D⁻¹) * D := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * Pmat) * D := by rw [hmat]
        _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * (Pmat * D) := by group
    have hPD : Pmat * D =
        diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') * Pmat := by
      simpa only [Pmat, D] using
        (TableBUM.permGL_swap_mul_diagHom (K := c.K) (d := n + 1) (i := i) (j := i')
          (c.diag b))
    have hPmat_sq : Pmat * Pmat = 1 := by
      simp only [Pmat]
      rw [← map_mul, Equiv.swap_mul_self, map_one]
    have hDeq : D = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
        diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') := by
      calc D = (D * Pmat) * Pmat := by rw [mul_assoc, hPmat_sq, mul_one]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * (Pmat * D)) * Pmat := by
              rw [hDP]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
              (diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') * Pmat)) * Pmat := by
              rw [hPD]
        _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
              (diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') * (Pmat * Pmat)) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
              diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') := by
              rw [hPmat_sq, mul_one]
    have hscal : Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ *
        diagHom (n + 1) (c.diag b ∘ Equiv.swap i i') =
        diagHom (n + 1) (fun k => μ * c.diag b (Equiv.swap i i' k)) := by
      apply Units.ext
      rw [Units.val_mul, coe_diagHom, coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      rfl
    have hDeq' : diagHom (n + 1) (c.diag b) =
        diagHom (n + 1) (fun k => μ * c.diag b (Equiv.swap i i' k)) := by
      rw [show diagHom (n + 1) (c.diag b) = D from rfl, hDeq, hscal]
    have hfun : c.diag b = fun k => μ * c.diag b (Equiv.swap i i' k) :=
      CFSG.SectionRank.OddCover.diagHom_injective (n := n + 1) (K := c.K) hDeq'
    have hk := congrFun hfun k
    rw [Equiv.swap_apply_of_ne_of_ne hki hki'] at hk
    have hμ1 : μ = 1 := by
      have h1 : μ * c.diag b k = 1 * c.diag b k := by rw [← hk, one_mul]
      exact mul_right_cancel h1
    have hi' := congrFun hfun i
    rw [Equiv.swap_apply_left] at hi'
    rw [hμ1, one_mul] at hi'
    exact hi'
  · intro hconst
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjL : (j : G) ∈ L := hJL hj
    have hmem : c.piL ⟨j, hjL⟩ ∈
        (TableBUE.blockSU (K := c.K) (n := 1) I).map (InndiagSU.frameMk h c.Q c.hQ) := by
      rw [← hJ]
      exact ⟨⟨j, hjL⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    obtain ⟨P, hP, hPj⟩ := hmem
    have hcomm : diagHom (n + 1) (c.diag b) * (P : GL (Fin (n + 1)) c.K) =
        (P : GL (Fin (n + 1)) c.K) * diagHom (n + 1) (c.diag b) :=
      TableBUE.diagHom_mul_comm_of_isBlockOn (S := I) (σ := c.diag b) hconst
        ((TableBUE.mem_blockSU (K := c.K) (n := 1) (S := I)).mp hP)
    let v : ↥(unitarySU 2 1 c.K (n + 1)) :=
      ⟨diagHom (n + 1) (c.diag b) * (P : GL (Fin (n + 1)) c.K) *
          (diagHom (n + 1) (c.diag b))⁻¹, by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact P.2⟩
    have hvP : (v : GL (Fin (n + 1)) c.K) = (P : GL (Fin (n + 1)) c.K) := by
      change diagHom (n + 1) (c.diag b) * (P : GL (Fin (n + 1)) c.K) *
          (diagHom (n + 1) (c.diag b))⁻¹ = (P : GL (Fin (n + 1)) c.K)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hv_eq : v = P := Subtype.ext hvP
    have hactP : c.act b (InndiagSU.frameMk h c.Q c.hQ P) =
        InndiagSU.frameMk h c.Q c.hQ P := by
      have h := (c.frameDiag_diag b).apply P v rfl
      rwa [hv_eq] at h
    have hactPi : c.act b (c.piL ⟨j, hjL⟩) = c.piL ⟨j, hjL⟩ := by
      rw [← hPj]
      exact hactP
    have hq : c.piL (c.conjB b ⟨j, hjL⟩ * ⟨j, hjL⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, c.piL_conjB, hactPi, mul_inv_cancel]
    have hz : c.conjB b ⟨j, hjL⟩ * ⟨j, hjL⟩⁻¹ ∈ Subgroup.center ↥L := by
      rw [← c.piL_ker]
      exact hq
    have hcone : c.conjB b ⟨j, hjL⟩ = ⟨j, hjL⟩ :=
      mul_inv_eq_one.mp (c.eq_one_of_mem_center_of_even hZ heven hz)
    have hconjG : (b : G) * (j : G) * (b : G)⁻¹ = (j : G) := by
      have h := congrArg Subtype.val hcone
      rwa [e6QTwoBstarConjAction_apply c.hNL b ⟨j, hjL⟩] at h
    calc (j : G) * (b : G) = ((b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by
          rw [hconjG]
      _ = (b : G) * (j : G) := by group

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

end

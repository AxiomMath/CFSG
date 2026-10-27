module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivLinear
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open
open CFSG.LieType.SemisimpleCentralizers.Held

private theorem ltrcle_blockdata {K : Type} [Field K] [Finite K] {d : ℕ}
    (M : GL (Fin d) K) (hord : ((orderOf M : ℕ) : K) ≠ 0)
    (W : Subgroup (GL (Fin d) K))
    (hW : CFSG.Open.IsComponentOf W
      (Subgroup.centralizer ({M} : Set (GL (Fin d) K)) ⊓ StatedSL d K)) :
    ∃ (r : ℕ) (D : Fin r → Type) (e : Fin r → ℕ) (_ : ∀ i, Field (D i))
      (_ : ∀ i, Finite (D i)) (_ : ∀ i, Algebra K (D i))
      (θ : (∀ i, GL (Fin (e i)) (D i)) →* GL (Fin d) K) (i : Fin r),
      Function.Injective θ ∧ θ.range = Subgroup.centralizer ({M} : Set (GL (Fin d) K)) ∧
      2 ≤ e i ∧
      W = ((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ ∧
      Nonempty (↥W ⧸ Subgroup.center ↥W ≃* StatedProj (StatedSL (e i) (D i))) := by
  classical
  obtain ⟨r, D, e, hFld, hFin, hAlg, _Φ, θ, _hd1, _hΦinj, hθinj, hθrange, _hθapply,
    ⟨i, hd2, hWeq⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsLinBlock_exists M hord W hW
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have eJ : ↥W ≃* ↥(StatedSL (e i) (D i)) :=
    (MulEquiv.subgroupCongr hWeq).trans
      ((Subgroup.equivMapOfInjective _ θ hθinj).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (e i) (D i))
          (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i) hms).symm)
  exact ⟨r, D, e, hFld, hFin, hAlg, θ, i, hθinj, hθrange, hd2, hWeq,
    nonempty_quotientCenter_equiv_statedProj eJ⟩

private theorem ltrcle_main {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    (S : Subgroup (GL (Fin d) K)) (hS : S = StatedSL d K)
    (M : GL (Fin d) K) (hMN : M ∈ Subgroup.normalizer (S : Set (GL (Fin d) K)))
    (hM : M ^ 3 = 1) {J : Subgroup (LargeEvenProj S)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggFix (TableB.projConj S ⟨M, hMN⟩))) :
    ∃ (r : ℕ) (D : Fin r → Type) (e : Fin r → ℕ) (_ : ∀ i, Field (D i))
      (_ : ∀ i, Finite (D i)) (_ : ∀ i, Algebra K (D i))
      (θ : (∀ i, GL (Fin (e i)) (D i)) →* GL (Fin d) K) (i : Fin r),
      Function.Injective θ ∧ θ.range = Subgroup.centralizer ({M} : Set (GL (Fin d) K)) ∧
      2 ≤ e i ∧
      ((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ ≤ S ∧
      J = ((((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ).comap
          S.subtype).map (LargeEvenProjMk S) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL (e i) (D i))) := by
  subst hS
  have hord : ((orderOf M : ℕ) : K) ≠ 0 := by
    have hdvd : orderOf M ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hM
    have hodd : Odd (orderOf M) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 M hodd
  have hαβ : ∀ k : ↥(StatedSL d K),
      LargeEvenProjMk (StatedSL d K) (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL M k) =
        TableB.projConj (StatedSL d K) ⟨M, hMN⟩ (LargeEvenProjMk (StatedSL d K) k) := by
    intro k
    rfl
  obtain ⟨Mtilde, hMtilde, hMJ⟩ :=
    CFSG.StandardType.TCJ.tcjLin_component_lift (LargeEvenProjMk (StatedSL d K))
      QuotientGroup.mk_surjective CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL M)
      (TableB.projConj (StatedSL d K) ⟨M, hMN⟩) hαβ hJ
  let W : Subgroup (GL (Fin d) K) := Mtilde.map (StatedSL d K).subtype
  have hW : CFSG.Assembly.IsComponentOf W
      (Subgroup.centralizer ({M} : Set (GL (Fin d) K)) ⊓ StatedSL d K) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.map_fixSubgroup_conjSL M]
    exact ⟨Subgroup.map_mono hMtilde.1, hMtilde.2.1.map (StatedSL d K).subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective Mtilde (StatedSL d K).subtype Subtype.val_injective).symm
        hMtilde.2.2⟩
  obtain ⟨r, D, e, hFld, hFin, hAlg, θ, i, hθinj, hθrange, hd2, hWeq, hWquot⟩ :=
    ltrcle_blockdata M hord W ((CFSG.Assembly.isComponentOf_iff_open).1 hW)
  have hWle : W ≤ StatedSL d K := fun x hx => (hW.1 hx).2
  have hMtilde_eq : Mtilde = W.comap (StatedSL d K).subtype :=
    (Subgroup.comap_map_eq_self_of_injective (StatedSL d K).subtype_injective Mtilde).symm
  have hJeq : J = (W.comap (StatedSL d K).subtype).map (LargeEvenProjMk (StatedSL d K)) := by
    rw [← hMJ, hMtilde_eq]
  have hperf : commutator ↥W = ⊤ := hW.2.2.1
  have hmemJ : ∀ x : ↥Mtilde, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J :=
    fun x => by
      rw [← hMJ]
      exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥Mtilde →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp Mtilde.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥Mtilde := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) = 1 := congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSL d K)) ∈ Subgroup.center ↥(StatedSL d K) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e' : ↥Mtilde ≃* ↥W :=
    Subgroup.equivMapOfInjective Mtilde (StatedSL d K).subtype Subtype.val_injective
  let f' : ↥W →* ↥J := fJ.comp e'.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e'.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥W := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e'.symm x : ↥Mtilde) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e'.surjective y
    have hx' : x = e' (e'.symm x) := (e'.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨φ⟩ := hWquot
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hperf f' hsurj' hker'
  refine ⟨r, D, e, hFld, hFin, hAlg, θ, i, hθinj, hθrange, hd2, ?_, ?_, ?_⟩
  · rw [← hWeq]; exact hWle
  · rw [← hWeq]; exact hJeq
  · exact ⟨ψ.trans φ⟩

theorem linearFixedComponentBlock {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    (M : GL (Fin d) K)
    (hMN : M ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)))
    (hM : M ^ 3 = 1)
    {J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (ggFix (TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨M, hMN⟩))) :
    ∃ (r : ℕ) (D : Fin r → Type) (e : Fin r → ℕ) (_ : ∀ i, Field (D i))
      (_ : ∀ i, Finite (D i)) (_ : ∀ i, Algebra K (D i))
      (θ : (∀ i, GL (Fin (e i)) (D i)) →* GL (Fin d) K) (i : Fin r),
      Function.Injective θ ∧ θ.range = Subgroup.centralizer ({M} : Set (GL (Fin d) K)) ∧
      2 ≤ e i ∧
      ((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ ≤
          LargeEvenSLGroup (Fin d) K ∧
      J = ((((StatedSL (e i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (e k)) (D k)) i)).map θ).comap
          (LargeEvenSLGroup (Fin d) K).subtype).map
            (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL (e i) (D i))) :=
  ltrcle_main h2 (LargeEvenSLGroup (Fin d) K) (largeEvenSLGroup_eq_statedSL d) M hMN hM hJ

end CFSG.StandardType.KD2Pieces1615

end

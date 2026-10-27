module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZFrameDiag
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZCube
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCoset
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentreFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentre
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Inv
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentSU
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S146A2
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch11SecSFacts2
import CFSG.Quasithin.Vol2.Ch11SecSFacts3
import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
import CFSG.Quasithin.Vol2.Ch11SecSI3
import CFSG.Quasithin.Vol2.Ch11SecSObl
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.Walter.J1Props
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups
section Helpers
open CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
private abbrev tzTorus_e6g : Equiv.Perm (Fin Tag.E6.rank) := CFSG.StandardType.KGCentE6.diagPermE6
private def tzTorus_hPar {L : Type} [Field L] (ξ : Lˣ) (κ : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → Lˣ :=
  fun j => ξ ^ iform (Pi.single j 1) κ
private theorem tzTorus_prod_zpow_eq_zpow_sum {L : Type} [Field L] (ζ : Lˣ)
    (e : Fin Tag.E6.rank → ℤ) : (∏ i, ζ ^ e i) = ζ ^ (∑ i, e i) := by
  classical
  have h : ∀ (s : Finset (Fin Tag.E6.rank)) (e : Fin Tag.E6.rank → ℤ),
      (∏ i ∈ s, ζ ^ e i) = ζ ^ (∑ i ∈ s, e i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro e; simp
    | insert a s ha ih => intro e; rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]
  simpa using h Finset.univ e
private theorem tzTorus_iform_eq_sum_single (β v : Fin Tag.E6.rank → ℤ) :
    iform β v = ∑ j, v j * iform β (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem tzTorus_rootChar_hPar {L : Type} [Field L]
    (ξ : Lˣ) (κ v : Fin Tag.E6.rank → ℤ) :
    rootChar (tzTorus_hPar ξ κ) v = ξ ^ iform v κ := by
  have hsum : iform v κ = ∑ i, v i * iform (Pi.single i 1) κ := by
    rw [iform_comm, tzTorus_iform_eq_sum_single]
    exact Finset.sum_congr rfl fun i _ => by rw [iform_comm]
  simp only [tzTorus_hPar, rootChar]
  calc (∏ i, (ξ ^ iform (Pi.single i 1) κ) ^ v i)
      = ∏ i, ξ ^ (v i * iform (Pi.single i 1) κ) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← zpow_mul, mul_comm]
    _ = ξ ^ (∑ i, v i * iform (Pi.single i 1) κ) := tzTorus_prod_zpow_eq_zpow_sum ξ _
    _ = ξ ^ iform v κ := by rw [hsum]
private theorem tzTorus_symmetrizer_E6_self (i : Fin Tag.E6.rank) : Tag.E6.symmetrizer i i = 1 := by
  have h1 : Tag.E6.symmetrizer = (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := rfl
  rw [h1]; simp
private theorem tzTorus_symmetrizedCartan_eq_cartan_E6
    (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
  rw [symmetrizedCartan_apply, tzTorus_symmetrizer_E6_self, one_mul]
private theorem tzTorus_symmetrizedCartan_e6g
    (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan (tzTorus_e6g i) (tzTorus_e6g j) = Tag.E6.symmetrizedCartan i j := by
  rw [tzTorus_symmetrizedCartan_eq_cartan_E6, tzTorus_symmetrizedCartan_eq_cartan_E6]
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem tzTorus_iform_permLattice_e6g
    (u v : Fin Tag.E6.rank → ℤ) :
    iform (permLattice tzTorus_e6g u) (permLattice tzTorus_e6g v) = iform u v := by
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp tzTorus_e6g (fun i => ∑ j, u (tzTorus_e6g.symm i) *
    Tag.E6.symmetrizedCartan i j * v (tzTorus_e6g.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp tzTorus_e6g (fun j => u (tzTorus_e6g.symm (tzTorus_e6g i)) *
    Tag.E6.symmetrizedCartan (tzTorus_e6g i) j * v (tzTorus_e6g.symm j))]
  simp [tzTorus_symmetrizedCartan_e6g]
private theorem tzTorus_iform_permLattice_perm_symm
    (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice tzTorus_e6g.symm x) y = iform x (permLattice tzTorus_e6g y) := by
  have h2 : permLattice tzTorus_e6g (permLattice tzTorus_e6g.symm x) = x := by
    simpa using CFSG.LieType.Chevalley.ToralSign.permLattice_symm_permLattice tzTorus_e6g.symm x
  have h := tzTorus_iform_permLattice_e6g (permLattice tzTorus_e6g.symm x) y
  rw [h2] at h
  exact h.symm
private theorem tzTorus_step_rootDiagUnit_hPar {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦeq : S.D.Φ = twistHom TwistTag.E6 L Fr) {w : WeylGroup Tag.E6}
    (hn : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
    (ξ : Lˣ) (κ : Fin Tag.E6.rank → ℤ) :
    S.D.step (rootDiagUnit Tag.E6 (tzTorus_hPar ξ κ)) =
      rootDiagUnit Tag.E6 (tzTorus_hPar (ξ ^ S.D.q) (w • permLattice tzTorus_e6g κ)) := by
  have hst : S.D.step = twFrob TwistTag.E6
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      twistHom TwistTag.E6 L Fr g * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹
    rw [hΦeq, hn]; rfl
  rw [hst]
  refine (twFrob_rootDiagUnit TwistTag.E6 Fr w (tzTorus_hPar ξ κ)).trans ?_
  change rootDiagUnit Tag.E6 (weylTuple w (fun i : Fin Tag.E6.rank =>
      Units.map Fr.toMonoidHom (tzTorus_hPar ξ κ (tzTorus_e6g.symm i)))) =
    rootDiagUnit Tag.E6 (tzTorus_hPar (ξ ^ S.D.q) (w • permLattice tzTorus_e6g κ))
  refine congrArg (rootDiagUnit Tag.E6) (funext fun i => ?_)
  rw [weylTuple]
  have hc : rootChar (fun i : Fin Tag.E6.rank =>
        Units.map Fr.toMonoidHom (tzTorus_hPar ξ κ (tzTorus_e6g.symm i))) (w⁻¹ • Pi.single i 1)
      = Units.map Fr.toMonoidHom (rootChar (tzTorus_hPar ξ κ)
          (permLattice tzTorus_e6g.symm (w⁻¹ • Pi.single i 1))) := by
    rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple Fr
      (fun i : Fin Tag.E6.rank => tzTorus_hPar ξ κ (tzTorus_e6g.symm i)) (w⁻¹ • Pi.single i 1)]
    exact congrArg (Units.map Fr.toMonoidHom)
      (rootChar_permLattice (tzTorus_hPar ξ κ) tzTorus_e6g.symm (w⁻¹ • Pi.single i 1)).symm
  rw [hc, tzTorus_rootChar_hPar]
  have harg : iform (permLattice tzTorus_e6g.symm (w⁻¹ • Pi.single i 1)) κ =
      iform (Pi.single i 1) (w • permLattice tzTorus_e6g κ) := by
    calc iform (permLattice tzTorus_e6g.symm (w⁻¹ • Pi.single i 1)) κ
        = iform (w⁻¹ • Pi.single i 1) (permLattice tzTorus_e6g κ) :=
          tzTorus_iform_permLattice_perm_symm (x := w⁻¹ • Pi.single i 1) (y := κ)
      _ = iform (Pi.single i 1) (w • permLattice tzTorus_e6g κ) := by
          have h := CFSG.LieType.Chevalley.iform_smul w (w⁻¹ • Pi.single i 1)
            (permLattice tzTorus_e6g κ)
          rw [smul_inv_smul] at h
          exact h.symm
  rw [harg, tzTorus_hPar]
  refine Units.ext ?_
  simp [hFr]
private theorem tzTorus_e6RootParams_hPar {L : Type} [Field L]
    (ζ : Lˣ) (m : Fin Tag.E6.rank → ℤ) :
    e6RootParams (fun l => ζ ^ m l) = tzTorus_hPar ζ m := by
  funext j
  rw [e6RootParams, tzTorus_hPar, iform_single_left, tzTorus_symmetrizer_E6_self, one_mul]
  calc (∏ l, (ζ ^ m l) ^ Tag.E6.cartan l j)
      = ∏ l, ζ ^ (m l * Tag.E6.cartan l j) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← zpow_mul]
    _ = ζ ^ (∑ l, m l * Tag.E6.cartan l j) := tzTorus_prod_zpow_eq_zpow_sum ζ _
    _ = ζ ^ (∑ l, Tag.E6.cartan j l * m l) := by
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [CFSG.StandardType.KGCentE6.cartan_symmetric_E6, mul_comm]
private theorem tzTorus_frobRootMap_map_zero {L : Type} [Field L]
    (D : LangDatum Tag.E6 L)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (h : FrobRootMap D ρ) : ρ 0 = 0 := by
  have h0 : ρ 0 = ρ 0 + ρ 0 := by simpa using frobRootMap_map_add D h 0 0
  exact (add_left_cancel (show ρ 0 + 0 = ρ 0 + ρ 0 by rw [add_zero]; exact h0)).symm
private theorem tzTorus_rootChar_pow_three {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (hap : ∀ j, a j ^ 3 = 1) (v : Fin Tag.E6.rank → ℤ) : rootChar a v ^ 3 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap j, one_zpow]
private theorem tzTorus_e6g_cartan (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (tzTorus_e6g i) (tzTorus_e6g j) = Tag.E6.cartan i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel
end Helpers
section SteinbergAdjoint
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_norm_torus
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ (2 ^ n)) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3)
    (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (hΨ : componentRoots (rootCharHom a) i = frameRoots σ')
    (c : SL(3, L)) (ζ : Lˣ) (hζ : ζ ^ 9 = 1)
    (hc : (c : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![(ζ : L), ((ζ ^ 2)⁻¹ : Lˣ), (ζ : L)]) :
    ∃ u : Fin Tag.E6.rank → Lˣ, (∀ l, u l ^ 3 = 1) ∧
      ψ c * S.D.step (ψ c) * S.D.step (S.D.step (ψ c)) = rootDiagUnit Tag.E6 (e6RootParams u) := by
  classical
  obtain ⟨Fr, hFr0, hΦeq⟩ := hΦ
  have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hFr0 c, ← hq]
  obtain ⟨w, hnw⟩ := S.D.n_weyl
  set κ : Fin Tag.E6.rank → ℤ := σ' 0 1 - σ' 1 2 with hκdef
  have hqpos : 0 < S.D.q := by rw [hq]; positivity
  have h3q : 3 ∣ S.D.q + 1 := by rw [hq]; exact h3
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hqpos
    exact ⟨x, by rw [hFr, hx]⟩
  have hst : S.D.step = twFrob TwistTag.E6
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      twistHom TwistTag.E6 L Fr g * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹
    rw [hΦeq, hnw]; rfl
  have hρ_root : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice tzTorus_e6g γ := by
    intro γ hγ
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) = rootSubgroup Tag.E6 L (w • permLattice tzTorus_e6g γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ)
      (IsRoot.smul (hγ.permLattice tzTorus_e6g_cartan) w) h3
  have hρ_all : ∀ μ : Fin Tag.E6.rank → ℤ, S.ρ μ = w • permLattice tzTorus_e6g μ := by
    intro μ
    let ρA : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
      { toFun := S.ρ, map_zero' := tzTorus_frobRootMap_map_zero (L := L) S.D S.frob,
        map_add' := frobRootMap_map_add S.D S.frob }
    let σA : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
      { toFun := fun v => w • permLattice tzTorus_e6g v, map_zero' := by simp [permLattice],
        map_add' := fun x y => by rw [permLattice_add, smul_add] }
    have h : ρA μ = σA μ := by
      conv_lhs => rw [show μ = ∑ i, μ i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) from by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      conv_rhs => rw [show μ = ∑ i, μ i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) from by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_zsmul]
      congr 1
      exact hρ_root (Pi.single i 1) (IsRoot.basis i)
    exact h
  have ht : (c : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun k => ((![ζ, (ζ ^ 2)⁻¹, ζ] : Fin 3 → Lˣ) k : L) := by
    rw [hc]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hψc : ψ c = rootDiagUnit Tag.E6 (tzTorus_hPar ζ κ) := by
    rw [tableZ_frame_diag hψ c ![ζ, (ζ ^ 2)⁻¹, ζ] ht]
    congr 1
    funext j
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [tzTorus_hPar, hκdef, iform_sub_right]
    rw [show ((ζ ^ 2)⁻¹ : Lˣ) = ζ ^ (-2 : ℤ) by rw [zpow_neg, zpow_ofNat],
      ← zpow_mul, ← zpow_add]
    congr 1
    ring
  have hstep : ∀ (ξ : Lˣ) (μ : Fin Tag.E6.rank → ℤ),
      S.D.step (rootDiagUnit Tag.E6 (tzTorus_hPar ξ μ)) =
        rootDiagUnit Tag.E6 (tzTorus_hPar (ξ ^ S.D.q) (S.ρ μ)) := by
    intro ξ μ
    rw [tzTorus_step_rootDiagUnit_hPar S hFr hΦeq hnw ξ μ, hρ_all μ]
  have hκcongr : ∀ j, (iform (Pi.single j 1) (S.ρ κ + κ) : ZMod 3) = 0 := by
    obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.glue_of_check2
        CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.noG2_E6 73
        CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.okE6 (by norm_num)
        CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.rdCheck2_E6 a hap i h6
    have h3L : ((3 : ℕ) : L) ≠ 0 := by
      intro h
      have h' := (CharP.cast_eq_zero_iff L 2 3).1 h
      norm_num at h'
    obtain ⟨ω, hω3, hω1⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.exists_cube_root_ne_one h3L
    obtain ⟨ε, hε, ha_eq⟩ := hglueAll ω hω3 hω1
    set m : Fin Tag.E6.rank → ℤ := γ₁ + (2 : ℤ) • γ₂ with hmdef
    have hm_eq : ∀ j, CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.a2Exp Tag.E6 γ₁ γ₂ j =
        iform (Pi.single j 1) m := by
      intro j
      rw [hmdef, iform_add_right, iform_smul_right,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.a2Exp_eq_iform
          (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two hP.1)
          (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two hP.2.1) j,
        iform_comm γ₁ (Pi.single j 1), iform_comm γ₂ (Pi.single j 1)]
    have ha : a = tzTorus_hPar ω (ε • m) := by
      funext j
      rw [ha_eq j, hm_eq j, tzTorus_hPar, iform_smul_right]
    have hchar : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = ω ^ iform v (ε • m) := by
      intro v; rw [ha, tzTorus_rootChar_hPar]
    have hroot : ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ iform v (S.ρ m + m) := by
      have hbasis : ∀ j, (3 : ℤ) ∣ iform (Pi.single j 1) (S.ρ m + m) := by
        intro j
        have hγ : IsRoot Tag.E6 (Pi.single j 1) := IsRoot.basis j
        have hγ' : IsRoot Tag.E6 (S.ρ.symm (Pi.single j 1)) :=
          (S.frob.isRoot_iff (S.ρ.symm (Pi.single j 1))).1 (by
            rw [Equiv.apply_symm_apply]; exact hγ)
        have heq := S.frob.rootChar_eq a hT (S.ρ.symm (Pi.single j 1)) hγ'
        rw [Equiv.apply_symm_apply] at heq
        have hx3 : (rootChar a (S.ρ.symm (Pi.single j 1))) ^ 3 = 1 := tzTorus_rootChar_pow_three hap _
        have hq1 : (rootChar a (S.ρ.symm (Pi.single j 1))) ^ (S.D.q + 1) = 1 := by
          obtain ⟨k, hk⟩ := h3q
          rw [hk, pow_mul, hx3, one_pow]
        have hxq : (rootChar a (S.ρ.symm (Pi.single j 1))) ^ S.D.q =
            (rootChar a (S.ρ.symm (Pi.single j 1)))⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          rw [mul_comm, ← pow_succ]; exact hq1
        have hxinv : rootChar a (S.ρ.symm (Pi.single j 1)) = (rootChar a (Pi.single j 1))⁻¹ := by
          rw [heq, hxq, inv_inv]
        have hsum1 : rootChar a (S.ρ.symm (Pi.single j 1) + Pi.single j 1) = 1 := by
          rw [rootChar_add, hxinv, inv_mul_cancel]
        rw [hchar (S.ρ.symm (Pi.single j 1) + Pi.single j 1)] at hsum1
        have hdvdω : (3 : ℤ) ∣ iform (S.ρ.symm (Pi.single j 1) + Pi.single j 1) (ε • m) := by
          haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
          have h : (orderOf ω : ℤ) ∣ iform (S.ρ.symm (Pi.single j 1) + Pi.single j 1) (ε • m) :=
            (orderOf_dvd_iff_zpow_eq_one (x := ω)).2 hsum1
          have h3z : ((orderOf ω : ℕ) : ℤ) = (3 : ℤ) := by rw [hord]; norm_num
          rwa [h3z] at h
        have hdvd : (3 : ℤ) ∣ iform (S.ρ.symm (Pi.single j 1) + Pi.single j 1) m := by
          rcases hε with rfl | rfl
          · simpa using hdvdω
          · rw [iform_smul_right] at hdvdω
            exact (Int.dvd_neg).1 (by simpa using hdvdω)
        have hiso : iform (S.ρ.symm (Pi.single j 1)) m = iform (Pi.single j 1) (S.ρ m) := by
          have h := S.frob.iform_eq (S.ρ.symm (Pi.single j 1)) m
          simpa using h.symm
        have hsplit : iform (S.ρ.symm (Pi.single j 1) + Pi.single j 1) m =
            iform (Pi.single j 1) (S.ρ m + m) := by
          rw [iform_add_left, hiso]
          exact (iform_add_right (Pi.single j 1) (S.ρ m) m).symm
        rwa [hsplit] at hdvd
      intro v
      rw [iform_comm, tzTorus_iform_eq_sum_single]
      refine Finset.dvd_sum fun i _ => ?_
      rw [iform_comm]
      exact dvd_mul_of_dvd_right (hbasis i) (v i)
    have hx_mem : σ' 0 1 = γ₁ ∨ σ' 0 1 = γ₂ ∨ σ' 0 1 = γ₁ + γ₂ ∨
        σ' 0 1 = -γ₁ ∨ σ' 0 1 = -γ₂ ∨ σ' 0 1 = -(γ₁ + γ₂) := by
      have hmem : σ' 0 1 ∈ frameRoots σ' := ⟨0, 1, by decide, rfl⟩
      rw [show frameRoots σ' = ({γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} :
        Set (Fin Tag.E6.rank → ℤ)) from hΨ.symm.trans hΨeq] at hmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    have hy_mem : σ' 1 2 = γ₁ ∨ σ' 1 2 = γ₂ ∨ σ' 1 2 = γ₁ + γ₂ ∨
        σ' 1 2 = -γ₁ ∨ σ' 1 2 = -γ₂ ∨ σ' 1 2 = -(γ₁ + γ₂) := by
      have hmem : σ' 1 2 ∈ frameRoots σ' := ⟨1, 2, by decide, rfl⟩
      rw [show frameRoots σ' = ({γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} :
        Set (Fin Tag.E6.rank → ℤ)) from hΨ.symm.trans hΨeq] at hmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    have hxy : iform (σ' 0 1) (σ' 1 2) = -1 := by
      have h02 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two
        (hψ.isRoot 0 2 (by decide))
      have h11 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two
        (hψ.isRoot 0 1 (by decide))
      have h22 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two
        (hψ.isRoot 1 2 (by decide))
      rw [← hψ.add 0 1 2, iform_add_left, iform_add_right, iform_add_right,
        iform_comm (σ' 1 2) (σ' 0 1), h11, h22] at h02
      omega
    obtain ⟨η, hη, hsign⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.exists_sign_three_dvd
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two hP.1)
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two hP.2.1)
        (by have h11 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.iform_self_eq_two hP.1
            have h := hP.2.2.2; omega)
        hx_mem hy_mem hxy
    have hB : ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ iform (κ - η • m) v := by
      intro v
      have h := hsign v
      have h1 : iform (σ' 0 1) v + 2 * iform (σ' 1 2) v = iform κ v + 3 * iform (σ' 1 2) v := by
        have e : σ' 0 1 + (2 : ℤ) • σ' 1 2 = κ + (3 : ℤ) • σ' 1 2 := by rw [hκdef]; abel
        calc iform (σ' 0 1) v + 2 * iform (σ' 1 2) v
            = iform (σ' 0 1) v + iform ((2 : ℤ) • σ' 1 2) v := by rw [iform_smul_left]
          _ = iform (σ' 0 1 + (2 : ℤ) • σ' 1 2) v := (iform_add_left _ _ _).symm
          _ = iform (κ + (3 : ℤ) • σ' 1 2) v := by rw [e]
          _ = iform κ v + iform ((3 : ℤ) • σ' 1 2) v := iform_add_left _ _ _
          _ = iform κ v + 3 * iform (σ' 1 2) v := by rw [iform_smul_left]
      have h2 : iform γ₁ v + 2 * iform γ₂ v = iform m v := by
        have e : γ₁ + (2 : ℤ) • γ₂ = m := hmdef.symm
        calc iform γ₁ v + 2 * iform γ₂ v
            = iform γ₁ v + iform ((2 : ℤ) • γ₂) v := by rw [iform_smul_left]
          _ = iform (γ₁ + (2 : ℤ) • γ₂) v := (iform_add_left _ _ _).symm
          _ = iform m v := by rw [e]
      rw [h1, h2] at h
      have h3 : (3 : ℤ) ∣ 3 * iform (σ' 1 2) v := dvd_mul_right 3 _
      have h4 : (3 : ℤ) ∣ (iform κ v + 3 * iform (σ' 1 2) v) - η * iform m v -
          (3 * iform (σ' 1 2) v) := dvd_sub h h3
      have h5 : (iform κ v + 3 * iform (σ' 1 2) v) - η * iform m v -
          (3 * iform (σ' 1 2) v) = iform κ v - η * iform m v := by ring
      rw [h5] at h4
      rw [iform_sub_left, iform_smul_left]
      exact h4
    have hS : ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ iform v (S.ρ (κ - η • m)) := by
      intro v
      have h := hB (S.ρ.symm v)
      rw [iform_comm]
      have hiso : iform (S.ρ (κ - η • m)) v = iform (κ - η • m) (S.ρ.symm v) := by
        have h := S.frob.iform_eq (κ - η • m) (S.ρ.symm v)
        rwa [Equiv.apply_symm_apply] at h
      rw [hiso]
      exact h
    have hfinal : ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ iform v (S.ρ κ + κ) := by
      intro v
      let ρA : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
        { toFun := S.ρ, map_zero' := tzTorus_frobRootMap_map_zero (L := L) S.D S.frob,
          map_add' := frobRootMap_map_add S.D S.frob }
      have hsub : S.ρ (κ - η • m) = S.ρ κ - η • S.ρ m := by
        change ρA (κ - η • m) = ρA κ - η • ρA m
        rw [map_sub, map_zsmul]
      have hdecomp : S.ρ κ + κ = S.ρ (κ - η • m) + η • (S.ρ m + m) + (κ - η • m) := by
        rw [hsub, smul_add]; abel
      have h1 : (3 : ℤ) ∣ iform v (S.ρ (κ - η • m)) := hS v
      have h2 : (3 : ℤ) ∣ iform v (η • (S.ρ m + m)) := by
        rw [iform_smul_right]
        exact dvd_mul_of_dvd_right (hroot v) η
      have h3 : (3 : ℤ) ∣ iform v (κ - η • m) := by rw [iform_comm]; exact hB v
      rw [hdecomp, iform_add_right, iform_add_right]
      exact dvd_add (dvd_add h1 h2) h3
    intro j
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hfinal (Pi.single j 1)
  have hcube : ∀ i, ((κ - S.ρ κ + S.ρ (S.ρ κ)) i : ZMod 3) = 0 :=
    e6_twistedCube_congr S.ρ (frobRootMap_map_add S.D S.frob) S.frob.iform_eq
      (e6_not_cosetW_of_tw S.D S.frob ⟨Fr, hFr, hΦeq⟩) κ hκcongr
  have hq3 : (S.D.q : ZMod 3) = -1 := by
    obtain ⟨k, hk⟩ := h3q
    have h : (S.D.q : ℤ) = 3 * (k : ℤ) - 1 := by omega
    rw [← Int.cast_natCast, h]
    push_cast
    have h3z : (3 : ZMod 3) = 0 := by decide
    rw [h3z]; ring
  refine ⟨fun l => ζ ^ (κ l + (S.D.q : ℤ) * (S.ρ κ) l + (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l), ?_, ?_⟩
  · intro l
    have hm3 : (3 : ℤ) ∣ κ l + (S.D.q : ℤ) * (S.ρ κ) l + (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l := by
      have h := hcube l
      simp only [Pi.sub_apply, Pi.add_apply] at h
      have hz : (((κ l + (S.D.q : ℤ) * (S.ρ κ) l + (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l : ℤ) : ZMod 3)) = 0 := by
        push_cast
        rw [hq3]
        push_cast at h
        ring_nf at h ⊢
        exact h
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    obtain ⟨t, ht⟩ := hm3
    calc (ζ ^ (κ l + (S.D.q : ℤ) * (S.ρ κ) l + (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l)) ^ 3
        = ζ ^ ((κ l + (S.D.q : ℤ) * (S.ρ κ) l + (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l) * 3) := by
          rw [← zpow_natCast, ← zpow_mul]; congr 1
      _ = ζ ^ (9 * t) := by rw [ht]; congr 1; ring
      _ = (ζ ^ 9) ^ t := by exact zpow_mul ζ (9 : ℤ) t
      _ = 1 := by rw [hζ, one_zpow]
  · have hs1 := hstep ζ κ
    have hs2 := hstep (ζ ^ S.D.q) (S.ρ κ)
    rw [hψc, hs1, hs2, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    rw [show ζ ^ S.D.q = ζ ^ (S.D.q : ℤ) by rw [zpow_natCast],
      show (ζ ^ (S.D.q : ℤ)) ^ S.D.q = ζ ^ ((S.D.q : ℤ) ^ 2) by
        rw [← zpow_natCast, ← zpow_mul]; ring_nf]
    congr 1
    rw [tzTorus_e6RootParams_hPar ζ (fun l => κ l + (S.D.q : ℤ) * (S.ρ κ) l +
      (S.D.q : ℤ) ^ 2 * (S.ρ (S.ρ κ)) l)]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply, tzTorus_hPar, tzTorus_hPar, tzTorus_hPar, tzTorus_hPar,
      ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add]
    congr 1
    change iform (Pi.single j 1) κ + (S.D.q : ℤ) * iform (Pi.single j 1) (S.ρ κ) +
        (S.D.q : ℤ) ^ 2 * iform (Pi.single j 1) (S.ρ (S.ρ κ)) =
      iform (Pi.single j 1) (κ + (S.D.q : ℤ) • S.ρ κ + (S.D.q : ℤ) ^ 2 • S.ρ (S.ρ κ))
    rw [iform_add_right, iform_add_right, iform_smul_right, iform_smul_right]
end SteinbergAdjoint
end CFSG.StandardType.TablePThreeKG

end

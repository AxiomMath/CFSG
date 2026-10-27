module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedPair
import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankRot
import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
import CFSG.LinearAlgebra.QuadraticPieceDihedral
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels
import CFSG.ClassicalInvolution.Q3.Q3PlanParams
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import Certificates.Certificate8046
import Certificates.Certificate8049

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {r : ℕ} {U : Fin r → Submodule F V}
  {E : Subgroup ↥(orthDerived Q)}

private theorem false_of_aniso_plane (hQ : (polarBilin Q).Nondegenerate)
    (hdim6 : 6 ≤ Module.finrank F V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hU : IsPlaneDecomp Q E ⊤ U)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    {P : Submodule F V} (hPW : P ≤ polarPerp Q (⨆ j, U j))
    (hP2 : Module.finrank F P = 2) (hPani : ∀ x ∈ P, Q x = 0 → x = 0) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hPreg : (polarBilin (Q.comp P.subtype)).Nondegenerate := by
    refine CFSG.LocalAnalysis.ComponentInitial.finite_anisotropic_plane_regular
      (Q := Q.comp P.subtype) ?_ ?_
    · simp [hP2]
    · intro x hx hQx
      exact hx (Subtype.ext (hPani x x.2 hQx))
  have htrivW : ∀ b ∈ E, ∀ x ∈ polarPerp Q (⨆ j, U j), (b : V ≃ₗ[F] V) x = x :=
    fun b hb x hx => hU.apply_of_perp b hb x Submodule.mem_top hx
  have htrivP : ∀ b ∈ E, ∀ x ∈ P, (b : V ≃ₗ[F] V) x = x :=
    fun b hb x hx => htrivW b hb x (hPW hx)
  obtain ⟨x, hxP, y, hyP, hQx, hQy, hkord⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.exists_orderOf_reflect_mul_reflect_eq
      (Q := Q) hP2 hPani hp hp2 hpq
  set k : V ≃ₗ[F] V := reflect Q x * reflect Q y with hkdef
  have hkO : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q x) (reflect_mem_orthogonalGroup Q y)
  have hkp : k ^ p = 1 := by
    rw [hkdef]
    rw [← hkord]
    exact pow_orderOf_eq_one _
  have hkΩ : k ∈ orthDerived Q :=
    CFSG.LocalAnalysis.GLTheoremA.T173M.mem_orthDerived_of_odd_pow_of_six_le Q hQ hdim6 hkO
      (hp.odd_of_ne_two hp2) hkp
  have hxPres : ∀ z ∈ P, reflect Q x z ∈ P := by
    intro z hz
    rw [reflect_apply hQx]
    exact P.sub_mem hz (P.smul_mem _ hxP)
  have hyPres : ∀ z ∈ P, reflect Q y z ∈ P := by
    intro z hz
    rw [reflect_apply hQy]
    exact P.sub_mem hz (P.smul_mem _ hyP)
  have hPres : ∀ u ∈ P, k u ∈ P := by
    intro u hu
    rw [hkdef, LinearEquiv.mul_apply]
    exact hxPres _ (hyPres u hu)
  have hPperp : ∀ w ∈ polarPerp Q P, k w = w := by
    intro w hw
    have hx0 : polar Q x w = 0 := mem_polarPerp_iff.1 hw x hxP
    have hy0 : polar Q y w = 0 := mem_polarPerp_iff.1 hw y hyP
    rw [hkdef, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hy0,
      reflect_apply_of_polar_eq_zero hx0]
  have hcomm : ∀ b ∈ E, k * (b : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V) * k := by
    intro b hb
    have hbO : (b : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      orthDerived_le_orthogonalGroup b.2
    exact (commute_of_apply_eq hPreg hbO (htrivP b hb) hPres hPperp).symm
  let kE : ↥(orthDerived Q) := ⟨k, hkΩ⟩
  have hkE : kE ∈ E := hsc kE (fun b hb => Subtype.ext (hcomm b hb)) (Subtype.ext hkp)
  have hkP : ∀ u ∈ P, k u = u := fun u hu => htrivP kE hkE u hu
  have hk1 : k = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ P ⊔ polarPerp Q P := by
      rw [(isCompl_polarPerp hPreg).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hkP u hu, hPperp w hw]
    rfl
  have hk1' : orderOf k = 1 := by rw [hk1, orderOf_one]
  rw [hkord] at hk1'
  exact hp.ne_one hk1'

theorem exists_planeFrame_of_selfCentralizing (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (k : ℕ) (U : Fin k → Submodule F V) (e : Fin k → ↥(orthDerived Q)),
      IsPlaneFrame Q p U e E ∧
      ((k = ℓ ∧ (⨆ j, U j) = ⊤) ∨
        (k + 1 = ℓ ∧ ∃ f f' : V, f ∈ polarPerp Q (⨆ j, U j) ∧ f' ∈ polarPerp Q (⨆ j, U j) ∧
          Q f = 0 ∧ Q f' = 0 ∧ QuadraticMap.polar Q f f' = 1)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdim6 : 6 ≤ Module.finrank F V := by omega
  have hreg : RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ :=
    exists_planeDecomp hQ hp hp2 hpq hE ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  choose g hgE hgfix hgpow using hU.exists_gen
  have hgp : ∀ j, (g j) ^ p = 1 := fun j => hE.2 (g j) (hgE j)
  let g' : (j : Fin r) → U j ≃ₗ[F] U j := fun j =>
    restrictEquiv (U j) (g j : V ≃ₗ[F] V) (hU.maps_to (g j) (hgE j) j)
      (hU.maps_to (g j)⁻¹ (E.inv_mem (hgE j)) j)
  have hg'mem : ∀ j, g' j ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j).subtype) := fun j =>
    CFSG.LinearAlgebra.restrictEquiv_mem_orthogonalGroup (orthDerived_le_orthogonalGroup (g j).2)
      (hU.maps_to (g j) (hgE j) j) (hU.maps_to (g j)⁻¹ (E.inv_mem (hgE j)) j)
  let rfun : (j : Fin r) → V ≃ₗ[F] V := fun j =>
    extendHom (isCompl_orthPerp (hU.toIsPlaneSystem.nondeg j)) ⟨g' j, hg'mem j⟩
  have hrfunP : ∀ j, (rfun j) ^ p = 1 := by
    intro j
    have hgp' : (g j : V ≃ₗ[F] V) ^ p = 1 := by
      rw [← Subgroup.coe_pow (orthDerived Q) (g j) p, hgp j, Subgroup.coe_one]
    have hgj'p : (g' j) ^ p = 1 := by
      refine LinearEquiv.ext fun x => Subtype.ext ?_
      rw [CFSG.LinearAlgebra.restrictEquiv_pow_apply (U j) (g j : V ≃ₗ[F] V) _ _ p x, hgp']
      rfl
    have : (⟨g' j, hg'mem j⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j).subtype))) ^ p
        = 1 := Subtype.ext hgj'p
    rw [show rfun j = extendHom (isCompl_orthPerp (hU.toIsPlaneSystem.nondeg j))
      ⟨g' j, hg'mem j⟩ from rfl, ← map_pow, this, map_one]
  have hrfun_apply : ∀ (j : Fin r) (x : U j),
      rfun j (x : V) = (g j : V ≃ₗ[F] V) (x : V) := by
    intro j x
    rw [show rfun j = extendHom (isCompl_orthPerp (hU.toIsPlaneSystem.nondeg j))
      ⟨g' j, hg'mem j⟩ from rfl, extendHom_apply_mem,
      CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv]
  have hrfun_fix : ∀ (j : Fin r) {w : V},
      w ∈ polarPerp Q (U j) → rfun j w = w := by
    intro j w hw
    exact extendHom_fix (isCompl_orthPerp (hU.toIsPlaneSystem.nondeg j)) ⟨g' j, hg'mem j⟩ hw
  have hrfun_ne_one : ∀ j, rfun j ≠ 1 := by
    intro j h1
    obtain ⟨x, hxU, hx0⟩ :=
      exists_ne_zero_mem_of_finrank_eq_two (U j) (hU.toIsPlaneSystem.finrank_eq j)
    have : (g j : V ≃ₗ[F] V) (x : V) = x := by
      rw [← hrfun_apply j ⟨x, hxU⟩, h1]
      rfl
    exact hx0 (hgfix j x hxU this)
  have hrfun_order : ∀ j, orderOf (rfun j) = p := fun j =>
    orderOf_eq_prime (hrfunP j) (hrfun_ne_one j)
  have hrfunΩ : ∀ j, rfun j ∈ orthDerived Q := fun j =>
    CFSG.LocalAnalysis.GLTheoremA.T173M.mem_orthDerived_of_odd_pow_of_six_le Q hQ hdim6
      (extendHom_mem _ _) (hp.odd_of_ne_two hp2) (hrfunP j)
  let rj : Fin r → ↥(orthDerived Q) := fun j => ⟨rfun j, hrfunΩ j⟩
  have hrfun_pow_apply : ∀ (j : Fin r) (n : ℕ) (x : U j),
      ((rfun j) ^ n) (x : V) = ((g j : V ≃ₗ[F] V) ^ n) (x : V) := fun j n x =>
    pow_apply_eq_of_apply_eq (fun y hy => hU.maps_to (g j) (hgE j) j y hy)
      (fun y hy => hrfun_apply j ⟨y, hy⟩) n (x : V) x.2
  have hrfun_comm : ∀ (j : Fin r) (b : ↥(orthDerived Q)), b ∈ E →
      rfun j * (b : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V) * rfun j := by
    intro j b hb
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ U j ⊔ polarPerp Q (U j) := by
      rw [(isCompl_polarPerp (hU.toIsPlaneSystem.nondeg j)).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    have hbu : (b : V ≃ₗ[F] V) u ∈ U j := hU.maps_to b hb j u hu
    have hbw : (b : V ≃ₗ[F] V) w ∈ polarPerp Q (U j) :=
      apply_mem_polarPerp (Bb := E) (fun c hc y hy => hU.maps_to c hc j y hy) hb hw
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, map_add, map_add,
      hrfun_apply j ⟨u, hu⟩, hrfun_apply j ⟨(b : V ≃ₗ[F] V) u, hbu⟩,
      hrfun_fix j hw, hrfun_fix j hbw]
    have hcommg : (g j : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) =
        (b : V ≃ₗ[F] V) * (g j : V ≃ₗ[F] V) :=
      congrArg (fun z : ↥E => ((z : ↥(orthDerived Q)) : V ≃ₗ[F] V))
        (hE.1.is_comm.comm (⟨g j, hgE j⟩ : ↥E) ⟨b, hb⟩)
    have hgu : (g j : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) u) =
        (b : V ≃ₗ[F] V) ((g j : V ≃ₗ[F] V) u) := by
      have := congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) hcommg) u
      simpa [LinearEquiv.mul_apply] using this
    rw [hgu, map_add]
  have hrjE : ∀ j, rj j ∈ E := by
    intro j
    refine hsc (rj j) (fun b hb => ?_) (Subtype.ext (hrfunP j))
    exact Subtype.ext (hrfun_comm j b hb)
  have hrj_order : ∀ j, orderOf (rj j) = p := by
    intro j
    change orderOf (⟨rfun j, hrfunΩ j⟩ : ↥(orthDerived Q)) = p
    rw [Subgroup.orderOf_mk]
    exact hrfun_order j
  have hother : ∀ i j : Fin r, i ≠ j → ∀ x ∈ U i, (rj j : V ≃ₗ[F] V) x = x := by
    intro i j hij x hx
    refine hrfun_fix j (mem_polarPerp_iff.2 fun y hy => ?_)
    rw [QuadraticMap.polar_comm]
    exact hU.toIsPlaneSystem.perp i j hij x hx y hy
  have hpow : ∀ b ∈ E, ∀ j : Fin r, ∃ n : ℕ, ∀ x ∈ U j,
      (b : V ≃ₗ[F] V) x = ((rj j : V ≃ₗ[F] V) ^ n) x := by
    intro b hb j
    obtain ⟨n, hn⟩ := hgpow j b hb
    refine ⟨n, fun x hx => ?_⟩
    rw [hn x hx]
    exact (hrfun_pow_apply j n ⟨x, hx⟩).symm
  have hframe : IsPlaneFrame Q p U rj E :=
  { toIsPlaneSystem := hU.toIsPlaneSystem
    orderOf_eq := hrj_order
    apply_of_perp := fun j x hx => hrfun_fix j hx
    maps_to := by
      intro j x hx
      rw [show (rj j : V ≃ₗ[F] V) x = rfun j x from rfl, hrfun_apply j ⟨x, hx⟩]
      exact hU.maps_to (g j) (hgE j) j x hx
    eq_zero_of_apply_eq := by
      intro j x hx hfix
      refine hgfix j x hx ?_
      rw [← hrfun_apply j ⟨x, hx⟩]
      exact hfix
    isElemAbelian := hE
    closure_eq := hU.closure_eq_of_exists_pow rj hrjE hother hpow }
  set W : Submodule F V := polarPerp Q (⨆ j, U j) with hWdef
  have hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict
      (polarNondegOn_orthPerp hQ (hU.toIsPlaneSystem.isCompl_iSup))
  have hUuniv : (⨆ j : Fin r, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin r)), U j := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
    · refine iSup₂_le fun j _ => le_iSup U j
  have hUfin : Module.finrank F ↥(⨆ j : Fin r, U j) = 2 * r := by
    rw [hUuniv, hU.toIsPlaneSystem.finrank_biSup, Finset.card_univ, Fintype.card_fin]
  have hdimW : Module.finrank F W = 2 * ℓ - 2 * r := by
    rw [hWdef, finrank_polarPerp hQ, hUfin, hdim]
  have hWAlt : (QuadraticMap.polarBilin (Q.comp W.subtype)).IsAlt := fun v => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul,
      CharTwo.add_self_eq_zero]
  have hWeven : Even (Module.finrank F W) :=
    LinearMap.BilinForm.IsAlt.even_finrank hWAlt hWnd
  have hdimWle : Module.finrank F W ≤ 2 := by
    by_contra hle
    obtain ⟨m, hm⟩ := hWeven
    have hm2 : 2 ≤ m := by omega
    have hdim2 : Module.finrank F W = 2 * m := by omega
    obtain ⟨a, b, hab⟩ := exists_isAnisoPair (Q := Q.comp W.subtype) hWnd hdim2 hm2
    have hab' : IsAnisoPair Q (a : V) (b : V) := IsAnisoPair.of_restrict hab
    let P : Submodule F V := Submodule.span F {(a : V), (b : V)}
    have hPW : P ≤ W := Submodule.span_le.mpr (by
      rintro z (rfl | rfl)
      · exact a.2
      · exact b.2)
    have hP2 : Module.finrank F P = 2 := hab'.finrank_span_pair
    have hPani : ∀ x ∈ P, Q x = 0 → x = 0 := fun x hx => hab'.eq_zero_of_mem_span_pair hx
    exact false_of_aniso_plane hQ hdim6 hp hp2 hpq hU hsc hPW hP2 hPani
  have hrle : r ≤ ℓ := by
    have h1 : Module.finrank F ↥(⨆ j : Fin r, U j) ≤ Module.finrank F V :=
      Submodule.finrank_le _
    rw [hUfin, hdim] at h1
    omega
  refine ⟨r, U, rj, hframe, ?_⟩
  rcases Nat.eq_zero_or_pos (Module.finrank F W) with hW0 | hWpos
  · left
    have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp hW0
    have hsup : (⨆ j, U j) ⊔ W = ⊤ := hU.toIsPlaneSystem.isCompl_iSup.sup_eq_top
    refine ⟨?_, ?_⟩
    · omega
    · rwa [hWbot, sup_bot_eq] at hsup
  · right
    obtain ⟨m, hm⟩ := hWeven
    have hW2 : Module.finrank F W = 2 := by omega
    have hr : r + 1 = ℓ := by omega
    have hWplus : IsPlusType (Q.restrict W) := by
      by_contra hani
      have hPani : ∀ x ∈ W, Q x = 0 → x = 0 := by
        intro x hxW hQx
        by_contra hx0
        exact hani ((CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two
          (Q := Q) hW2).2 ⟨x, hxW, hx0, hQx⟩)
      exact false_of_aniso_plane hQ hdim6 hp hp2 hpq hU hsc (le_refl W) hW2 hPani
    obtain ⟨f, hfW, hf0, hQf⟩ :=
      (CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two
        (Q := Q) hW2).1 hWplus
    have hWreg : PolarNondegOn Q W := by
      intro x hxW hx0
      refine Subtype.ext_iff.mp (hWnd.1 ⟨x, hxW⟩ fun y => ?_)
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      exact hx0 y y.2
    obtain ⟨v, hvW, hvf⟩ := hWreg.exists_polar_ne_zero hfW hf0
    have hh : polar Q f ((polar Q f v)⁻¹ • v) = 1 := by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hvf]
    let Pd := HypPair.ofPolarEqOne hQf hh
    refine ⟨hr, f, Pd.f, hfW, ?_, hQf, Pd.Q_f, ?_⟩
    · rw [HypPair.ofPolarEqOne_f]
      exact W.sub_mem (W.smul_mem _ hvW) (W.smul_mem _ hfW)
    · have := Pd.polar_ef
      rwa [HypPair.ofPolarEqOne_e] at this

end CFSG.StandardType.OmNsRootGen

end

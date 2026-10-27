module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
import all CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.Blueprint.LieModelAPI
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.SuN
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
import CFSG.Models.Transport
import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.T171Sh
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical2 Matrix
open scoped Pointwise commutatorElement MatrixGroups

private lemma cycFamily_norm_of_eq_one {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (hs : s = 1) (y : P.S 0) : P.norm y = y := by
  subst hs
  have hdiag : P.diag y = Pi.mulSingle 0 (P.iter 0 y) := by
    funext k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [Pi.mulSingle_eq_same]
    rfl
  rw [CycFamily.norm, MonoidHom.comp_apply, hdiag, P.mu_mulSingle, P.coe_iter, ZMod.val_zero,
    iterHom_zero]

theorem exists_unitary_frame_cover
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σf : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σf) (hΨ : componentRoots (rootCharHom a) i = frameRoots σf)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a' b, a' ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σf a' b) = σf (π b) (π a'))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (h32 : (ν, r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) ≠
      (3, 2)) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))) ∧
      ∃ (z : ModGL τ L) (f : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →* ModGL τ L),
        z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ∧
        (∀ X : SL(ν, L), iterHom S.D.step
            (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) (z * ψ X * z⁻¹) =
          z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹) ∧
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
          ∀ c : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)),
            f c = z * ψ (c : SL(ν, L)) * z⁻¹) ∧
        f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        f.ker ≤ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ∧
        ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)),
          S.D.step y = y →
          ∃ G : GL (Fin ν) L,
            ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * (G : Matrix (Fin ν) (Fin ν) L) = 1 ∧
            ∀ c c' : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)),
              (c' : SL(ν, L)) = conjSLn G (c : SL(ν, L)) → y * f c * y⁻¹ = f c' := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  obtain ⟨σQ, z, hσQ, hzZ, hnorm, hconj⟩ :=
    exists_unitary_untwist_kd264alg S hT i hν hψ hΨ π hπ hr hchar he hq
  have hσQc : ∀ c, σQ c = c ^ (r ^ (e * s)) := hσQ
  have hqpow : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  have hes : 1 ≤ e * s := Nat.succ_le_of_lt (Nat.mul_pos he hs0)
  have : CharP L r := hchar
  obtain ⟨-, hCqs, -⟩ :=
    stdUnitary_fixSubgroup (ν := ν) hr (f := e * s) hes σQ hσQc hν
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCq : CFSG.IsQuasisimple C := hCqs h32
  have hCperf : Group.IsPerfect C := hCq.1
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hkerne : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σf _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hSLq : CFSG.IsQuasisimple SL(ν, L) := isQuasisimple_specialLinearGroup hν
  have hker : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hSLq ψ.ker with h | h
    · exact h
    · exact absurd h hkerne
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hzA : ∀ u ∈ P.A, z * u * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun u hu => h hu
  have hZconj : ∀ x : ModGL τ L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro u hu
    have := hx _ (hzA u hu)
    have e1 : z * u * z⁻¹ * (z * x * z⁻¹) = z * (u * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * u * z⁻¹) = z * (x * u) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hkerne fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ ((c : C) : SL(ν, L)) * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS _)
  have hθfix : ∀ c : C, iterHom S.D.step s (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i _).2 (by
        have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
        rw [e]
        exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(ν, L),
      iterHom S.D.step s (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : iterHom S.D.step s (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (stdUnitary σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g * g⁻¹ ∈ P.Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (q : SL(ν, L)),
        Commute w q := fun w hw q => (Subgroup.mem_center_iff.1 hw q).symm
    have hfixc : stdUnitary σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
        (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    refine ⟨⟨⁅X, X'⁆, (hCmem _).2 hfixc⟩, ?_⟩
    rw [hθ]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθZ : ∀ c : C, θ c ∈ P.Z → c ∈ Subgroup.center C := by
    intro c hc
    rw [hθ] at hc
    have h := hcentral _ (hZconj _ hc)
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (Subgroup.mem_center_iff.1 h (d : SL(ν, L)))
  let θ₀ : C →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀ : ∀ c, ((θ₀ c : P.S 0) : ModGL τ L) = θ c := fun c => rfl
  let f : C →* ModGL τ L := P.norm.comp θ₀
  have hf : ∀ c : C, f c = P.norm (θ₀ c) := fun c => rfl
  have hfix : ∀ c, iterHom S.D.step s ((θ₀ c : P.S 0) : ModGL τ L) = θ₀ c := fun c => by
    rw [hθ₀]; exact hθfix c
  have hYW : ⁅P.Y, P.Y⁆ ≤ θ.range := by
    rw [Subgroup.commutator_le]
    intro u hu u' hu'
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    obtain ⟨hu0', huZ'⟩ := P.mem_Y.1 hu'
    rw [hP0] at hu0 hu0'
    exact hθY u u' hu0 hu0' huZ huZ'
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
  have hrsA : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, outerOrbitFamily_A]
    exact hx1
  have hle : R ≤ f.range := by
    intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y', hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y'
    congr 1
    exact Subtype.ext hc
  have hkerf : f.ker ≤ Subgroup.center C := by
    intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  have hperf_le : Group.IsPerfect C →
      f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro hperf
    rintro _ ⟨x, rfl⟩
    exact outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix x
  have hrange : f.range = R := le_antisymm (hperf_le hCperf) hle
  refine ⟨σQ, hσQc, z, f, hzZ, hconj, fun hs1 c => ?_, hrange, hkerf, ?_⟩
  · rw [hf c, cycFamily_norm_of_eq_one P hs1 (θ₀ c), hθ₀, hθ]
  intro y hyZ hyF
  have huZ : z⁻¹ * y * z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hyZ) hzZ
  obtain ⟨M, hM⟩ := exists_conj_frame_of_mem_kd264alg i (by omega) hψ hΨ huZ
  have hyA : ∀ A : SL(ν, L), y * (z * ψ A * z⁻¹) * y⁻¹ =
      z * ψ (conjSLn M A) * z⁻¹ := by
    intro A
    rw [← hM A]
    group
  have hMinv : ∀ A : SL(ν, L), ψ (conjSLn M⁻¹ A) =
      (z⁻¹ * y * z)⁻¹ * ψ A * (z⁻¹ * y * z) := by
    intro A
    have h1 := hM (conjSLn M⁻¹ A)
    rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one] at h1
    rw [← h1]
    group
  have hFs : iterHom S.D.step s y = y := iterHom_eq_self_of_fixed hyF s
  have hcomm : ∀ A : SL(ν, L),
      ψ (conjSLn (stdGL σQ M) (stdUnitary σQ.toRingHom A)) =
        ψ (conjSLn M (stdUnitary σQ.toRingHom A)) := by
    intro A
    have e2 : iterHom S.D.step s (y * (z * ψ A * z⁻¹) * y⁻¹) =
        y * iterHom S.D.step s (z * ψ A * z⁻¹) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFs]
    rw [hyA, hconj, hconj, hyA, stdUnitary_conjSLn] at e2
    exact mul_right_cancel (mul_left_cancel e2)
  have hstdsurj : Function.Surjective (stdUnitary (ν := ν) σQ.toRingHom) := fun X =>
    ⟨(stdUnitaryEquiv (ν := ν) σQ).symm X, (stdUnitaryEquiv (ν := ν) σQ).apply_symm_apply X⟩
  set Dm : GL (Fin ν) L := M⁻¹ * stdGL σQ M with hDm
  have hDψ : ∀ B : SL(ν, L), ψ (conjSLn Dm B) = ψ B := by
    intro B
    obtain ⟨A, rfl⟩ := hstdsurj B
    rw [hDm, conjSLn_mul, hMinv, hcomm, ← hM]
    group
  have hperfSL : Group.IsPerfect SL(ν, L) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hDtriv : ∀ B : SL(ν, L), conjSLn Dm B = B := by
    have hcentralD : ∀ B : SL(ν, L), B⁻¹ * conjSLn Dm B ∈ Subgroup.center SL(ν, L) := by
      intro B
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hDψ B, inv_mul_cancel]
    have hid :=
      CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        (conjSLn Dm) hcentralD
    intro B
    have := congrArg (fun f : SL(ν, L) →* SL(ν, L) => f B) hid
    simpa using this
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_conjSLn_kd264alg Dm hDtriv
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hc
    have : Nonempty (Fin ν) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero] at h1
    exact (Matrix.isUnits_det_units _).ne_zero h1
  set u : Lˣ := Units.mk0 c hc0 with hu
  have hMu : stdGL σQ M = M * Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
    have h1 : Dm = Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
      apply Units.ext
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    rw [← h1, hDm, mul_inv_cancel_left]
  have hσqs : ∀ c : L, σQ c = c ^ (S.D.q ^ s) := fun c => by
    rw [hσQc c, hqpow]
  obtain ⟨μ₀, hμ₀⟩ :=
    IsAlgClosed.exists_pow_nat_eq (u : L) (n := S.D.q ^ s + 1) (by omega)
  have hμ0 : μ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hμ₀
    exact u.ne_zero hμ₀.symm
  set μ : Lˣ := Units.mk0 μ₀ hμ0 with hμ
  set G : GL (Fin ν) L := M * Matrix.GeneralLinearGroup.scalar (Fin ν) μ with hG
  have hσμ : Units.map (σQ.toRingHom : L →* L) μ = u * μ⁻¹ := by
    apply Units.ext
    show σQ μ₀ = (u : L) * μ₀⁻¹
    rw [hσqs, ← hμ₀, pow_succ]
    field_simp
  have hGM : ∀ A : SL(ν, L), conjSLn G A = conjSLn M A := fun A => by
    rw [hG, conjSLn_mul_scalar]
  have hGstd : stdGL σQ G = G := by
    rw [hG, map_mul, hMu, stdGL_scalar, hσμ, mul_assoc, ← map_mul, _root_.mul_inv_rev,
      inv_inv, mul_comm μ u⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hGu : ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * G = 1 := by
    have h1 := congrArg (fun g : GL (Fin ν) L => (g : Matrix (Fin ν) (Fin ν) L)) hGstd
    simp only [coe_stdGL] at h1
    have hdet : IsUnit ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det := by
      have h0 : ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det =
          σQ (G : Matrix (Fin ν) (Fin ν) L).det := (RingHom.map_det σQ.toRingHom _).symm
      rw [h0]
      exact (Matrix.isUnits_det_units G).map σQ
    calc ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * (G : Matrix (Fin ν) (Fin ν) L) =
        ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
          (((G : Matrix (Fin ν) (Fin ν) L).map σQ)⁻¹)ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  refine ⟨G, hGu, ?_⟩
  intro c c' hc'
  have hθc' : θ c' = y * θ c * y⁻¹ := by
    rw [hθ, hθ, hc', hGM, ← hyA]
  have hw : ((θ₀ c' : P.S 0) : ModGL τ L) =
      y * ((θ₀ c : P.S 0) : ModGL τ L) * y⁻¹ := by
    rw [hθ₀, hθ₀]
    exact hθc'
  have h := cycFamily_norm_conj P hyF (u := θ₀ c) (w := θ₀ c') hw
  rw [hf c, hf c']
  exact h.symm

end CFSG.StandardType.RCKRP

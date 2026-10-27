module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentre
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreUntwCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
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

section TableZNormProof

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped commutatorElement

private theorem tzNorm_cycFamily_norm_of_eq_three {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (hs : s = 3) (y : P.S 0) :
    P.norm y = (y : G) * F (y : G) * F (F (y : G)) := by
  subst hs
  have hdiag : P.diag y =
      Pi.mulSingle (M := fun k => P.S k) (0 : ZMod 3) (P.iter 0 y) *
        Pi.mulSingle (M := fun k => P.S k) (1 : ZMod 3) (P.iter 1 y) *
        Pi.mulSingle (M := fun k => P.S k) (2 : ZMod 3) (P.iter 2 y) := by
    funext k
    have hall : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hall k with h | h | h
    · subst h
      rw [CycFamily.diag, MonoidHom.pi_apply, Pi.mul_apply, Pi.mul_apply,
        Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne (by decide : (0 : ZMod 3) ≠ 1),
        Pi.mulSingle_eq_of_ne (by decide : (0 : ZMod 3) ≠ 2), mul_one, mul_one]
    · subst h
      rw [CycFamily.diag, MonoidHom.pi_apply, Pi.mul_apply, Pi.mul_apply,
        Pi.mulSingle_eq_of_ne (by decide : (1 : ZMod 3) ≠ 0),
        Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne (by decide : (1 : ZMod 3) ≠ 2), one_mul, mul_one]
    · subst h
      rw [CycFamily.diag, MonoidHom.pi_apply, Pi.mul_apply, Pi.mul_apply,
        Pi.mulSingle_eq_of_ne (by decide : (2 : ZMod 3) ≠ 0),
        Pi.mulSingle_eq_of_ne (by decide : (2 : ZMod 3) ≠ 1),
        Pi.mulSingle_eq_same, one_mul, one_mul]
  rw [CycFamily.norm, MonoidHom.comp_apply, hdiag, map_mul, map_mul, CycFamily.mu_mulSingle,
    CycFamily.mu_mulSingle, CycFamily.mu_mulSingle]
  simp only [CycFamily.coe_iter]
  rw [show ZMod.val (1 : ZMod 3) = 1 from by decide,
    show ZMod.val (2 : ZMod 3) = 2 from by decide]
  simp [iterHom_succ, iterHom_zero]

private theorem tableZ_cube_norm_aux
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n)
    {ta : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (hap : ∀ j, ta j ^ 3 = 1)
    (i : KernelComponent (rootCharHom ta))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 3)
    (h6 : (componentRoots (rootCharHom ta) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ')
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3] (σ' x y) =
      σ' (π y) (π x)) :
    ∃ σQ : L ≃+* L, (∀ c, σQ c = c ^ (2 ^ (3 * n))) ∧
      ∃ f : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →* ModGL Tag.E6 L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) ∧
        (Group.IsPerfect ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) ∧
        ∀ (c : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ))) (t : Fin 3 → L),
          (((c : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal t) →
            ∃ w ∈ adjointGroup Tag.E6 L,
              f c = w * (ψ c * S.D.step (ψ c) * S.D.step (S.D.step (ψ c))) * w⁻¹ := by
  classical
  obtain ⟨hs0, hsPer, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hs3 : s = 3 := hsdef.trans hs
  have : NeZero s := ⟨hs0.ne'⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) 2 (n * s)
  have hσc : ∀ c, σQ c = c ^ (2 ^ (n * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L 2 (n * s) c := by rw [← hσQ]; rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = 2 ^ (n * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL Tag.E6 L →* ModGL Tag.E6 L := iterHom S.D.step s with hFs
  set P := outerOrbitFamily S hT i hsPer hmin with hP
  have hP0 : P.S 0 = rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  choose! ε hε using fun (a b : Fin 3) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin 3, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hπc : ∀ a b : Fin 3, a ≠ b →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ' a b) = σ' (π b) (π a) := by
    intro a b hab
    rw [hs3]
    exact hπ a b hab
  have hstepU : ∀ a b : Fin 3, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX Tag.E6 L (σ' a b) c) = pinnedX Tag.E6 L (σ' (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπc a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin 3 → Fin 3 → Lˣ := fun a b =>
    μ a b * ε a b ^ (2 ^ (n * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective Tag.E6 L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle (le_rfl : 3 ≤ 3) β hcoc
  set M : GL (Fin 3) L := CFSG.SectionRank.OddCover.diagHom 3 d *
    (CFSG.RankThree.Classical.permGL π : GL (Fin 3) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := 3) (by omega) M
  have hBconj : ∀ (a b : Fin 3) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin 3) (Fin 3) L, (M : Matrix (Fin 3) (Fin 3) L) * Y *
        (↑M⁻¹ : Matrix (Fin 3) (Fin 3) L) =
          (CFSG.SectionRank.OddCover.diagHom 3 d : Matrix (Fin 3) (Fin 3) L) *
          ((↑(CFSG.RankThree.Classical.permGL π : GL (Fin 3) L)⁻¹ : Matrix (Fin 3) (Fin 3) L) *
            Y * ((CFSG.RankThree.Classical.permGL π : GL (Fin 3) L) :
              Matrix (Fin 3) (Fin 3) L)) *
              (↑(CFSG.SectionRank.OddCover.diagHom 3 d)⁻¹ : Matrix (Fin 3) (Fin 3) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(3, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs0
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ) (Subgroup.mem_sup_right hy₁)
  have hnorm := mem_componentRootSpan_iff_conj_of_mem hzZ
  have hconj : ∀ X : SL(3, L),
      Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hzA : ∀ y ∈ P.A, z * y * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun y hy => h hy
  have hZconj : ∀ x : ModGL Tag.E6 L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro y hy
    have := hx _ (hzA y hy)
    have e1 : z * y * z⁻¹ * (z * x * z⁻¹) = z * (y * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * y * z⁻¹) = z * (x * y) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero Tag.E6 L (σ' _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective Tag.E6 L _ h1)
  have hcentral : ∀ X : SL(3, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(3, L) := by
    intro X hX
    refine mem_center_SL_of_commute (le_rfl : 3 ≤ 3) ψ hker fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ) with hCdef
  have hCmem : ∀ X : SL(3, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  let θ : C →* ModGL Tag.E6 L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS c)
  have hθfix : ∀ c : C, Fs (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
  have hpre : ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i),
      ∃ X : SL(3, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) :=
      (hnorm i _).2 (by
        have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
        rw [e]
        exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(3, L), Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(3, L) := by
    intro X hX
    have e : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (stdUnitary σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL Tag.E6 L, g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) → Fs g * g⁻¹ ∈ P.Z →
        Fs g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(3, L)) (hw : w ∈ Subgroup.center SL(3, L)) (y : SL(3, L)),
        Commute w y := fun w hw y => (Subgroup.mem_center_iff.1 hw y).symm
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
    intro d'
    exact Subtype.ext (Subgroup.mem_center_iff.1 h d')
  obtain ⟨f, hf1, hfker, hf2, hfn⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.rationalComponent_eq_range_of_hom_norm
      S hT i hsPer hmin θ hθS hθfix hθY hθZ
  have hσc3 : ∀ c, σQ c = c ^ (2 ^ (3 * n)) := by
    intro c
    rw [hσc c, hs3, Nat.mul_comm n 3]
  refine ⟨σQ, hσc3, f, hf1, hfker, hf2, fun c t hc => ?_⟩
  obtain ⟨g, hgU, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z (a := ta) i hzZ
  have hset : unionRoots (rootCharHom ta) ({i} : Set (KernelComponent (rootCharHom ta))) =
      componentRoots (rootCharHom ta) i := by
    ext α
    simp only [unionRoots, componentRoots, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have hgS0 : g ∈ P.S 0 := by
    rw [hP0]
    rwa [show unionRootSpan L (rootCharHom ta) ({i} : Set (KernelComponent (rootCharHom ta))) =
        rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) from by rw [unionRootSpan, hset]] at hgU
  let y0 : P.S 0 := ⟨g, hgS0⟩
  let ψ0 : P.S 0 := ⟨ψ c, by rw [hP0]; exact hψS c⟩
  have hgy : (y0 : ModGL Tag.E6 L) * ψ c * (y0 : ModGL Tag.E6 L)⁻¹ = z * ψ c * z⁻¹ := by
    have h1 := hgconj (ψ c) (hψS c)
    simpa using h1.symm
  have hθ0S : θ c ∈ P.S 0 := by rw [hP0]; exact hθS c
  have hfnc : f c = P.norm ⟨θ c, hθ0S⟩ := hfn c ⟨θ c, hθ0S⟩ rfl
  have hθ0eq : (⟨θ c, hθ0S⟩ : P.S 0) = y0 * ψ0 * y0⁻¹ := by
    apply Subtype.ext
    change θ c = (y0 : ModGL Tag.E6 L) * ψ c * (y0 : ModGL Tag.E6 L)⁻¹
    rw [hgy, hθ]
  have hfnorm : f c = P.norm (y0 * ψ0 * y0⁻¹) := hθ0eq ▸ hfnc
  have hnorm_mul : P.norm (y0 * ψ0 * y0⁻¹) = P.norm y0 * P.norm ψ0 * (P.norm y0)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have hnorm_psi : P.norm ψ0 = ψ c * S.D.step (ψ c) * S.D.step (S.D.step (ψ c)) :=
    tzNorm_cycFamily_norm_of_eq_three P hs3 ψ0
  refine ⟨P.norm y0, ?_, ?_⟩
  · have hA : P.A ≤ adjointGroup Tag.E6 L := by
      refine iSup_le fun k => ?_
      rw [hP, outerOrbitFamily_S]
      exact rootSpan_le_adjointGroup L _
    exact hA (P.norm_mem_A y0)
  · rw [hfnorm, hnorm_mul, hnorm_psi]

end TableZNormProof

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_cube_norm
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3)
    (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (hΨ : componentRoots (rootCharHom a) i = frameRoots σ')
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3] (σ' x y) =
      σ' (π y) (π x)) :
    ∃ σQ : L ≃+* L, (∀ c, σQ c = c ^ (2 ^ (3 * n))) ∧
      ∃ f : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →* ModGL Tag.E6 L,
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) ∧
        (Group.IsPerfect ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        ∀ (c : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ))) (t : Fin 3 → L),
          (((c : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal t) →
            ∃ w ∈ adjointGroup Tag.E6 L,
              f c = w * (ψ c * S.D.step (ψ c) * S.D.step (S.D.step (ψ c))) * w⁻¹ :=
  tableZ_cube_norm_aux S hn hq hT hap i hs h6 hψ hΨ π hπ

end CFSG.StandardType.TablePThreeKG

end

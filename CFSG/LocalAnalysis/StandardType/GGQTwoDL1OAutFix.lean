module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1ONorm
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityNonsplit
import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion

public section

namespace CFSG.StandardType.QTwo

open Module QuadraticMap
open CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType.RecipeFieldOmega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qtwoDL1_orthAut_of_fix_six_plus (hK : Nat.card K = 2)
    (α : MulAut ↥(orthDerived (coordinateQuadPlus 4 K)))
    {b : ↥(orthDerived (coordinateQuadPlus 4 K))} (hb3 : b ^ 3 = 1)
    (hb6 : finrank K (LinearMap.ker ((b : (Fin (2 * 4) → K) ≃ₗ[K]
      (Fin (2 * 4) → K)).toLinearMap - 1)) = 6) (hfix : α b = b) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K),
      ∀ y : ↥(orthDerived (coordinateQuadPlus 4 K)),
        (α y : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) =
          g * (y : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) * g⁻¹ := by
  classical
  let E : CFSG.StandardType.Triality.Om8 K ≃*
      ↥(orthDerived (coordinateQuadPlus 4 K)) :=
    (matrixLinearIso.subgroupMap (matrixDerived (coordinateQuadPlus 4 K))).trans
      (MulEquiv.subgroupCongr (matrixDerived_map (coordinateQuadPlus 4 K)))
  have he : ∀ y : CFSG.StandardType.Triality.Om8 K,
      (E y : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) =
        matrixLinearIso y.val := fun _ => rfl
  let α' : MulAut (CFSG.StandardType.Triality.Om8 K) := E.trans (α.trans E.symm)
  have hα' : ∀ y, E (α' y) = α (E y) := by
    intro y
    simp [α', MulEquiv.trans_apply]
  have hb3' : (E.symm b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hb6' : CFSG.StandardType.D4Rank.omFixDim (E.symm b) = 6 := by
    have hbmap : CFSG.StandardType.D4Rank.omRep (E.symm b) =
        (b : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)).toLinearMap := by
      change (matrixLinearIso (E.symm b).val).toLinearMap = _
      apply congrArg LinearEquiv.toLinearMap
      rw [← he, MulEquiv.apply_symm_apply]
    exact (congrArg (fun f : Module.End K (Fin (2 * 4) → K) =>
      finrank K (LinearMap.ker (f - 1))) hbmap).trans hb6
  have hfix' : α' (E.symm b) = E.symm b := by
    apply E.injective
    rw [hα', MulEquiv.apply_symm_apply, hfix]
  obtain ⟨g, hg, hact⟩ :=
    CFSG.StandardType.OrdPTri.exists_matrixIsometry_of_fix_six_of_card_two hK α' hb3' hb6' hfix'
  refine ⟨matrixLinearIso g, ?_, ?_⟩
  · have h := Subgroup.mem_map_of_mem matrixLinearIso.toMonoidHom hg
    rwa [matrixIsometries_map] at h
  · intro y
    have h := congrArg matrixLinearIso (hact (E.symm y))
    rw [map_mul, map_mul, map_inv, ← he, ← he, hα', MulEquiv.apply_symm_apply] at h
    exact h

theorem qtwoDL1_orthAut_of_fix_six_of_isometry {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hK : Nat.card K = 2)
    (e : Q.IsometryEquiv (coordinateQuadPlus 4 K)) (α : MulAut ↥(orthDerived Q))
    {b : ↥(orthDerived Q)} (hb3 : b ^ 3 = 1)
    (hb6 : finrank K (LinearMap.ker ((b : V ≃ₗ[K] V).toLinearMap - 1)) = 6)
    (hfix : α b = b) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ y : ↥(orthDerived Q), (α y : V ≃ₗ[K] V) = g * (y : V ≃ₗ[K] V) * g⁻¹ := by
  classical
  let E := orthDerivedEquiv e
  have he : ∀ y : ↥(orthDerived Q),
      (E y : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) =
        linConj e.toLinearEquiv (y : V ≃ₗ[K] V) := fun _ => rfl
  let α' : MulAut ↥(orthDerived (coordinateQuadPlus 4 K)) := MulAut.congr E α
  have hα' : ∀ y, α' (E y) = E (α y) := by
    intro y
    simp [α', MulAut.congr_apply]
  have hker : LinearMap.ker ((E b : (Fin (2 * 4) → K) ≃ₗ[K]
      (Fin (2 * 4) → K)).toLinearMap - 1) =
      (LinearMap.ker ((b : V ≃ₗ[K] V).toLinearMap - 1)).map e.toLinearEquiv.toLinearMap := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨e.toLinearEquiv.symm v, ?_, e.toLinearEquiv.apply_symm_apply v⟩
      have h := congrArg e.toLinearEquiv.symm hv
      rw [he] at h
      change e.toLinearEquiv.symm
        (e.toLinearEquiv ((b : V ≃ₗ[K] V) (e.toLinearEquiv.symm v))) =
          e.toLinearEquiv.symm v at h
      simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.coe_coe] using h
    · rintro ⟨w, hw, rfl⟩
      rw [he]
      change e.toLinearEquiv ((b : V ≃ₗ[K] V)
        (e.toLinearEquiv.symm (e.toLinearEquiv w))) = e.toLinearEquiv w
      rw [LinearEquiv.symm_apply_apply]
      simpa only [LinearEquiv.coe_coe] using congrArg e.toLinearEquiv hw
  have hb6' : finrank K (LinearMap.ker ((E b : (Fin (2 * 4) → K) ≃ₗ[K]
      (Fin (2 * 4) → K)).toLinearMap - 1)) = 6 := by
    rw [hker, LinearEquiv.finrank_map_eq]
    exact hb6
  obtain ⟨g', hg', hact⟩ := qtwoDL1_orthAut_of_fix_six_plus hK α'
    (show (E b) ^ 3 = 1 by rw [← map_pow, hb3, map_one]) hb6'
    (by rw [hα', hfix])
  let g := (linConj e.toLinearEquiv).symm g'
  have hgg : linConj e.toLinearEquiv g = g' := MulEquiv.apply_symm_apply _ _
  have hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [← map_orthogonalGroup_linConj e, Subgroup.mem_map_equiv] at hg'
    exact hg'
  refine ⟨g, hg, ?_⟩
  intro y
  apply (linConj e.toLinearEquiv).injective
  rw [map_mul, map_mul, map_inv, hgg, ← he, ← he]
  have h := hact (E y)
  rwa [hα'] at h

omit [Finite K] in
theorem qtwoDL1_orthAut_of_semilinear {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {Q : QuadraticForm K V} (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (α : MulAut ↥(orthDerived Q))
    (hsemi : ∀ β : MulAut (ProjOrthDerived Q),
      CFSG.RankThree.PartOne.KCOrthogonalAut.InducedBySemilinear Q β) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ y : ↥(orthDerived Q), (α y : V ≃ₗ[K] V) = g * (y : V ≃ₗ[K] V) * g⁻¹ := by
  let E : ↥(orthDerived Q) ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective (piOrth Q) ⟨piOrth_injective hQ, piOrth_surjective⟩
  obtain ⟨g, hg, hact⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_isometry_of_inducedBySemilinear hK (hsemi (MulAut.congr E α))
  refine ⟨g, hg, ?_⟩
  intro y
  obtain ⟨hy, h⟩ := hact y
  have h' : E (α y) = E ⟨g * (y : V ≃ₗ[K] V) * g⁻¹, hy⟩ := by
    have hα : (MulAut.congr E α) (E y) = E (α y) := by simp [MulAut.congr_apply]
    rw [← hα]
    exact h
  exact congrArg Subtype.val (E.injective h')

theorem qtwoDL1_oChart_finrank_single {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ) (l : Fin Φ.r) :
    finrank Φ.F (LinearMap.ker ((Φ.Δ.τ (fun a => Multiplicative.ofAdd
      (if a = l then (1 : ZMod p) else 0))).toLinearMap - 1)) + 2 = 2 * Φ.r := by
  classical
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
    (by simpa [hF] using Φ.hpq)
  subst p
  let f : Fin Φ.r → Multiplicative (ZMod 3) := fun a =>
    Multiplicative.ofAdd (if a = l then (1 : ZMod 3) else 0)
  have hζ : ((C.ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) ≠ 1 := by
    intro h
    apply C.ζ_ne_one
    apply Subtype.ext
    exact Units.ext h
  have hfix : ∀ v : Φ.V, Φ.Δ.τ f v = v ↔ C.χ v l = 0 := by
    intro v
    constructor
    · intro hv
      have h := congrArg (fun w : Φ.V => C.χ w l) hv
      rw [C.torus, CFSG.ClassicalInvolution.PhanDn.diagHom_apply] at h
      have h' : ((C.ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) * C.χ v l = C.χ v l := by
        simpa [f, ZMod.val_one 3] using h
      have hmul :
          ((((C.ζ : (GaloisField 2 2)ˣ) : GaloisField 2 2) - 1) * C.χ v l) = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact h'
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hζ)
    · intro hv
      apply C.χ.injective
      funext a
      rw [C.torus, CFSG.ClassicalInvolution.PhanDn.diagHom_apply]
      by_cases ha : a = l
      · subst a
        simp [hv]
      · simp [f, ha]
  let π : (Fin Φ.r → GaloisField 2 2) →ₗ[Φ.F] GaloisField 2 2 := LinearMap.proj l
  have hπ : Function.Surjective π := fun z => ⟨fun _ => z, rfl⟩
  have hker : LinearMap.ker ((Φ.Δ.τ f).toLinearMap - 1) =
      (LinearMap.ker π).map C.χ.symm.toLinearMap := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_map]
    change Φ.Δ.τ f v = v ↔ ∃ w, π w = 0 ∧ C.χ.symm w = v
    rw [hfix]
    constructor
    · intro hv
      exact ⟨C.χ v, hv, C.χ.symm_apply_apply v⟩
    · rintro ⟨w, hw, rfl⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hw
  have hdim := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, C.E.finrank_eq,
    Module.finrank_pi_fintype] at hdim
  simp only [C.E.finrank_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hdim
  rw [hker, LinearEquiv.finrank_map_eq]
  change finrank Φ.F (LinearMap.ker π) + 2 = 2 * Φ.r
  omega

theorem qtwoDL1_orthAut_of_torus_fixed {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ)
    {i j k : Fin Φ.r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (α : MulAut ↥(orthDerived Φ.Q))
    (hfix : ∀ (f : Fin Φ.r → Multiplicative (ZMod p)), f i = f j → f j = f k →
      ∀ t : ↥(orthDerived Φ.Q), (t : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f → α t = t) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
      ∀ y : ↥(orthDerived Φ.Q),
        (α y : Φ.V ≃ₗ[Φ.F] Φ.V) = g * (y : Φ.V ≃ₗ[Φ.F] Φ.V) * g⁻¹ := by
  classical
  have hr := Φ.hr
  have hQ := qtwoDL1_oChart_nondeg Φ C
  have hdim := qtwoDL1_oChart_finrank Φ C
  have : Nontrivial Φ.V := by
    let l : Fin Φ.r := ⟨0, by omega⟩
    refine ⟨⟨0, C.χ.symm (fun _ => 1), ?_⟩⟩
    intro h
    have h' := congrArg (fun v : Φ.V => C.χ v l) h
    simp at h'
  by_cases hr4 : Φ.r = 4
  · have hdim4 : finrank Φ.F Φ.V = 2 * 4 := by simpa only [hr4] using hdim
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Φ.Q hQ
      (n := 4) (by omega) hdim4 with ⟨⟨e⟩⟩ | ⟨b, c, hbc, ⟨e⟩⟩
    · have hJ : ({i, j, k} : Finset (Fin Φ.r)).card = 3 :=
        Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩
      obtain ⟨l, hli, hlj, hlk⟩ : ∃ l : Fin Φ.r, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
        by_contra! h
        have hcover : (Finset.univ : Finset (Fin Φ.r)) ⊆ {i, j, k} := by
          intro a _
          by_cases hai : a = i
          · simp [hai]
          by_cases haj : a = j
          · simp [haj]
          simp [h a hai haj]
        have hc := Finset.card_le_card hcover
        rw [Finset.card_univ, Fintype.card_fin, hJ] at hc
        omega
      let f : Fin Φ.r → Multiplicative (ZMod p) := fun a =>
        Multiplicative.ofAdd (if a = l then (1 : ZMod p) else 0)
      let t : ↥(orthDerived Φ.Q) :=
        ⟨Φ.Δ.τ f, Φ.hA (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)⟩
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        Nat.prime_three).mp (by simpa [hF] using Φ.hpq)
      have hf3 : f ^ 3 = 1 := by
        funext a
        apply Multiplicative.toAdd.injective
        rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one,
          nsmul_eq_mul]
        have h3 : ((3 : ℕ) : ZMod p) = 0 :=
          (congrArg (fun n : ℕ => (n : ZMod p)) hp3.symm).trans (ZMod.natCast_self p)
        rw [h3, zero_mul]
      have ht3 : t ^ 3 = 1 := by
        apply Subtype.ext
        change (Φ.Δ.τ f) ^ 3 = 1
        rw [← map_pow, hf3, map_one]
      have ht6 : finrank Φ.F
          (LinearMap.ker ((t : Φ.V ≃ₗ[Φ.F] Φ.V).toLinearMap - 1)) = 6 := by
        have h : finrank Φ.F
            (LinearMap.ker ((t : Φ.V ≃ₗ[Φ.F] Φ.V).toLinearMap - 1)) + 2 = 2 * Φ.r :=
          qtwoDL1_oChart_finrank_single Φ hF C l
        omega
      have htfix : α t = t := hfix f
        (by simp [f, hli.symm, hlj.symm]) (by simp [f, hlj.symm, hlk.symm]) t rfl
      exact qtwoDL1_orthAut_of_fix_six_of_isometry hF
        (e.trans (coordinatePlusIsometry 4 Φ.F))
        α ht3 ht6 htfix
    · let S : Φ.V ≃ₗ[Φ.F] (Fin (2 * 4) → Φ.F) := e.toLinearEquiv.trans
        (coordinateMinusIsometry 4 Φ.F
          (by omega) b c).toLinearEquiv
      have hS : ∀ v, coordinateQuadMinus 4 Φ.F (by omega) b c (S v) = (1 : Φ.Fˣ) * Φ.Q v := by
        intro v
        change coordinateQuadMinus 4 Φ.F (by omega) b c
          ((coordinateMinusIsometry 4 Φ.F
            (by omega) b c) (e v)) = (1 : Φ.Fˣ) * Φ.Q v
        rw [QuadraticMap.IsometryEquiv.map_app, e.map_app, Units.val_one, one_mul]
      exact qtwoDL1_orthAut_of_semilinear hF hQ α fun β =>
        CFSG.RankThree.PartOne.KCOrthogonalAut.inducedBySemilinear_of_similarity S 1 hS
          (CFSG.RankThree.PartOne.KCOrthogonalAut.inducedBySemilinear_of_image_eq_top
            (by omega) _ (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus
              Φ.F 4 (by omega) b c hbc)) β
  · have hr5 : 5 ≤ Φ.r := by omega
    exact qtwoDL1_orthAut_of_semilinear hF hQ α fun β =>
      CFSG.RankThree.PartOne.KCOrthogonalAut.orthogonal_aut_semilinear Φ.Q hQ
        (by rw [hdim]; omega) (by intro h8; rw [hdim] at h8; omega) β

end CFSG.StandardType.QTwo

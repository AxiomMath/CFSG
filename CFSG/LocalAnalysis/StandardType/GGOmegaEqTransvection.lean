module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvGraphInv
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCentCoord
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDict
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockGUOrder
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
public import CFSG.LargeExtraspecial.DWFldOrth
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorRot
public import CFSG.LocalAnalysis.StandardType.GGFusionOrthPlaneComp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.ClassicalBlocks Matrix
open Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal

private noncomputable def ggOmW5a_fix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) : Submodule K (ι → K) :=
  LinearMap.ker (Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id)

private noncomputable def ggOmW5a_com {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) : Submodule K (ι → K) :=
  LinearMap.range (Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id)

private noncomputable def ggOmW5a_toLinEquiv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) : (ι → K) ≃ₗ[K] (ι → K) :=
  (Matrix.GeneralLinearGroup.toLin s).toLinearEquiv

private theorem ggOmW5a_polar_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (u v : V) :
    Q (u + v) - Q u - Q v = QuadraticMap.polar Q u v := rfl

private lemma ggOmW5aA_toLinEquiv_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) (v : ι → K) :
    ggOmW5a_toLinEquiv b v = (b : Matrix ι ι K) *ᵥ v := rfl

private lemma ggOmW5aA_toLin_sub_id {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) :
    ((ggOmW5a_toLinEquiv b : (ι → K) ≃ₗ[K] (ι → K)) : (ι → K) →ₗ[K] (ι → K)) - 1 =
      Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id := by
  ext v
  simp [ggOmW5aA_toLinEquiv_apply]

private lemma ggOmW5aA_toLinEquiv_eq_lib {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) :
    ggOmW5a_toLinEquiv s = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K s := rfl

private theorem ggOmW5aA_isCompl_fix_com {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (f : V ≃ₗ[K] V) {m : ℕ} (hm : Odd m)
    (hfm : f ^ m = 1) :
    IsCompl (LinearMap.ker ((f : V →ₗ[K] V) - 1))
      (LinearMap.range ((f : V →ₗ[K] V) - 1)) := by
  classical
  set F : Module.End K V := (f : V →ₗ[K] V) with hF
  set g : Module.End K V := F - 1 with hg
  have hFm : F ^ m = 1 := by
    have h : ∀ k : ℕ, ((f ^ k : V ≃ₗ[K] V) : V →ₗ[K] V) = F ^ k := by
      intro k
      induction k with
      | zero => simp [hF, Module.End.one_eq_id]
      | succ k ih => rw [pow_succ, LinearEquiv.coe_toLinearMap_mul, ih, pow_succ]
    have h' := congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V)) hfm
    rw [h m] at h'
    simpa [Module.End.one_eq_id] using h'
  have h1g : (1 + g : Module.End K V) = F := by rw [hg]; abel
  have hFg : (1 + g) ^ m = 1 := by rw [h1g, hFm]
  have hFg' : (g + 1) ^ m = 1 := by rw [add_comm]; exact hFg
  let Q : K[X] := ∑ i ∈ Finset.range m, (X + 1) ^ i
  have hQeval : aeval g Q = ∑ i ∈ Finset.range m, (g + 1) ^ i := by
    simp [Q]
  have hQg : aeval g Q * g + 1 = (g + 1) ^ m := by
    rw [hQeval]
    exact geom_sum_mul_add g m
  have hQgm : aeval g Q * g = 0 := by
    have h := hQg
    rw [hFg'] at h
    exact add_right_cancel (h.trans (zero_add 1).symm)
  have hQcoeff : Q.coeff 0 = (m : K) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [Q, Polynomial.eval_finsetSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcoeff : (Q - Polynomial.C (m : K)).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, hQcoeff, Polynomial.coeff_C]
    simp
  obtain ⟨R, hR⟩ := Polynomial.X_dvd_iff.mpr hcoeff
  have hRg : Commute (aeval g R) g := by
    have h := (Commute.all R Polynomial.X).map (Polynomial.aeval g)
    simpa using h
  have hsplit : aeval g Q = (m : K) • (1 : Module.End K V) + g * aeval g R := by
    have h := congrArg (Polynomial.aeval g) hR
    rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, Algebra.smul_def, mul_one, add_comm]
  have hzero : (m : K) • g + g ^ 2 * aeval g R = 0 := by
    have h := hQgm
    rw [hsplit, add_mul, smul_mul_assoc, one_mul, mul_assoc, hRg.eq, ← mul_assoc,
      ← pow_two] at h
    exact h
  have hQg2 : g ^ 2 * aeval g R = (m : K) • g := by
    have hself : (m : K) • g + (m : K) • g = 0 := by
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have h2 : (m : K) • g + g ^ 2 * aeval g R = (m : K) • g + (m : K) • g := by
      rw [hzero, hself]
    exact add_left_cancel h2
  have hm0 : (m : K) ≠ 0 := by
    intro h
    exact (Nat.not_even_iff_odd.2 hm)
      (even_iff_two_dvd.mpr ((CharP.cast_eq_zero_iff K 2 m).mp h))
  set a : Module.End K V := (m : K)⁻¹ • aeval g R with ha
  have hag : a * g = g * a := by
    rw [ha, smul_mul_assoc, mul_smul_comm, hRg.eq]
  have hga : g ^ 2 * a = g := by
    rw [ha, mul_smul_comm, hQg2, smul_smul, inv_mul_cancel₀ hm0, one_smul]
  have hge : g * (g * a) = g := by rw [← mul_assoc, ← pow_two, hga]
  have heg : (g * a) * g = g := by rw [mul_assoc, hag, ← mul_assoc, ← pow_two, hga]
  have he_idem : IsIdempotentElem (g * a) := by
    show (g * a) * (g * a) = g * a
    rw [(mul_assoc (g * a) g a).symm, heg]
  have hrange : LinearMap.range (g * a) = LinearMap.range g := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact ⟨a y, rfl⟩
    · rintro x ⟨y, rfl⟩
      exact ⟨g y, by rw [← Module.End.mul_apply, heg]⟩
  have hker : LinearMap.ker (g * a) = LinearMap.ker g := by
    apply le_antisymm
    · intro x hx
      simp only [LinearMap.mem_ker] at hx ⊢
      calc g x = (g * (g * a)) x := by rw [hge]
        _ = g ((g * a) x) := by rw [Module.End.mul_apply]
        _ = 0 := by rw [hx, map_zero]
    · intro x hx
      simp only [LinearMap.mem_ker] at hx ⊢
      calc (g * a) x = (a * g) x := by rw [hag]
        _ = a (g x) := by rw [Module.End.mul_apply]
        _ = 0 := by rw [hx, map_zero]
  rw [← hrange, ← hker]
  exact (LinearMap.IsIdempotentElem.isCompl he_idem).symm

private theorem ggOmW5a_fix_isCompl_com {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b : GL ι K) (hodd : Odd (orderOf b)) :
    IsCompl (ggOmW5a_fix b) (ggOmW5a_com b) := by
  rw [ggOmW5a_fix, ggOmW5a_com]
  have h := ggOmW5aA_isCompl_fix_com (V := ι → K) (ggOmW5a_toLinEquiv b) hodd ?_
  · rwa [ggOmW5aA_toLin_sub_id b] at h
  · rw [ggOmW5aA_toLinEquiv_eq_lib, ← map_pow, pow_orderOf_eq_one, map_one]

private lemma ggOmW5aA_polar_of_matrixOrthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K}
    (hb : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (x y : ι → K) :
    QuadraticMap.polar Φ ((b : Matrix ι ι K) *ᵥ x) ((b : Matrix ι ι K) *ᵥ y) =
      QuadraticMap.polar Φ x y := by
  have hb' : ∀ v, ⇑Φ ((b : Matrix ι ι K) *ᵥ v) = ⇑Φ v := hb
  rw [← ggOmW5a_polar_apply Φ ((b : Matrix ι ι K) *ᵥ x) ((b : Matrix ι ι K) *ᵥ y),
    ← ggOmW5a_polar_apply Φ x y, ← Matrix.mulVec_add, hb' (x + y), hb' x, hb' y]

private theorem ggOmW5a_polar_fix_com_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    (hb : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) :
    ∀ u ∈ ggOmW5a_fix b, ∀ w ∈ ggOmW5a_com b, QuadraticMap.polarBilin Φ u w = 0 := by
  intro u hu w hw
  have hu' : (b : Matrix ι ι K) *ᵥ u = u := by
    rw [ggOmW5a_fix, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, sub_eq_zero] at hu
    exact hu
  rw [ggOmW5a_com, LinearMap.mem_range] at hw
  obtain ⟨v, hv⟩ := hw
  rw [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply] at hv
  rw [← hv, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right,
    show QuadraticMap.polar Φ u ((b : Matrix ι ι K) *ᵥ v) =
      QuadraticMap.polar Φ ((b : Matrix ι ι K) *ᵥ u) ((b : Matrix ι ι K) *ᵥ v) by rw [hu'],
    ggOmW5aA_polar_of_matrixOrthogonal Φ hb u v, sub_self]

private theorem ggOmW5a_fix_nondegenerate {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (hb : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hodd : Odd (orderOf b)) :
    ∀ u ∈ ggOmW5a_fix b,
      (∀ w ∈ ggOmW5a_fix b, QuadraticMap.polarBilin Φ u w = 0) → u = 0 := by
  intro u hu hper
  refine hΦ.1 u fun x => ?_
  have htop : ggOmW5a_fix b ⊔ ggOmW5a_com b = ⊤ :=
    (ggOmW5a_fix_isCompl_com b hodd).sup_eq_top
  have hx : x ∈ ggOmW5a_fix b ⊔ ggOmW5a_com b := by rw [htop]; trivial
  obtain ⟨x1, hx1, x2, hx2, hxsum⟩ := Submodule.mem_sup.mp hx
  have h1 : QuadraticMap.polar Φ u x1 = 0 := by
    simpa [QuadraticMap.polarBilin_apply_apply] using hper x1 hx1
  have h2 : QuadraticMap.polar Φ u x2 = 0 := by
    simpa [QuadraticMap.polarBilin_apply_apply] using
      ggOmW5a_polar_fix_com_zero Φ b hb u hu x2 hx2
  rw [← hxsum, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right, h1, h2,
    add_zero]

private theorem ggOmW5a_fix_eq_fixSpace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) :
    ggOmW5a_fix b =
      CFSG.RankThree.OrthogonalInvolutions.fixSpace (ggOmW5a_toLinEquiv b) := by
  rw [ggOmW5a_fix, CFSG.RankThree.OrthogonalInvolutions.fixSpace, ggOmW5aA_toLin_sub_id b]

private theorem ggOmW5a_com_eq_commSpace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) :
    ggOmW5a_com b =
      CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv b) := by
  rw [ggOmW5a_com, CFSG.RankThree.OrthogonalInvolutions.commSpace, ggOmW5aA_toLin_sub_id b]

private lemma ggOmW5aA_mulVec_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b s : GL ι K) (hsb : s * b = b * s) (u : ι → K) :
    (b : Matrix ι ι K) *ᵥ ((s : Matrix ι ι K) *ᵥ u) =
      (s : Matrix ι ι K) *ᵥ ((b : Matrix ι ι K) *ᵥ u) := by
  have h : ((s * b : GL ι K) : Matrix ι ι K) = ((b * s : GL ι K) : Matrix ι ι K) := by
    rw [hsb]
  rw [Units.val_mul, Units.val_mul] at h
  have h2 := congrArg (fun M : Matrix ι ι K => M *ᵥ u) h
  simpa only [Matrix.mulVec_mulVec] using h2.symm

private theorem ggOmW5a_s_maps_fix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b s : GL ι K) (hsb : s * b = b * s) :
    ∀ u : ι → K, u ∈ ggOmW5a_fix b → (s : Matrix ι ι K) *ᵥ u ∈ ggOmW5a_fix b := by
  intro u hu
  simp only [ggOmW5a_fix, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
    LinearMap.id_apply, sub_eq_zero] at hu ⊢
  rw [ggOmW5aA_mulVec_comm b s hsb u, hu]

private theorem ggOmW5a_commSpace_le_fix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b s : GL ι K) (hodd : Odd (orderOf b))
    (hsV1 : ∀ u ∈ ggOmW5a_fix b, (s : Matrix ι ι K) *ᵥ u ∈ ggOmW5a_fix b)
    (hsV' : ∀ w ∈ ggOmW5a_com b, (s : Matrix ι ι K) *ᵥ w = w) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s) ≤
      ggOmW5a_fix b := by
  intro x hx
  rw [← ggOmW5a_com_eq_commSpace s] at hx
  rw [ggOmW5a_com, LinearMap.mem_range] at hx
  obtain ⟨v, hv⟩ := hx
  rw [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply] at hv
  rw [← hv]
  have htop : ggOmW5a_fix b ⊔ ggOmW5a_com b = ⊤ :=
    (ggOmW5a_fix_isCompl_com b hodd).sup_eq_top
  have hv' : v ∈ ggOmW5a_fix b ⊔ ggOmW5a_com b := by rw [htop]; trivial
  obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Submodule.mem_sup.mp hv'
  have hmem1 : (s : Matrix ι ι K) *ᵥ v1 - v1 ∈ ggOmW5a_fix b :=
    Submodule.sub_mem _ (hsV1 v1 hv1) hv1
  have hmem2 : (s : Matrix ι ι K) *ᵥ v2 - v2 ∈ ggOmW5a_fix b := by
    rw [hsV' v2 hv2, sub_self]
    exact Submodule.zero_mem _
  rw [← hv12, Matrix.mulVec_add]
  have hdecomp : (s : Matrix ι ι K) *ᵥ v1 + (s : Matrix ι ι K) *ᵥ v2 - (v1 + v2) =
      ((s : Matrix ι ι K) *ᵥ v1 - v1) + ((s : Matrix ι ι K) *ᵥ v2 - v2) := by
    abel
  rw [hdecomp]
  exact add_mem hmem1 hmem2

private theorem ggOmW5a_matrixOrthogonal_iff_orthogonalGroup {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (s : GL ι K) :
    s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ ↔
      ggOmW5a_toLinEquiv s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  change (∀ v, ⇑Φ ((s : Matrix ι ι K) *ᵥ v) = ⇑Φ v) ↔
    ∀ v, Φ (ggOmW5a_toLinEquiv s v) = Φ v
  constructor <;> intro h v
  · simpa [ggOmW5aA_toLinEquiv_apply] using h v
  · simpa [ggOmW5aA_toLinEquiv_apply] using h v

private lemma ggOmW5aA_exists_ne_zero_ne_one_of_card_ne_two {K : Type} [Field K] [Fintype K]
    (hK : Nat.card K ≠ 2) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  haveI : Nontrivial K := ⟨0, 1, zero_ne_one⟩
  have h1 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have h2 : 2 < Nat.card K := by omega
  have hcard : ({0, 1} : Finset K).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]
    exact zero_ne_one
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [hcard, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h2
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, ?_, ?_⟩
  · intro h
    exact hc (by simp [h])
  · intro h
    exact hc (by simp [h])

private theorem ggOmW5aA_omegaGroup_le_commutator {ι K : Type} [Fintype ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h4 : 4 ≤ Fintype.card ι)
    (h5 : 5 ≤ Fintype.card ι) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
  have hdim : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  have h4' : 4 ≤ Module.finrank K (ι → K) := by rw [hdim]; exact h4
  have h5' : 5 ≤ Module.finrank K (ι → K) := by rw [hdim]; exact h5
  refine (CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le
    (V := ι → K) hΦ h4').trans ?_
  by_cases hK2 : Nat.card K = 2
  · haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK2
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.elementaryGroup_le_commutator
      (V := ι → K) hΦ (Or.inl h5')
  · obtain ⟨c, hc0, hc1⟩ := ggOmW5aA_exists_ne_zero_ne_one_of_card_ne_two (K := K) hK2
    exact CFSG.RankThree.GF2n.Stroth80.Classify.elementaryGroup_le_commutator
      (V := ι → K) hΦ hc0 hc1

private theorem ggOmW5aA_omegaGroup_eq_commutator {ι K : Type} [Fintype ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h4 : 4 ≤ Fintype.card ι)
    (h5 : 5 ≤ Fintype.card ι) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆ :=
  le_antisymm (ggOmW5aA_omegaGroup_le_commutator Φ hΦ h4 h5)
    (CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup hΦ)

private theorem ggOmW5a_statedOmega_iff_omegaGroup {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι) (s : GL ι K) :
    s ∈ StatedOmega ⇑Φ ↔
      ggOmW5a_toLinEquiv s ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
    ← ggOmW5aA_omegaGroup_eq_commutator Φ hΦ (by omega) (by omega),
    Subgroup.mem_comap]
  rfl

private theorem ggOmW5a_fix_s_not_mem_omega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ) :
    ¬ Even (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
      (ggOmW5a_toLinEquiv s))) := by
  intro heven
  refine hsΩ ((ggOmW5a_statedOmega_iff_omegaGroup Φ hΦ h8 s).mpr ?_)
  refine (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup (Q := Φ)
    (hQ := hΦ)).mpr ⟨?_, heven⟩
  exact (ggOmW5a_matrixOrthogonal_iff_orthogonalGroup Φ s).mp hs

private theorem ggOmW5a_block_decomp {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    ∃ P : Finset (Matrix ι ι K),
      (∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0) ∧ ∑ ε ∈ P, ε = 1 ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' →
        ∀ x ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
        ∀ y ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε', Commute x y) ∧
      (⨆ ε ∈ P, glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) =
        (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype ∧
      Nat.card ↥((Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype) =
        ∏ ε ∈ P, Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) :=
  centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd

private theorem ggOmW5a_block_iso_linear {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε e e' : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = d ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E) :=
  blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hε he he' hne hεe

private theorem ggOmW5a_block_iso_unitary {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = (Fintype.card K ^ d) ^ 2 ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε = 2 * d ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(GUFull m (Fintype.card K ^ d) E)) :=
  blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hε hp h1

open CFSG.RankThree.PartOne.KCPrimary

private lemma ggOmW5aB_toLinEquiv_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) :
    ggOmW5a_toLinEquiv s = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K s := rfl

private lemma ggOmW5aB_toLinEquiv_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (v : ι → K) :
    ggOmW5a_toLinEquiv s v = (s : Matrix ι ι K) *ᵥ v := by
  rw [ggOmW5aB_toLinEquiv_eq, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]

private lemma ggOmW5aB_toLinEquiv_toLinearMap {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) :
    (ggOmW5a_toLinEquiv s).toLinearMap = Matrix.toLin' (s : Matrix ι ι K) := by
  apply LinearMap.ext
  intro v
  change ggOmW5a_toLinEquiv s v = Matrix.toLin' (s : Matrix ι ι K) v
  rw [ggOmW5aB_toLinEquiv_apply, Matrix.toLin'_apply]

private lemma ggOmW5aB_toLinEquiv_mul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s t : GL ι K) :
    ggOmW5a_toLinEquiv (s * t) = ggOmW5a_toLinEquiv s * ggOmW5a_toLinEquiv t := by
  rw [ggOmW5aB_toLinEquiv_eq, ggOmW5aB_toLinEquiv_eq, ggOmW5aB_toLinEquiv_eq, map_mul]

private lemma ggOmW5aB_toLinAlgEquiv'_eq_toLin' {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (M : Matrix ι ι K) :
    Matrix.toLinAlgEquiv' M = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

private lemma ggOmW5aB_oddOrderIsometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    OddOrderIsometry Φ (orderOf b) (ggOmW5a_toLinEquiv b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hb
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
      Subgroup.mem_comap] at h
    rw [ggOmW5aB_toLinEquiv_eq]
    exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Φ) h
  · rw [ggOmW5aB_toLinEquiv_eq]
    have h := map_pow (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) b (orderOf b)
    rw [pow_orderOf_eq_one b, map_one] at h
    exact h.symm
  · intro h0
    have h2 : 2 ∣ orderOf b := (CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0
    exact hodd.not_two_dvd_nat h2
  · intro v hv
    exact hΦ.1 v hv

private lemma ggOmW5aB_squarefree_minpoly {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) := by
  rw [← ggOmW5aB_toLinEquiv_toLinearMap b]
  exact (ggOmW5aB_oddOrderIsometry Φ hΦ b hb hodd).squarefree_minpoly

private lemma ggOmW5aB_adjoin_mul_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {a c : Matrix ι ι K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    (hc : c ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) :
    a * c = c * a := by
  have hA : Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) =
      Algebra.adjoin K ({(b : Matrix ι ι K)} : Set (Matrix ι ι K)) := by
    rw [Set.image_singleton]
  rw [hA, Algebra.adjoin_singleton_eq_range_aeval] at ha hc
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hc
  rw [← hr, ← hs, ← map_mul, ← map_mul, mul_comm r s]

private noncomputable def ggOmW5aB_fixedProjection {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (b : GL ι K) : Matrix ι ι K :=
  (Matrix.toLinAlgEquiv' (R := K) (n := ι)).symm
    (primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) (X - 1))

private lemma ggOmW5aB_fixedProjection_toLin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) :
    Matrix.toLinAlgEquiv' (ggOmW5aB_fixedProjection b) =
      primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) (X - 1) := by
  rw [ggOmW5aB_fixedProjection, AlgEquiv.apply_symm_apply]

private lemma ggOmW5aB_fixedProjection_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) :
    ggOmW5aB_fixedProjection b ∈
      Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) := by
  have hA : Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) =
      Algebra.adjoin K ({(b : Matrix ι ι K)} : Set (Matrix ι ι K)) := by
    rw [Set.image_singleton]
  have hmem : Matrix.toLinAlgEquiv' (ggOmW5aB_fixedProjection b) ∈
      Algebra.adjoin K ({Matrix.toLin' (b : Matrix ι ι K)} :
        Set (Module.End K (ι → K))) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, ggOmW5aB_fixedProjection_toLin,
      primaryProjection]
    exact ⟨primaryIdempotent (Matrix.toLin' (b : Matrix ι ι K)) (X - 1), rfl⟩
  have hmap : (Algebra.adjoin K ({(b : Matrix ι ι K)} : Set (Matrix ι ι K))).map
      (Matrix.toLinAlgEquiv' (R := K) (n := ι)) =
      Algebra.adjoin K ({Matrix.toLin' (b : Matrix ι ι K)} :
        Set (Module.End K (ι → K))) := by
    rw [AlgHom.map_adjoin]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Set.mem_singleton_iff.mpr (ggOmW5aB_toLinAlgEquiv'_eq_toLin' (b : Matrix ι ι K))
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨(b : Matrix ι ι K), Set.mem_singleton _, rfl⟩
  rw [hA]
  rw [← hmap] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  rwa [Matrix.toLinAlgEquiv'.injective hyeq] at hy

private lemma ggOmW5aB_fixedProjection_idem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K))) :
    IsIdempotentElem (ggOmW5aB_fixedProjection b) := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul, ggOmW5aB_fixedProjection_toLin]
  exact CFSG.RankThree.PartOne.KCUnitary.primaryProjection_mul_self
    (ggOmW5aB_squarefree_minpoly Φ hΦ b hb hodd) hX1

private lemma ggOmW5aB_G_isUnit_det {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det := by
  have hEqB : Matrix.toLinearMap₂' K (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      = QuadraticMap.polarBilin Φ := by
    rw [show LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) from rfl]
    exact Matrix.toLinearMap₂'_toMatrix' _
  have hJnd : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · apply hΦ.1 v
      intro w
      have h := hv w
      rwa [← Matrix.toLinearMap₂'_apply'
        (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)), hEqB] at h
    · apply hΦ.2 w
      intro v
      have h := hw v
      rwa [← Matrix.toLinearMap₂'_apply'
        (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)), hEqB] at h
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

private lemma ggOmW5aB_formAdj_id {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (G a : Matrix ι ι K) : formAdj (RingHom.id K) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id K)) = a from by ext i j; rfl]

private lemma ggOmW5aB_formAdj_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G a : Matrix ι ι K} (hG : IsUnit G.det) (y : ι → K) :
    G.mulVec ((formAdj (RingHom.id K) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [ggOmW5aB_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma ggOmW5aB_dotProduct_mulVec_transpose {ι K : Type} [Fintype ι] [CommSemiring K]
    (M : Matrix ι ι K) (x y : ι → K) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma ggOmW5aB_polar_eq_dot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x y : ι → K) :
    QuadraticMap.polar Φ x y =
      dotProduct x ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma ggOmW5aB_formAdj_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det)
    (a : Matrix ι ι K) (x y : ι → K) :
    QuadraticMap.polar Φ (a.mulVec x) y =
      QuadraticMap.polar Φ x ((formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) a).mulVec y) := by
  rw [ggOmW5aB_polar_eq_dot Φ, ggOmW5aB_polar_eq_dot Φ,
    ggOmW5aB_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).mulVec y),
    ggOmW5aB_formAdj_mulVec hG y]

private lemma ggOmW5aB_polar_primaryProjection_reciprocal
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) {u : V}
    (hu : u ∈ primaryComponent x.toLinearMap r) (y : V) :
    QuadraticMap.polar Q u y =
      QuadraticMap.polar Q u (primaryProjection x.toLinearMap (reciprocalPolynomial r) y) := by
  classical
  have hsum : y = ∑ a ∈ primaryFactors x.toLinearMap, primaryProjection x.toLinearMap a y := by
    have := LinearMap.congr_fun (sum_primaryProjection hx.squarefree_minpoly) y
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  have h := map_sum (QuadraticMap.polarBilin Q u)
    (fun a => primaryProjection x.toLinearMap a y) (primaryFactors x.toLinearMap)
  simp only [QuadraticMap.polarBilin_apply_apply] at h
  conv_lhs => rw [hsum]
  rw [h, Finset.sum_eq_single (reciprocalPolynomial r)]
  · intro a ha har
    exact hx.polar_primaryComponent_eq_zero hr ha har hu
      (primaryProjection_mem hx.squarefree_minpoly ha y)
  · intro hr'
    exact absurd (hx.reciprocalPolynomial_mem hr) hr'

private lemma ggOmW5aB_polar_adjoint_primaryProjection
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {c : K[X]} (hc : c ∈ primaryFactors x.toLinearMap) (u w : V) :
    QuadraticMap.polar Q (primaryProjection x.toLinearMap c u) w =
      QuadraticMap.polar Q u (primaryProjection x.toLinearMap (reciprocalPolynomial c) w) := by
  have h1 := ggOmW5aB_polar_primaryProjection_reciprocal hx hc
    (primaryProjection_mem hx.squarefree_minpoly hc u) w
  have hc' := hx.reciprocalPolynomial_mem hc
  have h2 := ggOmW5aB_polar_primaryProjection_reciprocal hx hc'
    (primaryProjection_mem hx.squarefree_minpoly hc' w) u
  rw [hx.reciprocal_reciprocal_eq hc] at h2
  calc QuadraticMap.polar Q (primaryProjection x.toLinearMap c u) w
      = QuadraticMap.polar Q (primaryProjection x.toLinearMap c u)
          (primaryProjection x.toLinearMap (reciprocalPolynomial c) w) := h1
    _ = QuadraticMap.polar Q (primaryProjection x.toLinearMap (reciprocalPolynomial c) w)
          (primaryProjection x.toLinearMap c u) := QuadraticMap.polar_comm Q _ _
    _ = QuadraticMap.polar Q (primaryProjection x.toLinearMap (reciprocalPolynomial c) w) u :=
          h2.symm
    _ = QuadraticMap.polar Q u (primaryProjection x.toLinearMap (reciprocalPolynomial c) w) :=
          QuadraticMap.polar_comm Q _ _

private lemma ggOmW5aB_matrix_adjoint_primaryProjection
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {c : K[X]} (hc : c ∈ primaryFactors x.toLinearMap) {e : Matrix ι ι K}
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection x.toLinearMap c) :
    Matrix.toLinAlgEquiv' (formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) =
      primaryProjection x.toLinearMap (reciprocalPolynomial c) := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    ggOmW5aB_G_isUnit_det Φ hΦ
  rw [ggOmW5aB_toLinAlgEquiv'_eq_toLin']
  apply LinearMap.ext
  intro w
  rw [← sub_eq_zero]
  apply hΦ.1
  intro u
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left, sub_eq_zero]
  rw [QuadraticMap.polar_comm Φ _ u, QuadraticMap.polar_comm Φ _ u]
  have h1 : QuadraticMap.polar Φ u (Matrix.toLin' (formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) w) =
      QuadraticMap.polar Φ (e.mulVec u) w := by
    rw [Matrix.toLin'_apply, ← ggOmW5aB_formAdj_apply Φ hG e u w]
  rw [h1, ← ggOmW5aB_polar_adjoint_primaryProjection hx hc u w,
    ← Matrix.toLinAlgEquiv'_apply, hae]

private lemma ggOmW5aB_fixedProjection_adjoint {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K))) :
    formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (ggOmW5aB_fixedProjection b) = ggOmW5aB_fixedProjection b := by
  have hx := ggOmW5aB_oddOrderIsometry Φ hΦ b hb hodd
  have hxlin : (ggOmW5a_toLinEquiv b).toLinearMap = Matrix.toLin' (b : Matrix ι ι K) :=
    ggOmW5aB_toLinEquiv_toLinearMap b
  have hX1' : (X - 1 : K[X]) ∈ primaryFactors (ggOmW5a_toLinEquiv b).toLinearMap := by
    rwa [hxlin]
  have hae : Matrix.toLinAlgEquiv' (ggOmW5aB_fixedProjection b) =
      primaryProjection (ggOmW5a_toLinEquiv b).toLinearMap (X - 1) := by
    rw [ggOmW5aB_fixedProjection_toLin, ← hxlin]
  have h := ggOmW5aB_matrix_adjoint_primaryProjection Φ hΦ hx hX1' hae
  rw [reciprocalPolynomial_X_sub_one] at h
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, hae]

private lemma ggOmW5aB_fixedProjection_range_le {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K))) :
    (Matrix.toLin' (b : Matrix ι ι K) - 1) * Matrix.toLin' (ggOmW5aB_fixedProjection b) = 0 := by
  have hsq := ggOmW5aB_squarefree_minpoly Φ hΦ b hb hodd
  have hdvd : minpoly K (Matrix.toLin' (b : Matrix ι ι K)) ∣
      (X - 1 : K[X]) * primaryIdempotent (Matrix.toLin' (b : Matrix ι ι K))
        (X - 1 : K[X]) :=
    (primaryIdempotent_spec hsq hX1).2.2
  have hzero : aeval (Matrix.toLin' (b : Matrix ι ι K))
      ((X - 1 : K[X]) * primaryIdempotent (Matrix.toLin' (b : Matrix ι ι K))
        (X - 1 : K[X])) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  rw [← ggOmW5aB_toLinAlgEquiv'_eq_toLin' (ggOmW5aB_fixedProjection b),
    ggOmW5aB_fixedProjection_toLin, primaryProjection]
  rw [show Matrix.toLin' (b : Matrix ι ι K) - 1 =
      aeval (Matrix.toLin' (b : Matrix ι ι K)) (X - 1 : K[X]) from by
    rw [map_sub, aeval_X, map_one]]
  rw [← map_mul]
  exact hzero

private lemma ggOmW5aB_fixedProjection_mul_eps_eq_zero {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hne : (b : Matrix ι ι K) * ε ≠ ε)
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K))) :
    ggOmW5aB_fixedProjection b * ε = 0 := by
  classical
  set A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) with hA
  set E₁ : Matrix ι ι K := ggOmW5aB_fixedProjection b with hE₁
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun x hx y hy => ggOmW5aB_adjoin_mul_comm b hx hy
  have hE₁mem : E₁ ∈ A := ggOmW5aB_fixedProjection_mem b
  have hE₁idem : IsIdempotentElem E₁ :=
    ggOmW5aB_fixedProjection_idem Φ hΦ b hb hodd hX1
  have hE₁adj : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) E₁ =
      E₁ := ggOmW5aB_fixedProjection_adjoint Φ hΦ b hb hodd hX1
  set f : Matrix ι ι K := E₁ * ε with hf
  have hfmem : f ∈ A := A.mul_mem hE₁mem hε.1
  have hfidem : IsIdempotentElem f := by
    rw [hf]
    show (E₁ * ε) * (E₁ * ε) = E₁ * ε
    calc (E₁ * ε) * (E₁ * ε)
        = E₁ * (ε * (E₁ * ε)) := by rw [mul_assoc]
      _ = E₁ * ((ε * E₁) * ε) := by rw [mul_assoc]
      _ = E₁ * ((E₁ * ε) * ε) := by rw [hcomm ε hε.1 E₁ hE₁mem]
      _ = E₁ * (E₁ * (ε * ε)) := by rw [mul_assoc]
      _ = (E₁ * E₁) * (ε * ε) := by rw [mul_assoc]
      _ = E₁ * ε := by rw [hE₁idem.eq, hε.2.1.eq]
  have hfadj : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) f = f := by
    rw [hf, CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K)
      (ggOmW5aB_G_isUnit_det Φ hΦ) E₁ ε, hε.2.2.2.1,
      hE₁adj, hcomm ε hε.1 E₁ hE₁mem]
  have hfe : f * ε = f := by
    rw [hf, mul_assoc, hε.2.1.eq]
  rcases hε.2.2.2.2 f hfmem hfidem hfadj hfe with h0 | heq
  · rw [hf] at h0
    exact h0
  · exfalso
    rw [hf] at heq
    apply hne
    have hproj : Matrix.toLin' (b : Matrix ι ι K) * Matrix.toLin' E₁ = Matrix.toLin' E₁ := by
      have h := ggOmW5aB_fixedProjection_range_le Φ hΦ b hb hodd hX1
      rw [sub_mul, one_mul, sub_eq_zero] at h
      exact h
    have hproj_apply : ∀ w, Matrix.toLin' (b : Matrix ι ι K) (Matrix.toLin' E₁ w) =
        Matrix.toLin' E₁ w := by
      intro w
      have h := congrArg (fun T : (ι → K) →ₗ[K] (ι → K) => T w) hproj
      rwa [Module.End.mul_apply] at h
    have hEε : ∀ v, Matrix.toLin' ε v = Matrix.toLin' E₁ (Matrix.toLin' ε v) := by
      intro v
      conv_lhs => rw [← heq]
      rw [Matrix.toLin'_mul_apply]
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    calc Matrix.toLin' ((b : Matrix ι ι K) * ε) v
        = Matrix.toLin' (b : Matrix ι ι K) (Matrix.toLin' ε v) :=
          Matrix.toLin'_mul_apply (b : Matrix ι ι K) ε v
      _ = Matrix.toLin' (b : Matrix ι ι K) (Matrix.toLin' E₁ (Matrix.toLin' ε v)) :=
            congrArg (Matrix.toLin' (b : Matrix ι ι K)) (hEε v)
      _ = Matrix.toLin' E₁ (Matrix.toLin' ε v) := hproj_apply _
      _ = Matrix.toLin' ε v := (hEε v).symm

private lemma ggOmW5aB_eps_apply_fix_eq_zero {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hne : (b : Matrix ι ι K) * ε ≠ ε) :
    ∀ u : ι → K, u ∈ ggOmW5a_fix b → (ε : Matrix ι ι K) *ᵥ u = 0 := by
  intro u hu
  by_cases hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K))
  · have hE₁ε : ggOmW5aB_fixedProjection b * ε = 0 :=
      ggOmW5aB_fixedProjection_mul_eps_eq_zero Φ hΦ b hb hodd ε hε hne hX1
    have hεE₁ : ε * ggOmW5aB_fixedProjection b = 0 := by
      rw [← hE₁ε, ggOmW5aB_adjoin_mul_comm b hε.1 (ggOmW5aB_fixedProjection_mem b)]
    have hu' : Matrix.toLin' (ggOmW5aB_fixedProjection b) u = u := by
      rw [← ggOmW5aB_toLinAlgEquiv'_eq_toLin' (ggOmW5aB_fixedProjection b),
        ggOmW5aB_fixedProjection_toLin]
      refine primaryProjection_of_mem (ggOmW5aB_squarefree_minpoly Φ hΦ b hb hodd) hX1 ?_
      rw [mem_primaryComponent,
        show aeval (Matrix.toLin' (b : Matrix ι ι K)) (X - 1 : K[X]) =
          Matrix.toLin' (b : Matrix ι ι K) - 1 from by rw [map_sub, aeval_X, map_one]]
      exact LinearMap.mem_ker.mp hu
    have hu'' : ggOmW5aB_fixedProjection b *ᵥ u = u := by
      rw [← Matrix.toLin'_apply]
      exact hu'
    calc (ε : Matrix ι ι K) *ᵥ u
        = ε *ᵥ (ggOmW5aB_fixedProjection b *ᵥ u) := by rw [hu'']
      _ = (ε * ggOmW5aB_fixedProjection b) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hεE₁, Matrix.zero_mulVec]
  · have hX1' : (X - 1 : K[X]) ∉ primaryFactors (ggOmW5a_toLinEquiv b).toLinearMap := by
      rwa [ggOmW5aB_toLinEquiv_toLinearMap b]
    have hbot : ggOmW5a_fix b = ⊥ := by
      rw [ggOmW5a_fix_eq_fixSpace b]
      exact fixedSpace_eq_bot_of_not_mem hX1'
    rw [hbot, Submodule.mem_bot] at hu
    rw [hu, Matrix.mulVec_zero]

private lemma ggOmW5aB_restrictFixed_eq_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b g : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hne : (b : Matrix ι ι K) * ε ≠ ε)
    (hfix : (g : Matrix ι ι K) * (1 - ε) = 1 - ε)
    (hgm : ggOmW5a_toLinEquiv g ∈ isometryCentralizer Φ (ggOmW5a_toLinEquiv b)) :
    isometryRestrictFixed Φ (ggOmW5a_toLinEquiv b) ⟨ggOmW5a_toLinEquiv g, hgm⟩ = 1 := by
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  rw [coe_isometryRestrictFixed, LinearEquiv.coe_one, id]
  have heps0 : (ε : Matrix ι ι K) *ᵥ (w : ι → K) = 0 := by
    apply ggOmW5aB_eps_apply_fix_eq_zero Φ hΦ b hb hodd ε hε hne
    rw [ggOmW5a_fix_eq_fixSpace b]
    exact w.2
  rw [ggOmW5aB_toLinEquiv_apply]
  calc (g : Matrix ι ι K) *ᵥ (w : ι → K)
      = (g : Matrix ι ι K) *ᵥ ((1 - ε : Matrix ι ι K) *ᵥ (w : ι → K)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, heps0, sub_zero]
    _ = ((g : Matrix ι ι K) * (1 - ε)) *ᵥ (w : ι → K) := by rw [Matrix.mulVec_mulVec]
    _ = (1 - ε : Matrix ι ι K) *ᵥ (w : ι → K) := by rw [hfix]
    _ = (w : ι → K) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, heps0, sub_zero]

private theorem ggOmW5a_block_fix_complement_mem_omega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b g : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hg : g ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hgb : g * b = b * g)
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hne : (b : Matrix ι ι K) * ε ≠ ε)
    (hfix : (g : Matrix ι ι K) * (1 - ε) = 1 - ε) :
    g ∈ StatedOmega ⇑Φ := by
  have hgm : ggOmW5a_toLinEquiv g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ :=
    (ggOmW5a_matrixOrthogonal_iff_orthogonalGroup Φ g).mp hg
  have hgcomm : Commute (ggOmW5a_toLinEquiv g) (ggOmW5a_toLinEquiv b) := by
    rw [commute_iff_eq, ← ggOmW5aB_toLinEquiv_mul, ← ggOmW5aB_toLinEquiv_mul, hgb]
  have hgmem : ggOmW5a_toLinEquiv g ∈ isometryCentralizer Φ (ggOmW5a_toLinEquiv b) := by
    rw [isometryCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨hgm, hgcomm⟩
  have hfix1 : isometryRestrictFixed Φ (ggOmW5a_toLinEquiv b)
      ⟨ggOmW5a_toLinEquiv g, hgmem⟩ = 1 :=
    ggOmW5aB_restrictFixed_eq_one Φ hΦ b g hb hodd ε hε hne hfix hgmem
  have hx : OddOrderIsometry Φ (orderOf b) (ggOmW5a_toLinEquiv b) :=
    ggOmW5aB_oddOrderIsometry Φ hΦ b hb hodd
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hD := DFunLike.congr_fun
    (hx.dicksonCentralizer_eq_dicksonFixed hodd hΦ hRep) ⟨ggOmW5a_toLinEquiv g, hgmem⟩
  have hL : dicksonCentralizer Φ (ggOmW5a_toLinEquiv b) hΦ ⟨ggOmW5a_toLinEquiv g, hgmem⟩ =
      CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ ⟨ggOmW5a_toLinEquiv g, hgm⟩ := by
    apply congrArg (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ)
    exact Subtype.ext rfl
  have hR : dicksonFixed hx ⟨ggOmW5a_toLinEquiv g, hgmem⟩ = 1 := by
    have h2 : dicksonFixed hx ⟨ggOmW5a_toLinEquiv g, hgmem⟩ =
        CFSG.RankThree.OrthogonalInvolutions.dicksonHom
          (Φ.comp (fixedSpace (ggOmW5a_toLinEquiv b)).subtype)
          hx.polarBilin_fixed_nondegenerate
          ⟨isometryRestrictFixed Φ (ggOmW5a_toLinEquiv b) ⟨ggOmW5a_toLinEquiv g, hgmem⟩,
            isometryRestrictFixed_mem_orthogonalGroup _⟩ := rfl
    rw [h2]
    have h3 : (⟨isometryRestrictFixed Φ (ggOmW5a_toLinEquiv b) ⟨ggOmW5a_toLinEquiv g, hgmem⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ :
        TauCeti.QuadraticMap.orthogonalGroup
          (Φ.comp (fixedSpace (ggOmW5a_toLinEquiv b)).subtype)) = 1 := by
      apply Subtype.ext
      exact hfix1
    rw [h3, map_one]
  have hd1 : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ
      ⟨ggOmW5a_toLinEquiv g, hgm⟩ = 1 := by
    rw [← hL, hD, hR]
  have heven := even_finrank_commSpace_of_dicksonHom_eq_one hΦ hd1
  have homega : ggOmW5a_toLinEquiv g ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ :=
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hgm, heven⟩
  exact (ggOmW5a_statedOmega_iff_omegaGroup Φ hΦ h8 g).mpr homega

private lemma ggOmW5aC_pair_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ x ∈ Units.val '' S, ∀ y ∈ Units.val '' S, x * y = y * x := by
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨s', hs', rfl⟩
  simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F))
    (hS s hs s' hs')

private lemma ggOmW5aC_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  intro a ha b hb
  exact Algebra.adjoin_induction₂ (R := F) (A := Matrix ι ι F) (s := Units.val '' S)
    (p := fun a b _ _ => a * b = b * a)
    (fun x y hx hy => ggOmW5aC_pair_comm S hS x hx y hy)
    (fun r₁ r₂ => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun x y z hx hy hz hxz hyz => by rw [add_mul, mul_add, hxz, hyz])
    (fun x y z hx hy hz hxy hxz => by rw [mul_add, add_mul, hxy, hxz])
    (fun x y z hx hy hz hxz hyz => by
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
    (fun x y z hx hy hz hxy hxz => by
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc])
    (x := a) (y := b) ha hb

private lemma ggOmW5aC_adjoin_commute_S {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (a : Matrix ι ι F) (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (s : GL ι F) (hs : s ∈ S) :
    a * (s : Matrix ι ι F) = (s : Matrix ι ι F) * a :=
  ggOmW5aC_adjoin_comm S hS a ha (s : Matrix ι ι F)
    (Algebra.subset_adjoin ⟨s, hs, rfl⟩)

private lemma ggOmW5aC_mem_adjoin_commute {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (x : U) (hx : x ∈ (Subgroup.centralizer S).comap j) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(j x : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(j x : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) t ht
    have hm : (t : Matrix ι ι F) * (j x : Matrix ι ι F) =
        (j x : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
    exact hm.symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F {(j x : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  intro a ha
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (j x) (Set.mem_singleton _)

private lemma ggOmW5aC_inv_comm {R : Type} [Ring R] {x xi e : R} (hx : x * xi = 1)
    (hxi : xi * x = 1) (hc : x * e = e * x) : xi * e = e * xi := by
  calc xi * e = xi * e * (x * xi) := by rw [hx, mul_one]
    _ = xi * (e * x) * xi := by noncomm_ring
    _ = xi * (x * e) * xi := by rw [hc]
    _ = xi * x * e * xi := by noncomm_ring
    _ = e * xi := by rw [hxi]; noncomm_ring

private lemma ggOmW5aC_blk_val_mul_inv {R : Type} [Ring R] (x xi e : R) (hx : x * xi = 1)
    (hid : e * e = e) (hci : xi * e = e * xi) :
    (x * e + (1 - e)) * (xi * e + (1 - e)) = 1 := by
  have hxe : x * (xi * e) = e := by rw [← mul_assoc, hx, one_mul]
  have hexi : e * (xi * e) = xi * e := by
    calc e * (xi * e) = (e * xi) * e := by rw [mul_assoc]
      _ = (xi * e) * e := by rw [← hci]
      _ = xi * (e * e) := by rw [mul_assoc]
      _ = xi * e := by rw [hid]
  have hxe' : (x * e) * (xi * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private lemma ggOmW5aC_blk_inv_mul {R : Type} [Ring R] (x xi e : R) (hxi : xi * x = 1)
    (hid : e * e = e) (hc : x * e = e * x) :
    (xi * e + (1 - e)) * (x * e + (1 - e)) = 1 := by
  have hxe : xi * (x * e) = e := by rw [← mul_assoc, hxi, one_mul]
  have hexi : e * (x * e) = x * e := by
    calc e * (x * e) = (e * x) * e := by rw [mul_assoc]
      _ = (x * e) * e := by rw [← hc]
      _ = x * (e * e) := by rw [mul_assoc]
      _ = x * e := by rw [hid]
  have hxe' : (xi * e) * (x * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private noncomputable def ggOmW5aC_blkAux {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) : GL ι F :=
  Units.mk ((x : Matrix ι ι F) * e + (1 - e))
    (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e))
    (ggOmW5aC_blk_val_mul_inv (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.mul_inv x) hid.eq
      (ggOmW5aC_inv_comm (Units.mul_inv x) (Units.inv_mul x) hcomm))
    (ggOmW5aC_blk_inv_mul (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.inv_mul x) hid.eq hcomm)

private noncomputable def ggOmW5aC_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) : GL ι F := by
  classical
  exact if h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e)
    then Classical.choose h else 1

private lemma ggOmW5aC_blk_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (ggOmW5aC_blk x e : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) := by
  have h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) :=
    ⟨ggOmW5aC_blkAux x e hid hcomm, rfl⟩
  rw [ggOmW5aC_blk, dif_pos h]
  exact Classical.choose_spec h

private lemma ggOmW5aC_blk_mem_centralizer {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (x : U)
    (hx : x ∈ (Subgroup.centralizer S).comap j) (e : Matrix ι ι F)
    (heA : e ∈ Algebra.adjoin F (Units.val '' S)) (hid : IsIdempotentElem e)
    (hxe : (j x : Matrix ι ι F) * e = e * (j x : Matrix ι ι F)) :
    ggOmW5aC_blk (j x) e ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ggOmW5aC_blk_val (j x) e hid hxe]
  have hxs : (s : Matrix ι ι F) * (j x : Matrix ι ι F) =
      (j x : Matrix ι ι F) * (s : Matrix ι ι F) := by
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) s hs
    simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
  have hes : e * (s : Matrix ι ι F) = (s : Matrix ι ι F) * e :=
    ggOmW5aC_adjoin_commute_S S hS e heA s hs
  have h1 : (s : Matrix ι ι F) * ((j x : Matrix ι ι F) * e) =
      (j x : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
    rw [← mul_assoc, hxs, mul_assoc]
  noncomm_ring [hxs, hes, h1]

private lemma ggOmW5aC_blk_mem_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    ggOmW5aC_blk x e ∈ glFixing (1 - e) := by
  change ((ggOmW5aC_blk x e : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
  rw [ggOmW5aC_blk_val x e hid hxe]
  have h1 : e * (e * (x : Matrix ι ι F)) = e * (x : Matrix ι ι F) := by
    rw [← mul_assoc, hid.eq]
  noncomm_ring [hid.eq, hxe, h1]

private lemma ggOmW5aC_polar_eq_dot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x y : ι → K) :
    QuadraticMap.polar Φ x y =
      dotProduct x ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma ggOmW5aC_formAdj_id {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (G a : Matrix ι ι K) : formAdj (RingHom.id K) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id K)) = a from by ext i j; rfl]

private lemma ggOmW5aC_formAdj_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G a : Matrix ι ι K} (hG : IsUnit G.det) (y : ι → K) :
    G.mulVec ((formAdj (RingHom.id K) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [ggOmW5aC_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma ggOmW5aC_dotProduct_mulVec_transpose {ι K : Type} [Fintype ι] [CommSemiring K]
    (M : Matrix ι ι K) (x y : ι → K) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma ggOmW5aC_formAdj_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det)
    (a : Matrix ι ι K) (x y : ι → K) :
    QuadraticMap.polar Φ (a.mulVec x) y =
      QuadraticMap.polar Φ x ((formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) a).mulVec y) := by
  rw [ggOmW5aC_polar_eq_dot Φ, ggOmW5aC_polar_eq_dot Φ,
    ggOmW5aC_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).mulVec y),
    ggOmW5aC_formAdj_mulVec hG y]

private lemma ggOmW5aC_polar_selfAdjoint {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det)
    {E : Matrix ι ι K}
    (hE : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) E = E) (x y : ι → K) :
    QuadraticMap.polar Φ (E.mulVec x) y = QuadraticMap.polar Φ x (E.mulVec y) := by
  rw [ggOmW5aC_formAdj_apply Φ hG E x y, hE]

private lemma ggOmW5aC_blk_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det)
    {E A : Matrix ι ι K} (hEid : IsIdempotentElem E)
    (hEadj : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) E = E)
    (hAE : A * E = E * A) (hAiso : ∀ v, Φ (A.mulVec v) = Φ v) :
    ∀ v, Φ ((A * E + (1 - E)).mulVec v) = Φ v := by
  intro v
  have hE1 : E * (1 - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hEid, sub_self]
  have hE1mul : E.mulVec ((1 - E).mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, hE1, Matrix.zero_mulVec]
  have hsplit1 : (1 - E).mulVec v = v - E.mulVec v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hX : (A * E + (1 - E)).mulVec v =
      A.mulVec (E.mulVec v) + (1 - E).mulVec v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  rw [hX, QuadraticMap.map_add (⇑Φ)]
  have hQA : Φ (A.mulVec (E.mulVec v)) = Φ (E.mulVec v) := hAiso _
  have hpolar : QuadraticMap.polar Φ (A.mulVec (E.mulVec v)) ((1 - E).mulVec v) = 0 := by
    have hAu : A.mulVec (E.mulVec v) = E.mulVec (A.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAE]
    rw [hAu, ggOmW5aC_polar_selfAdjoint Φ hG hEadj (A.mulVec v) ((1 - E).mulVec v),
      hE1mul]
    exact QuadraticMap.polar_zero_right Φ (A.mulVec v)
  have hQv : Φ v = Φ (E.mulVec v) + Φ ((1 - E).mulVec v) := by
    have hvs : v = E.mulVec v + (1 - E).mulVec v := by
      rw [hsplit1]
      abel
    conv_lhs => rw [hvs]
    rw [QuadraticMap.map_add (⇑Φ),
      ggOmW5aC_polar_selfAdjoint Φ hG hEadj v ((1 - E).mulVec v), hE1mul,
      QuadraticMap.polar_zero_right, add_zero]
  rw [hQA, hpolar, add_zero, hQv]

private lemma ggOmW5aC_statedOmega_le_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) :
    StatedOmega ⇑Φ ≤ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ := by
  rw [CFSG.Blueprint.EvenSource.statedOmega_eq_commutator]
  exact Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact (CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ).mul_mem
      ((CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ).mul_mem
        ((CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ).mul_mem h₁ h₂)
        ((CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ).inv_mem h₁))
      ((CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ).inv_mem h₂))

private lemma ggOmW5aC_gram_isUnit {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det := by
  have hEqB : Matrix.toLinearMap₂' K (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      = QuadraticMap.polarBilin Φ := by
    rw [show LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) from rfl]
    exact Matrix.toLinearMap₂'_toMatrix' _
  have hJnd : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · apply hΦ.1 v
      intro w
      have h := hv w
      rwa [← Matrix.toLinearMap₂'_apply'
        (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)), hEqB] at h
    · apply hΦ.2 w
      intro v
      have h := hw v
      rwa [← Matrix.toLinearMap₂'_apply'
        (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)), hEqB] at h
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

private lemma ggOmW5aC_gram_transpose {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) :
    Matrix.transpose ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).map (RingHom.id K))
      = LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  rw [show (⇑(RingHom.id K) : K → K) = id from rfl, Matrix.map_id]
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply]
  exact QuadraticMap.polar_comm Φ (Pi.single j 1) (Pi.single i 1)

private lemma ggOmW5aC_gram_transpose_mul_of_isometry {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) {s : Matrix ι ι K}
    (hs : ∀ x : ι → K, Φ (Matrix.mulVec s x) = Φ x) :
    Matrix.transpose s * (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) * s =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  let G := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hpol : ∀ x y : ι → K,
      QuadraticMap.polar Φ (Matrix.mulVec s x) (Matrix.mulVec s y) =
        QuadraticMap.polar Φ x y := by
    intro x y
    have hsum : Φ (Matrix.mulVec s x + Matrix.mulVec s y) = Φ (x + y) := by
      rw [← Matrix.mulVec_add, hs]
    have hEq : Φ (Matrix.mulVec s x) + Φ (Matrix.mulVec s y)
          + QuadraticMap.polar Φ (Matrix.mulVec s x) (Matrix.mulVec s y) =
        Φ x + Φ y + QuadraticMap.polar Φ x y := by
      rw [← QuadraticMap.map_add Φ (Matrix.mulVec s x) (Matrix.mulVec s y), hsum,
        QuadraticMap.map_add Φ x y]
    have hEq' : Φ x + Φ y
          + QuadraticMap.polar Φ (Matrix.mulVec s x) (Matrix.mulVec s y) =
        Φ x + Φ y + QuadraticMap.polar Φ x y := by
      simpa [hs x, hs y] using hEq
    exact add_left_cancel hEq'
  have hmul : ∀ x y : ι → K,
      dotProduct (Matrix.mulVec s x) (G.mulVec (Matrix.mulVec s y)) =
        dotProduct x ((Matrix.transpose s * G * s).mulVec y) := by
    intro x y
    rw [ggOmW5aC_dotProduct_mulVec_transpose s x (G.mulVec (Matrix.mulVec s y))]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hbil : Matrix.toBilin' (Matrix.transpose s * G * s) = Matrix.toBilin' G := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    rw [← hmul x y, ← ggOmW5aC_polar_eq_dot Φ (Matrix.mulVec s x) (Matrix.mulVec s y),
      ← ggOmW5aC_polar_eq_dot Φ x y]
    exact hpol x y
  have hmat := congrArg (LinearMap.BilinForm.toMatrix' (R₁ := K)) hbil
  rw [LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix'_toBilin'] at hmat
  exact hmat

private lemma ggOmW5aC_exists_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠ e ∧
        ε = e + formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e)) := by
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun x => rfl)
    (ggOmW5aC_gram_isUnit Φ hΦ) (ggOmW5aC_gram_transpose Φ) ?_ ?_ hε
  · intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    simpa using ggOmW5aC_gram_transpose_mul_of_isometry Φ (s := (b : Matrix ι ι K)) hb

private lemma ggOmW5aC_formAdj_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
      (formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) := by
  let G := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hG : IsUnit G.det := ggOmW5aC_gram_isUnit Φ hΦ
  have hSU : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G * (s : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    simpa using ggOmW5aC_gram_transpose_mul_of_isometry Φ (s := (b : Matrix ι ι K)) hb
  have hScomm : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hmem : formAdj (RingHom.id K) G e ∈ A :=
    Geo.formAdj_mem_adjoin (RingHom.id K) hG hSU he.1
  have hidem : IsIdempotentElem (formAdj (RingHom.id K) G e) := by
    show formAdj (RingHom.id K) G e * formAdj (RingHom.id K) G e = formAdj (RingHom.id K) G e
    rw [← Geo.formAdj_mul (RingHom.id K) hG e e, he.2.1.eq]
  have hne : formAdj (RingHom.id K) G e ≠ 0 := by
    intro h0
    have h := congrArg (formAdj (RingHom.id K) G) h0
    rw [Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG (ggOmW5aC_gram_transpose Φ) e,
      show formAdj (RingHom.id K) G (0 : Matrix ι ι K) = 0 by simp [formAdj]] at h
    exact he.2.2.1 h
  refine ⟨hmem, hidem, hne, ?_⟩
  intro f hfA hfid hfe
  have hfmem : formAdj (RingHom.id K) G f ∈ A :=
    Geo.formAdj_mem_adjoin (RingHom.id K) hG hSU hfA
  have hfidem : IsIdempotentElem (formAdj (RingHom.id K) G f) := by
    show formAdj (RingHom.id K) G f * formAdj (RingHom.id K) G f = formAdj (RingHom.id K) G f
    rw [← Geo.formAdj_mul (RingHom.id K) hG f f, hfid.eq]
  have hkey : formAdj (RingHom.id K) G f * e = formAdj (RingHom.id K) G f := by
    have h : e * formAdj (RingHom.id K) G f = formAdj (RingHom.id K) G f := by
      have h := congrArg (formAdj (RingHom.id K) G) hfe
      rw [Geo.formAdj_mul (RingHom.id K) hG f (formAdj (RingHom.id K) G e),
        Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG (ggOmW5aC_gram_transpose Φ) e] at h
      exact h
    exact (ggOmW5aC_adjoin_comm ({b} : Set (GL ι K)) hScomm
      (formAdj (RingHom.id K) G f) hfmem e he.1).trans h
  rcases he.2.2.2 (formAdj (RingHom.id K) G f) hfmem hfidem hkey with h0 | hee
  · left
    have h := congrArg (formAdj (RingHom.id K) G) h0
    rw [Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG (ggOmW5aC_gram_transpose Φ) f,
      show formAdj (RingHom.id K) G (0 : Matrix ι ι K) = 0 by simp [formAdj]] at h
    exact h
  · right
    have h := congrArg (formAdj (RingHom.id K) G) hee
    rw [Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG (ggOmW5aC_gram_transpose Φ) f] at h
    exact h

private lemma ggOmW5aC_odd_card_pow_add_one {K : Type} [Field K] [Fintype K] [CharP K 2]
    {d : ℕ} (hd : 1 ≤ d) : Odd (Fintype.card K ^ d + 1) := by
  obtain ⟨n, -, hcard⟩ := FiniteField.card (K := K) 2
  have hn1 : 1 ≤ (n : ℕ) := n.2
  have hcardd : Fintype.card K ^ d = 2 ^ ((n : ℕ) * d) := by
    rw [hcard, pow_mul]
  have hpos : 0 < (n : ℕ) * d := Nat.mul_pos hn1 hd
  have heven : Even (2 ^ ((n : ℕ) * d)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    rw [hm, pow_succ]
    exact ⟨2 ^ m, by ring⟩
  have hodd : Odd (2 ^ ((n : ℕ) * d) + 1) := by
    obtain ⟨t, ht⟩ := heven
    exact ⟨t, by omega⟩
  rwa [← hcardd] at hodd

private lemma ggOmW5aC_sq_sub_one (Q : ℕ) : (Q + 1) * (Q - 1) = Q ^ 2 - 1 := by
  rcases Q with _ | n
  · simp
  · have h2 : (n + 1 : ℕ) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have h4 : (n + 1) - 1 = n := by omega
    have h3 : (n + 1 + 1 : ℕ) * n = n ^ 2 + 2 * n := by ring
    rw [h2, h4, h3]
    omega

private lemma ggOmW5aC_charP_two {E : Type} [Field E] [Fintype E] {Q : ℕ}
    (hE : Fintype.card E = Q ^ 2) (hOdd : Odd (Q + 1)) : CharP E 2 := by
  obtain ⟨p, hpchar, n, hpn, hcard⟩ := FiniteField.card' (K := E)
  have hpn' : p ^ (n : ℕ) = Q ^ 2 := by rw [← hcard, hE]
  have hQeven : Even Q := by
    obtain ⟨k, hk⟩ := hOdd
    exact ⟨k, by omega⟩
  have h2dvdQ : 2 ∣ Q ^ 2 := by
    obtain ⟨k, hk⟩ := hQeven
    exact ⟨2 * k ^ 2, by rw [hk]; ring⟩
  have h2dvd : 2 ∣ p ^ (n : ℕ) := by rw [hpn']; exact h2dvdQ
  have h2d : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
  have hp2 : p = 2 := by
    by_contra hpne
    have hpodd : Odd p := hpn.odd_of_ne_two hpne
    obtain ⟨k, hk⟩ := hpodd
    obtain ⟨l, hl⟩ := h2d
    omega
  rw [← hp2]
  exact hpchar

private lemma ggOmW5aC_charP_two_of_card_pow {K E : Type} [Field K] [Fintype K] [CharP K 2]
    [Field E] [Fintype E] {d : ℕ} (hd : 1 ≤ d)
    (hE : Fintype.card E = Fintype.card K ^ d) : CharP E 2 := by
  obtain ⟨p, hpchar, n, hpn, hcard⟩ := FiniteField.card' (K := E)
  obtain ⟨m, -, hKcard⟩ := FiniteField.card (K := K) 2
  have hm1 : 1 ≤ (m : ℕ) := m.2
  have hpn' : p ^ (n : ℕ) = 2 ^ ((m : ℕ) * d) := by
    rw [← hcard, hE, hKcard, pow_mul]
  have hpos : 0 < (m : ℕ) * d := Nat.mul_pos hm1 hd
  have h2dvd : 2 ∣ p ^ (n : ℕ) := by
    rw [hpn']
    exact ⟨2 ^ ((m : ℕ) * d - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ (m : ℕ) * d)]⟩
  have h2d : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
  have hp2 : p = 2 := by
    by_contra hpne
    have hpodd : Odd p := hpn.odd_of_ne_two hpne
    obtain ⟨k, hk⟩ := hpodd
    obtain ⟨l, hl⟩ := h2d
    omega
  rw [← hp2]
  exact hpchar

private lemma ggOmW5aC_exists_normOne_ne_one {E : Type} [Field E] [Fintype E] {Q : ℕ}
    (hE : Fintype.card E = Q ^ 2) :
    ∃ ζ : E, ζ ^ (Q + 1) = 1 ∧ ζ ≠ 1 := by
  have hcard : Nat.card E - 1 = (Q + 1) * (Q - 1) := by
    rw [Nat.card_eq_fintype_card, hE, ← ggOmW5aC_sq_sub_one Q]
  have hdvd : Q + 1 ∣ Nat.card E - 1 := by
    rw [hcard]; exact Nat.dvd_mul_right (Q + 1) (Q - 1)
  obtain ⟨ζ, hζ⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd
    (K := E) (d := Q + 1) hdvd
  have hQ2 : 2 ≤ Q := by
    have h1 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [hE] at h1
    nlinarith
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (by omega)⟩

private lemma ggOmW5aC_diagonal_mem_GUFull {E : Type} [Field E] {m Q : ℕ} (hQ : 0 < Q)
    (d : Fin m → E) (hd : ∀ i, d i ^ (Q + 1) = 1) :
    ∃ D : GL (Fin m) E, (D : Matrix (Fin m) (Fin m) E) = Matrix.diagonal d ∧
      D ∈ GUFull m Q E := by
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h
    have h1 := hd i
    rw [h, zero_pow (by omega : Q + 1 ≠ 0)] at h1
    exact zero_ne_one h1
  let D : GL (Fin m) E :=
    Units.mk (Matrix.diagonal d) (Matrix.diagonal (fun i => (d i)⁻¹))
      (by
        ext i j
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl, mul_inv_cancel₀ (hd0 i)]
        · rw [if_neg hij, if_neg hij])
      (by
        ext i j
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl, inv_mul_cancel₀ (hd0 i)]
        · rw [if_neg hij, if_neg hij])
  have hDval : (D : Matrix (Fin m) (Fin m) E) = Matrix.diagonal d := rfl
  refine ⟨D, hDval, ?_⟩
  apply Subgroup.subset_closure
  show ((D : Matrix (Fin m) (Fin m) E).map (· ^ Q))ᵀ * (D : Matrix (Fin m) (Fin m) E) = 1
  rw [hDval]
  have hmap : (Matrix.diagonal d).map (· ^ Q) = Matrix.diagonal (fun i => d i ^ Q) :=
    Matrix.diagonal_map (f := fun x : E => x ^ Q) (zero_pow (by omega : Q ≠ 0))
  have htr : (Matrix.diagonal (fun i => d i ^ Q) : Matrix (Fin m) (Fin m) E)ᵀ
      = Matrix.diagonal (fun i => d i ^ Q) := by
    ext i j
    rw [Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]
  rw [hmap, htr]
  ext i j
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, ← pow_succ]
    exact hd i
  · rw [if_neg hij, if_neg hij]

private theorem ggOmW5aC_center_GL {E : Type} [Field E] [CharP E 2] {m : ℕ} (z : GL (Fin m) E)
    (hz : ∀ g : GL (Fin m) E, z * g = g * z) (hz2 : z * z = 1) : z = 1 := by
  by_cases hm : m = 0
  · subst hm
    apply Units.ext
    ext i j
    exact Fin.elim0 i
  · haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have hzmem : z ∈ Subgroup.center (GL (Fin m) E) :=
      Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    have hval : (z : Matrix (Fin m) (Fin m) E) ∈ Set.range (Matrix.scalar (Fin m)) :=
      (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hzmem
    obtain ⟨c, hc⟩ := hval
    have hz2val : (z : Matrix (Fin m) (Fin m) E) * (z : Matrix (Fin m) (Fin m) E) = 1 := by
      simpa using congrArg (fun w : GL (Fin m) E => (w : Matrix (Fin m) (Fin m) E)) hz2
    have hsq : Matrix.scalar (Fin m) (c * c) = Matrix.scalar (Fin m) (1 : E) := by
      rw [map_mul, hc, hz2val, map_one]
    have hsq' : c * c = 1 := Matrix.scalar_inj.mp hsq
    have hc1 : c = 1 := by
      apply CharTwo.sq_inj.mp
      rw [pow_two, pow_two, hsq', mul_one]
    apply Units.ext
    rw [← hc, hc1]
    simp

private theorem ggOmW5aC_center_GU {E : Type} [Field E] [Fintype E] {m Q : ℕ}
    (hE : Fintype.card E = Q ^ 2) (hOdd : Odd (Q + 1)) (z : GUFull m Q E)
    (hz : ∀ g : GUFull m Q E, z * g = g * z) (hz2 : z * z = 1) : z = 1 := by
  have hQ2 : 0 < Q := by
    by_contra h
    have hQ0 : Q = 0 := Nat.eq_zero_of_not_pos h
    have h1 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [hE, hQ0] at h1
    norm_num at h1
  haveI : CharP E 2 := ggOmW5aC_charP_two hE hOdd
  obtain ⟨ζ, hζpow, hζne⟩ := ggOmW5aC_exists_normOne_ne_one hE
  let zgl : GL (Fin m) E := z
  have hzgl2 : zgl * zgl = 1 := by
    have h := congrArg (fun w : GUFull m Q E => (w : GL (Fin m) E)) hz2
    simpa [zgl] using h
  have hzgl2mat : (zgl : Matrix (Fin m) (Fin m) E) * (zgl : Matrix (Fin m) (Fin m) E) = 1 := by
    simpa using congrArg (fun w : GL (Fin m) E => (w : Matrix (Fin m) (Fin m) E)) hzgl2
  have hzglcomm : ∀ g : GL (Fin m) E, g ∈ GUFull m Q E → zgl * g = g * zgl := by
    intro g hg
    have h := hz ⟨g, hg⟩
    simpa [zgl] using congrArg (fun w : GUFull m Q E => (w : GL (Fin m) E)) h
  have hoff : ∀ i j : Fin m, i ≠ j → (zgl : Matrix (Fin m) (Fin m) E) i j = 0 := by
    intro i j hij
    let d : Fin m → E := Function.update (fun _ => (1 : E)) i ζ
    have hd : ∀ k, d k ^ (Q + 1) = 1 := by
      intro k
      by_cases hk : k = i
      · subst hk; simp [d, hζpow]
      · simp [d, Function.update_of_ne hk]
    obtain ⟨D, hDval, hDmem⟩ := ggOmW5aC_diagonal_mem_GUFull hQ2 d hd
    have hcomm : zgl * D = D * zgl := hzglcomm D hDmem
    have hentry := congrArg (fun w : GL (Fin m) E => (w : Matrix (Fin m) (Fin m) E)) hcomm
    simp only [Units.val_mul] at hentry
    rw [hDval] at hentry
    have hentry2 := congrArg (fun N : Matrix (Fin m) (Fin m) E => N i j) hentry
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry2
    have hfj : d j = 1 := by simp [d, Function.update_of_ne (Ne.symm hij)]
    have hfi : d i = ζ := by simp [d, Function.update_self]
    rw [hfj, hfi, mul_one] at hentry2
    have hzero : (ζ - 1) * (zgl : Matrix (Fin m) (Fin m) E) i j = 0 := by
      rw [sub_mul, one_mul, ← hentry2, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hζne)
  have hdiag : (zgl : Matrix (Fin m) (Fin m) E)
      = Matrix.diagonal (fun i => (zgl : Matrix (Fin m) (Fin m) E) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij]; simp [Matrix.diagonal_apply, hij]
  have hdiag1 : ∀ i, (zgl : Matrix (Fin m) (Fin m) E) i i = 1 := by
    intro i
    have h := congrArg (fun N : Matrix (Fin m) (Fin m) E => N i i) hzgl2mat
    rw [hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply,
      if_pos rfl] at h
    exact CharTwo.sq_inj.mp (by rw [pow_two, pow_two, h, mul_one])
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij; rw [hdiag1 i]; simp
  · rw [hoff i j hij]; simp [hij]

private theorem ggOmW5a_s_eq_one_on_com {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    ∀ w ∈ ggOmW5a_com b, (s : Matrix ι ι K) *ᵥ w = w := by
  obtain ⟨P, hPprim, hPorth, hPsum, hPcomm, hPsup, -⟩ :=
    ggOmW5a_block_decomp Φ hΦ h8 b hb hodd
  let G := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hbA : (b : Matrix ι ι K) ∈ A := Algebra.subset_adjoin ⟨b, rfl, rfl⟩
  have hScomm : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    ggOmW5aC_adjoin_comm ({b} : Set (GL ι K)) hScomm
  have hbO : b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ :=
    ggOmW5aC_statedOmega_le_orth Φ hb
  have hs_mem : s ∈ (Subgroup.centralizer ({b} : Set (GL ι K))).comap
      (MonoidHom.id (GL ι K)) := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hsb
  have hsA : ∀ ε ∈ P, (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K) := fun ε hεP =>
    ggOmW5aC_mem_adjoin_commute (MonoidHom.id (GL ι K)) ({b} : Set (GL ι K))
      s hs_mem ε (hPprim ε hεP).1
  have hblockfix : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (s : Matrix ι ι K) * ε = ε := by
    intro ε hεP hne
    have hεA : ε ∈ A := (hPprim ε hεP).1
    have hid : IsIdempotentElem ε := (hPprim ε hεP).2.1
    have hadj : formAdj (RingHom.id K) G ε = ε := (hPprim ε hεP).2.2.2.1
    have hse : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K) := hsA ε hεP
    let gε : GL ι K := ggOmW5aC_blk s ε
    have hgεval : (gε : Matrix ι ι K) = (s : Matrix ι ι K) * ε + (1 - ε) :=
      ggOmW5aC_blk_val s ε hid hse
    have hgεfix : (gε : Matrix ι ι K) * (1 - ε) = 1 - ε :=
      ggOmW5aC_blk_mem_glFixing s ε hid hse
    have hgεcent : gε ∈ Subgroup.centralizer ({b} : Set (GL ι K)) :=
      ggOmW5aC_blk_mem_centralizer (MonoidHom.id (GL ι K)) ({b} : Set (GL ι K))
        hScomm s hs_mem ε hεA hid hse
    have hgεiso : ∀ v : ι → K, Φ ((gε : Matrix ι ι K) *ᵥ v) = Φ v := by
      rw [hgεval]
      exact ggOmW5aC_blk_isometry Φ (ggOmW5aC_gram_isUnit Φ hΦ) hid hadj hse hs
    have hgεO : gε ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ := hgεiso
    have hgεb : gε * b = b * gε := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hgεval]
      have hsb' : (s : Matrix ι ι K) * b = b * (s : Matrix ι ι K) := by
        simpa only [Units.val_mul] using
          congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hsb
      have heb : ε * (b : Matrix ι ι K) = (b : Matrix ι ι K) * ε := hAcomm ε hεA b hbA
      have h1 : ((s : Matrix ι ι K) * ε) * (b : Matrix ι ι K) =
          (b : Matrix ι ι K) * ((s : Matrix ι ι K) * ε) := by
        rw [Matrix.mul_assoc, heb, ← Matrix.mul_assoc, hsb', Matrix.mul_assoc]
      have h2 : (1 - ε) * (b : Matrix ι ι K) = (b : Matrix ι ι K) * (1 - ε) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, heb]
      rw [Matrix.add_mul, Matrix.mul_add, h1, h2]
    have hgεΩ : gε ∈ StatedOmega ⇑Φ :=
      ggOmW5a_block_fix_complement_mem_omega Φ hΦ h8 b gε hb hodd hgεO hgεb ε
        (hPprim ε hεP) hne hgεfix
    have hgεG : (⟨gε, hgεΩ⟩ : ↥(StatedOmega ⇑Φ)) ∈
        glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε := by
      rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      exact ⟨hgεcent, hgεfix⟩
    have hgε2 : gε * gε = 1 := by
      apply Units.ext
      rw [Units.val_mul, hgεval, Units.val_one]
      have hs2' : (s : Matrix ι ι K) * (s : Matrix ι ι K) = 1 := by
        simpa only [Units.val_mul, Units.val_one] using
          congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hs2
      have h1 : ((s : Matrix ι ι K) * ε) * ((s : Matrix ι ι K) * ε) = ε := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc ε (s : Matrix ι ι K) ε, ← hse,
          Matrix.mul_assoc, ← Matrix.mul_assoc (s : Matrix ι ι K) (s : Matrix ι ι K) (ε * ε),
          hs2', Matrix.one_mul, hid.eq]
      have h2 : ((s : Matrix ι ι K) * ε) * (1 - ε) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hid.eq, sub_self]
      have h3 : (1 - ε) * ((s : Matrix ι ι K) * ε) = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, ← hse, Matrix.mul_assoc,
          hid.eq, sub_self]
      have h4 : (1 - ε) * (1 - ε) = 1 - ε := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hid.eq, sub_self,
          sub_zero]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3, h4]
      rw [add_zero, zero_add, add_sub_cancel]
    have hgεcentral : ∀ h ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε,
        (⟨gε, hgεΩ⟩ : ↥(StatedOmega ⇑Φ)) * h =
          h * (⟨gε, hgεΩ⟩ : ↥(StatedOmega ⇑Φ)) := by
      intro h hh
      apply Subtype.ext
      apply Units.ext
      have hhin : (h : GL ι K) ∈ Subgroup.centralizer ({b} : Set (GL ι K)) ⊓
          glFixing (1 - ε) := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hh)
      have hhcent : (h : GL ι K) ∈ Subgroup.centralizer ({b} : Set (GL ι K)) := hhin.1
      have hh_eps : ((h : GL ι K) : Matrix ι ι K) * ε =
          ε * ((h : GL ι K) : Matrix ι ι K) :=
        ggOmW5aC_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
          h (Subgroup.mem_comap.mpr hhcent) ε hεA
      have hsh : (s : Matrix ι ι K) * ((h : GL ι K) : Matrix ι ι K) =
          ((h : GL ι K) : Matrix ι ι K) * (s : Matrix ι ι K) := by
        have hmem : (h : GL ι K) ∈
            Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ StatedOmega ⇑Φ :=
          Subgroup.mem_inf.mpr ⟨hhcent, h.2⟩
        have := hsC (h : GL ι K) hmem
        simpa only [Units.val_mul] using
          congrArg (fun u : GL ι K => (u : Matrix ι ι K)) this
      change (gε : Matrix ι ι K) * ((h : GL ι K) : Matrix ι ι K) =
        ((h : GL ι K) : Matrix ι ι K) * (gε : Matrix ι ι K)
      have h1 : ((s : Matrix ι ι K) * ε) * ((h : GL ι K) : Matrix ι ι K) =
          ((h : GL ι K) : Matrix ι ι K) * ((s : Matrix ι ι K) * ε) := by
        rw [Matrix.mul_assoc, ← hh_eps, ← Matrix.mul_assoc, hsh, Matrix.mul_assoc]
      have h2 : (1 - ε) * ((h : GL ι K) : Matrix ι ι K) =
          ((h : GL ι K) : Matrix ι ι K) * (1 - ε) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hh_eps]
      rw [hgεval, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have hgεone : gε = 1 := by
      let B : Subgroup ↥(StatedOmega ⇑Φ) :=
        glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
      let x : ↥B := ⟨⟨gε, hgεΩ⟩, hgεG⟩
      have hx2 : x * x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact hgε2
      have hxcent : ∀ y : ↥B, x * y = y * x := by
        intro y
        apply Subtype.ext
        exact hgεcentral y y.2
      obtain ⟨e, heprim, hee, hcase⟩ := ggOmW5aC_exists_prim Φ hΦ b hbO (hPprim ε hεP)
      have hxeq : x = 1 := by
        rcases hcase with heq | ⟨hene, hneadj, hεeq⟩
        · obtain ⟨d, m, E, hEfield, hFintype, hd1, hEcard, hdim, hdeg, hφ⟩ :=
            ggOmW5a_block_iso_unitary Φ hΦ h8 b hb hodd (hPprim ε hεP)
              (heq ▸ heprim) hne
          obtain ⟨φ⟩ := hφ
          have hφx2 : φ x * φ x = 1 := by rw [← map_mul, hx2, map_one]
          have hφxc : ∀ y : ↥(GUFull m (Fintype.card K ^ d) E),
              φ x * y = y * φ x := by
            intro y
            simpa using congrArg φ (hxcent (φ.symm y))
          have hodd' : Odd (Fintype.card K ^ d + 1) :=
            ggOmW5aC_odd_card_pow_add_one hd1
          have hφx1 := ggOmW5aC_center_GU hEcard hodd' (φ x) hφxc hφx2
          exact φ.injective (by rw [hφx1, map_one])
        · have he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
              (formAdj (RingHom.id K) G e) :=
            ggOmW5aC_formAdj_prim Φ hΦ b hbO heprim
          obtain ⟨d, m, E, hEfield, hFintype, hd1, hEcard, hdim, hdeg, hφ⟩ :=
            ggOmW5a_block_iso_linear Φ hΦ h8 b hb hodd (hPprim ε hεP) heprim he'
              hneadj.symm hεeq
          obtain ⟨φ⟩ := hφ
          haveI : CharP E 2 := ggOmW5aC_charP_two_of_card_pow hd1 hEcard
          have hφx2 : φ x * φ x = 1 := by rw [← map_mul, hx2, map_one]
          have hφxc : ∀ y : GL (Fin m) E, φ x * y = y * φ x := by
            intro y
            simpa using congrArg φ (hxcent (φ.symm y))
          have hφx1 := ggOmW5aC_center_GL (φ x) hφxc hφx2
          exact φ.injective (by rw [hφx1, map_one])
      have hx1 : (⟨gε, hgεΩ⟩ : ↥(StatedOmega ⇑Φ)) = 1 := by
        have h2 := Subtype.ext_iff.mp hxeq
        simpa [x] using h2
      exact Subtype.ext_iff.mp hx1
    have h1 : ((s : Matrix ι ι K) * ε + (1 - ε)) * ε = ε := by
      rw [← hgεval, hgεone, Units.val_one, Matrix.one_mul]
    have : (s : Matrix ι ι K) * ε = ε := by
      have h2 : ((s : Matrix ι ι K) * ε + (1 - ε)) * ε = (s : Matrix ι ι K) * ε := by
        noncomm_ring [hid.eq]
      rw [← h2, h1]
    exact this
  intro w hw
  have hsw : (s : Matrix ι ι K) *ᵥ w = w := by
    have hwsum : w = ∑ ε ∈ P, ε *ᵥ w := by
      calc w = (1 : Matrix ι ι K) *ᵥ w := (Matrix.one_mulVec w).symm
        _ = (∑ ε ∈ P, ε) *ᵥ w := by rw [hPsum]
        _ = ∑ ε ∈ P, ε *ᵥ w := by rw [Matrix.sum_mulVec]
    rw [hwsum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun ε hεP => ?_
    by_cases hbε : (b : Matrix ι ι K) * ε = ε
    ·
      have hzero : ε *ᵥ w = 0 := by
        obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
        rw [← hu]
        rw [LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply, Matrix.mulVec_sub]
        have heb : ε * (b : Matrix ι ι K) = (b : Matrix ι ι K) * ε :=
          hAcomm ε (hPprim ε hεP).1 b hbA
        rw [Matrix.mulVec_mulVec, heb, hbε, sub_self]
      rw [hzero]
      simp
    ·
      have hfixε : (s : Matrix ι ι K) * ε = ε := hblockfix ε hεP hbε
      rw [Matrix.mulVec_mulVec, hfixε]
  exact hsw

private noncomputable def ggOmW5aD_fusionPolar (K : Type) [Field K]
    (x y : Fin 2 ⊕ Fin 2 → K) : K :=
  ∑ i : Fin 2, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i))

private def ggOmW5aD_basE (K : Type) [Field K] (i : Fin 2) : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inl i) 1

private def ggOmW5aD_basF (K : Type) [Field K] (i : Fin 2) : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inr i) 1

private theorem ggOmW5aD_fusionPolar_eq (K : Type) [Field K] [CharP K 2]
    (x y : Fin 2 ⊕ Fin 2 → K) :
    QuadraticMap.polar (ggFusionPlaneQuadratic K 2) x y = ggOmW5aD_fusionPolar K x y := by
  simp only [QuadraticMap.polar, ggFusionPlaneQuadratic, ggOmW5aD_fusionPolar, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf
  simp [show (2 : K) = 0 from CharP.cast_eq_zero K 2]

private theorem ggOmW5aD_fusionPolar_add (K : Type) [Field K]
    (x x' y : Fin 2 ⊕ Fin 2 → K) :
    ggOmW5aD_fusionPolar K (x + x') y =
      ggOmW5aD_fusionPolar K x y + ggOmW5aD_fusionPolar K x' y := by
  simp only [ggOmW5aD_fusionPolar, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf

private theorem ggOmW5aD_fusionPolar_smul (K : Type) [Field K]
    (a : K) (x y : Fin 2 ⊕ Fin 2 → K) :
    ggOmW5aD_fusionPolar K (a • x) y = a * ggOmW5aD_fusionPolar K x y := by
  simp only [ggOmW5aD_fusionPolar, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf

private noncomputable def ggOmW5aD_fusionForm (K : Type) [Field K] [CharP K 2] :
    QuadraticForm K (Fin 2 ⊕ Fin 2 → K) :=
  QuadraticMap.ofPolar (ggFusionPlaneQuadratic K 2)
    (by
      intro a x
      simp only [ggFusionPlaneQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring_nf)
    (by
      intro x x' y
      rw [ggOmW5aD_fusionPolar_eq K, ggOmW5aD_fusionPolar_eq K, ggOmW5aD_fusionPolar_eq K]
      exact ggOmW5aD_fusionPolar_add K x x' y)
    (by
      intro a x y
      rw [ggOmW5aD_fusionPolar_eq K, ggOmW5aD_fusionPolar_eq K]
      exact ggOmW5aD_fusionPolar_smul K a x y)

private theorem ggOmW5aD_fusionForm_apply (K : Type) [Field K] [CharP K 2]
    (v : Fin 2 ⊕ Fin 2 → K) :
    ggOmW5aD_fusionForm K v = ggFusionPlaneQuadratic K 2 v := rfl

private theorem ggOmW5aD_fusionForm_polar_eq (K : Type) [Field K] [CharP K 2]
    (x y : Fin 2 ⊕ Fin 2 → K) :
    (ggOmW5aD_fusionForm K).polarBilin x y = ggOmW5aD_fusionPolar K x y := by
  rw [QuadraticMap.polarBilin_apply_apply]
  change QuadraticMap.polar (ggFusionPlaneQuadratic K 2) x y = ggOmW5aD_fusionPolar K x y
  exact ggOmW5aD_fusionPolar_eq K x y

private theorem ggOmW5aD_fusionForm_nondegenerate (K : Type) [Field K] [CharP K 2] :
    (ggOmW5aD_fusionForm K).polarBilin.Nondegenerate := by
  constructor
  · intro x hx
    funext k
    rcases k with k | k
    · have h : ggOmW5aD_fusionPolar K x (ggOmW5aD_basF K k) = 0 := by
        rw [← ggOmW5aD_fusionForm_polar_eq K]
        exact hx (ggOmW5aD_basF K k)
      simpa [ggOmW5aD_fusionPolar, ggOmW5aD_basF, Pi.single_apply, Finset.sum_eq_single k,
        add_comm] using h
    · have h : ggOmW5aD_fusionPolar K x (ggOmW5aD_basE K k) = 0 := by
        rw [← ggOmW5aD_fusionForm_polar_eq K]
        exact hx (ggOmW5aD_basE K k)
      simpa [ggOmW5aD_fusionPolar, ggOmW5aD_basE, Pi.single_apply, Finset.sum_eq_single k,
        add_comm] using h
  · intro y hy
    funext k
    rcases k with k | k
    · have h : ggOmW5aD_fusionPolar K (ggOmW5aD_basF K k) y = 0 := by
        rw [← ggOmW5aD_fusionForm_polar_eq K]
        exact hy (ggOmW5aD_basF K k)
      simpa [ggOmW5aD_fusionPolar, ggOmW5aD_basF, Pi.single_apply, Finset.sum_eq_single k,
        add_comm] using h
    · have h : ggOmW5aD_fusionPolar K (ggOmW5aD_basE K k) y = 0 := by
        rw [← ggOmW5aD_fusionForm_polar_eq K]
        exact hy (ggOmW5aD_basE K k)
      simpa [ggOmW5aD_fusionPolar, ggOmW5aD_basE, Pi.single_apply, Finset.sum_eq_single k,
        add_comm] using h

private def ggOmW5aD_W (K : Type) [Field K] : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | v (Sum.inl 0) = v (Sum.inl 1) ∧ v (Sum.inr 0) = v (Sum.inr 1)}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by simp only [Pi.add_apply]; rw [ha1, hb1], by simp only [Pi.add_apply]; rw [ha2, hb2]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro c v ⟨h1, h2⟩
    exact ⟨by simp only [Pi.smul_apply]; rw [h1], by simp only [Pi.smul_apply]; rw [h2]⟩

private theorem ggOmW5aD_W_finrank (K : Type) [Field K] :
    Module.finrank K (ggOmW5aD_W K) = 2 := by
  let φ : (K × K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun p => p.1 • (ggOmW5aD_basE K 0 + ggOmW5aD_basE K 1) +
        p.2 • (ggOmW5aD_basF K 0 + ggOmW5aD_basF K 1)
      map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add, add_smul, smul_add]; abel
      map_smul' := by
        intro c p
        funext j
        rcases j with j | j <;> fin_cases j <;>
          simp [ggOmW5aD_basE, ggOmW5aD_basF, Pi.single_apply, smul_add, smul_smul,
            smul_eq_mul] }
  have hrange : ggOmW5aD_W K = LinearMap.range φ := by
    ext v
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(v (Sum.inl 0), v (Sum.inr 0)), ?_⟩
      funext j
      rcases j with j | j <;> fin_cases j <;>
        simp [φ, ggOmW5aD_basE, ggOmW5aD_basF, Pi.single_apply, h1, h2]
    · rintro ⟨p, rfl⟩
      refine ⟨?_, ?_⟩ <;>
        simp [φ, ggOmW5aD_basE, ggOmW5aD_basF, Pi.single_apply]
  rw [hrange, LinearMap.finrank_range_of_inj]
  · rw [Module.finrank_prod, Module.finrank_self]
  · intro p q hpq
    have h0 := congrFun hpq (Sum.inl 0)
    have h1 := congrFun hpq (Sum.inr 0)
    simp [φ, ggOmW5aD_basE, ggOmW5aD_basF, Pi.single_apply] at h0 h1
    exact Prod.ext h0 h1

private theorem ggOmW5aD_fusionForm_isPlusType (K : Type) [Field K] [CharP K 2] :
    CFSG.GroupTheory.WeirSylow.IsPlusType (ggOmW5aD_fusionForm K) := by
  refine ⟨ggOmW5aD_W K, ?_, ?_⟩
  · rw [ggOmW5aD_W_finrank, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin]
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    rw [ggOmW5aD_fusionForm_apply, ggFusionPlaneQuadratic, Fin.sum_univ_two]
    rw [h1, h2]
    ring_nf
    simp [show (2 : K) = 0 from CharP.cast_eq_zero K 2]

private theorem ggOmW5a_small_exception_center {K W : Type} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hexc : SmallFixedException Q)
    {z : W ≃ₗ[K] W} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, z * y = y * z) : z = 1 := by
  classical
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have h2 : (2 : ℕ) ∣ Nat.card K := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self 2 n.ne_zero
    omega
  have hdata : Module.finrank K W = 4 ∧
      (∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
      Nat.card K = 2 := by
    rcases hexc with ⟨-, h3⟩ | ⟨⟨h4, hS⟩, h | h3⟩
    · exact absurd h3 hK3
    · exact ⟨h4, hS, h⟩
    · exact absurd h3 hK3
  obtain ⟨h4, ⟨S, hSdim, hSsing⟩, hK2⟩ := hdata
  have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    ⟨S, by rw [hSdim, h4], hSsing⟩
  have hQ0nd : (ggOmW5aD_fusionForm K).polarBilin.Nondegenerate :=
    ggOmW5aD_fusionForm_nondegenerate K
  have hQ0plus : CFSG.GroupTheory.WeirSylow.IsPlusType (ggOmW5aD_fusionForm K) :=
    ggOmW5aD_fusionForm_isPlusType K
  obtain ⟨ψ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff hQ hQ0nd
    (n := 2) (by rw [h4])
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
    (iff_of_true hplusQ hQ0plus)
  let c := CFSG.RankThree.PartOne.linConj ψ.toLinearEquiv
  let z₀ : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) := c z
  have hz₀O : z₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K) := by
    change c z ∈ TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K)
    rw [← CFSG.RankThree.PartOne.map_orthogonalGroup_linConj ψ]
    exact Subgroup.mem_map_of_mem c.toMonoidHom hz
  have hz₀c : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K),
      TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K)⁆,
      z₀ * y = y * z₀ := by
    intro y hy
    change c z * y = y * c z
    have hy' : y ∈ (CFSG.RankThree.Classical2.orthDerived Q).map c.toMonoidHom := by
      rw [CFSG.RankThree.PartOne.map_orthDerived_linConj ψ]
      exact hy
    obtain ⟨y', hy'', hyy⟩ := Subgroup.mem_map.mp hy'
    have h := hzc y' hy''
    rw [← hyy]
    exact (map_mul c z y').symm.trans ((congrArg c h).trans (map_mul c y' z))
  let TL := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2) K
  let g : GL (Fin 2 ⊕ Fin 2) K := TL.symm z₀
  have hTLg : TL g = z₀ := MulEquiv.apply_symm_apply TL z₀
  have hLE : CFSG.Assembly.LargeEvenOrthGroup (ggFusionPlaneQuadratic K 2) =
      (TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K)).comap TL.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (Q := ggOmW5aD_fusionForm K) (Q₀ := ggFusionPlaneQuadratic K 2)
      (funext (ggOmW5aD_fusionForm_apply K))
  have hcommap : (⁅CFSG.Assembly.LargeEvenOrthGroup (ggFusionPlaneQuadratic K 2),
      CFSG.Assembly.LargeEvenOrthGroup (ggFusionPlaneQuadratic K 2)⁆).map TL.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K),
        TauCeti.QuadraticMap.orthogonalGroup (ggOmW5aD_fusionForm K)⁆ := by
    rw [hLE, Subgroup.map_commutator,
      Subgroup.map_comap_eq_self_of_surjective (f := TL.toMonoidHom) TL.surjective]
  have hgcomm : ∀ w ∈ ⁅CFSG.Assembly.LargeEvenOrthGroup (ggFusionPlaneQuadratic K 2),
      CFSG.Assembly.LargeEvenOrthGroup (ggFusionPlaneQuadratic K 2)⁆, g * w = w * g := by
    intro w hw
    apply TL.injective
    rw [map_mul, map_mul, hTLg]
    exact hz₀c (TL w) (by
      rw [← hcommap]
      exact Subgroup.mem_map_of_mem TL.toMonoidHom hw)
  have hg1 : g = 1 :=
    CFSG.StandardType.ggFusionPlane_eq_one_of_commute (m := 2) hK2 (by norm_num) hgcomm
  have hz₀1 : z₀ = 1 := by rw [← hTLg, hg1, map_one]
  exact c.injective (by rw [show c z = z₀ from rfl, hz₀1, map_one])

private theorem ggOmW5a_eq_one_of_commute_orthDerived {K W : Type} [Field K] [Fintype K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K W) {z : W ≃ₗ[K] W}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, z * y = y * z) : z = 1 := by
  by_cases hexc : SmallFixedException Q
  · exact ggOmW5a_small_exception_center Q hQ hexc hz hzc
  · exact LayerCores.OrthRegular.eq_one_of_commute_orthDerived hQ (by omega) hexc hz hzc

private theorem ggOmW5aD_fixSpace_reflect {K W : Type} [Field K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a : W} (ha : Q a ≠ 0)
    (h2 : Module.finrank K W = 2) :
    CFSG.RankThree.OrthogonalInvolutions.fixSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a) = K ∙ a := by
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  have hra : CFSG.ClassicalGroups.Orthogonal.reflect Q a a = a :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      (CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q a)
  have hdim : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.fixSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a)) = 1 := by
    have h := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a)
    have hc : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (CFSG.ClassicalGroups.Orthogonal.reflect Q a)) = 1 := by
      let _ : Invertible (Q a) := invertibleOfNonzero ha
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
      exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ a
    omega
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem, CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace]
    exact hra
  · rw [finrank_span_singleton ha0, hdim]

private theorem ggOmW5aD_plane_omega_eq_bot {K W : Type} [Field K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h2 : Module.finrank K W = 2)
    {s : W ≃ₗ[K] W} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hsΩ : s ∉ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
    (hsc : ∀ y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ, s * y = y * s) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ = ⊥ := by
  classical
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero (Q := Q) hQ
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  set r : W ≃ₗ[K] W := CFSG.ClassicalGroups.Orthogonal.reflect Q a with hr
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a
  have hrδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨r, hrO⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) :=
    CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_reflect hQ ha
  have htwo : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hsδne : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨s, hs⟩ ≠ 1 := by
    intro h1
    apply hsΩ
    have hmem := MonoidHom.mem_ker.mpr h1
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hsδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨s, hs⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) := (htwo _).resolve_left hsδne
  have hsrδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
      ⟨s * r, mul_mem hs hrO⟩ = 1 := by
    rw [show (⟨s * r, mul_mem hs hrO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
        ⟨s, hs⟩ * ⟨r, hrO⟩ from rfl, map_mul, hsδ, hrδ]
    rw [← ofAdd_add, show ((1 : ZMod 2) + 1) = 0 from rfl, ofAdd_zero]
  have hsr_mem : s * r ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ := by
    have hmem := MonoidHom.mem_ker.mpr hsrδ
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hsr : s * r = r * s := by
    have h := hsc (s * r) hsr_mem
    exact mul_left_cancel (by rw [h]; group)
  have hcomm : ∀ u ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
      u * r = r * u := by
    intro u hu
    have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hu).1
    have huδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨u, huO⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker]
      exact Subgroup.mem_subgroupOf.mpr hu
    have hu_s : u * s = s * u := (hsc u hu).symm
    have hu_sr : u * (s * r) = (s * r) * u :=
      CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hQ h2 huO
        (mul_mem hs hrO) huδ hsrδ
    have h1 : u * (s * r) = s * (u * r) := by
      rw [← mul_assoc u s r, hu_s, mul_assoc]
    have h2 : (s * r) * u = s * (r * u) := by rw [mul_assoc]
    exact mul_left_cancel (by rw [← h1, hu_sr, h2])
  refine le_antisymm ?_ bot_le
  intro u hu
  rw [Subgroup.mem_bot]
  have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hu).1
  have hur : u * r = r * u := hcomm u hu
  have hra : r a = a := by
    rw [hr]
    exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      (CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q a)
  have hua_fix : u a ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace r := by
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace]
    calc r (u a) = (r * u) a := (LinearEquiv.mul_apply r u a).symm
      _ = (u * r) a := by rw [hur]
      _ = u (r a) := LinearEquiv.mul_apply u r a
      _ = u a := by rw [hra]
  have hfixeq : CFSG.RankThree.OrthogonalInvolutions.fixSpace r = K ∙ a := by
    rw [hr]
    exact ggOmW5aD_fixSpace_reflect Q hQ ha h2
  rw [hfixeq] at hua_fix
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hua_fix
  have hQua : Q (u a) = Q a := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp huO a
  rw [← hlam, QuadraticMap.map_smul, smul_eq_mul] at hQua
  have hlam2 : lam * lam = 1 := by
    refine mul_right_cancel₀ ha ?_
    rw [one_mul]
    exact hQua
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hlam1 : lam = 1 := by
    have h8 : (lam - 1) ^ 2 = 0 := by
      have : (lam - 1) ^ 2 = lam * lam - 1 - 2 * (lam - 1) := by ring
      rw [this, hlam2, h2K]
      ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h8)
  have hua : u a = a := by rw [← hlam, hlam1, one_smul]
  have huδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨u, huO⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker]
    exact Subgroup.mem_subgroupOf.mpr hu
  have hu_rot : u ∈ CFSG.RankThree.PartOne.KCOrthComm.rotGroup Q hQ :=
    CFSG.RankThree.PartOne.KCOrthComm.mem_rotGroup.mpr ⟨huO, huδ⟩
  rcases (CFSG.RankThree.PartOne.KCOrthComm.mem_rotGroup_iff (hQ := hQ) h2 huO).mp hu_rot with
    h1 | hfix
  · exact h1
  · exact absurd (hfix a hua) ha0

private theorem ggOmW5a_plane_card_eq_two {K W : Type} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h2 : Module.finrank K W = 2)
    {s : W ≃ₗ[K] W} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hsΩ : s ∉ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
    (hsc : ∀ y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ, s * y = y * s) :
    Fintype.card K = 2 := by
  have hbot : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ = ⊥ :=
    ggOmW5aD_plane_omega_eq_bot Q hQ h2 hs hsΩ hsc
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hcardΩ : Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) = 1 := by
    rw [hbot]
    simp
  have hidx := Subgroup.relIndex_mul_card
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_eq_left.mpr (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ),
    CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ, hcardΩ] at hidx
  have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by omega
  have hq2 : Nat.card K = 2 := by
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
        (K := K) (V := W) hQ (m := 0) (by rw [h2]) (ε := (1 : ℤ)) (Or.inl ⟨rfl, hplus⟩)
      rw [hcardO] at hcard
      have hmain : (2 : ℤ) = 2 * ((Nat.card K : ℤ) - 1) := by simpa using hcard
      have hq : (Nat.card K : ℤ) = 2 := by linarith
      exact_mod_cast hq
    · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
        (K := K) (V := W) hQ (m := 0) (by rw [h2]) (ε := (-1 : ℤ)) (Or.inr ⟨rfl, hplus⟩)
      rw [hcardO] at hcard
      have hmain : (2 : ℤ) = 2 * ((Nat.card K : ℤ) + 1) := by simpa using hcard
      have hq : (Nat.card K : ℤ) = 0 := by linarith
      have hq0 : Nat.card K = 0 := by exact_mod_cast hq
      have h1 := Finite.one_lt_card (α := K)
      omega
  rwa [Nat.card_eq_fintype_card] at hq2

private noncomputable abbrev ggOmW5aE_ML {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] :
    GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (Matrix.GeneralLinearGroup.toLin (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

private theorem ggOmW5aE_ML_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) (v : ι → K) :
    ggOmW5aE_ML A v = (A : Matrix ι ι K) *ᵥ v := by
  simp only [ggOmW5aE_ML, MulEquiv.trans_apply,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply]

private theorem ggOmW5aE_toLin_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) (v : ι → K) :
    ggOmW5a_toLinEquiv A v = (A : Matrix ι ι K) *ᵥ v := by
  change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v = (A : Matrix ι ι K) *ᵥ v
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply]

private theorem ggOmW5aE_toLin_eq_ML {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) : ggOmW5a_toLinEquiv A = ggOmW5aE_ML A := by
  ext v
  rw [ggOmW5aE_toLin_apply, ggOmW5aE_ML_apply]

private theorem ggOmW5aE_symm_eq_self {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (hs2 : s * s = 1) :
    (ggOmW5a_toLinEquiv s).symm = ggOmW5a_toLinEquiv s := by
  have hSS : ggOmW5aE_ML s * ggOmW5aE_ML s = 1 := by
    have h := congrArg ggOmW5aE_ML hs2
    simpa only [map_mul, map_one] using h
  rw [ggOmW5aE_toLin_eq_ML s]
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.symm_apply_eq]
  exact (congrArg (fun f => f v) hSS).symm

private theorem ggOmW5aE_mem_matrixOrthogonal {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    b ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ :=
  (ggOmW5a_matrixOrthogonal_iff_orthogonalGroup Φ b).mpr
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Φ hΦ
      ((ggOmW5a_statedOmega_iff_omegaGroup Φ hΦ h8 b).mp hb))

private theorem ggOmW5aE_s_maps_fix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b s : GL ι K) (hsb : s * b = b * s) :
    ∀ u : ι → K, u ∈ ggOmW5a_fix b → ggOmW5a_toLinEquiv s u ∈ ggOmW5a_fix b := by
  intro u hu
  rw [ggOmW5aE_toLin_apply]
  exact ggOmW5a_s_maps_fix b s hsb u hu

private theorem ggOmW5aE_s_fixes_com {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    ∀ w : ι → K, w ∈ ggOmW5a_com b → ggOmW5a_toLinEquiv s w = w := by
  intro w hw
  rw [ggOmW5aE_toLin_apply]
  exact ggOmW5a_s_eq_one_on_com Φ hΦ h8 b hb hodd s hs hs2 hsb hsC w hw

private theorem ggOmW5aE_polarBilin_fix_nondegenerate {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    (QuadraticMap.polarBilin (Φ.comp (ggOmW5a_fix b).subtype)).Nondegenerate := by
  have hbO := ggOmW5aE_mem_matrixOrthogonal Φ hΦ h8 hb
  constructor
  · intro u hu
    apply Subtype.ext
    exact ggOmW5a_fix_nondegenerate Φ b hΦ hbO hodd u u.2 (fun w hw => by
      have h := hu ⟨w, hw⟩
      rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] at h)
  · intro u hu
    apply Subtype.ext
    exact ggOmW5a_fix_nondegenerate Φ b hΦ hbO hodd u u.2 (fun w hw => by
      have h := hu ⟨w, hw⟩
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] at h
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact h)

private theorem ggOmW5aE_even_finrank {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    Even (Module.finrank K (ggOmW5a_fix b)) := by
  have hnd := ggOmW5aE_polarBilin_fix_nondegenerate Φ hΦ h8 b hb hodd
  have halt : (QuadraticMap.polarBilin (Φ.comp (ggOmW5a_fix b).subtype)).IsAlt := fun u => by
    rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype]
    exact CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Φ (u : ι → K)
  exact LinearMap.BilinForm.IsAlt.even_finrank halt hnd

private theorem ggOmW5aE_finrank_commSpace_restrict {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (b s : GL ι K) (hodd : Odd (orderOf b))
    (hsV' : ∀ w : ι → K, w ∈ ggOmW5a_com b → ggOmW5a_toLinEquiv s w = w)
    (h1 : ∀ u : ι → K, u ∈ ggOmW5a_fix b → ggOmW5a_toLinEquiv s u ∈ ggOmW5a_fix b)
    (h2 : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (ggOmW5a_toLinEquiv s).symm u ∈ ggOmW5a_fix b) :
    Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (ggOmW5a_toLinEquiv s)) =
      Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2)) := by
  classical
  have hc := ggOmW5a_fix_isCompl_com b hodd
  have hmap : CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s) =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2)).map
        (ggOmW5a_fix b).subtype := by
    ext y
    constructor
    · intro hy
      rw [Submodule.mem_map]
      obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hy
      obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
      refine ⟨restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 u - u,
        CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace _ _, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, coe_restrictEquiv, map_add]
      rw [hsV' (r : ι → K) r.2]
      abel
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hz
      refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨(u : ι → K), ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, coe_restrictEquiv]
  rw [hmap, Submodule.finrank_map_subtype_eq]

private theorem ggOmW5aE_restrict_mem_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) (b s : GL ι K)
    (hs : ggOmW5a_toLinEquiv s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ)
    (h1 : ∀ u : ι → K, u ∈ ggOmW5a_fix b → ggOmW5a_toLinEquiv s u ∈ ggOmW5a_fix b)
    (h2 : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (ggOmW5a_toLinEquiv s).symm u ∈ ggOmW5a_fix b) :
    restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 ∈
      TauCeti.QuadraticMap.orthogonalGroup (Φ.comp (ggOmW5a_fix b).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, coe_restrictEquiv]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hs (w : ι → K)

private theorem ggOmW5aE_restrict_not_mem_omega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b s : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s)
    (h1 : ∀ u : ι → K, u ∈ ggOmW5a_fix b → ggOmW5a_toLinEquiv s u ∈ ggOmW5a_fix b)
    (h2 : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (ggOmW5a_toLinEquiv s).symm u ∈ ggOmW5a_fix b) :
    restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 ∉
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Φ.comp (ggOmW5a_fix b).subtype)
        (ggOmW5aE_polarBilin_fix_nondegenerate Φ hΦ h8 b hb hodd) := by
  intro hy
  have hsV' := ggOmW5aE_s_fixes_com Φ hΦ h8 b hb hodd s hs hs2 hsb hsC
  have heven : Even (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
      (restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2))) :=
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hy).2
  have hfin := ggOmW5aE_finrank_commSpace_restrict b s hodd hsV' h1 h2
  exact ggOmW5a_fix_s_not_mem_omega Φ hΦ h8 s hs hsΩ (hfin.symm ▸ heven)

private theorem ggOmW5aE_restrict_centralizes {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b s : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s)
    (h1 : ∀ u : ι → K, u ∈ ggOmW5a_fix b → ggOmW5a_toLinEquiv s u ∈ ggOmW5a_fix b)
    (h2 : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (ggOmW5a_toLinEquiv s).symm u ∈ ggOmW5a_fix b) :
    ∀ y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Φ.comp (ggOmW5a_fix b).subtype)
        (ggOmW5aE_polarBilin_fix_nondegenerate Φ hΦ h8 b hb hodd),
      restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 * y =
        y * restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 := by
  intro y hy
  classical
  have hc := ggOmW5a_fix_isCompl_com b hodd
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup (Φ.comp (ggOmW5a_fix b).subtype) :=
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hy).1
  have hxfix : ∀ u ∈ ggOmW5a_fix b, ggOmW5a_toLinEquiv b u = u := by
    intro u hu
    have hmem : u ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace
        (ggOmW5a_toLinEquiv b) := by
      rw [← ggOmW5a_fix_eq_fixSpace b]; exact hu
    exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hmem
  have hxR : ∀ w ∈ ggOmW5a_com b, ggOmW5a_toLinEquiv b w ∈ ggOmW5a_com b := by
    intro w hw
    rw [ggOmW5a_com_eq_commSpace b] at hw ⊢
    obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hw
    exact CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr
      ⟨ggOmW5a_toLinEquiv b v,
        (map_sub (ggOmW5a_toLinEquiv b) (ggOmW5a_toLinEquiv b v) v).symm⟩
  have hGW : ∀ u : ι → K, u ∈ ggOmW5a_fix b → glue hc y 1 u ∈ ggOmW5a_fix b := by
    intro u hu
    have h := glue_apply hc y 1 ⟨u, hu⟩ (0 : ggOmW5a_com b)
    rw [show glue hc y 1 u = (y ⟨u, hu⟩ : ggOmW5a_fix b) from by
      simpa only [LinearEquiv.coe_one, id_eq, map_zero, add_zero, Submodule.coe_zero] using h]
    exact (y ⟨u, hu⟩).2
  have hGW' : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (glue hc y 1).symm u ∈ ggOmW5a_fix b := by
    intro u hu
    have hGu : glue hc y 1 (((y.symm ⟨u, hu⟩ : ggOmW5a_fix b)) : ι → K) = u := by
      have h := glue_apply hc y 1 (y.symm ⟨u, hu⟩) (0 : ggOmW5a_com b)
      simpa only [LinearEquiv.coe_one, id_eq, map_zero, add_zero, Submodule.coe_zero,
        LinearEquiv.apply_symm_apply] using h
    have huniq : (glue hc y 1).symm u =
        (((y.symm ⟨u, hu⟩ : ggOmW5a_fix b)) : ι → K) := by
      rw [LinearEquiv.symm_apply_eq]
      exact hGu.symm
    rw [huniq]
    exact (y.symm ⟨u, hu⟩).2
  have hGrestr : restrictEquiv (ggOmW5a_fix b) (glue hc y 1) hGW hGW' = y := by
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    rw [coe_restrictEquiv]
    have h := glue_apply hc y 1 u (0 : ggOmW5a_com b)
    simpa only [LinearEquiv.coe_one, id_eq, map_zero, add_zero, Submodule.coe_zero] using h
  have hGO : glue hc y 1 ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
    have hbO := ggOmW5aE_mem_matrixOrthogonal Φ hΦ h8 hb
    have hyu : Φ (((y u : ggOmW5a_fix b)) : ι → K) = Φ (((u : ggOmW5a_fix b)) : ι → K) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO u
    rw [show glue hc y 1 ((u : ι → K) + ((r : ggOmW5a_com b) : ι → K)) =
        (((y u : ggOmW5a_fix b)) : ι → K) + ((r : ggOmW5a_com b) : ι → K) from by
      have h := glue_apply hc y 1 u r
      simpa only [LinearEquiv.coe_one, id_eq] using h]
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq Φ,
      CFSG.RankThree.OrthogonalInvolutions.map_add_eq Φ, ← QuadraticMap.polarBilin_apply_apply,
      ← QuadraticMap.polarBilin_apply_apply,
      ggOmW5a_polar_fix_com_zero Φ b hbO (y u) (y u).2 r r.2,
      ggOmW5a_polar_fix_com_zero Φ b hbO u u.2 r r.2, add_zero, add_zero, hyu]
  have hGω : glue hc y 1 ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ := by
    refine CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hGO, ?_⟩
    have hyeven : Even (Module.finrank K
        (CFSG.RankThree.OrthogonalInvolutions.commSpace y)) :=
      (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hy).2
    have hmap : CFSG.RankThree.OrthogonalInvolutions.commSpace (glue hc y 1) =
        (CFSG.RankThree.OrthogonalInvolutions.commSpace y).map
          (ggOmW5a_fix b).subtype := by
      ext z
      constructor
      · intro hz
        rw [Submodule.mem_map]
        obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hz
        obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
        refine ⟨y u - u,
          CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace y u, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub]
        have h := glue_apply hc y 1 u r
        rw [show glue hc y 1 ((u : ι → K) + ((r : ggOmW5a_com b) : ι → K)) =
            (((y u : ggOmW5a_fix b)) : ι → K) + ((r : ggOmW5a_com b) : ι → K) from by
          simpa only [LinearEquiv.coe_one, id_eq] using h]
        abel
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨u, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hz
        refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr
          ⟨(u : ι → K), ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub]
        have h := glue_apply hc y 1 u (0 : ggOmW5a_com b)
        simp only [LinearEquiv.coe_one, id_eq, map_zero, add_zero, Submodule.coe_zero] at h
        rw [h]
    rw [hmap, Submodule.finrank_map_subtype_eq]
    exact hyeven
  have hGx : glue hc y 1 * ggOmW5a_toLinEquiv b =
      ggOmW5a_toLinEquiv b * glue hc y 1 := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hc v
    have hxu := hxfix u u.2
    have hxyu := hxfix (y u) (y u).2
    have hxr := hxR r r.2
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, hxu]
    rw [show glue hc y 1 ((u : ι → K) + ggOmW5a_toLinEquiv b ((r : ggOmW5a_com b) : ι → K)) =
        (((y u : ggOmW5a_fix b)) : ι → K) +
          ggOmW5a_toLinEquiv b ((r : ggOmW5a_com b) : ι → K) from by
      have h := glue_apply hc y 1 u
        ⟨ggOmW5a_toLinEquiv b ((r : ggOmW5a_com b) : ι → K), hxr⟩
      simpa only [LinearEquiv.coe_one, id_eq] using h]
    rw [show glue hc y 1 ((u : ι → K) + ((r : ggOmW5a_com b) : ι → K)) =
        (((y u : ggOmW5a_fix b)) : ι → K) + ((r : ggOmW5a_com b) : ι → K) from by
      have h := glue_apply hc y 1 u r
      simpa only [LinearEquiv.coe_one, id_eq] using h]
    rw [map_add, hxyu]
  let Gmat : GL ι K := ggOmW5aE_ML.symm (glue hc y 1)
  have hGmat : ggOmW5aE_ML Gmat = glue hc y 1 := MulEquiv.apply_symm_apply _ _
  have hGmatc : Gmat * b = b * Gmat := by
    apply ggOmW5aE_ML.injective
    rw [map_mul, map_mul, hGmat, ← ggOmW5aE_toLin_eq_ML]
    exact hGx
  have hGmatΩ : Gmat ∈ StatedOmega ⇑Φ :=
    (ggOmW5a_statedOmega_iff_omegaGroup Φ hΦ h8 Gmat).mpr (by
      rw [ggOmW5aE_toLin_eq_ML, hGmat]; exact hGω)
  have hsc := hsC Gmat (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hGmatc, hGmatΩ⟩)
  have hSG : ggOmW5a_toLinEquiv s * glue hc y 1 =
      glue hc y 1 * ggOmW5a_toLinEquiv s := by
    have h := congrArg ggOmW5aE_ML hsc
    simpa only [map_mul, hGmat, ← ggOmW5aE_toLin_eq_ML] using h
  have hmain : restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 *
      restrictEquiv (ggOmW5a_fix b) (glue hc y 1) hGW hGW' =
      restrictEquiv (ggOmW5a_fix b) (glue hc y 1) hGW hGW' *
      restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simp only [LinearEquiv.mul_apply, coe_restrictEquiv]
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hSG]
  rw [hGrestr] at hmain
  exact hmain

private theorem ggOmW5a_plane_structure {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    Fintype.card K = 2 ∧ Module.finrank K (ggOmW5a_fix b) = 2 := by
  have hQ₁ := ggOmW5aE_polarBilin_fix_nondegenerate Φ hΦ h8 b hb hodd
  have h1 := ggOmW5aE_s_maps_fix b s hsb
  have h2 : ∀ u : ι → K, u ∈ ggOmW5a_fix b →
      (ggOmW5a_toLinEquiv s).symm u ∈ ggOmW5a_fix b := by
    intro u hu
    rw [ggOmW5aE_symm_eq_self s hs2]
    exact h1 u hu
  let S₁ := restrictEquiv (ggOmW5a_fix b) (ggOmW5a_toLinEquiv s) h1 h2
  have hsO : ggOmW5a_toLinEquiv s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ :=
    (ggOmW5a_matrixOrthogonal_iff_orthogonalGroup Φ s).mp hs
  have hS₁O : S₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (Φ.comp (ggOmW5a_fix b).subtype) :=
    ggOmW5aE_restrict_mem_orthogonal Φ b s hsO h1 h2
  have hS₁Ω : S₁ ∉ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Φ.comp (ggOmW5a_fix b).subtype) hQ₁ :=
    ggOmW5aE_restrict_not_mem_omega Φ hΦ h8 b s hb hodd hs hsΩ hs2 hsb hsC h1 h2
  have hS₁c : ∀ y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Φ.comp (ggOmW5a_fix b).subtype) hQ₁, S₁ * y = y * S₁ :=
    ggOmW5aE_restrict_centralizes Φ hΦ h8 b s hb hodd hsC h1 h2
  have hEven : Even (Module.finrank K (ggOmW5a_fix b)) :=
    ggOmW5aE_even_finrank Φ hΦ h8 b hb hodd
  have hlt4 : Module.finrank K (ggOmW5a_fix b) < 4 := by
    by_contra hle
    push Not at hle
    have hz : S₁ = 1 :=
      ggOmW5a_eq_one_of_commute_orthDerived (Φ.comp (ggOmW5a_fix b).subtype) hQ₁ hle hS₁O
        (fun y hy => hS₁c y (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ₁ hy))
    exact hS₁Ω (hz ▸ Subgroup.one_mem _)
  have hpos : 0 < Module.finrank K (ggOmW5a_fix b) := by
    by_contra h
    have h0 : Module.finrank K (ggOmW5a_fix b) = 0 := by omega
    haveI : Subsingleton (ggOmW5a_fix b) := Module.finrank_zero_iff.mp h0
    have hz : S₁ = 1 := Subsingleton.elim _ _
    exact hS₁Ω (hz ▸ Subgroup.one_mem _)
  have hfin : Module.finrank K (ggOmW5a_fix b) = 2 := by
    obtain ⟨k, hk⟩ := hEven
    omega
  exact ⟨ggOmW5a_plane_card_eq_two (Φ.comp (ggOmW5a_fix b).subtype) hQ₁ hfin hS₁O hS₁Ω hS₁c,
    hfin⟩

private theorem ggOmW5a_card_eq_two {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    Fintype.card K = 2 :=
  (ggOmW5a_plane_structure Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC).1

private theorem ggOmW5a_finrank_fix_eq_two {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id)) = 2 :=
  (ggOmW5a_plane_structure Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC).2

private lemma ggOmW5aF_toLinEquiv_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (u : ι → K) :
    ggOmW5a_toLinEquiv s u = (s : Matrix ι ι K) *ᵥ u := by
  change (Matrix.GeneralLinearGroup.toLin s).toLinearEquiv u = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]

private lemma ggOmW5aF_eq_one_of_ne_zero {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {x : K} (hx : x ≠ 0) : x = 1 := by
  have h2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card]; exact hK
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp h2
  exact (huniq x hx).trans (huniq 1 one_ne_zero).symm

private lemma ggOmW5aF_quad_expand {ι K : Type} [Field K]
    (Φ : QuadraticForm K (ι → K)) (u v : ι → K) (c : K) :
    Φ (u + c • v) = Φ u + (c * c) * Φ v + c * QuadraticMap.polar Φ u v := by
  simp only [QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
    smul_eq_mul]

private lemma ggOmW5aF_polar_expand {ι K : Type} [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K)) (u w v : ι → K) (cu cw : K) :
    QuadraticMap.polar Φ (u + cu • v) (w + cw • v) =
      QuadraticMap.polar Φ u w + cw * QuadraticMap.polar Φ u v +
        cu * QuadraticMap.polar Φ v w := by
  rw [QuadraticMap.polar_add_left]
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right]
  rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Φ v]
  simp only [smul_eq_mul, mul_zero, add_zero]

private theorem ggOmW5a_exists_transvection_polar {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) (s : GL ι K)
    (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ) (hsΩ : s ∉ StatedOmega ⇑Φ)
    (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    ∃ v : ι → K, v ∈ ggOmW5a_fix b ∧ Φ v = 1 ∧
      ∀ u : ι → K, (s : Matrix ι ι K) *ᵥ u = u + QuadraticMap.polar Φ u v • v := by
  obtain ⟨hK, hV1⟩ := ggOmW5a_plane_structure Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC
  have hsV' : ∀ w ∈ ggOmW5a_com b, (s : Matrix ι ι K) *ᵥ w = w :=
    ggOmW5a_s_eq_one_on_com Φ hΦ h8 b hb hodd s hs hs2 hsb hsC
  have hsV1 : ∀ u ∈ ggOmW5a_fix b, (s : Matrix ι ι K) *ᵥ u ∈ ggOmW5a_fix b :=
    ggOmW5a_s_maps_fix b s hsb
  have hle : CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s) ≤
      ggOmW5a_fix b := ggOmW5a_commSpace_le_fix b s hodd hsV1 hsV'
  have hnotEven : ¬ Even (Module.finrank K
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s))) :=
    ggOmW5a_fix_s_not_mem_omega Φ hΦ h8 s hs hsΩ
  have hSO : ggOmW5a_toLinEquiv s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ :=
    (ggOmW5a_matrixOrthogonal_iff_orthogonalGroup Φ s).mp hs
  have hSne : ggOmW5a_toLinEquiv s ≠ 1 := by
    intro h1
    apply hsΩ
    rw [ggOmW5a_statedOmega_iff_omegaGroup Φ hΦ h8 s, h1]
    exact (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ).one_mem
  have hrank : Module.finrank K
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s)) = 1 := by
    have hle2 : Module.finrank K
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s)) ≤ 2 := by
      have h := Submodule.finrank_mono hle
      rw [hV1] at h
      exact h
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hnotEven
    omega
  obtain ⟨v, hvne, hvspan⟩ := (finrank_eq_one_iff' (K := K)
    (V := ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace (ggOmW5a_toLinEquiv s)))).mp hrank
  choose c hc using fun u : ι → K =>
    hvspan ⟨ggOmW5a_toLinEquiv s u - u,
      CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace (ggOmW5a_toLinEquiv s) u⟩
  have hc' : ∀ u : ι → K, c u • (v : ι → K) = ggOmW5a_toLinEquiv s u - u :=
    fun u => by simpa using congrArg Subtype.val (hc u)
  have hSu : ∀ u : ι → K, ggOmW5a_toLinEquiv s u = u + c u • (v : ι → K) := fun u => by
    have h := eq_add_of_sub_eq (hc' u).symm
    rw [h, add_comm]
  have hcne : ∃ u₀ : ι → K, c u₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hSne
    ext u
    simp [hSu u, h u]
  obtain ⟨u₀, hu₀⟩ := hcne
  have hQlin : ∀ u : ι → K,
      (c u * c u) * Φ (v : ι → K) + c u * QuadraticMap.polar Φ u (v : ι → K) = 0 := by
    intro u
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hSO u
    rw [hSu u, ggOmW5aF_quad_expand] at h
    linear_combination h
  have hBlin : ∀ u w : ι → K, c w * QuadraticMap.polar Φ u (v : ι → K) +
      c u * QuadraticMap.polar Φ (v : ι → K) w = 0 := by
    intro u w
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hSO u w
    rw [hSu u, hSu w, ggOmW5aF_polar_expand] at h
    linear_combination h
  have hQ0 : c u₀ * Φ (v : ι → K) + QuadraticMap.polar Φ u₀ (v : ι → K) = 0 := by
    have hfac : c u₀ * (c u₀ * Φ (v : ι → K) +
        QuadraticMap.polar Φ u₀ (v : ι → K)) = 0 := by
      rw [← hQlin u₀]; ring
    exact (mul_eq_zero.mp hfac).resolve_left hu₀
  have hB0 : QuadraticMap.polar Φ u₀ (v : ι → K) ≠ 0 := by
    intro h0
    have hΦv0 : Φ (v : ι → K) = 0 := by
      have h := hQ0
      rw [h0, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hu₀
    have hBv : ∀ w : ι → K, QuadraticMap.polar Φ (v : ι → K) w = 0 := by
      intro w
      have h := hBlin u₀ w
      rw [h0, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hu₀
    have hvzero : (v : ι → K) = 0 :=
      hΦ.1 (v : ι → K) fun w => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hBv w
    exact hvne (Subtype.ext hvzero)
  have hQ0e : c u₀ * Φ (v : ι → K) = QuadraticMap.polar Φ u₀ (v : ι → K) := by
    have h := eq_neg_of_add_eq_zero_left hQ0
    rw [CharTwo.neg_eq] at h
    exact h
  have hkey : ∀ w : ι → K, c w * Φ (v : ι → K) = QuadraticMap.polar Φ (v : ι → K) w := by
    intro w
    have h1 : c w * QuadraticMap.polar Φ u₀ (v : ι → K) =
        c u₀ * QuadraticMap.polar Φ (v : ι → K) w := by
      have h := eq_neg_of_add_eq_zero_left (hBlin u₀ w)
      rw [CharTwo.neg_eq] at h
      exact h
    have hmul : (c w * Φ (v : ι → K)) * QuadraticMap.polar Φ u₀ (v : ι → K) =
        QuadraticMap.polar Φ (v : ι → K) w * QuadraticMap.polar Φ u₀ (v : ι → K) := by
      calc (c w * Φ (v : ι → K)) * QuadraticMap.polar Φ u₀ (v : ι → K)
          = c w * QuadraticMap.polar Φ u₀ (v : ι → K) * Φ (v : ι → K) := by ring
        _ = (c u₀ * QuadraticMap.polar Φ (v : ι → K) w) * Φ (v : ι → K) := by rw [h1]
        _ = (c u₀ * Φ (v : ι → K)) * QuadraticMap.polar Φ (v : ι → K) w := by ring
        _ = QuadraticMap.polar Φ u₀ (v : ι → K) *
              QuadraticMap.polar Φ (v : ι → K) w := by rw [hQ0e]
        _ = QuadraticMap.polar Φ (v : ι → K) w *
              QuadraticMap.polar Φ u₀ (v : ι → K) := by ring
    exact mul_right_cancel₀ hB0 hmul
  have hΦv_ne : Φ (v : ι → K) ≠ 0 := by
    intro h0
    have h := hQ0e
    rw [h0, mul_zero] at h
    exact hB0 h.symm
  have hΦv1 : Φ (v : ι → K) = 1 := ggOmW5aF_eq_one_of_ne_zero hK hΦv_ne
  have hc_eq : ∀ w : ι → K, c w = QuadraticMap.polar Φ w (v : ι → K) := by
    intro w
    have h := hkey w
    rw [hΦv1, mul_one] at h
    rw [h]
    exact QuadraticMap.polar_comm Φ (v : ι → K) w
  refine ⟨(v : ι → K), hle v.2, hΦv1, ?_⟩
  intro u
  simp only [← ggOmW5aF_toLinEquiv_apply s u, hSu u, hc_eq u]

private theorem ggOmW5a_transvection_formula {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (s : GL ι K) (v : ι → K)
    (hs : ∀ u : ι → K, (s : Matrix ι ι K) *ᵥ u = u + QuadraticMap.polar Φ u v • v) :
    ∀ u : ι → K, (s : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v := by
  intro u
  rw [ggOmW5a_polar_apply Φ u v]
  exact hs u

theorem eq_transvection_of_centralizes {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (s : GL ι K) (hs : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    (hsΩ : s ∉ StatedOmega ⇑Φ) (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, s * g = g * s) :
    Fintype.card K = 2 ∧
      Module.finrank K (LinearMap.ker (Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id)) = 2 ∧
      ∃ v ∈ LinearMap.ker (Matrix.toLin' (b : Matrix ι ι K) - LinearMap.id), Φ v = 1 ∧
        ∀ u : ι → K, (s : Matrix ι ι K) *ᵥ u = u + (Φ (u + v) - Φ u - Φ v) • v := by
  refine ⟨ggOmW5a_card_eq_two Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC,
    ggOmW5a_finrank_fix_eq_two Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC, ?_⟩
  obtain ⟨v, hv, hΦv, htrans⟩ :=
    ggOmW5a_exists_transvection_polar Φ hΦ h8 b hb hodd s hs hsΩ hs2 hsb hsC
  exact ⟨v, hv, hΦv, ggOmW5a_transvection_formula Φ s v htrans⟩

end CFSG.StandardType.ClassicalBlocks

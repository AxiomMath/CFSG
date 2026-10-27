module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.ClassicalGroups.Unitary.PerpQuotient
public import CFSG.LieType.SeitzGeneration.UnitaryCenters
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open CFSG.ClassicalGroups.Unitary

variable {L : Type} [Field L]

private theorem u7wt_exists_iso_orth {K : Type*} [Field K] [CharP K 2] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 4 ≤ n) {a : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) :
    ∃ b : Fin n → K, b ≠ 0 ∧ herm σ b b = 0 ∧ herm σ a b = 0 ∧
      b ∉ Submodule.span K {a} := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨φ, hφ⟩ := exists_eQuotEquiv_isometry (σ := σ) hσ (by omega : 3 ≤ n) ha0 ha
  have hn2 : 2 ≤ n - 2 := by omega
  obtain ⟨c, hc0, hc⟩ := CFSG.LieType.SeitzGeneration.Centers.exists_isotropic_ne_zero
    (σ := σ) hσ hn2
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (p := spanVecPerp σ a) (φ.symm c)
  have hφx : φ (Submodule.Quotient.mk (p := spanVecPerp σ a) x) = c := by
    rw [hx, LinearEquiv.apply_symm_apply]
  refine ⟨x.1, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hxzero : x = 0 := Subtype.ext h0
    have hc00 : c = 0 := by
      have h := hφx
      rw [hxzero] at h
      simpa using h.symm
    exact hc0 hc00
  · rw [← hφ x x, hφx, hc]
  · simpa using (mem_perp (σ := σ) (e := a) (v := x.1)).mp x.2
  · intro hmem
    have hxperp : x ∈ spanVecPerp σ a := by
      show (x : Fin n → K) ∈ spanVec a
      exact hmem
    have hmk0 : Submodule.Quotient.mk (p := spanVecPerp σ a) x = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := spanVecPerp σ a)).mpr hxperp
    have hc00 : c = 0 := by
      have h := hφx
      rw [hmk0] at h
      simpa using h.symm
    exact hc0 hc00

theorem exists_isotropic_third [IsAlgClosed L] [CharP L 2] (σ : L ≃+* L) {f : ℕ} (hf : 1 ≤ f)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {v u : Fin 6 → L} (hv : ∀ i, σ (σ (v i)) = v i)
    (hu : ∀ i, σ (σ (u i)) = u i) (hind : LinearIndependent L ![v, u])
    (hvv : ∑ i, σ (v i) * v i = 0) (huu : ∑ i, σ (u i) * u i = 0)
    (hvu : ∑ i, σ (v i) * u i = 0) :
    ∃ w : Fin 6 → L, (∀ i, σ (σ (w i)) = w i) ∧ LinearIndependent L ![v, u, w] ∧
      ∑ i, σ (w i) * w i = 0 ∧ ∑ i, σ (v i) * w i = 0 ∧ ∑ i, σ (u i) * w i = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : Subfield L := (σ.toRingHom.comp σ.toRingHom).eqLocusField (RingHom.id L) with hFdef
  have hFmem : ∀ c : L, c ∈ F ↔ σ (σ c) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField]
    exact Iff.rfl
  have hσσ : ∀ c : L, σ (σ c) = c ^ 2 ^ (2 * f) := fun c => by
    calc σ (σ c) = (σ c) ^ 2 ^ f := hσ (σ c)
      _ = (c ^ 2 ^ f) ^ 2 ^ f := by rw [hσ c]
      _ = c ^ (2 ^ f * 2 ^ f) := by rw [← pow_mul]
      _ = c ^ 2 ^ (f + f) := by rw [← pow_add]
      _ = c ^ 2 ^ (2 * f) := by rw [← two_mul]
  have hFpow : ∀ c : L, c ∈ F ↔ c ^ 2 ^ (2 * f) = c := fun c => by rw [hFmem c, hσσ c]
  have hFcard : Nat.card F = (2 ^ f) ^ 2 := by
    have hpow : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
    rw [hpow, ← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := L) (ℓ := 2)
      (e := 2 * f) (by omega)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hFpow)
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact pow_ne_zero 2 (pow_ne_zero f (by norm_num)))
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := f) hFcard
  set σF : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f with hσFdef
  have hσF : IsUnitaryInvolution σF := by
    rw [hσFdef]
    exact isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hFcard
  have hσF_apply : ∀ c : F, ((σF c : F) : L) = σ (c : L) := by
    intro c
    have h1 : ((σF c : F) : L) = (c : L) ^ 2 ^ f := by
      rw [hσFdef, CFSG.LieType.BorelTits.unitaryInvolution_apply]
      exact map_pow (Subfield.subtype F) c (2 ^ f)
    rw [h1, hσ]
  let vF : Fin 6 → F := fun i => ⟨v i, (hFmem (v i)).mpr (hv i)⟩
  let uF : Fin 6 → F := fun i => ⟨u i, (hFmem (u i)).mpr (hu i)⟩
  have hvF_coe : ∀ i, ((vF i : F) : L) = v i := fun i => rfl
  have huF_coe : ∀ i, ((uF i : F) : L) = u i := fun i => rfl
  have hcoe_herm : ∀ x y : Fin 6 → F,
      ((herm σF x y : F) : L) = ∑ i, σ ((x i : F) : L) * ((y i : F) : L) := by
    intro x y
    rw [herm_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσF_apply]
  have hvF_iso : herm σF vF vF = 0 := by
    apply Subtype.ext
    rw [hcoe_herm]
    exact hvv
  have huF_iso : herm σF uF uF = 0 := by
    apply Subtype.ext
    rw [hcoe_herm]
    exact huu
  have hvuF : herm σF vF uF = 0 := by
    apply Subtype.ext
    rw [hcoe_herm]
    exact hvu
  have hvFuF_ind : LinearIndependent F ![vF, uF] := by
    have h := linearIndependent_algebraMap_comp_iff (R := F) (S := L) (v := ![vF, uF])
    have hfam : (fun i => algebraMap F L ∘ ![vF, uF] i) = ![v, u] := by
      funext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hfam] at h
    exact h.mp hind
  have hvF0 : vF ≠ 0 := hvFuF_ind.ne_zero 0
  have huF_notmem : uF ∉ Submodule.span F {vF} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hrel : c • vF + (-1 : F) • uF = 0 := by rw [hc]; simp
    have hne : (-1 : F) ≠ 0 := by norm_num
    exact hne (LinearIndependent.pair_iff.mp hvFuF_ind c (-1) hrel).2
  obtain ⟨φ, hφ⟩ := exists_eQuotEquiv_isometry (σ := σF) hσF (by norm_num : 3 ≤ 6) hvF0 hvF_iso
  let u4 : perp σF vF := ⟨uF, (mem_perp (σ := σF) (e := vF) (v := uF)).mpr hvuF⟩
  have hu4val : u4.1 = uF := rfl
  let a4 : Fin 4 → F := φ (Submodule.Quotient.mk (p := spanVecPerp σF vF) u4)
  have ha4val : a4 = φ (Submodule.Quotient.mk (p := spanVecPerp σF vF) u4) := rfl
  have ha40 : a4 ≠ 0 := by
    intro h0
    have hφ0 : φ (Submodule.Quotient.mk (p := spanVecPerp σF vF) u4) = 0 := by
      rw [← ha4val, h0]
    have hmk0 : Submodule.Quotient.mk (p := spanVecPerp σF vF) u4 = 0 := by
      have h := congrArg φ.symm hφ0
      simpa using h
    have hu4mem : u4 ∈ spanVecPerp σF vF :=
      (Submodule.Quotient.mk_eq_zero (p := spanVecPerp σF vF)).mp hmk0
    exact huF_notmem (by
      rw [spanVecPerp, Submodule.mem_comap] at hu4mem
      change uF ∈ spanVec vF at hu4mem
      simpa [spanVec] using hu4mem)
  have ha4iso : herm σF a4 a4 = 0 := by
    rw [ha4val, hφ u4 u4, hu4val]
    exact huF_iso
  obtain ⟨b4, hb40, hb4iso, ha4b4, hb4notmem⟩ :=
    u7wt_exists_iso_orth (σ := σF) hσF (n := 4) (by norm_num) ha40 ha4iso
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (p := spanVecPerp σF vF) (φ.symm b4)
  have hφx : φ (Submodule.Quotient.mk (p := spanVecPerp σF vF) x) = b4 := by
    rw [hx, LinearEquiv.apply_symm_apply]
  let wF : Fin 6 → F := x.1
  have hwFval : wF = x.1 := rfl
  have hvFwF : herm σF vF wF = 0 := by
    rw [hwFval]
    exact (mem_perp (σ := σF) (e := vF) (v := x.1)).mp x.2
  have hwFiso : herm σF wF wF = 0 := by
    rw [hwFval, ← hφ x x, hφx, hb4iso]
  have huFwF : herm σF uF wF = 0 := by
    rw [hwFval, ← hu4val, ← hφ u4 x, ← ha4val, hφx]
    exact ha4b4
  have hwF_notmem : wF ∉ Submodule.span F {vF, uF} := by
    intro hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hsub : x - β • u4 ∈ spanVecPerp σF vF := by
      show (x - β • u4 : perp σF vF) ∈ spanVecPerp σF vF
      rw [spanVecPerp, Submodule.mem_comap]
      change wF - β • uF ∈ Submodule.span F {vF}
      have hw : wF - β • uF = α • vF := by rw [← hαβ]; abel
      rw [hw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self vF)
    have hcls : Submodule.Quotient.mk (p := spanVecPerp σF vF) x =
        β • Submodule.Quotient.mk (p := spanVecPerp σF vF) u4 := by
      have h0 : Submodule.Quotient.mk (p := spanVecPerp σF vF) (x - β • u4) = 0 :=
        (Submodule.Quotient.mk_eq_zero (p := spanVecPerp σF vF)).mpr hsub
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] at h0
      exact h0
    have hb4a4 : b4 = β • a4 := by
      rw [← hφx, hcls, map_smul, ha4val]
    exact hb4notmem (Submodule.mem_span_singleton.mpr ⟨β, hb4a4.symm⟩)
  have hLI3 : LinearIndependent F ![vF, uF, wF] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • vF + g 1 • uF + g 2 • wF = 0 := by
      have h := hg
      rw [Fin.sum_univ_three] at h
      simpa using h
    by_cases hg2 : g 2 = 0
    · have h2 : g 0 • vF + g 1 • uF = 0 := by
        rw [hg2, zero_smul, add_zero] at hg'
        exact hg'
      have h01 := LinearIndependent.pair_iff.mp hvFuF_ind (g 0) (g 1) h2
      intro i
      fin_cases i <;> simp [hg2, h01.1, h01.2]
    · refine (hwF_notmem (Submodule.mem_span_pair.mpr
        ⟨(g 2)⁻¹ * g 0, (g 2)⁻¹ * g 1, ?_⟩)).elim
      have h : g 2 • wF = g 0 • vF + g 1 • uF := by
        have hneg : g 2 • wF = -(g 0 • vF + g 1 • uF) := by
          have h' : g 2 • wF + (g 0 • vF + g 1 • uF) = 0 := by
            rw [← hg']; abel
          exact eq_neg_of_add_eq_zero_left h'
        rwa [CharTwo.neg_eq] at hneg
      calc ((g 2)⁻¹ * g 0) • vF + ((g 2)⁻¹ * g 1) • uF
          = (g 2)⁻¹ • (g 0 • vF + g 1 • uF) := by module
        _ = (g 2)⁻¹ • (g 2 • wF) := by rw [h]
        _ = wF := by rw [smul_smul, inv_mul_cancel₀ hg2, one_smul]
  let wL : Fin 6 → L := fun i => (wF i : L)
  have hfam3 : (fun i => algebraMap F L ∘ ![vF, uF, wF] i) = ![v, u, wL] := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hLI3L : LinearIndependent L ![v, u, wL] := by
    have hiff := linearIndependent_algebraMap_comp_iff (R := F) (S := L) (v := ![vF, uF, wF])
    have h := hiff.mpr hLI3
    rwa [hfam3] at h
  have hwLwL : ∑ i, σ (wL i) * wL i = 0 := by
    have h := hcoe_herm wF wF
    rw [hwFiso] at h
    simpa [wL] using h.symm
  have hvFwL : ∑ i, σ (v i) * wL i = 0 := by
    have h := hcoe_herm vF wF
    rw [hvFwF] at h
    simpa [hvF_coe, wL] using h.symm
  have huFwL : ∑ i, σ (u i) * wL i = 0 := by
    have h := hcoe_herm uF wF
    rw [huFwF] at h
    simpa [huF_coe, wL] using h.symm
  refine ⟨wL, fun i => (hFmem (wL i)).mp (wF i).2, hLI3L, hwLwL, hvFwL, huFwL⟩

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

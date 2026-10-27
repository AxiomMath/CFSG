module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairFix
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSUCover
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSUTop
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSUWitt
import CFSG.LocalAnalysis.StandardType.GGK0LQSuN
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Open.StatedSUFieldChange
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreSU
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftSplit
import CFSG.RankThree.Classical2.SLnConjLemmas
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.StandardType.RCKRP

private lemma rck_pair_conj {G : Type*} [Group G] (step : G →* G) {u : G} (hu : step u = u)
    (U : Subgroup G) (y : G)
    (hU : (U.map (MulAut.conj y).toMonoidHom).map step =
      U.map (MulAut.conj y).toMonoidHom) :
    (U.map (MulAut.conj (u * y)).toMonoidHom).map step =
        U.map (MulAut.conj (u * y)).toMonoidHom ∧
      (U.map (MulAut.conj y).toMonoidHom ⊓ step.eqLocus (MonoidHom.id _)).map
          (MulAut.conj u).toMonoidHom =
        U.map (MulAut.conj (u * y)).toMonoidHom ⊓ step.eqLocus (MonoidHom.id _) := by
  have hconj_map : ∀ X : Subgroup G,
      (X.map (MulAut.conj u).toMonoidHom).map step =
        (X.map step).map (MulAut.conj u).toMonoidHom := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, hu]
  have hUuy : U.map (MulAut.conj (u * y)).toMonoidHom =
      (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hFix : (step.eqLocus (MonoidHom.id G)).map (MulAut.conj u).toMonoidHom =
      step.eqLocus (MonoidHom.id G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      change step x = x at hx
      change step (u * x * u⁻¹) = u * x * u⁻¹
      rw [map_mul, map_mul, map_inv, hu, hx]
    · intro hg
      change step g = g at hg
      refine ⟨u⁻¹ * g * u, ?_, ?_⟩
      · change step (u⁻¹ * g * u) = u⁻¹ * g * u
        rw [map_mul, map_mul, map_inv, hu, hg]
      · change u * (u⁻¹ * g * u) * u⁻¹ = g
        group
  refine ⟨?_, ?_⟩
  · calc
      (U.map (MulAut.conj (u * y)).toMonoidHom).map step
          = ((U.map (MulAut.conj y).toMonoidHom).map
              (MulAut.conj u).toMonoidHom).map step := by rw [hUuy]
      _ = ((U.map (MulAut.conj y).toMonoidHom).map step).map
            (MulAut.conj u).toMonoidHom := hconj_map _
      _ = (U.map (MulAut.conj y).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by rw [hU]
      _ = U.map (MulAut.conj (u * y)).toMonoidHom := hUuy.symm
  · calc
      (U.map (MulAut.conj y).toMonoidHom ⊓ step.eqLocus (MonoidHom.id G)).map
          (MulAut.conj u).toMonoidHom
          = (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj u).toMonoidHom ⊓
              (step.eqLocus (MonoidHom.id G)).map (MulAut.conj u).toMonoidHom := by
            rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective]
      _ = (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj u).toMonoidHom ⊓
            step.eqLocus (MonoidHom.id G) := by rw [hFix]
      _ = U.map (MulAut.conj (u * y)).toMonoidHom ⊓
            step.eqLocus (MonoidHom.id G) := by rw [hUuy]

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix in
theorem rckPairSU_holds :
    RCKPairSU := by
  classical
  intro τ p₀ S a hT p hp hp2 hTp i h hq hkind hQS
  obtain ⟨hs0, -, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.outer_componentOrbitLength_spec S hT i
  set r := compRank (componentRoots (rootCharHom a) i) with hr
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  set g := h * s with hg
  have hh1 : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · exfalso
      have hq1 : S.D.q = 1 := by rw [hq, h0, pow_zero]
      have hp' := S.hqpow.1
      rw [hq1] at hp'
      exact not_isPrimePow_one hp'
    · exact hpos
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.mul_pos hh1 hs0
  have hg1 : 1 ≤ g := hgpos
  have hpL : (p : GGL) ≠ 0 := by
    intro h0
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).mp h0
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact hp2 h2
    · exact (Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr hodd)) (even_iff_two_dvd.mpr hd)
  have hrn : 2 ≤ r ∧ (componentRoots (rootCharHom a) i).ncard = r * (r + 1) := by
    have h' := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hkind
    simpa only [hr] using h'
  obtain ⟨ν, ψ, σf, κ, hν3, hψ, hκ, hnorm, hΨ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_frame_of_typeA_tag_T_of_prime
      CFSG.HardMathSupport.Timmesfeld.CrossChar.g2LongA2Frame_proved S hp hpL hTp i
      hrn.1 hrn.2
  have hcard : (CFSG.HardMathSupport.Timmesfeld.CrossChar.frameRoots σf).ncard =
      ν * (ν - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm
  have hEq : ν * (ν - 1) = r * (r + 1) := by
    rw [← hcard, ← hΨ, hrn.2]
  have hνr : ν = r + 1 := by
    obtain ⟨m, hm⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel] at hEq
    have hmr : m = r := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
    omega
  have hψC : ψ.range ≤ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
    rw [hψ.range]
    refine (rootSpan_mono ?_).trans le_sup_right
    intro δ hδ
    rw [← hΨ] at hδ
    exact hδ.1
  have h32' : (ν, 2 ^ g) ≠ (3, 2) := by
    intro hcon
    have h1 : ν = 3 := congrArg Prod.fst hcon
    have h2 : 2 ^ g = 2 := congrArg Prod.snd hcon
    have hr2 : r = 2 := by omega
    have hqs : S.D.q ^ s = 2 := by
      rw [hq, ← pow_mul, ← hg]
      exact h2
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hQS
      (CFSG.StandardType.GGK0LQ.lq_suN_solvable S hp hpL hT hTp i hkind ⟨hr2, hqs⟩)
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_perm S hT i hkind hν3 hψ hκ hnorm hΨ
  obtain ⟨σQ, hσQ, z, f, hzZ, hconjF, hf1, hfr, hfk, -⟩ :=
    exists_unitary_frame_cover (L := GGL) S hT i hν3 hψ hΨ π hπ Nat.prime_two
      (inferInstance : CharP GGL 2) hh1 hq (by simpa [hg] using h32')
  set GF : Type := GaloisField 2 (2 * g) with hGFdef
  have hGF : Nat.card GF = (2 ^ g) ^ 2 := by
    rw [hGFdef]
    exact CFSG.LieType.Universal.card_galoisField_two_mul 2 g hg1
  set M₀ : LieUniversal :=
    ⟨CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g) ν,
      CFSG.LieType.Universal.Unitary.rootDatum hGF ν⟩ with hM₀
  have hK : ggU .PSU ν g = M₀ := by
    rw [hM₀]
    simp only [ggU, CFSG.LieType.Universal.lieUniversal, hg1, ↓reduceDIte]
    rfl
  obtain ⟨F, hFcard, eC, heC⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.two_suN_exists_equiv_link
      (L := GGL) (ℓ := 2) (f := g) Nat.prime_two hg1 σQ hσQ hν3
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin ν) GGL) :=
    CFSG.RankThree.Classical2.fixSubgroup
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.stdUnitaryEquiv (ν := ν) σQ)
  have hfinC : Finite C :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.stdUnitary_fixSubgroup
      (L := GGL) Nat.prime_two hg1 σQ hσQ hν3).1
  have hfinF : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
  have hcard_eq : Nat.card GF = Nat.card F := by rw [hGF, hFcard]
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype GF := Fintype.ofFinite GF
  have hcardF : Fintype.card GF = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard_eq
  set e₁ : GF ≃+* F := FiniteField.ringEquivOfCardEq hcardF
  have hFchar : ∀ c : GGL, c ∈ F ↔ σQ (σQ c) = c := by
    have hFsub : (F : Set GGL) ⊆ {c : GGL | σQ (σQ c) = c} := by
      intro c hc
      have hpow : c ^ Nat.card F = c := by
        have h := FiniteField.pow_card (K := F) (⟨c, hc⟩ : F)
        have h2 : (⟨c, hc⟩ : F) ^ Nat.card F = ⟨c, hc⟩ := by
          rw [Nat.card_eq_fintype_card]
          exact h
        have h3 := congrArg (fun x : F => F.subtype x) h2
        simpa only [map_pow, Subfield.coe_subtype] using h3
      rw [hFcard] at hpow
      change σQ (σQ c) = c
      rw [hσQ, hσQ, ← pow_mul]
      convert hpow using 2
      ring
    have hsetB : ({c : GGL | σQ (σQ c) = c} : Set GGL) =
        {c : GGL | c ^ 2 ^ (2 * g) = c} := by
      ext c
      simp only [Set.mem_setOf_eq]
      have hexp : 2 ^ g * 2 ^ g = 2 ^ (2 * g) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hσQ, hσQ, ← pow_mul, hexp]
    have hBcard : Nat.card {c : GGL | σQ (σQ c) = c} = (2 ^ g) ^ 2 := by
      rw [hsetB, CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := GGL) (ℓ := 2)
        (e := 2 * g) (by omega)]
      rw [← pow_mul]
      congr 1
      omega
    have hscard_F : (F : Set GGL).ncard = (2 ^ g) ^ 2 := by
      change Nat.card F = (2 ^ g) ^ 2
      exact hFcard
    have htcard : ({c : GGL | σQ (σQ c) = c} : Set GGL).ncard = (2 ^ g) ^ 2 := by
      rw [← Nat.card_coe_set_eq, hBcard]
    have htfin : ({c : GGL | σQ (σQ c) = c} : Set GGL).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [htcard]; positivity)
    have hFeq : (F : Set GGL) = {c : GGL | σQ (σQ c) = c} :=
      Set.eq_of_subset_of_ncard_le hFsub (by rw [htcard, hscard_F]) htfin
    intro c
    exact Set.ext_iff.mp hFeq c
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix
    (F := GF) (p := 2) (f := g) hGF ν
  set ι : M₀.K ≃* C :=
    (SURep.ggFrameEquiv hGF P hP).trans
      ((CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g)).trans eC) with hι
  set φ : M₀.K →* ModGL τ GGL := f.comp ι.toMonoidHom with hφ
  have hrange : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
      ← MonoidHom.range_eq_map]
    exact hfr
  have hker : φ.ker ≤ Subgroup.center M₀.K := by
    intro x hx
    have hx1 : ι x ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [hφ] at hx
      simpa using hx
    have hx2 : ι x ∈ Subgroup.center C := hfk hx1
    exact (Subgroup.comap_center_le_center (f := ι.toMonoidHom) ι.injective) hx2
  have hfinMK : Finite M₀.K := Finite.of_equiv (α := C) (h := hfinC) ι.symm.toEquiv
  have hperf : Group.IsPerfect M₀.K := by
    have h := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := GF) (p := 2) (f := g)
      hGF hν3 h32'
    exact h.ofSurjective (f := (CFSG.LieType.Universal.Unitary.equivStatedSU
      (F := GF) (p := 2) (f := g) hGF ν).symm.toMonoidHom)
      (CFSG.LieType.Universal.Unitary.equivStatedSU
        (F := GF) (p := 2) (f := g) hGF ν).symm.surjective
  have hodd : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M₀.K :=
    (CFSG.SeitzReduction.UnitaryPilot.oddCentralSplit_statedSU (F := GF) (f := g) hGF
      (by omega) h32').of_mulEquiv
      (CFSG.LieType.Universal.Unitary.equivStatedSU (F := GF) (p := 2) (f := g) hGF ν).symm
  have hdataGF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 g GF :=
    ⟨Nat.prime_two, hg1, by rw [hGF, ← pow_mul, mul_comm]⟩
  refine ⟨M₀, φ, ?_, ?_, hrange, hker, hfinMK, hperf, hodd, ?_⟩
  ·
    rw [← hνr, ← hg]
    exact hK.symm
  ·
    exact Or.inl ⟨.PSU, ν, Or.inr (Or.inl rfl), ⟨Nat.prime_two, hg1, hν3, h32'⟩, hK.symm⟩
  ·
    intro hs1 β hβ hlong
    have hconj1 : ∀ X : Matrix.SpecialLinearGroup (Fin ν) GGL,
        S.D.step (z * ψ X * z⁻¹) =
          z * ψ (CFSG.HardMathSupport.Timmesfeld.CrossChar.stdUnitary σQ.toRingHom X) * z⁻¹ := by
      rw [hs1] at hconjF
      have h1 : iterHom S.D.step 1 = S.D.step := by
        ext x
        rfl
      intro X
      have h := hconjF X
      rw [h1] at h
      simpa only [map_mul, map_mul, map_inv] using h
    have hφx : ∀ x : M₀.K,
        φ x = z * ψ ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) * z⁻¹ := by
      intro x
      change f (ι x) = z * ψ ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) * z⁻¹
      exact hf1 hs1 (ι x)
    set Pw : GL (Fin ν) GGL :=
      Matrix.GeneralLinearGroup.map (F.subtype.comp e₁.toRingHom) P with hPw
    have hW : ((Pw : Matrix (Fin ν) (Fin ν) GGL).map σQ)ᵀ * (Pw : Matrix (Fin ν) (Fin ν) GGL) =
        CFSG.LieType.Universal.Unitary.antidiag ν := by
      have hbar_e : ∀ c : GF,
          (F.subtype.comp e₁.toRingHom)
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g c) =
          σQ ((F.subtype.comp e₁.toRingHom) c) := by
        intro c
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow, hσQ]
      have hP' : ((P : Matrix (Fin ν) (Fin ν) GF).map
          (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g))ᵀ *
          (P : Matrix (Fin ν) (Fin ν) GF) =
          CFSG.LieType.Universal.Unitary.antidiag ν := hP
      have hPij : ∀ i j, (∑ k,
          CFSG.LieType.BorelTits.unitaryInvolution GF 2 g ((P : Matrix (Fin ν) (Fin ν) GF) k i) *
            (P : Matrix (Fin ν) (Fin ν) GF) k j) =
          CFSG.LieType.Universal.Unitary.antidiag ν i j := by
        intro i j
        have h := congrArg (fun A : Matrix (Fin ν) (Fin ν) GF => A i j) hP'
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using h
      ext i j
      calc (((Pw : Matrix (Fin ν) (Fin ν) GGL).map σQ)ᵀ *
              (Pw : Matrix (Fin ν) (Fin ν) GGL)) i j
          = ∑ k, σQ ((Pw : Matrix (Fin ν) (Fin ν) GGL) k i) *
              (Pw : Matrix (Fin ν) (Fin ν) GGL) k j := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
        _ = ∑ k, σQ ((F.subtype.comp e₁.toRingHom)
              ((P : Matrix (Fin ν) (Fin ν) GF) k i)) *
              (F.subtype.comp e₁.toRingHom)
                ((P : Matrix (Fin ν) (Fin ν) GF) k j) := by
            simp only [hPw, Matrix.GeneralLinearGroup.map_apply]
        _ = ∑ k, (F.subtype.comp e₁.toRingHom)
              (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g
                ((P : Matrix (Fin ν) (Fin ν) GF) k i)) *
              (F.subtype.comp e₁.toRingHom)
                ((P : Matrix (Fin ν) (Fin ν) GF) k j) := by
            simp only [hbar_e]
        _ = (F.subtype.comp e₁.toRingHom) (∑ k,
              CFSG.LieType.BorelTits.unitaryInvolution GF 2 g
                ((P : Matrix (Fin ν) (Fin ν) GF) k i) *
              (P : Matrix (Fin ν) (Fin ν) GF) k j) := by
            simp only [map_sum, map_mul]
        _ = (F.subtype.comp e₁.toRingHom)
              (CFSG.LieType.Universal.Unitary.antidiag ν i j) := by
            rw [hPij]
        _ = CFSG.LieType.Universal.Unitary.antidiag ν i j := by
            simp only [CFSG.LieType.Universal.Unitary.antidiag, Matrix.of_apply]
            split_ifs <;> simp
    have hιmat : ∀ x : M₀.K,
        (((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) : Matrix (Fin ν) (Fin ν) GGL) =
          (Pw : Matrix (Fin ν) (Fin ν) GGL) *
            (CFSG.LieType.Universal.Unitary.SUExtras.mat
              (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g) ν x).map
                (F.subtype.comp e₁.toRingHom) *
            ((Pw⁻¹ : GL (Fin ν) GGL) : Matrix (Fin ν) (Fin ν) GGL) := by
      have hPwcoe : ((P : Matrix (Fin ν) (Fin ν) GF).map
          (⇑F.subtype ∘ ⇑e₁)) = (Pw : Matrix (Fin ν) (Fin ν) GGL) := by
        rw [hPw]
        ext i j
        rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
        rfl
      have hPwinv : ((((P⁻¹ : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF).map
          (⇑F.subtype ∘ ⇑e₁))) =
          ((Pw⁻¹ : GL (Fin ν) GGL) : Matrix (Fin ν) (Fin ν) GGL) := by
        have h := congrArg (fun Y : GL (Fin ν) GGL =>
          (Y : Matrix (Fin ν) (Fin ν) GGL))
          (Matrix.GeneralLinearGroup.map_inv
            (f := F.subtype.comp e₁.toRingHom) P)
        rw [Matrix.GeneralLinearGroup.coe_inv, ← hPw] at h
        ext i j
        simpa only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply,
          RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, Matrix.GeneralLinearGroup.coe_inv] using
          congrFun (congrFun h i) j
      intro x
      have hPmat : ((SURep.ggFrameEquiv hGF P hP x :
          ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 g GF ν)) : GL (Fin ν) GF) =
          P * (x : GL (Fin ν) GF) * P⁻¹ := by
        have h1 := SURep.coe_ggFrameEquiv_symm hGF P hP
          (SURep.ggFrameEquiv hGF P hP x)
        rw [MulEquiv.symm_apply_apply] at h1
        rw [h1]
        group
      have hιx : (ι x : C) = eC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g)
          (SURep.ggFrameEquiv hGF P hP x)) := rfl
      rw [hιx]
      rw [heC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g)
        (SURep.ggFrameEquiv hGF P hP x))]
      rw [CFSG.RankThree.Classical2.coe_statedSUToSL,
        CFSG.Open.StatedSUFieldChange.statedSUEquiv_coe,
        CFSG.Open.StatedSUFieldChange.glEquiv_coe]
      rw [hPmat]
      simp only [Matrix.map_mul, Matrix.map_map, Units.val_mul, hPwcoe, hPwinv]
      rfl
    obtain ⟨y, hyC, hstab, hstab', hfix, hfix'⟩ :=
      rckSU_pair_of_witt S.D.step (by omega) hψ σQ
        (H := torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
        hzZ hψC hconj1 Pw hW
    have htop : (M₀.D.rootGroup (ggTopRoot ν)).map φ =
        (rootSubgroup τ GGL (σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
      let e : GF →+* GGL := F.subtype.comp e₁.toRingHom
      have hbar_e : ∀ t : GF,
          e (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g t) = σQ (e t) := by
        intro t
        change (F.subtype.comp e₁.toRingHom)
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g t) =
          σQ ((F.subtype.comp e₁.toRingHom) t)
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow, hσQ]
      ext w
      constructor
      · intro hw
        rw [Subgroup.mem_map] at hw
        obtain ⟨x, hx, rfl⟩ := hw
        have hx' : x ∈ CFSG.LieType.Universal.Unitary.rootGroup
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) ν
            (ggTopRoot ν) := hx
        obtain ⟨c, hc, hmat⟩ := (rckSU_mem_rootGroup_top_iff
          (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) (by omega) x).mp hx'
        let s : GGL := e c
        have hs : s + σQ s = 0 := by
          have h := congrArg e hc
          simpa only [map_add, map_zero, hbar_e c] using h
        have hXmat : (((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) :
            Matrix (Fin ν) (Fin ν) GGL) =
            (Pw : Matrix (Fin ν) (Fin ν) GGL) *
              (1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) s) *
              ((Pw⁻¹ : GL (Fin ν) GGL) : Matrix (Fin ν) (Fin ν) GGL) := by
          rw [hιmat x, hmat]
          rw [Matrix.map_add e (fun a b => map_add e a b)]
          rw [Matrix.map_one e (map_zero e) (map_one e), Matrix.map_single]
        exact (hfix (φ x)).2
          ⟨s, hs, ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL), hXmat, hφx x⟩
      · intro hw
        obtain ⟨s, hs, X, hXmat, hw_eq⟩ := (hfix w).1 hw
        have hsF : s ∈ F := by
          have h1 : σQ s = -s := by linear_combination hs
          rw [hFchar, h1, map_neg, h1, neg_neg]
        let c : GF := e₁.symm ⟨s, hsF⟩
        have hec : e c = s := by
          change F.subtype (e₁ (e₁.symm ⟨s, hsF⟩)) = s
          rw [RingEquiv.apply_symm_apply]
          rfl
        have hc : c + CFSG.LieType.BorelTits.unitaryInvolution GF 2 g c = 0 := by
          apply (F.subtype.comp e₁.toRingHom).injective
          rw [map_add, map_zero, hbar_e c, hec, hs]
        obtain ⟨x, hxmat⟩ := rckSU_exists_top (n := ν) (by omega) hc
        have hxroot : x ∈ M₀.D.rootGroup (ggTopRoot ν) :=
          (rckSU_mem_rootGroup_top_iff
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) (by omega) x).2
            ⟨c, hc, hxmat⟩
        have hmatmap : (CFSG.LieType.Universal.Unitary.SUExtras.mat
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g) ν x).map e =
            1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) s := by
          rw [hxmat]
          rw [Matrix.map_add e (fun a b => map_add e a b)]
          rw [Matrix.map_one e (map_zero e) (map_one e), Matrix.map_single, hec]
        have hιX : ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) = X := by
          apply Subtype.ext
          rw [hιmat x, hXmat, hmatmap]
        refine ⟨x, hxroot, ?_⟩
        rw [hφx x, hιX]
        exact hw_eq.symm
    have hbot : (M₀.D.rootGroup (-ggTopRoot ν)).map φ =
        (rootSubgroup τ GGL (-σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
      let e : GF →+* GGL := F.subtype.comp e₁.toRingHom
      have hbar_e : ∀ t : GF,
          e (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g t) = σQ (e t) := by
        intro t
        change (F.subtype.comp e₁.toRingHom)
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g t) =
          σQ ((F.subtype.comp e₁.toRingHom) t)
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow, hσQ]
      ext w
      constructor
      · intro hw
        rw [Subgroup.mem_map] at hw
        obtain ⟨x, hx, rfl⟩ := hw
        have hx' : x ∈ CFSG.LieType.Universal.Unitary.rootGroup
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) ν
            (-ggTopRoot ν) := hx
        obtain ⟨c, hc, hmat⟩ := (rckSU_mem_rootGroup_neg_top_iff
          (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) (by omega) x).mp hx'
        let s : GGL := e c
        have hs : s + σQ s = 0 := by
          have h := congrArg e hc
          simpa only [map_add, map_zero, hbar_e c] using h
        have hXmat : (((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) :
            Matrix (Fin ν) (Fin ν) GGL) =
            (Pw : Matrix (Fin ν) (Fin ν) GGL) *
              (1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ s) *
              ((Pw⁻¹ : GL (Fin ν) GGL) : Matrix (Fin ν) (Fin ν) GGL) := by
          rw [hιmat x, hmat]
          rw [Matrix.map_add e (fun a b => map_add e a b)]
          rw [Matrix.map_one e (map_zero e) (map_one e), Matrix.map_single]
        exact (hfix' (φ x)).2
          ⟨s, hs, ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL), hXmat, hφx x⟩
      · intro hw
        obtain ⟨s, hs, X, hXmat, hw_eq⟩ := (hfix' w).1 hw
        have hsF : s ∈ F := by
          have h1 : σQ s = -s := by linear_combination hs
          rw [hFchar, h1, map_neg, h1, neg_neg]
        let c : GF := e₁.symm ⟨s, hsF⟩
        have hec : e c = s := by
          change F.subtype (e₁ (e₁.symm ⟨s, hsF⟩)) = s
          rw [RingEquiv.apply_symm_apply]
          rfl
        have hc : c + CFSG.LieType.BorelTits.unitaryInvolution GF 2 g c = 0 := by
          apply (F.subtype.comp e₁.toRingHom).injective
          rw [map_add, map_zero, hbar_e c, hec, hs]
        obtain ⟨x, hxmat⟩ := rckSU_exists_neg_top (n := ν) (by omega) hc
        have hxroot : x ∈ M₀.D.rootGroup (-ggTopRoot ν) :=
          (rckSU_mem_rootGroup_neg_top_iff
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hGF) (by omega) x).2
            ⟨c, hc, hxmat⟩
        have hmatmap : (CFSG.LieType.Universal.Unitary.SUExtras.mat
            (CFSG.LieType.BorelTits.unitaryInvolution GF 2 g) ν x).map e =
            1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ s := by
          rw [hxmat]
          rw [Matrix.map_add e (fun a b => map_add e a b)]
          rw [Matrix.map_one e (map_zero e) (map_one e), Matrix.map_single, hec]
        have hιX : ((ι x : C) : Matrix.SpecialLinearGroup (Fin ν) GGL) = X := by
          apply Subtype.ext
          rw [hιmat x, hXmat, hmatmap]
        refine ⟨x, hxroot, ?_⟩
        rw [hφx x, hιX]
        exact hw_eq.symm
    obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hlong
    have hγ₀top : γ₀ = ggTopRoot ν := by
      have hγ₀' : γ₀ ∈ roots (CFSG.LieType.Universal.Unitary.isFiniteType_cartan ν)
          (CFSG.LieType.Universal.Unitary.divisible ν) := hγ₀
      refine rckSU_eq_ggTopRoot_of_maxHeight (n := ν) (by omega) hγ₀' ?_
      intro δ hδ
      exact hmax δ hδ
    subst γ₀
    obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hGF
    let hct := CFSG.LieType.Universal.Unitary.isCTGroupDatum hGF ν (by omega) ζ hζ
    let n : M₀.K := CFSG.LieType.Steinberg.nrep (D := M₀.D) hct w
    let u : ModGL τ GGL := φ n
    have hact := CFSG.LieType.Steinberg.actsAs_nrep (D := M₀.D) hct w
    have hnegroot : -ggTopRoot ν ∈ M₀.D.roots :=
      CFSG.LieType.Steinberg.OfCartan.neg_mem_roots
        (CFSG.LieType.Universal.Unitary.isFiniteType_cartan ν)
        (ggTopRoot_mem_roots (n := ν) (by omega))
    have htopact := hact (ggTopRoot ν) (ggTopRoot_mem_roots (n := ν) (by omega))
    have hbotact := hact (-ggTopRoot ν) hnegroot
    have hu_range : u ∈ φ.range := ⟨n, rfl⟩
    rw [hrange] at hu_range
    have hu_span : u ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
      Subgroup.commutator_le_self _ hu_range
    have hu_Γ : u ∈ S.Γ := (Subgroup.mem_inf.mp hu_span).2
    have hu_model : u ∈ S.D.model := Subgroup.commutator_le_self _ hu_Γ
    have hu_step : S.D.step u = u := by
      simpa only [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        using (S.D.mem_model.mp hu_model).2
    have hmapconj : ∀ H : Subgroup M₀.K,
        (H.map (MulAut.conj n).toMonoidHom).map φ =
          (H.map φ).map (MulAut.conj u).toMonoidHom := by
      intro H
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv, u]
    set γ : Fin τ.rank → ℤ := σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) with hγdef
    have hγmem : γ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ, hγdef]
      refine ⟨⟨0, by omega⟩, Fin.rev ⟨0, by omega⟩, ?_, rfl⟩
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      omega
    let zz : ModGL τ GGL := u * y
    have huC : u ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) :=
      rationalComponent_le_torusGroup_sup_rootSpan_kernelRoots S i hs1 hu_range
    have hzC : zz ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) :=
      Subgroup.mul_mem _ huC hyC
    obtain ⟨hzstab, hzfix⟩ :=
      rck_pair_conj S.D.step hu_step (rootSubgroup τ GGL γ) y hstab
    obtain ⟨hzmstab, hzfix'⟩ :=
      rck_pair_conj S.D.step hu_step (rootSubgroup τ GGL (-γ)) y hstab'
    have htopβ : (M₀.D.rootGroup (weylAction M₀.D.isFiniteType w (ggTopRoot ν))).map φ =
        (rootSubgroup τ GGL γ).map (MulAut.conj zz).toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _) := by
      calc
        (M₀.D.rootGroup (weylAction M₀.D.isFiniteType w (ggTopRoot ν))).map φ
            = ((M₀.D.rootGroup (ggTopRoot ν)).map
                (MulAut.conj n).toMonoidHom).map φ := by rw [← htopact]
        _ = ((M₀.D.rootGroup (ggTopRoot ν)).map φ).map
              (MulAut.conj u).toMonoidHom := hmapconj _
        _ = (((rootSubgroup τ GGL γ).map (MulAut.conj y).toMonoidHom) ⊓
              S.D.step.eqLocus (MonoidHom.id _)).map
                (MulAut.conj u).toMonoidHom := by rw [htop]
        _ = (rootSubgroup τ GGL γ).map (MulAut.conj zz).toMonoidHom ⊓
              S.D.step.eqLocus (MonoidHom.id _) := hzfix
    have hnegact : weylAction M₀.D.isFiniteType w (-ggTopRoot ν) =
        -weylAction M₀.D.isFiniteType w (ggTopRoot ν) :=
      LinearMap.map_neg (f := weylAction M₀.D.isFiniteType w) (ggTopRoot ν)
    have hbotβ : (M₀.D.rootGroup (-weylAction M₀.D.isFiniteType w (ggTopRoot ν))).map φ =
        (rootSubgroup τ GGL (-γ)).map (MulAut.conj zz).toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _) := by
      rw [← hnegact]
      calc
        (M₀.D.rootGroup (weylAction M₀.D.isFiniteType w (-ggTopRoot ν))).map φ
            = ((M₀.D.rootGroup (-ggTopRoot ν)).map
                (MulAut.conj n).toMonoidHom).map φ := by rw [← hbotact]
        _ = ((M₀.D.rootGroup (-ggTopRoot ν)).map φ).map
              (MulAut.conj u).toMonoidHom := hmapconj _
        _ = (((rootSubgroup τ GGL (-γ)).map (MulAut.conj y).toMonoidHom) ⊓
              S.D.step.eqLocus (MonoidHom.id _)).map
                (MulAut.conj u).toMonoidHom := by rw [hbot]
        _ = (rootSubgroup τ GGL (-γ)).map (MulAut.conj zz).toMonoidHom ⊓
              S.D.step.eqLocus (MonoidHom.id _) := hzfix'
    exact ⟨γ, hγmem, zz, hzC, hzstab, hzmstab, htopβ, hbotβ⟩

end CFSG.StandardType.RCKRP

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSUCover
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

public section

namespace CFSG.StandardType.RCKRP

open Matrix in
private lemma entries_mem_fixed_of_unitary {L : Type} [Field L] {F : Subfield L} {ν : ℕ}
    {σ : L ≃+* L} (hF : ∀ c : L, c ∈ F ↔ σ (σ c) = c) {G : GL (Fin ν) L}
    (hG : ((G : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ *
      (G : Matrix (Fin ν) (Fin ν) L) = 1) :
    ∀ i j, G i j ∈ F := by
  classical
  have hGt : (G : Matrix (Fin ν) (Fin ν) L)ᵀ *
      (G : Matrix (Fin ν) (Fin ν) L).map σ = 1 := by
    have h := congrArg Matrix.transpose hG
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h
  have hGσ : (((G : Matrix (Fin ν) (Fin ν) L).map σ).map σ)ᵀ *
      (G : Matrix (Fin ν) (Fin ν) L).map σ = 1 := by
    have h := congrArg (fun M : Matrix (Fin ν) (Fin ν) L => M.map σ) hG
    rw [Matrix.map_mul, Matrix.transpose_map] at h
    rwa [show (1 : Matrix (Fin ν) (Fin ν) L).map (⇑σ) = 1 from
      Matrix.map_one (⇑σ) (map_zero σ.toRingHom) (map_one σ.toRingHom)] at h
  have hfix : ((G : Matrix (Fin ν) (Fin ν) L).map σ).map σ =
      (G : Matrix (Fin ν) (Fin ν) L) := by
    have hleft := Matrix.left_inv_eq_left_inv hGσ hGt
    have h := congrArg Matrix.transpose hleft
    simpa only [Matrix.transpose_transpose] using h
  intro i j
  rw [hF]
  have h := congrArg (fun M : Matrix (Fin ν) (Fin ν) L => M i j) hfix
  simpa only [Matrix.map_apply] using h

open Matrix in
private lemma exists_gl_preimage {K L : Type} [Field K] [Field L] {F : Subfield L} {ν : ℕ}
    (e : K ≃+* F) {G : GL (Fin ν) L} (hmem : ∀ i j, G i j ∈ F) :
    ∃ A : GL (Fin ν) K,
      (A : Matrix (Fin ν) (Fin ν) K).map (F.subtype.comp e.toRingHom) =
        (G : Matrix (Fin ν) (Fin ν) L) := by
  classical
  let Bm : Matrix (Fin ν) (Fin ν) F := fun i j => ⟨G i j, hmem i j⟩
  have hBmap : Bm.map F.subtype = (G : Matrix (Fin ν) (Fin ν) L) := by
    ext i j
    rfl
  have hdetG : (G : Matrix (Fin ν) (Fin ν) L).det ≠ 0 := by
    intro h0
    have hmul : (G : Matrix (Fin ν) (Fin ν) L) *
        ((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetB : Bm.det ≠ 0 := by
    intro h0
    have h1 : F.subtype Bm.det = (Bm.map F.subtype).det := RingHom.map_det F.subtype Bm
    rw [h0, map_zero, hBmap] at h1
    exact hdetG h1.symm
  let B : GL (Fin ν) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm hdetB
  have hBcoe : (B : Matrix (Fin ν) (Fin ν) F) = Bm :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero Bm hdetB
  let A : GL (Fin ν) K :=
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin ν) e).symm B
  refine ⟨A, ?_⟩
  have hAe : (A : Matrix (Fin ν) (Fin ν) K).map e.toRingHom = Bm := by
    have h1 := CFSG.Adapters.RankTwoModelTransports.glCongr_symm_coe (ι := Fin ν) e B
    rw [h1]
    ext i j
    simp [hBcoe]
  calc (A : Matrix (Fin ν) (Fin ν) K).map (F.subtype.comp e.toRingHom)
      = ((A : Matrix (Fin ν) (Fin ν) K).map e.toRingHom).map F.subtype := by
        rw [Matrix.map_map]
        rfl
    _ = Bm.map F.subtype := by rw [hAe]
    _ = (G : Matrix (Fin ν) (Fin ν) L) := hBmap

private lemma frame_dim {ν r : ℕ} (h : ν * (ν - 1) = r * (r + 1)) (hν : 3 ≤ ν) :
    ν = r + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have hm : m = r := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
  omega

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix in
theorem rckCarrierSU_holds :
    RCKCarrierSU := by
  classical
  intro τ p₀ S a hT p hp hp2 hTp i h hq hkind hr3 hQS
  clear hQS
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
  have hνr : ν = r + 1 := frame_dim hEq hν3
  have hν4 : 4 ≤ ν := by omega
  have h32' : (ν, 2 ^ g) ≠ (3, 2) := by
    intro hcon
    have h1 : ν = 3 := congrArg Prod.fst hcon
    omega
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_perm S hT i hkind hν3 hψ hκ hnorm hΨ
  obtain ⟨σQ, hσQ, -, f, -, -, -, hfr, hfk, hact⟩ :=
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
  refine ⟨M₀, φ, ?_, ?_, hrange, hker, hfinMK, hperf, hodd, ?_, ?_⟩
  ·
    rw [← hνr, ← hg]
    exact hK.symm
  ·
    refine Or.inl ⟨.PSU, ν, Or.inr (Or.inl rfl),
      ⟨Nat.prime_two, hg1, hν3, h32'⟩, ?_⟩
    exact hK.symm
  ·
    exact ⟨ggTopRoot ν, ggTopRoot_mem_roots (by omega),
      CFSG.StandardType.RestSU.ggTopRoot_longRoot (F := GF) hGF (by omega)⟩
  ·
    intro b hb
    obtain ⟨hbmem, hbstep⟩ :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf (n := S.D.n) (Φ := S.D.Φ)).mp hb
    have hbinv := inv_mem hbmem
    have hbZ' : b⁻¹ ∈ CFSG.LieType.Chevalley.torusGroup τ GGL ⊔
        CFSG.Blueprint.Chevalley.rootSpan τ GGL
          (CFSG.LieType.Chevalley.kernelRoots (rootCharHom a)) :=
      Subgroup.mem_sup_left hbinv
    have hstepb : S.D.step b = b :=
      hbstep
    have hbstep' : S.D.step b⁻¹ = b⁻¹ := by
      rw [map_inv, hstepb]
    obtain ⟨G, hGu, hGconj⟩ := hact b⁻¹ hbZ' hbstep'
    have hentries : ∀ i j, G i j ∈ F := entries_mem_fixed_of_unitary hFchar hGu
    obtain ⟨A, hAcoe0⟩ := exists_gl_preimage (F := F) e₁ (G := G) hentries
    have hAcoe : ((A : Matrix (Fin ν) (Fin ν) GF).map (F.subtype ∘ e₁)) =
        (G : Matrix (Fin ν) (Fin ν) GGL) := hAcoe0
    have hAinv' : (((A⁻¹ : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF).map
        (F.subtype.comp e₁.toRingHom)) = ((G : Matrix (Fin ν) (Fin ν) GGL))⁻¹ := by
      have hmapinv : (((A⁻¹ : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF).map
          (F.subtype.comp e₁.toRingHom)) =
          (((A : Matrix (Fin ν) (Fin ν) GF).map
            (F.subtype.comp e₁.toRingHom))⁻¹) := by
        have h1 : Matrix.GeneralLinearGroup.map (F.subtype.comp e₁.toRingHom) A⁻¹ =
            (Matrix.GeneralLinearGroup.map (F.subtype.comp e₁.toRingHom) A)⁻¹ :=
          Matrix.GeneralLinearGroup.map_inv (f := F.subtype.comp e₁.toRingHom) A
        have h3 := congrArg (fun Y : GL (Fin ν) GGL =>
          (Y : Matrix (Fin ν) (Fin ν) GGL)) h1
        rw [Matrix.GeneralLinearGroup.coe_inv] at h3
        exact h3
      rw [hmapinv, hAcoe0]
    have hAinv : (((A⁻¹ : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF).map
        (F.subtype ∘ e₁)) = ((G : Matrix (Fin ν) (Fin ν) GGL))⁻¹ := hAinv'
    have hbar_e : ∀ c : GF,
        e₁ (CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar hdataGF c) = σQ (e₁ c) := by
      intro c
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, map_pow, hσQ]
      rfl
    have hAG : ∀ i j, (F.subtype.comp e₁.toRingHom)
        ((A : Matrix (Fin ν) (Fin ν) GF) i j) =
        (G : Matrix (Fin ν) (Fin ν) GGL) i j := by
      intro i j
      have h := congrArg (fun M : Matrix (Fin ν) (Fin ν) GGL => M i j) hAcoe0
      simpa only [Matrix.map_apply] using h
    have hA : A ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        hdataGF ((1 : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
      rw [Units.val_one, Matrix.mul_one]
      refine Matrix.map_injective (f := F.subtype.comp e₁.toRingHom)
        ((Subfield.subtype_injective F).comp e₁.injective) ?_
      have hmapbar : ((A : Matrix (Fin ν) (Fin ν) GF).map hdataGF.bar).map
          (F.subtype.comp e₁.toRingHom) =
          ((G : Matrix (Fin ν) (Fin ν) GGL).map σQ) := by
        ext i j
        simp only [Matrix.map_apply]
        rw [show (F.subtype.comp e₁.toRingHom)
            (hdataGF.bar ((A : Matrix (Fin ν) (Fin ν) GF) i j)) =
            σQ ((F.subtype.comp e₁.toRingHom)
              ((A : Matrix (Fin ν) (Fin ν) GF) i j)) from
          hbar_e ((A : Matrix (Fin ν) (Fin ν) GF) i j)]
        rw [hAG i j]
      have hkey : ((((A : Matrix (Fin ν) (Fin ν) GF).map hdataGF.bar)ᵀ *
          (A : Matrix (Fin ν) (Fin ν) GF)).map (F.subtype.comp e₁.toRingHom)) =
          (((G : Matrix (Fin ν) (Fin ν) GGL).map σQ)ᵀ *
            (G : Matrix (Fin ν) (Fin ν) GGL)) := by
        rw [Matrix.map_mul, Matrix.transpose_map, hmapbar]
        rw [show (A : Matrix (Fin ν) (Fin ν) GF).map (F.subtype.comp e₁.toRingHom) =
            (G : Matrix (Fin ν) (Fin ν) GGL) from hAcoe0]
      change ((((A : Matrix (Fin ν) (Fin ν) GF).map hdataGF.bar)ᵀ *
        (A : Matrix (Fin ν) (Fin ν) GF)).map (F.subtype.comp e₁.toRingHom)) =
        ((1 : Matrix (Fin ν) (Fin ν) GF).map (F.subtype.comp e₁.toRingHom))
      rw [hkey, hGu,
        Matrix.map_one (⇑(F.subtype.comp e₁.toRingHom))
          (map_zero (F.subtype.comp e₁.toRingHom)) (map_one (F.subtype.comp e₁.toRingHom))]
    have hy : ∀ x x' : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 g GF ν),
        (x' : GL (Fin ν) GF) = A * x * A⁻¹ →
        b⁻¹ * SURep.ggFrameU hGF φ P hP x * b = SURep.ggFrameU hGF φ P hP x' := by
      intro x x' hxx'
      have hmat : ((x' : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF) =
          (A : Matrix (Fin ν) (Fin ν) GF) *
            ((x : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF) *
            ((A⁻¹ : GL (Fin ν) GF) : Matrix (Fin ν) (Fin ν) GF) := by
        have h := congrArg (fun Y : GL (Fin ν) GF =>
          (Y : Matrix (Fin ν) (Fin ν) GF)) hxx'
        simpa only [Units.val_mul] using h
      have hc : ((eC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g) x') : C) :
            Matrix.SpecialLinearGroup (Fin ν) GGL) =
          CFSG.RankThree.Classical2.conjSLn G
            ((eC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g) x) : C) :
              Matrix.SpecialLinearGroup (Fin ν) GGL) := by
        have hcoe : ∀ y : ↥(CFSG.Open.StatedSU ν (2 ^ g) F),
            ((CFSG.RankThree.Classical2.statedSUToSL F ν (2 ^ g) y :
              Matrix.SpecialLinearGroup (Fin ν) GGL) :
              Matrix (Fin ν) (Fin ν) GGL) =
            ((y : GL (Fin ν) F) : Matrix (Fin ν) (Fin ν) F).map F.subtype :=
          fun y => CFSG.RankThree.Classical2.coe_statedSUToSL F ν (2 ^ g) y
        apply Subtype.ext
        rw [CFSG.RankThree.Classical2.coe_conjSLn, Matrix.GeneralLinearGroup.coe_inv]
        rw [heC, heC]
        rw [hcoe, hcoe]
        rw [CFSG.Open.StatedSUFieldChange.statedSUEquiv_coe,
          CFSG.Open.StatedSUFieldChange.statedSUEquiv_coe]
        rw [CFSG.Open.StatedSUFieldChange.glEquiv_coe,
          CFSG.Open.StatedSUFieldChange.glEquiv_coe]
        rw [hmat]
        simp only [Matrix.map_mul]
        simp only [Matrix.map_map]
        rw [hAcoe, hAinv]
      have hx : SURep.ggFrameU hGF φ P hP x =
          f (eC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g) x)) := by
        rw [SURep.ggFrameU_apply, hφ]
        change f (ι ((SURep.ggFrameEquiv hGF P hP).symm x)) = _
        rw [hι]
        simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        rfl
      have hx' : SURep.ggFrameU hGF φ P hP x' =
          f (eC (CFSG.Open.StatedSUFieldChange.statedSUEquiv e₁ ν (2 ^ g) x')) := by
        rw [SURep.ggFrameU_apply, hφ]
        change f (ι ((SURep.ggFrameEquiv hGF P hP).symm x')) = _
        rw [hι]
        simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        rfl
      rw [hx, hx']
      exact hGconj _ _ hc
    exact CFSG.StandardType.OrdPFieldNsUD.ggPsiInnerDiag_of_frame_conj
      hGF hdataGF hν4 hP hA hy

end CFSG.StandardType.RCKRP

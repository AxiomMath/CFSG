module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUAux
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.RankTwoClassical
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
open CFSG.SeitzReduction.F4Pilot (conjTr_mapMatrix mapMatrix_antidiag)

theorem irgUB_fieldData (g : ℕ) (hg : 1 ≤ g) : UnitaryFieldData 2 g (irgU_F g) where
  prime := Nat.prime_two
  one_le := hg
  card := by
    rw [irgU_F, GaloisField.card 2 (2 * g) (by omega)]

theorem irgUB_bar_apply_eq_sigma (g : ℕ) (hg : 1 ≤ g) (c : irgU_F g) :
    (irgUB_fieldData g hg).bar c = irgU_sigma g c := by
  rw [UnitaryFieldData.bar_apply, irgU_sigma,
    CFSG.LieType.BorelTits.unitaryInvolution_apply]

theorem irgUB_bar_eq_sigma (g : ℕ) (hg : 1 ≤ g) :
    ((irgUB_fieldData g hg).bar : irgU_F g → irgU_F g) = ⇑(irgU_sigma g) :=
  funext (irgUB_bar_apply_eq_sigma g hg)

theorem irgUB_conjTr_inv_mul_antidiag {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n) :
    conjTr σ (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * antidiag n =
      (P : Matrix (Fin n) (Fin n) F) := by
  have hcancel : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc
    conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n
        = conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)) := by
          rw [hP]
    _ = (conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          conjTr σ (P : Matrix (Fin n) (Fin n) F)) * (P : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.mul_assoc]
    _ = conjTr σ ((P : Matrix (Fin n) (Fin n) F) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          (P : Matrix (Fin n) (Fin n) F) := by
          rw [conjTr_mul]
    _ = 1 * (P : Matrix (Fin n) (Fin n) F) := by
          rw [hcancel, conjTr_one]
    _ = (P : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.one_mul]

theorem irgUB_witt_mem {F : Type} [Field F] {n : ℕ} (σ φ : F ≃+* F)
    (hφ : ∀ c, φ (σ c) = σ (φ c)) (P A W : GL (Fin n) F)
    (hW : W = P⁻¹ * (A * Matrix.GeneralLinearGroup.map φ.toRingHom P))
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1) :
    conjTr σ (W : Matrix (Fin n) (Fin n) F) * antidiag n *
      (W : Matrix (Fin n) (Fin n) F) = antidiag n := by
  rw [hW]
  simp only [Units.val_mul]
  set Pm : Matrix (Fin n) (Fin n) F := (P : Matrix (Fin n) (Fin n) F) with hPm
  set Am : Matrix (Fin n) (Fin n) F := (A : Matrix (Fin n) (Fin n) F) with hAm
  set Qm : Matrix (Fin n) (Fin n) F :=
    ((Matrix.GeneralLinearGroup.map φ.toRingHom P : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) with hQm
  set Pi : Matrix (Fin n) (Fin n) F :=
    ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hPi
  have hQ : Qm = Pm.map φ := by
    rw [hQm, hPm]
    rfl
  have hPiJ : conjTr σ Pi * antidiag n = Pm := by
    rw [hPi, hPm]
    exact irgUB_conjTr_inv_mul_antidiag σ P hP
  have hPmPi : Pm * Pi = 1 := by
    rw [hPi, hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiJPi : conjTr σ Pi * antidiag n * Pi = 1 := by
    rw [hPiJ, hPmPi]
  have hA' : conjTr σ Am * Am = 1 := by
    rw [hAm]
    exact hA
  have hP' : conjTr σ Pm * Pm = antidiag n := by
    rw [hPm]
    exact hP
  have hstep : conjTr σ (Pi * (Am * Qm)) * antidiag n * (Pi * (Am * Qm)) =
      conjTr σ Qm * conjTr σ Am * (conjTr σ Pi * antidiag n * Pi) * (Am * Qm) := by
    simp only [conjTr_mul, Matrix.mul_assoc]
  rw [hstep]
  rw [hPiJPi, Matrix.mul_one]
  rw [Matrix.mul_assoc (conjTr σ Qm) (conjTr σ Am) (Am * Qm)]
  rw [← Matrix.mul_assoc (conjTr σ Am) Am Qm, hA', Matrix.one_mul]
  rw [hQ, ← RingEquiv.mapMatrix_apply, conjTr_mapMatrix φ hφ, ← map_mul, hP',
    mapMatrix_antidiag]


theorem irgUB_exists_semilinear_of_admissible
    {n g : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (hq : (n, 2 ^ g) ≠ (3, 2))
    (θ : MulAut (Unitary.SU (irgU_sigma g) n ⧸
      Subgroup.center (Unitary.SU (irgU_sigma g) n))) :
    ∃ (φ : irgU_F g ≃+* irgU_F g) (W : GL (Fin n) (irgU_F g)),
      conjTr (irgU_sigma g) (W : Matrix (Fin n) (Fin n) (irgU_F g)) * antidiag n *
          (W : Matrix (Fin n) (Fin n) (irgU_F g)) = antidiag n ∧
      ∀ x : Unitary.SU (irgU_sigma g) n,
        ∃ y : Unitary.SU (irgU_sigma g) n,
          (y : GL (Fin n) (irgU_F g)) =
              W * (Matrix.GeneralLinearGroup.map φ.toRingHom
                (x : GL (Fin n) (irgU_F g))) * W⁻¹ ∧
          θ (QuotientGroup.mk' (Subgroup.center (Unitary.SU (irgU_sigma g) n)) x) =
            QuotientGroup.mk' (Subgroup.center (Unitary.SU (irgU_sigma g) n)) y := by
  classical
  let K := irgU_F g
  let σ := irgU_sigma g
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := (irgUB_fieldData g hg).charP
  haveI : Finite K := (irgUB_fieldData g hg).finite
  have hK : Nat.card K = (2 ^ g) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 g hg
  let h : UnitaryFieldData 2 g K := irgUB_fieldData g hg
  have hbar : ((h : UnitaryFieldData 2 g K).bar : K → K) = ⇑σ := irgUB_bar_eq_sigma g hg
  obtain ⟨r, ε, hr, hε, hn_eq⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  subst hn_eq
  have hq' : ¬(2 * r + ε = 3 ∧ 2 ^ g = 2) := by
    rintro ⟨h1, h2⟩
    exact hq (by rw [h1, h2])
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := 2) (f := g) hK (2 * r + ε)
  let e : Unitary.SU σ (2 * r + ε) ≃* unitarySU 2 g K (2 * r + ε) :=
    (conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := g) hK (2 * r + ε)))
  have he_apply : ∀ x : Unitary.SU σ (2 * r + ε),
      (e x : GL (Fin (2 * r + ε)) K) = P * (x : GL (Fin (2 * r + ε)) K) * P⁻¹ := by
    intro x
    rfl
  have he_symm_apply : ∀ y : unitarySU 2 g K (2 * r + ε),
      ((e.symm y : Unitary.SU σ (2 * r + ε)) : GL (Fin (2 * r + ε)) K) =
        P⁻¹ * (y : GL (Fin (2 * r + ε)) K) * P := by
    intro y
    rfl
  have hcent := (isQuasisimple_statedSU_of_card (p := 2) (f := g) (F := K) hK
    (by omega : 3 ≤ 2 * r + ε) hq).2
  have hZ : Subgroup.center (unitarySU 2 g K (2 * r + ε)) = unitaryScalars h (2 * r + ε) := by
    rw [unitaryScalars_eq h (by omega : 1 ≤ 2 * r + ε)]
    exact hcent
  let E : (Unitary.SU σ (2 * r + ε) ⧸
      Subgroup.center (Unitary.SU σ (2 * r + ε))) ≃* unitaryPSU h (2 * r + ε) :=
    (QuotientGroup.congr _ _ e (map_center_mulEquiv e)).trans
      (QuotientGroup.quotientMulEquivOfEq hZ)
  have hE_mk : ∀ x : Unitary.SU σ (2 * r + ε),
      E (QuotientGroup.mk' (Subgroup.center (Unitary.SU σ (2 * r + ε))) x) =
        unitaryProj h (2 * r + ε) (e x) := by
    intro x
    dsimp only [E]
    rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply]
    rw [show (QuotientGroup.congr
        (Subgroup.center (Unitary.SU σ (2 * r + ε)))
        (Subgroup.center (unitarySU 2 g K (2 * r + ε)))
        e (map_center_mulEquiv e)) ↑x = ↑(e x) from
      QuotientGroup.congr_mk
        (Subgroup.center (Unitary.SU σ (2 * r + ε)))
        (Subgroup.center (unitarySU 2 g K (2 * r + ε)))
        e (map_center_mulEquiv e) x]
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hE_symm : ∀ z : unitarySU 2 g K (2 * r + ε),
      E.symm (unitaryProj h (2 * r + ε) z) =
        QuotientGroup.mk' (Subgroup.center (Unitary.SU σ (2 * r + ε))) (e.symm z) := by
    intro z
    apply E.injective
    rw [E.apply_symm_apply, hE_mk, MulEquiv.apply_symm_apply]
  let θ' : MulAut (unitaryPSU h (2 * r + ε)) := (MulAut.congr E) θ
  have hθ' : ∀ a, θ' (E a) = E (θ a) := by
    intro a
    simp only [θ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨φ, A, hA, hAg⟩ :=
    exists_unitary_semilinear_psu_of_admissible h hr hε (by omega) hq' θ'
  have hA' : conjTr σ (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
      (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = 1 := by
    have h := hA
    rw [hbar] at h
    simpa [conjTr] using h
  have hφσ : ∀ c, φ (σ c) = σ (φ c) := by
    intro c
    have h := irgU_ringEquiv_commute_unitaryInvolution (F := K) 2 g φ c
    simpa [σ, irgU_sigma] using h
  let W : GL (Fin (2 * r + ε)) K :=
    P⁻¹ * (A * Matrix.GeneralLinearGroup.map φ.toRingHom P)
  refine ⟨φ, W, ?_, ?_⟩
  · exact irgUB_witt_mem σ φ hφσ P A W rfl hP hA'
  · intro x
    obtain ⟨hz, hβ⟩ := hAg (e x)
    let y : Unitary.SU σ (2 * r + ε) :=
      e.symm ⟨A * glAut φ
        (e x : GL (Fin (2 * r + ε)) K) * A⁻¹, hz⟩
    refine ⟨y, ?_, ?_⟩
    · have hy : (y : GL (Fin (2 * r + ε)) K) =
          P⁻¹ * (A * glAut φ
            (e x : GL (Fin (2 * r + ε)) K) * A⁻¹) * P :=
        he_symm_apply _
      have hgl : glAut φ
            (e x : GL (Fin (2 * r + ε)) K) =
          glAut φ P *
            glAut φ
              (x : GL (Fin (2 * r + ε)) K) *
            (glAut φ P)⁻¹ := by
        rw [he_apply]
        simp only [map_mul, map_inv]
      have hglP : glAut φ P =
          Matrix.GeneralLinearGroup.map φ.toRingHom P := Units.ext rfl
      have hglx : glAut φ (x : GL (Fin (2 * r + ε)) K) =
          Matrix.GeneralLinearGroup.map φ.toRingHom
            (x : GL (Fin (2 * r + ε)) K) := Units.ext rfl
      rw [hy, hgl, hglP, hglx]
      dsimp only [W]
      group
    · have h1 : E (θ (QuotientGroup.mk'
          (Subgroup.center (Unitary.SU σ (2 * r + ε))) x)) =
          unitaryProj h (2 * r + ε) ⟨_, hz⟩ := by
        rw [← hθ' (QuotientGroup.mk' (Subgroup.center (Unitary.SU σ (2 * r + ε))) x),
          hE_mk x]
        exact hβ
      rw [← E.symm_apply_apply
        (θ (QuotientGroup.mk' (Subgroup.center (Unitary.SU σ (2 * r + ε))) x)), h1,
        hE_symm ⟨_, hz⟩]

end CFSG.StandardType.RCKRP

end

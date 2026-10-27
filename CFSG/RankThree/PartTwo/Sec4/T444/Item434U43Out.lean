module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Sylow
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43OutAlg
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

local notation "Mat4" => Matrix (Fin 4) (Fin 4) F9

theorem hU9 : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

theorem bar9_apply (x : F9) : hU9.bar x = x ^ 3 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

abbrev idG : Matrix (Fin 4) (Fin 4) F9 := ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)

theorem isPrimeFormGram_one9 : IsPrimeFormGram (1 : GL (Fin 4) F9) := by
  refine ⟨by simp, fun i j => ?_⟩
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

abbrev PF : Type := primeFormP hU9 idG

noncomputable def ePF : unitaryPSU hU9 4 ≃* PF :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hU9 4)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU hU9 4)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

noncomputable def eUXP : UX ≃* PF :=
  (unitaryPSUEquiv hU9 (by norm_num : 1 ≤ 4)).symm.trans ePF

@[expose] noncomputable def toGram (g : SUg) : gramSU hU9 idG :=
  MulEquiv.subgroupCongr (unitarySU_eq_gramSU hU9 4) g

theorem eUXP_piU (g : SUg) : eUXP (piU g) = ((toGram g : gramSU hU9 idG) : PF) := by
  have h1 : (unitaryPSUEquiv hU9 (by norm_num : 1 ≤ 4)).symm (piU g) = unitaryProj hU9 4 g :=
    (MulEquiv.symm_apply_eq _).mpr (unitaryPSUEquiv_unitaryProj hU9 (by norm_num) g).symm
  unfold eUXP
  rw [MulEquiv.trans_apply, h1]
  exact QuotientGroup.congr_mk _ _ _ _ g

theorem ringEquiv_F9 (φ : F9 ≃+* F9) : (∀ x, φ x = x) ∨ (∀ x, φ x = x ^ 3) := by
  have hI : ((⟨0, 1⟩ : F9) * ⟨0, 1⟩) = -1 := by decide
  have h1 : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = -1 := by rw [← map_mul, hI, map_neg, map_one]
  have h2 : ∀ y : F9, y * y = -1 → y = ⟨0, 1⟩ ∨ y = -⟨0, 1⟩ := by decide
  have hx : ∀ x : F9, x = ((x.re.val : ℕ) : F9) + ((x.im.val : ℕ) : F9) * ⟨0, 1⟩ := by decide
  have hy : ∀ x : F9, ((x.re.val : ℕ) : F9) + ((x.im.val : ℕ) : F9) * (-⟨0, 1⟩) = x ^ 3 := by
    decide
  rcases h2 _ h1 with h | h
  · left
    intro x
    conv_lhs => rw [hx x]
    rw [map_add, map_mul, map_natCast, map_natCast, h, ← hx x]
  · right
    intro x
    conv_lhs => rw [hx x]
    rw [map_add, map_mul, map_natCast, map_natCast, h, hy x]

theorem eq_of_scalar_cube {g' y : GL (Fin 4) F9} {c : F9ˣ} (hy3 : y ^ 3 = 1) (hg3 : g' ^ 3 = 1)
    (hs : g'⁻¹ * y = Matrix.GeneralLinearGroup.scalar (Fin 4) c) (hc4 : c ^ 4 = 1) : g' = y := by
  have hcomm : Commute g' (Matrix.GeneralLinearGroup.scalar (Fin 4) c) := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : F9) (fun _ => Commute.all _ _) (g' : Mat4)).symm.eq
  have hy : y = g' * Matrix.GeneralLinearGroup.scalar (Fin 4) c := by rw [← hs]; group
  have h3 : (Matrix.GeneralLinearGroup.scalar (Fin 4) c) ^ 3 = 1 := by
    have e : y ^ 3 = g' ^ 3 * (Matrix.GeneralLinearGroup.scalar (Fin 4) c) ^ 3 := by
      conv_lhs => rw [hy]
      exact hcomm.mul_pow 3
    rw [hy3, hg3, one_mul] at e
    exact e.symm
  have hc3 : c ^ 3 = 1 := by
    rw [← map_pow] at h3
    exact scalar_injective (by rw [h3, map_one])
  have hc1 : c = 1 := by
    calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc4, hc3]; simp
  rw [hc1, map_one, mul_one] at hy
  exact hy.symm

theorem conj_eq_of_fix {A : primeFormUnitary hU9 idG} {φ : F9 ≃+* F9} {y : SUg} (hy3 : y ^ 3 = 1)
    (hfix : (primeFormConjHom hU9 idG A * primeFormFieldHom hU9 isPrimeFormGram_one9 φ)
      (eUXP (piU y)) = eUXP (piU y)) :
    (A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9)⁻¹ =
      (y : GL (Fin 4) F9) := by
  rw [eUXP_piU, MulAut.mul_apply] at hfix
  have h1 : primeFormFieldHom hU9 isPrimeFormGram_one9 φ ((toGram y : gramSU hU9 idG) : PF) =
      ((primeFormFieldSU hU9 isPrimeFormGram_one9 φ (toGram y) : gramSU hU9 idG) : PF) :=
    primeFormFieldAut_mk hU9 isPrimeFormGram_one9 φ (toGram y)
  rw [h1, primeFormConjHom_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, hc4, hc⟩ := hfix
  have hcoe : (((A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9)⁻¹)⁻¹ *
      (y : GL (Fin 4) F9)) = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
    rw [← hc]
    rfl
  have hg3 : ((A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9)⁻¹) ^ 3 =
      1 := by
    rw [conj_pow, ← map_pow]
    have : (y : GL (Fin 4) F9) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hy3]
      rfl
    rw [this, map_one]
    group
  exact eq_of_scalar_cube (by rw [← Subgroup.coe_pow, hy3]; rfl) hg3 hcoe hc4

theorem inner_of_fix_triple {z a b : SUg} {zc ac bc Qc Tc Tic : List ℕ} {u : Fin 4 → F9}
    (hz : toMat z = dec4 zc) (ha : toMat a = dec4 ac) (hb : toMat b = dec4 bc)
    (hz3 : z ^ 3 = 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hg : OutGood (dec4 zc) (dec4 ac) (dec4 bc) (dec4 Qc) (dec4 Tc) (dec4 Tic) u)
    (α : MulAut UX) (hαz : α (piU z) = piU z) (hαa : α (piU a) = piU a)
    (hαb : α (piU b) = piU b) : α ∈ (MulAut.conj : UX →* MulAut UX).range := by
  set α' : MulAut PF := MulAut.congr eUXP α with hα'
  have hα'x : ∀ x : UX, α' (eUXP x) = eUXP (α x) := fun x => by
    rw [hα']
    simp [MulAut.congr_apply]
  obtain ⟨φ, ⟨A, hA⟩, -⟩ :=
    (unitary_prime_form_full_semilinear_realization hU9 isPrimeFormGram_one9 (by norm_num)
      (by norm_num)).2.2.2.2.1 α'
  have hfix : ∀ y : SUg, y ^ 3 = 1 → α (piU y) = piU y →
      ((A : GL (Fin 4) F9) : Mat4) * ((y : GL (Fin 4) F9) : Mat4).map φ =
        ((y : GL (Fin 4) F9) : Mat4) * ((A : GL (Fin 4) F9) : Mat4) := by
    intro y hy3 hy
    have h1 := conj_eq_of_fix (A := A) (φ := φ) hy3 (by rw [← hA, hα'x, hy])
    have h2 : (A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9) =
        (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9) := by
      calc (A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9)
          = ((A : GL (Fin 4) F9) * glAut φ (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9)⁻¹) *
            (A : GL (Fin 4) F9) := by group
        _ = (y : GL (Fin 4) F9) * (A : GL (Fin 4) F9) := by rw [h1]
    have h3 := congrArg (fun g : GL (Fin 4) F9 => (g : Mat4)) h2
    simpa only [Units.val_mul, coe_glAut] using h3
  have hdetA : ((A : GL (Fin 4) F9) : Mat4).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hAu : (((A : GL (Fin 4) F9) : Mat4).map (· ^ 3))ᵀ * ((A : GL (Fin 4) F9) : Mat4) = 1 := by
    have h := A.2
    rw [mem_primeFormUnitary] at h
    simp only [Units.val_one, Matrix.mul_one] at h
    have e : ((A : GL (Fin 4) F9) : Mat4).map hU9.bar = ((A : GL (Fin 4) F9) : Mat4).map (· ^ 3) :=
      Matrix.ext fun i j => bar9_apply _
    rwa [e] at h
  have hz' : (((z : GL (Fin 4) F9) : Mat4)) = dec4 zc := hz
  have ha' : (((a : GL (Fin 4) F9) : Mat4)) = dec4 ac := ha
  have hb' : (((b : GL (Fin 4) F9) : Mat4)) = dec4 bc := hb
  have hfz := hfix z hz3 hαz
  have hfa := hfix a ha3 hαa
  have hfb := hfix b hb3 hαb
  rw [hz'] at hfz
  rw [ha'] at hfa
  rw [hb'] at hfb
  rcases ringEquiv_F9 φ with hφ | hφ
  ·
    have hmap : ∀ M : Mat4, M.map φ = M := fun M => Matrix.ext fun i j => hφ _
    rw [hmap] at hfz hfa hfb
    have hdet1 : ((A : GL (Fin 4) F9) : Mat4).det = 1 := plain_det hg hfa hfb hAu
    have hAgram : (A : GL (Fin 4) F9) ∈ gramSU hU9 idG := by
      rw [mem_gramSU_iff_unitary]
      exact ⟨A.2, hdet1⟩
    have hφ1 : φ = 1 := RingEquiv.ext hφ
    have hα'A : α' = primeFormConjHom hU9 idG A := by
      rw [hA, hφ1, map_one, mul_one]
    set s : gramSU hU9 idG := ⟨(A : GL (Fin 4) F9), hAgram⟩ with hs
    have hconj : α' = MulAut.conj (s : PF) := by
      rw [hα'A]
      exact primeFormConjHom_eq_conj hU9 idG s
    refine ⟨eUXP.symm (s : PF), ?_⟩
    ext x
    apply eUXP.injective
    rw [MulAut.conj_apply, ← hα'x, hconj, MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp
  · exfalso
    have hmap : ∀ M : Mat4, M.map φ = M.map (· ^ 3) := fun M => Matrix.ext fun i j => hφ _
    rw [hmap] at hfz hfa hfb
    exact twisted_false hg hfa hfb hfz hdetA

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.StandardType.KGLangTorAUniFrame
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangTorALangElt
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
import CFSG.LocalAnalysis.StandardType.GGL45TGSU
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangTorAUniCoreAux_dvd_add_one {p x : ℕ} (hp : p.Prime) (h : p ∣ x ^ p + 1) : p ∣ x + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((x ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h1
  rw [← ZMod.natCast_eq_zero_iff]
  simpa using h1

private theorem kgLangTorAUniCoreAux_torusVec_pow_eq_one {d n : ℕ} {F : Type} [Field F] {i j : Fin d} {t : Fˣ}
    (hij : i ≠ j) (ht : t ^ (2 ^ n + 1) = 1) (k : Fin d) :
    (NbrLangTypeA.torusVec i j t k : F) ^ (2 ^ n + 1) = 1 := by
  have htF : (t : F) ^ (2 ^ n + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  rw [NbrLangTypeA.torusVec_apply]
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, if_neg hij]
    rw [Units.val_mul, Units.val_one, mul_one, htF]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl]
      rw [Units.val_mul, Units.val_one, one_mul, Units.val_inv_eq_inv_val, inv_pow, htF, inv_one]
    · rw [if_neg hkj]
      rw [Units.val_mul, Units.val_one, mul_one, one_pow]

private theorem kgLangTorAUniCoreAux_torusElt_mem_su {d n : ℕ} {F : Type} [Field F] {i j : Fin d} {t : Fˣ}
    (h : UnitaryFieldData 2 n F) (hij : i ≠ j) (ht : t ^ (2 ^ n + 1) = 1) :
    Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i j t) ∈
      LargeEvenSUGroup (Fin d) F (2 ^ n) := by
  rw [GGL45TG.SU.mem_su_iff h]
  refine ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, NbrLangTypeA.coe_torusElt,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, h.bar_apply, ← pow_succ]
      exact kgLangTorAUniCoreAux_torusVec_pow_eq_one hij ht a
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  · simpa using Matrix.SpecialLinearGroup.coeToGL_det (NbrLangTypeA.torusElt i j t)

private theorem kgLangTorAUniCoreAux_map_subtype_unitary {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    (h₀ : UnitaryFieldData 2 (n / p) (semilinearFixedSubfield σ))
    {P : GL (Fin d) (semilinearFixedSubfield σ)}
    (hP : P ∈ UnitaryHigher.primeFormUnitary h₀
      (RankThree.PartOne.KCUnitaryModel.idGram (semilinearFixedSubfield σ) d)) :
    Matrix.transpose (((↑(Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map (unitaryFieldData_of_card hn hF).bar) *
      ((↑(Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
  have hPmat : Matrix.transpose (((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
      Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map h₀.bar) *
      ((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) = 1 := by
    have hp' := hP
    rw [UnitaryHigher.mem_primeFormUnitary] at hp'
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hp'
  have hbar : (((↑(Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map (unitaryFieldData_of_card hn hF).bar) =
      (((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map h₀.bar).map
        (semilinearFixedSubfield σ).subtype := by
    ext i j
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    exact kgLangTorA_pow_eq_on_fixed hn hp hp2 hF hσ (P i j)
  rw [hbar, show Matrix.transpose ((((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map h₀.bar).map
        (semilinearFixedSubfield σ).subtype) =
      (Matrix.transpose (((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map h₀.bar)).map
        (semilinearFixedSubfield σ).subtype from Matrix.transpose_map]
  change (Matrix.transpose (((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
      Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map h₀.bar)).map
      (semilinearFixedSubfield σ).subtype *
      ((↑P : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).map
        (semilinearFixedSubfield σ).subtype = 1
  rw [← Matrix.map_mul, hPmat, Matrix.map_one _ (map_zero _) (map_one _)]

theorem kgLangTorA_uni_core_split {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    (hXf : ∀ x ∈ X, f₀ * x = x * f₀)
    (hsplit : p ∣ 2 ^ n + 1) (hcard : p ^ (d / p + 2) ≤ Nat.card X) :
    ∃ e s : GL (Fin d) F, e ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e ∧ e ^ p = 1 ∧
      e ∉ LargeEvenScalars (Fin d) F ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e ∧
      ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        B * e = e * B ∧ B * s = s * B := by
  classical
  have hd0 : 0 < d := by omega
  have hd2 : 2 ≤ d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
  obtain ⟨hpn, hcard0⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ
  set q₀ : ℕ := 2 ^ (n / p) with hq₀
  have hnpad : 1 ≤ n / p := by
    obtain ⟨k, hk⟩ := hpn
    have hk1 : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      omega
    rw [hk, Nat.mul_div_right k hp.pos]
    exact hk1
  let h₀ : UnitaryFieldData 2 (n / p) (semilinearFixedSubfield σ) :=
    unitaryFieldData_of_card hnpad hcard0
  have h2np : 2 ^ n = q₀ ^ p := by
    obtain ⟨k, hk⟩ := hpn
    have hk' : n / p = k := by rw [hk, Nat.mul_div_right k hp.pos]
    rw [hk, hq₀, hk', ← pow_mul, mul_comm]
  have hpq₀ : p ∣ q₀ + 1 := by
    have h : p ∣ q₀ ^ p + 1 := by rwa [← h2np]
    exact kgLangTorAUniCoreAux_dvd_add_one hp h
  obtain ⟨X₀, hX₀ab, hX₀U, hX₀card, hX₀last⟩ :=
    kgLangTorA_uni_frame_group hF hn hd hdq hp hp2 hσ hX hXI hf₀ hXf
  have hcardX₀ : p ^ (d / p + 2) ≤ Nat.card X₀ := hcard.trans hX₀card
  obtain ⟨P, hP, hPd⟩ := TableBUD.ggPGUTorality h₀ hp hpq₀ hX₀ab hX₀U hcardX₀
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h₀ hp hpq₀
  let ω₀ : (semilinearFixedSubfield σ)ˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hω₀p : ω₀ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hζ.pow_eq_one
  have hω₀1 : ω₀ ≠ 1 := by
    intro h
    exact hζ.ne_one hp.one_lt (Units.ext_iff.mp h)
  let ωF : Fˣ := Units.map (semilinearFixedSubfield σ).subtype ω₀
  have hωFp : ωF ^ p = 1 := by
    rw [← map_pow, hω₀p, map_one]
  have hωF1 : ωF ≠ 1 := by
    intro h
    exact hω₀1 (Units.map_injective (semilinearFixedSubfield σ).subtype_injective h)
  have hωFpF : (ωF : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hωFp, Units.val_one]
  have hωFq : (ωF : F) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hsplit
    rw [hk, pow_mul, hωFpF, one_pow]
  have hωFσ : σ (ωF : F) = (ωF : F) := by
    have hfix := RingHom.mem_eqLocusField.mp (ω₀ : semilinearFixedSubfield σ).2
    simpa [ωF] using hfix
  obtain ⟨c, hcq, hcσ⟩ :=
    kgLangTorA_hilbert90_unitary hn hF hp hσ hωFpF hωFq
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcq
    rw [zero_pow (by omega : 2 ^ n + 1 ≠ 0)] at hcq
    exact zero_ne_one hcq
  let cF : Fˣ := Units.mk0 c hc0
  have hcFq : (cF : F) ^ (2 ^ n + 1) = 1 := hcq
  have hcFσ : σ (cF : F) = (ωF : F) * (cF : F) := hcσ
  let i0 : Fin d := ⟨0, hd0⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let Dω : GL (Fin d) F :=
    Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF)
  let Dc : GL (Fin d) F :=
    Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF)
  let U : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P
  let e : GL (Fin d) F := U * Dω * U⁻¹
  let s : GL (Fin d) F := U * Dc * U⁻¹
  have hDωσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) Dω = Dω := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
      (Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF)) = _
    rw [show Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF)) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom
          (NbrLangTypeA.torusElt i0 i1 ωF)) from Units.ext rfl]
    rw [NbrLangTypeA.map_torusElt]
    have hσF : Units.map (σ : F →* F) ωF = ωF := Units.ext hωFσ
    rw [hσF]
  have hDωp : Dω ^ p = 1 := by
    show Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF) ^ p = 1
    rw [← map_pow (Matrix.SpecialLinearGroup.toGL)]
    rw [show NbrLangTypeA.torusElt i0 i1 ωF =
        (NbrLangTypeA.torusHom i0 i1) ωF from rfl]
    rw [← map_pow (NbrLangTypeA.torusHom i0 i1), hωFp, map_one, map_one]
  have hDcσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) Dc = Dω * Dc := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
      (Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF)) = _
    rw [show Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF)) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom
          (NbrLangTypeA.torusElt i0 i1 cF)) from Units.ext rfl]
    rw [NbrLangTypeA.map_torusElt]
    have hσcF : Units.map (σ : F →* F) cF = ωF * cF := Units.ext hcFσ
    rw [hσcF]
    show Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 (ωF * cF)) =
      Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF) *
        Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF)
    rw [← map_mul (Matrix.SpecialLinearGroup.toGL)]
    congr 1
    exact map_mul (NbrLangTypeA.torusHom i0 i1) ωF cF
  let h : UnitaryFieldData 2 n F := unitaryFieldData_of_card hn hF
  have h01 : i0 ≠ i1 := by
    intro hh
    have h' := congrArg Fin.val hh
    simp only [i0, i1] at h'
    omega
  have hωFu : ωF ^ (2 ^ n + 1) = 1 := by
    obtain ⟨m, hm⟩ := hsplit
    rw [hm, pow_mul, hωFp, one_pow]
  have hcFu : cF ^ (2 ^ n + 1) = 1 := Units.ext hcFq
  have hDωsu : Dω ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    kgLangTorAUniCoreAux_torusElt_mem_su h h01 hωFu
  have hDcsu : Dc ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    kgLangTorAUniCoreAux_torusElt_mem_su h h01 hcFu
  have hDωmat : Matrix.transpose ((↑Dω : Matrix (Fin d) (Fin d) F).map h.bar) *
      (↑Dω : Matrix (Fin d) (Fin d) F) = 1 :=
    ((GGL45TG.SU.mem_su_iff h).mp hDωsu).1
  have hDωdet : (↑Dω : Matrix (Fin d) (Fin d) F).det = 1 :=
    ((GGL45TG.SU.mem_su_iff h).mp hDωsu).2
  have hDcmat : Matrix.transpose ((↑Dc : Matrix (Fin d) (Fin d) F).map h.bar) *
      (↑Dc : Matrix (Fin d) (Fin d) F) = 1 :=
    ((GGL45TG.SU.mem_su_iff h).mp hDcsu).1
  have hDcdet : (↑Dc : Matrix (Fin d) (Fin d) F).det = 1 :=
    ((GGL45TG.SU.mem_su_iff h).mp hDcsu).2
  have hUmat : Matrix.transpose ((↑U : Matrix (Fin d) (Fin d) F).map h.bar) *
      (↑U : Matrix (Fin d) (Fin d) F) = 1 :=
    kgLangTorAUniCoreAux_map_subtype_unitary hF hn hp hp2 hσ h₀ hP
  have hU' : U ∈ UnitaryHigher.primeFormUnitary h
      (RankThree.PartOne.KCUnitaryModel.idGram F d) := by
    rw [UnitaryHigher.mem_primeFormUnitary]
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hUmat
  have hDω' : Dω ∈ UnitaryHigher.primeFormUnitary h
      (RankThree.PartOne.KCUnitaryModel.idGram F d) := by
    rw [UnitaryHigher.mem_primeFormUnitary]
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hDωmat
  have hDc' : Dc ∈ UnitaryHigher.primeFormUnitary h
      (RankThree.PartOne.KCUnitaryModel.idGram F d) := by
    rw [UnitaryHigher.mem_primeFormUnitary]
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hDcmat
  have hDωcoe : (↑Dω : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => (NbrLangTypeA.torusVec i0 i1 ωF k : F)) := by
    show (↑(Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF)) :
      Matrix (Fin d) (Fin d) F) = _
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, NbrLangTypeA.coe_torusElt]
  have hDωnotscal : Dω ∉ LargeEvenScalars (Fin d) F := by
    intro hsc
    rw [largeEvenScalars_def] at hsc
    obtain ⟨cc, hcc⟩ := hsc
    have hcc' : (↑Dω : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) (cc : F) := by
      rw [← hcc, Matrix.GeneralLinearGroup.coe_scalar]
    have h0 := congrFun (congrFun hcc' i0) i0
    have h1 := congrFun (congrFun hcc' i1) i1
    rw [hDωcoe, Matrix.diagonal_apply_eq, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h0 h1
    rw [NbrLangTypeA.torusVec_apply, if_pos rfl, if_neg h01, mul_one] at h0
    rw [NbrLangTypeA.torusVec_apply, if_neg (Ne.symm h01), if_pos rfl, one_mul] at h1
    have hωeq : ωF = ωF⁻¹ := Units.ext (by rw [h0, h1])
    have hω2 : ωF ^ 2 = 1 := by
      rw [pow_two, congrArg (fun x => ωF * x) hωeq, mul_inv_cancel]
    have hω1 : ωF = 1 := by
      have hg : ωF ^ Nat.gcd 2 p = 1 := (pow_gcd_eq_one).mpr ⟨hω2, hωFp⟩
      have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
      rwa [hcop.gcd_eq_one, pow_one] at hg
    exact hωF1 hω1
  have hUσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) U = U := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P) = _
    exact NbrLangTypeA.map_pow_map_subtype (σ := σ) P 1
  refine ⟨e, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GGL45TG.SU.mem_su_iff h]
    refine ⟨?_, ?_⟩
    · have he' : e ∈ UnitaryHigher.primeFormUnitary h
          (RankThree.PartOne.KCUnitaryModel.idGram F d) := by
        show U * Dω * U⁻¹ ∈ _
        exact mul_mem (mul_mem hU' hDω') (inv_mem hU')
      have h := (UnitaryHigher.mem_primeFormUnitary).mp he'
      simpa [RankThree.PartOne.KCUnitaryModel.idGram] using h
    · show (↑(U * Dω * U⁻¹) : Matrix (Fin d) (Fin d) F).det = 1
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hDωdet, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · rw [GGL45TG.SU.mem_su_iff h]
    refine ⟨?_, ?_⟩
    · have hs' : s ∈ UnitaryHigher.primeFormUnitary h
          (RankThree.PartOne.KCUnitaryModel.idGram F d) := by
        show U * Dc * U⁻¹ ∈ _
        exact mul_mem (mul_mem hU' hDc') (inv_mem hU')
      have h := (UnitaryHigher.mem_primeFormUnitary).mp hs'
      simpa [RankThree.PartOne.KCUnitaryModel.idGram] using h
    · show (↑(U * Dc * U⁻¹) : Matrix (Fin d) (Fin d) F).det = 1
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hDcdet, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · show Matrix.GeneralLinearGroup.map (σ : F →+* F) (U * Dω * U⁻¹) = U * Dω * U⁻¹
    rw [map_mul, map_mul, map_inv, hUσ, hDωσ]
  · show (U * Dω * U⁻¹) ^ p = 1
    rw [conj_pow, hDωp, mul_one, mul_inv_cancel]
  · intro hsc
    apply hDωnotscal
    have hcen : e ∈ Subgroup.center (GL (Fin d) F) := TableB.scalars_le_center hsc
    have hDωe : Dω = e := by
      have h1 : U⁻¹ * e * U = e := by
        rw [Subgroup.mem_center_iff.mp hcen U⁻¹]
        group
      rw [show Dω = U⁻¹ * (U * Dω * U⁻¹) * U from by group,
        show U * Dω * U⁻¹ = e from rfl, h1]
    rwa [hDωe]
  · have hDcomm : Dω * Dc = Dc * Dω := by
      show Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF) *
          Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF) =
        Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 cF) *
          Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ωF)
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, NbrLangTypeA.coe_torusElt,
        NbrLangTypeA.coe_torusElt, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      exact mul_comm _ _
    show Matrix.GeneralLinearGroup.map (σ : F →+* F) (U * Dc * U⁻¹) =
      (U * Dc * U⁻¹) * (U * Dω * U⁻¹)
    rw [map_mul, map_mul, map_inv, hUσ, hDcσ]
    rw [show (U * Dc * U⁻¹) * (U * Dω * U⁻¹) = U * (Dc * Dω) * U⁻¹ from by group]
    rw [hDcomm]
  · intro B hBgu x hxX hBx
    obtain ⟨cB, M, hMx, hBeq⟩ := hX₀last B hBgu x hxX hBx
    have hMdiag : (↑(P⁻¹ * M * P) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)).IsDiag := hPd M hMx
    let ιM : GL (Fin d) F :=
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M
    have hDM'eq : U⁻¹ * ιM * U =
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (P⁻¹ * M * P) := by
      show (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P)⁻¹ *
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M *
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype P = _
      rw [← map_inv, ← map_mul, ← map_mul]
    have hDM'diag : (↑(U⁻¹ * ιM * U) : Matrix (Fin d) (Fin d) F).IsDiag := by
      rw [hDM'eq]
      intro a b hab
      rw [Matrix.GeneralLinearGroup.map_apply, hMdiag hab, map_zero]
    have hDM'_torus : ∀ t : Fˣ, (U⁻¹ * ιM * U) *
        Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t) =
        Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t) * (U⁻¹ * ιM * U) := by
      intro t
      have h1 := NbrLangTypeA.slConjugation_torusElt hDM'diag i0 i1 t
      have h2 : (Matrix.SpecialLinearGroup.toGL
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F
            (U⁻¹ * ιM * U) (NbrLangTypeA.torusElt i0 i1 t)) : GL (Fin d) F) =
          (U⁻¹ * ιM * U) * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t) *
            (U⁻¹ * ιM * U)⁻¹ :=
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation d F
          (U⁻¹ * ιM * U) _
      rw [h1] at h2
      calc (U⁻¹ * ιM * U) * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t)
          = ((U⁻¹ * ιM * U) * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t) *
              (U⁻¹ * ιM * U)⁻¹) * (U⁻¹ * ιM * U) := by group
        _ = Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 t) *
              (U⁻¹ * ιM * U) := by rw [← h2]
    have hιMe : ιM * e = e * ιM := by
      have h1 : ιM = U * (U⁻¹ * ιM * U) * U⁻¹ := by group
      rw [h1]
      show (U * (U⁻¹ * ιM * U) * U⁻¹) * (U * Dω * U⁻¹) =
        (U * Dω * U⁻¹) * (U * (U⁻¹ * ιM * U) * U⁻¹)
      rw [show (U * (U⁻¹ * ιM * U) * U⁻¹) * (U * Dω * U⁻¹) =
          U * ((U⁻¹ * ιM * U) * Dω) * U⁻¹ from by group]
      rw [show (U * Dω * U⁻¹) * (U * (U⁻¹ * ιM * U) * U⁻¹) =
          U * (Dω * (U⁻¹ * ιM * U)) * U⁻¹ from by group]
      rw [hDM'_torus ωF]
    have hιMs : ιM * s = s * ιM := by
      have h1 : ιM = U * (U⁻¹ * ιM * U) * U⁻¹ := by group
      rw [h1]
      show (U * (U⁻¹ * ιM * U) * U⁻¹) * (U * Dc * U⁻¹) =
        (U * Dc * U⁻¹) * (U * (U⁻¹ * ιM * U) * U⁻¹)
      rw [show (U * (U⁻¹ * ιM * U) * U⁻¹) * (U * Dc * U⁻¹) =
          U * ((U⁻¹ * ιM * U) * Dc) * U⁻¹ from by group]
      rw [show (U * Dc * U⁻¹) * (U * (U⁻¹ * ιM * U) * U⁻¹) =
          U * (Dc * (U⁻¹ * ιM * U)) * U⁻¹ from by group]
      rw [hDM'_torus cF]
    constructor
    · rw [hBeq]
      show (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) * e =
        e * (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM)
      calc (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) * e
          = Matrix.GeneralLinearGroup.scalar (Fin d) cB * (ιM * e) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) cB * (e * ιM) := by rw [hιMe]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) cB * e) * ιM := by group
        _ = (e * Matrix.GeneralLinearGroup.scalar (Fin d) cB) * ιM := by
              rw [(TypeA.commute_scalar_GL cB e).eq]
        _ = e * (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) := by group
    · rw [hBeq]
      show (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) * s =
        s * (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM)
      calc (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) * s
          = Matrix.GeneralLinearGroup.scalar (Fin d) cB * (ιM * s) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) cB * (s * ιM) := by rw [hιMs]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) cB * s) * ιM := by group
        _ = (s * Matrix.GeneralLinearGroup.scalar (Fin d) cB) * ιM := by
              rw [(TypeA.commute_scalar_GL cB s).eq]
        _ = s * (Matrix.GeneralLinearGroup.scalar (Fin d) cB * ιM) := by group

private theorem kgLangTorAUniCoreAux_herm_smul {d n : ℕ} {F : Type} [Field F]
    (c : F) (M : Matrix (Fin d) (Fin d) F) :
    TableBUD.herm n (c • M) = c ^ (2 ^ n + 1) • TableBUD.herm n M := by
  rw [TableBUD.herm, TableBUD.herm]
  have hmap : (c • M).map (· ^ 2 ^ n) = c ^ 2 ^ n • M.map (· ^ 2 ^ n) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, mul_pow]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

private theorem kgLangTorAUniCoreAux_herm_one {d n : ℕ} {F : Type} [Field F] :
    TableBUD.herm n (1 : Matrix (Fin d) (Fin d) F) = 1 := by
  rw [TableBUD.herm]
  have hmap : (1 : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.map_apply]
    · simp [Matrix.map_apply, Matrix.one_apply, h]
  rw [hmap, Matrix.transpose_one, Matrix.one_mul]

private theorem kgLangTorAUniCoreAux_herm_scalar {d n : ℕ} {F : Type} [Field F] (c : F) :
    TableBUD.herm n (Matrix.scalar (Fin d) c) =
      c ^ (2 ^ n + 1) • (1 : Matrix (Fin d) (Fin d) F) := by
  have h : Matrix.scalar (Fin d) c = c • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h, kgLangTorAUniCoreAux_herm_smul, kgLangTorAUniCoreAux_herm_one]

private theorem kgLangTorAUniCoreAux_herm_map {d n : ℕ} {F : Type} [Field F]
    (f : F →+* F) (M : Matrix (Fin d) (Fin d) F) :
    TableBUD.herm n (M.map f) = (TableBUD.herm n M).map f := by
  rw [TableBUD.herm, TableBUD.herm]
  have h1 : (M.map f).map (· ^ 2 ^ n) = (M.map (· ^ 2 ^ n)).map f := by
    ext i j; simp [Matrix.map_apply, map_pow]
  rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul]

private theorem kgLangTorAUniCoreAux_projConj_mk {d : ℕ} {F : Type} [Field F]
    (H : Subgroup (GL (Fin d) F))
    (A : Subgroup.normalizer (H : Set (GL (Fin d) F))) (h : H) :
    TableB.projConj H A (LargeEvenProjMk H h) =
      LargeEvenProjMk H (H.normalizerMonoidHom A h) :=
  TableB.projConj_mk H A h

private theorem kgLangTorAUniCoreAux_eq_projConj_of_graph {d : ℕ} {F : Type} [Field F]
    {S : Subgroup (GL (Fin d) F)} {B : GL (Fin d) F}
    (hBnorm : B ∈ Subgroup.normalizer (S : Set (GL (Fin d) F)))
    {x : MulAut (LargeEvenProj S)}
    (hx : LargeEvenGraphAut (LargeEvenProjMk S)
      (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x) :
    x = TableB.projConj S ⟨B, hBnorm⟩ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [TableB.projConj_mk]
    exact hx g ⟨B * (g : GL (Fin d) F) * B⁻¹,
      (Subgroup.mem_normalizer_iff.mp hBnorm g).mp g.2⟩ rfl

theorem kgLangTorA_uni_core_nonsplit {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    (hXf : ∀ x ∈ X, f₀ * x = x * f₀)
    (hns : ¬ p ∣ 2 ^ n + 1) (hcard : 1 < Nat.card X) :
    ∃ e s : GL (Fin d) F, e ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e ∧ e ^ p = 1 ∧
      e ∉ LargeEvenScalars (Fin d) F ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e ∧
      ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        B * e = e * B ∧ B * s = s * B := by
  classical
  have hd0 : 0 < d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  let h : UnitaryFieldData 2 n F := unitaryFieldData_of_card hn hF
  haveI : CharP F 2 := h.charP
  haveI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set m : ℕ := 2 ^ n + 1 with hm
  have hnotp : ¬ p ∣ m := by rw [hm]; exact hns
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotp
  set N : ℕ := m ^ (p - 1) with hN
  have hp2le : 2 ≤ p := hp.two_le
  have hNm : m ∣ N := by
    rw [hN]
    simpa using pow_dvd_pow m (show 1 ≤ p - 1 by omega)
  have hNmod : N % p = 1 := by
    rw [hN]
    have hf : m ^ (p - 1) ≡ 1 [MOD p] := by
      simpa [Nat.totient_prime hp] using Nat.ModEq.pow_totient hcop.symm
    rw [Nat.ModEq] at hf
    rwa [Nat.mod_eq_of_lt hp.one_lt] at hf
  have hunit_pow : ∀ u : Fˣ, (u : F) ^ m = 1 → u ^ N = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hNm
    rw [hk, pow_mul]
    have hu' : u ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hu
    rw [hu', one_pow]
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
  have hxne : x ≠ 1 := fun hh => hx1 (Subtype.ext hh)
  have hS := TableBUE.gu_subset_normalizer (d := d) h
  obtain ⟨B, hBgu, hBx⟩ := TableB.exists_eq_projConj hS (hXI x hxX)
  have hBnorm : B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    hS hBgu
  have hBgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x := by
    intro g g' hgg'
    rw [hBx, kgLangTorAUniCoreAux_projConj_mk]
    exact congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (Subtype.ext hgg'.symm)
  obtain ⟨c, hc⟩ := kgLangTorA_uni_semifixed hF hn hd hdq hf₀ hBgu hBgraph (hXf x hxX)
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hBgu
  have hBherm : TableBUD.herm n (B : Matrix (Fin d) (Fin d) F) = μ • 1 := by
    simpa [TableBUD.herm] using hμ
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq (q := 2 ^ n) hq2 hF hμ0 hμq
  let B₁ : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * B
  have hB₁def : B₁ = Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * B := rfl
  have hB₁norm : B₁ ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := by
    rw [hB₁def]
    refine Subgroup.mul_mem _ (TableB.scalar_mem_normalizer _
      (show Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ ∈ LargeEvenScalars (Fin d) F from
        ⟨l⁻¹, rfl⟩)) hBnorm
  have hB₁coe : (B₁ : Matrix (Fin d) (Fin d) F) =
      (l : F)⁻¹ • (B : Matrix (Fin d) (Fin d) F) := by
    rw [hB₁def, TableB.coe_scalar_mul, Units.val_inv_eq_inv_val]
  have hB₁herm : TableBUD.herm n (B₁ : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [hB₁coe, kgLangTorAUniCoreAux_herm_smul]
    have hli : (l : F)⁻¹ ^ (2 ^ n + 1) = μ⁻¹ := by rw [inv_pow, hl]
    rw [hli, hBherm, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hB₁gu : B₁ ∈ LargeEvenGUSet (Fin d) F (2 ^ n) :=
    ⟨1, one_ne_zero, one_pow _, by simpa [TableBUD.herm] using hB₁herm⟩
  have hz : Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ ∈ LargeEvenScalars (Fin d) F :=
    ⟨l⁻¹, rfl⟩
  have hB₁eq : (⟨B₁, hB₁norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) =
      (⟨Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹,
          TableB.scalar_mem_normalizer _ hz⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) * ⟨B, hBnorm⟩ := by
    apply Subtype.ext
    exact hB₁def
  have hB₁ρ : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B₁, hB₁norm⟩ = x := by
    rw [hB₁eq, map_mul, TableB.projConj_of_scalar _ hz, one_mul]
    exact hBx.symm
  have hB₁graph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => (g' : GL (Fin d) F) = B₁ * g * B₁⁻¹) x := by
    intro g g' hgg'
    rw [← hB₁ρ, kgLangTorAUniCoreAux_projConj_mk]
    exact congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (Subtype.ext hgg'.symm)
  obtain ⟨c', hc'⟩ := kgLangTorA_uni_semifixed hF hn hd hdq hf₀ hB₁gu hB₁graph (hXf x hxX)
  have hc'q : (c' : F) ^ (2 ^ n + 1) = 1 := by
    have hc'mat : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) B₁ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (c' : F) • (B₁ : Matrix (Fin d) (Fin d) F) := by
      have hh := congrArg (fun z : GL (Fin d) F => (z : Matrix (Fin d) (Fin d) F)) hc'
      rw [TableB.coe_scalar_mul] at hh
      exact hh
    have hhermσ : TableBUD.herm n ((Matrix.GeneralLinearGroup.map (σ : F →+* F) B₁ :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [show ((Matrix.GeneralLinearGroup.map (σ : F →+* F) B₁ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) = (B₁ : Matrix (Fin d) (Fin d) F).map (σ : F →+* F)
          from rfl, kgLangTorAUniCoreAux_herm_map, hB₁herm]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.map_apply]
      · simp [Matrix.map_apply, Matrix.one_apply, hij]
    rw [hc'mat, kgLangTorAUniCoreAux_herm_smul, hB₁herm] at hhermσ
    have h00 := congrFun (congrFun hhermσ ⟨0, hd0⟩) ⟨0, hd0⟩
    simpa using h00
  have hc'N : c' ^ N = 1 := hunit_pow c' (by simpa [hm] using hc'q)
  let E : GL (Fin d) F := B₁ ^ N
  have hEdef : E = B₁ ^ N := rfl
  have hEherm : TableBUD.herm n (E : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [hEdef, Units.val_pow_eq_pow_val, TableBUD.herm_pow h (ν := 1) (by simpa using hB₁herm) N]
    simp
  have hdetB₁ : (B₁ : Matrix (Fin d) (Fin d) F).det ^ (2 ^ n + 1) = 1 := by
    have hd := congrArg Matrix.det hB₁herm
    rw [TableBUD.herm, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      TableBUD.map_pow_eq_map_bar h] at hd
    rw [show ((B₁ : Matrix (Fin d) (Fin d) F).map h.bar) =
        (h.bar : F →+* F).mapMatrix (B₁ : Matrix (Fin d) (Fin d) F) from rfl,
      ← RingHom.map_det, UnitaryFieldData.bar_apply] at hd
    rwa [← pow_succ] at hd
  have hdetpow : ∀ k : ℕ, ((B₁ ^ k : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det =
      (B₁ : Matrix (Fin d) (Fin d) F).det ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Units.val_mul, Matrix.det_mul, ih, pow_succ]
  have hdetE : (E : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [hEdef, hdetpow]
    obtain ⟨k, hk⟩ := hNm
    rw [hk, pow_mul, hdetB₁, one_pow]
  have hEsu : E ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    rw [GGL45TG.SU.mem_su_iff h]
    exact ⟨by rw [← TableBUD.map_pow_eq_map_bar h]; exact hEherm, hdetE⟩
  have hEσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) E = E := by
    rw [hEdef, map_pow, hc', (TypeA.commute_scalar_GL c' B₁).mul_pow, ← map_pow, hc'N,
      map_one, one_mul]
  have hB₁pρ : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
      ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ p) = 1 := by
    rw [map_pow, hB₁ρ, hX.2 x hxX]
  obtain ⟨u, hu⟩ := kgLangTorA_uni_scalar hF hn hd hdq hB₁pρ
  have hu' : B₁ ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) u := by simpa using hu.symm
  have huq : (u : F) ^ (2 ^ n + 1) = 1 := by
    have h1 : TableBUD.herm n ((B₁ ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [Units.val_pow_eq_pow_val, TableBUD.herm_pow h (ν := 1) (by simpa using hB₁herm) p]
      simp
    rw [hu', Matrix.GeneralLinearGroup.coe_scalar, kgLangTorAUniCoreAux_herm_scalar] at h1
    have h00 := congrFun (congrFun h1 ⟨0, hd0⟩) ⟨0, hd0⟩
    simpa using h00
  have huN : u ^ N = 1 := hunit_pow u (by simpa [hm] using huq)
  have hEp : E ^ p = 1 := by
    have h1 : (B₁ ^ N) ^ p = (B₁ ^ p) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hEdef, h1, hu', ← map_pow, huN, map_one]
  have hEρ : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
      ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N) = x := by
    rw [map_pow, hB₁ρ, pow_eq_pow_mod N (hX.2 x hxX), hNmod, pow_one]
  have he_not_scalar : E ∉ LargeEvenScalars (Fin d) F := by
    intro hEsc
    have h1 : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
          (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N) = 1 := by
      have h3 : ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
          (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N) =
          (⟨(E : GL (Fin d) F), TableB.scalar_mem_normalizer _ hEsc⟩ :
            Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) := by
        apply Subtype.ext
        rfl
      rw [h3]
      exact TableB.projConj_of_scalar _ hEsc
    rw [hEρ] at h1
    exact hxne h1
  have he_comm : ∀ B' ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x' ∈ X,
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (fun g g' => (g' : GL (Fin d) F) = B' * g * B'⁻¹) x' →
      B' * E = E * B' := by
    intro B' hB'gu x' hx'X hB'x'
    have hB'norm : B' ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := hS hB'gu
    have hB'ρ : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n)) ⟨B', hB'norm⟩ = x' :=
      (kgLangTorAUniCoreAux_eq_projConj_of_graph hB'norm hB'x').symm
    have hζρ : TableB.projConj (LargeEvenSUGroup (Fin d) F (2 ^ n))
        ((⟨B', hB'norm⟩ : Subgroup.normalizer
            (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) *
          (⟨B₁, hB₁norm⟩ : Subgroup.normalizer
            (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N *
          (⟨B', hB'norm⟩ : Subgroup.normalizer
            (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))⁻¹ *
          ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
            (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hB'ρ, hEρ]
      have hcommx : x' * x = x * x' :=
        congrArg Subtype.val (hX.1.is_comm.comm ⟨x', hx'X⟩ ⟨x, hxX⟩)
      rw [hcommx]
      group
    obtain ⟨uζ, huζ⟩ := kgLangTorA_uni_scalar hF hn hd hdq hζρ
    let Z : GL (Fin d) F := ((⟨B', hB'norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) *
      (⟨B₁, hB₁norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N *
      (⟨B', hB'norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))⁻¹ *
      ((⟨B₁, hB₁norm⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) ^ N)⁻¹)
    have hZeq : Z = Matrix.GeneralLinearGroup.scalar (Fin d) uζ := huζ.symm
    have hZE : Z * E = B' * E * B'⁻¹ := by
      show ((B' * E * B'⁻¹ * E⁻¹) * E : GL (Fin d) F) = B' * E * B'⁻¹
      group
    have hconjE : B' * E * B'⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) uζ * E := by
      rw [← hZE, hZeq]
    have huζp : uζ ^ p = 1 := by
      have h1 : (B' * E * B'⁻¹) ^ p = 1 := by rw [conj_pow, hEp, mul_one, mul_inv_cancel]
      have h2 : (Matrix.GeneralLinearGroup.scalar (Fin d) uζ * E) ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin d) (uζ ^ p) := by
        rw [(TypeA.commute_scalar_GL uζ E).mul_pow, ← map_pow, hEp, mul_one]
      have h3 : Matrix.GeneralLinearGroup.scalar (Fin d) (uζ ^ p) = 1 := by
        rw [← h2, ← hconjE]; exact h1
      exact TypeA.PGLTor.scalar_injective (by rw [h3, map_one])
    have huζq : uζ ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      obtain ⟨ν, hν0, hνq, hν⟩ := hB'gu
      have hν' : Matrix.transpose ((B' : Matrix (Fin d) (Fin d) F).map h.bar) *
          (B' : Matrix (Fin d) (Fin d) F) = ν • 1 := by
        rwa [← TableBUD.map_pow_eq_map_bar h]
      have hEbar : Matrix.transpose ((E : Matrix (Fin d) (Fin d) F).map h.bar) *
          (E : Matrix (Fin d) (Fin d) F) = 1 := by
        rwa [← TableBUD.map_pow_eq_map_bar h]
      have hPQ : (B' : Matrix (Fin d) (Fin d) F) *
          ((B'⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hcu := TableB.conj_unitary_of_similitude h.bar hν' hPQ hEbar
      have hZEherm : TableBUD.herm n ((Z * E : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
        have hval : ((Z * E : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
            (B' : Matrix (Fin d) (Fin d) F) * (E : Matrix (Fin d) (Fin d) F) *
              ((B'⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
          rw [hZE, Units.val_mul, Units.val_mul]
        rw [hval, TableBUD.herm, TableBUD.map_pow_eq_map_bar h]
        exact hcu
      have hcoeeq : ((Z * E : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          (uζ : F) • (E : Matrix (Fin d) (Fin d) F) := by
        rw [hZE, hconjE, TableB.coe_scalar_mul]
      rw [hcoeeq, kgLangTorAUniCoreAux_herm_smul, hEherm] at hZEherm
      have h00 := congrFun (congrFun hZEherm ⟨0, hd0⟩) ⟨0, hd0⟩
      simpa [hm] using h00
    have huζ1 : uζ = 1 := by
      have hg : uζ ^ Nat.gcd p m = 1 := (pow_gcd_eq_one).mpr ⟨huζp, huζq⟩
      rw [hcop.gcd_eq_one, pow_one] at hg
      exact hg
    have hZ1 : Z = 1 := by rw [hZeq, huζ1, map_one]
    have hcomm1 : B' * E * B'⁻¹ * E⁻¹ = 1 := by
      show Z = 1
      exact hZ1
    have hconj : B' * E * B'⁻¹ = E := by
      rw [← mul_inv_eq_one]
      exact hcomm1
    calc B' * E = (B' * E * B'⁻¹) * B' := by group
      _ = E * B' := by rw [hconj]
  obtain ⟨s₀, P₀, hs₀P, hs₀σ⟩ := kgLangTorA_lang_poly hp hσ hEσ hEp
  obtain ⟨s₁, P₁, hs₁P, hs₁herm, hs₁σ⟩ :=
    kgLangTorA_unitary_correct hp hp2 hF hEherm hEσ hEp hs₀P hs₀σ
  have hs₁P'mat : (s₁ : Matrix (Fin d) (Fin d) F) =
      P₁.smeval (E : Matrix (Fin d) (Fin d) F) := by
    rw [hs₁P, Polynomial.aeval_eq_smeval]
  have hs₁E : s₁ * E = E * s₁ := Units.ext <| by
    show (s₁ : Matrix (Fin d) (Fin d) F) * (E : Matrix (Fin d) (Fin d) F) =
      (E : Matrix (Fin d) (Fin d) F) * (s₁ : Matrix (Fin d) (Fin d) F)
    rw [hs₁P'mat]
    exact (Polynomial.smeval_commute_left F P₁ (Commute.refl (E : Matrix (Fin d) (Fin d) F))).eq
  let s : GL (Fin d) F := s₁ ^ N
  have hsdef : s = s₁ ^ N := rfl
  have hsσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * E :=
    kgLangTorA_pow_lang hs₁E hEp hs₁σ hNmod
  have hsherm : TableBUD.herm n (s : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [hsdef, Units.val_pow_eq_pow_val,
      TableBUD.herm_pow h (ν := 1) (by simpa [TableBUD.herm] using hs₁herm) N]
    simp
  have hsdetq : (s₁ : Matrix (Fin d) (Fin d) F).det ^ (2 ^ n + 1) = 1 := by
    have hd := congrArg Matrix.det hs₁herm
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      TableBUD.map_pow_eq_map_bar h] at hd
    rw [show ((s₁ : Matrix (Fin d) (Fin d) F).map h.bar) =
        (h.bar : F →+* F).mapMatrix (s₁ : Matrix (Fin d) (Fin d) F) from rfl,
      ← RingHom.map_det, UnitaryFieldData.bar_apply] at hd
    rwa [← pow_succ] at hd
  have hdetpow₁ : ∀ k : ℕ, ((s₁ ^ k : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det =
      (s₁ : Matrix (Fin d) (Fin d) F).det ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Units.val_mul, Matrix.det_mul, ih, pow_succ]
  have hsdet : (s : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [hsdef, hdetpow₁]
    obtain ⟨k, hk⟩ := hNm
    rw [hk, pow_mul, hsdetq, one_pow]
  have hssu : s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    rw [GGL45TG.SU.mem_su_iff h]
    exact ⟨by rw [← TableBUD.map_pow_eq_map_bar h]; exact hsherm, hsdet⟩
  have hs_comm : ∀ B' ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x' ∈ X,
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (fun g g' => (g' : GL (Fin d) F) = B' * g * B'⁻¹) x' →
      B' * s = s * B' := by
    intro B' hB'gu x' hx'X hB'x'
    have hB'E : B' * E = E * B' := he_comm B' hB'gu x' hx'X hB'x'
    have hB'Emat : Commute (B' : Matrix (Fin d) (Fin d) F) (E : Matrix (Fin d) (Fin d) F) := by
      rw [commute_iff_eq]
      have hh := congrArg (fun z : GL (Fin d) F => (z : Matrix (Fin d) (Fin d) F)) hB'E
      simpa [Units.val_mul] using hh
    have hs₁B_mat : Commute (s₁ : Matrix (Fin d) (Fin d) F) (B' : Matrix (Fin d) (Fin d) F) := by
      rw [hs₁P'mat]
      exact Polynomial.smeval_commute_left F P₁ hB'Emat.symm
    have hs₁B : s₁ * B' = B' * s₁ := Units.ext hs₁B_mat.eq
    have hpow : Commute s₁ B' := hs₁B
    have := (hpow.pow_left N).eq
    rw [hsdef]
    exact this.symm
  refine ⟨E, s, hEsu, hssu, hEσ, hEp, he_not_scalar, hsσ, ?_⟩
  intro B' hB'gu x' hx'X hB'x'
  exact ⟨he_comm B' hB'gu x' hx'X hB'x', hs_comm B' hB'gu x' hx'X hB'x'⟩

theorem kgLangTorA_uni_core {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    (hXf : ∀ x ∈ X, f₀ * x = x * f₀)
    (hcard : 1 < Nat.card X) (hsplit : p ∣ 2 ^ n + 1 → p ^ (d / p + 2) ≤ Nat.card X) :
    ∃ e s : GL (Fin d) F, e ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e ∧ e ^ p = 1 ∧
      e ∉ LargeEvenScalars (Fin d) F ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e ∧
      ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        B * e = e * B ∧ B * s = s * B := by
  by_cases h : p ∣ 2 ^ n + 1
  · exact kgLangTorA_uni_core_split hF hn hd hdq hp hp2 hσ hX hXI hf₀ hXf h (hsplit h)
  · exact kgLangTorA_uni_core_nonsplit hF hn hd hdq hp hp2 hσ hX hXI hf₀ hXf h hcard

end CFSG.StandardType

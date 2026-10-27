module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniFixed
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniWeight
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniCore
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

private theorem kgLangS1AUniFrameAux_dvd_add_one {p x : ℕ} (hp : p.Prime)
    (h : p ∣ x ^ p + 1) : p ∣ x + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((x ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h1
  rw [← ZMod.natCast_eq_zero_iff]
  simpa using h1

private theorem kgLangS1AUniFrameAux_map_subtype_unitary {d n p : ℕ} {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    (h₀ : UnitaryFieldData 2 (n / p) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ))
    {P : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)}
    (hP : P ∈ UnitaryHigher.primeFormUnitary h₀
      (RankThree.PartOne.KCUnitaryModel.idGram
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ) d)) :
    Matrix.transpose (((↑(Matrix.GeneralLinearGroup.map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (unitaryFieldData_of_card hn hF).bar) *
      ((↑(Matrix.GeneralLinearGroup.map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
  have hPmat : Matrix.transpose (((↑P : GL (Fin d)
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) : Matrix (Fin d) (Fin d)
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map h₀.bar) *
      ((↑P : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) = 1 := by
    have hp' := hP
    rw [UnitaryHigher.mem_primeFormUnitary] at hp'
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hp'
  have hbar : (((↑(Matrix.GeneralLinearGroup.map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype P) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (unitaryFieldData_of_card hn hF).bar) =
      (((↑P : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map h₀.bar).map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype := by
    ext i j
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    exact kgLangTorA_pow_eq_on_fixed hn hp hp2 hF hσ (P i j)
  rw [hbar, show Matrix.transpose ((((↑P : GL (Fin d)
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map h₀.bar).map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype) =
      (Matrix.transpose (((↑P : GL (Fin d)
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map h₀.bar)).map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype from Matrix.transpose_map]
  change (Matrix.transpose (((↑P : GL (Fin d)
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
      Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map h₀.bar)).map
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype *
      ((↑P : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).map
        (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype = 1
  rw [← Matrix.map_mul, hPmat, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem kgLangS1AUniFrameAux_scalar_cancel {d : ℕ} {F : Type} [Field F]
    {c c' : Fˣ} {X Y : GL (Fin d) F}
    (h : (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c * X)) :
    X * Y = Y * X := by
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin d) c *
      Matrix.GeneralLinearGroup.scalar (Fin d) c') * (X * Y) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) c' *
        Matrix.GeneralLinearGroup.scalar (Fin d) c) * (Y * X) := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin d) c *
        Matrix.GeneralLinearGroup.scalar (Fin d) c') * (X * Y)
        = (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) :=
            Commute.mul_mul_mul_comm (TypeA.PGLTor.commute_scalar c' X)
              (Matrix.GeneralLinearGroup.scalar (Fin d) c) Y
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c' * Y) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c * X) := h
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          Matrix.GeneralLinearGroup.scalar (Fin d) c) * (Y * X) :=
            Commute.mul_mul_mul_comm (TypeA.PGLTor.commute_scalar c Y).symm
              (Matrix.GeneralLinearGroup.scalar (Fin d) c') X
  rw [← map_mul, ← map_mul, mul_comm c' c] at h1
  exact mul_left_cancel h1

theorem kgLangS1A_uni_frame {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) (hd : d = p ∨ d = 2 * p) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian p X)
    (hXI : ∀ x ∈ X, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    {f₀ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hf₀ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (fun g g' => ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ) f₀)
    (hXf : ∀ x ∈ X, f₀ * x = x * f₀) (hsplit : p ∣ 2 ^ n + 1) (hcard : p ^ 2 ≤ Nat.card X)
    (hab : ∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
      ∀ B' ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x' ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B' * g * B'⁻¹) x' → B * B' = B' * B) :
    ∃ (U : GL (Fin d) F) (a : Fin d → ℤ),
      Matrix.GeneralLinearGroup.map (σ : F →+* F) U = U ∧
      U ∈ TableB.unitGroup (ι := Fin d) h.bar ∧
      (∀ B ∈ LargeEvenGUSet (Fin d) F (2 ^ n), ∀ x ∈ X,
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
          (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹) x →
        ∀ i j, a i ≠ a j → ((U⁻¹ * B * U : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0) ∧
      ∑ i, a i = 0 ∧ ∃ i j, ¬ (p : ℤ) ∣ a i - a j := by
  classical
  have hn : 1 ≤ n := h.one_le
  have hF : Nat.card F = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have hp3 : 3 ≤ p := by
    have hpl := hp.two_le
    omega
  have hd3 : 3 ≤ d := by
    rcases hd with hdp | hdp <;> omega
  haveI : CharP F 2 := h.charP
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GroupTheory.SteinbergBK.semilinearFixedSubfield σ) := Fintype.ofFinite _
  let ι : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ) →* GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype
  obtain ⟨hpn, hcard0⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ
  have hnpad : 1 ≤ n / p := by
    obtain ⟨k, hk⟩ := hpn
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', mul_zero] at hk
      omega
    rw [hk, Nat.mul_div_right k hp.pos]
    exact hk1
  have hpow : (2 ^ (n / p)) ^ p = 2 ^ n := by
    obtain ⟨k, hk⟩ := hpn
    have hk' : n / p = k := by rw [hk, Nat.mul_div_right k hp.pos]
    rw [hk', ← pow_mul, hk, mul_comm]
  have hpq : p ∣ 2 ^ (n / p) + 1 := by
    apply kgLangS1AUniFrameAux_dvd_add_one hp
    rw [hpow]
    exact hsplit
  have h₀ : UnitaryFieldData 2 (n / p)
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ) :=
    unitaryFieldData_of_card hnpad hcard0
  obtain ⟨S, hmemS, hprojS, hcardS, hSgu, hdecomp⟩ :=
    kgLangS1A_uni_fixed_group hF hn hd3 hdq hp hp2 hσ hX hXI hf₀ hXf
  have hSnorm : LargeEvenGUSet (Fin d) F (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    TableBUE.gu_subset_normalizer h
  let H : Subgroup (GL (Fin d) F) := LargeEvenSUGroup (Fin d) F (2 ^ n)
  have hcomm : ∀ M ∈ S, ∀ N ∈ S, M * N = N * M := by
    intro M hMS N hNS
    obtain ⟨hMn, hMX⟩ := (hmemS M).mp hMS
    obtain ⟨hNn, hNX⟩ := (hmemS N).mp hNS
    obtain ⟨B, hBgu, hBx⟩ := TableB.exists_eq_projConj hSnorm
      (hXI (TableB.projConj H ⟨ι M, hMn⟩) hMX)
    obtain ⟨B', hB'gu, hB'x⟩ := TableB.exists_eq_projConj hSnorm
      (hXI (TableB.projConj H ⟨ι N, hNn⟩) hNX)
    have hgraphB : LargeEvenGraphAut (LargeEvenProjMk H)
        (fun g g' => (g' : GL (Fin d) F) = B * g * B⁻¹)
        (TableB.projConj H ⟨ι M, hMn⟩) := by
      rw [hBx]
      intro g g' hgg'
      change TableB.projConj H ⟨B, hSnorm hBgu⟩ (g : LargeEvenProj H) =
        (g' : LargeEvenProj H)
      rw [TableB.projConj_mk, QuotientGroup.eq]
      have hA : (Subgroup.normalizerMonoidHom H ⟨B, hSnorm hBgu⟩ g : H) = g' := by
        apply Subtype.ext
        change (↑(SMul.smul (⟨B, hSnorm hBgu⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) g : H) : GL (Fin d) F) =
          (g' : GL (Fin d) F)
        rw [Subgroup.smul_coe, Subgroup.coe_inv]
        exact hgg'.symm
      rw [hA, inv_mul_cancel]
      exact Subgroup.one_mem _
    have hgraphB' : LargeEvenGraphAut (LargeEvenProjMk H)
        (fun g g' => (g' : GL (Fin d) F) = B' * g * B'⁻¹)
        (TableB.projConj H ⟨ι N, hNn⟩) := by
      rw [hB'x]
      intro g g' hgg'
      change TableB.projConj H ⟨B', hSnorm hB'gu⟩ (g : LargeEvenProj H) =
        (g' : LargeEvenProj H)
      rw [TableB.projConj_mk, QuotientGroup.eq]
      have hA : (Subgroup.normalizerMonoidHom H ⟨B', hSnorm hB'gu⟩ g : H) = g' := by
        apply Subtype.ext
        change (↑(SMul.smul (⟨B', hSnorm hB'gu⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) g : H) : GL (Fin d) F) =
          (g' : GL (Fin d) F)
        rw [Subgroup.smul_coe, Subgroup.coe_inv]
        exact hgg'.symm
      rw [hA, inv_mul_cancel]
      exact Subgroup.one_mem _
    have hBB' : B * B' = B' * B :=
      hab B hBgu (TableB.projConj H ⟨ι M, hMn⟩) hMX hgraphB
        B' hB'gu (TableB.projConj H ⟨ι N, hNn⟩) hNX hgraphB'
    have hmemM : B * (ι M)⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin d) F)) :=
      Subgroup.mul_mem _ (hSnorm hBgu) (Subgroup.inv_mem _ hMn)
    have hprojM : TableB.projConj H ⟨B * (ι M)⁻¹, hmemM⟩ = 1 := by
      rw [show (⟨B * (ι M)⁻¹, hmemM⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) =
          (⟨B, hSnorm hBgu⟩ : Subgroup.normalizer (H : Set (GL (Fin d) F))) *
            (⟨ι M, hMn⟩ : Subgroup.normalizer (H : Set (GL (Fin d) F)))⁻¹
          from Subtype.ext rfl,
        map_mul, map_inv, ← hBx]
      simp
    have hkerM : B * (ι M)⁻¹ ∈ LargeEvenScalars (Fin d) F :=
      kgLangTorA_uni_scalar hF hn hd3 hdq hprojM
    obtain ⟨c, hc⟩ := hkerM
    have hBeq : B = Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M := by
      rw [hc]
      group
    have hmemN : B' * (ι N)⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin d) F)) :=
      Subgroup.mul_mem _ (hSnorm hB'gu) (Subgroup.inv_mem _ hNn)
    have hprojN : TableB.projConj H ⟨B' * (ι N)⁻¹, hmemN⟩ = 1 := by
      rw [show (⟨B' * (ι N)⁻¹, hmemN⟩ :
            Subgroup.normalizer (H : Set (GL (Fin d) F))) =
          (⟨B', hSnorm hB'gu⟩ : Subgroup.normalizer (H : Set (GL (Fin d) F))) *
            (⟨ι N, hNn⟩ : Subgroup.normalizer (H : Set (GL (Fin d) F)))⁻¹
          from Subtype.ext rfl,
        map_mul, map_inv, ← hB'x]
      simp
    have hkerN : B' * (ι N)⁻¹ ∈ LargeEvenScalars (Fin d) F :=
      kgLangTorA_uni_scalar hF hn hd3 hdq hprojN
    obtain ⟨c', hc'⟩ := hkerN
    have hB'eq : B' = Matrix.GeneralLinearGroup.scalar (Fin d) c' * ι N := by
      rw [hc']
      group
    have hscaled : (Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c' * ι N) =
        (Matrix.GeneralLinearGroup.scalar (Fin d) c' * ι N) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M) := by
      simpa only [hBeq, hB'eq] using hBB'
    have hι : ι M * ι N = ι N * ι M :=
      kgLangS1AUniFrameAux_scalar_cancel hscaled
    have hmap : ι (M * N) = ι (N * M) := by
      rw [map_mul, map_mul, hι]
    exact Matrix.GeneralLinearGroup.map_injective
      (f := (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype)
      (GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype_injective hmap
  have hcardS' : p ^ 2 *
      (Nat.card (GroupTheory.SteinbergBK.semilinearFixedSubfield σ) - 1) ≤ Nat.card S := by
    rw [hcardS]
    exact Nat.mul_le_mul_right _ hcard
  obtain ⟨P, hP, a, hdiag, hsum, hne⟩ :=
    kgLangS1A_uni_weight h₀ hp hpq hd hprojS hcomm hSgu hcardS'
  let U : GL (Fin d) F := ι P
  have hbar_eq : h.bar = (unitaryFieldData_of_card hn hF).bar := by
    ext c
    simp only [UnitaryFieldData.bar_apply h,
      UnitaryFieldData.bar_apply (unitaryFieldData_of_card hn hF)]
  have hUσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) U = U := by
    dsimp only [U]
    simpa using NbrLangTypeA.map_pow_map_subtype (σ := σ)
      (N₀ := (P : GL (Fin d) (GroupTheory.SteinbergBK.semilinearFixedSubfield σ))) 1
  have hU : U ∈ TableB.unitGroup (ι := Fin d) h.bar := by
    rw [TableB.mem_unitGroup, hbar_eq]
    exact kgLangS1AUniFrameAux_map_subtype_unitary hF hn hp hp2 hσ h₀ hP
  refine ⟨U, a, hUσ, hU, ?_, hsum, hne⟩
  intro B hBgu x hxX hBx
  obtain ⟨c, M, hMS, hBeq⟩ := hdecomp B hBgu x hxX hBx
  have hBeq' : B = Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M := by
    simpa only [ι] using hBeq
  have hconj : U⁻¹ * B * U = Matrix.GeneralLinearGroup.scalar (Fin d) c *
      ι (P⁻¹ * M * P) := by
    rw [hBeq']
    calc U⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) c * ι M) * U
        = Matrix.GeneralLinearGroup.scalar (Fin d) c * (U⁻¹ * ι M * U) := by
            rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm c U⁻¹]
            group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * ι (P⁻¹ * M * P) := by
            congr 1
            dsimp only [U]
            simp only [map_mul, map_inv]
  intro i j hij
  rw [hconj, TableB.coe_scalar_mul, Matrix.smul_apply,
    Matrix.GeneralLinearGroup.map_apply, hdiag M hMS i j hij]
  simp

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeReduce
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Iso
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Lag

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUD TableBUE TableBU63
  TableBUI
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

namespace LID63

variable {K : Type} [Field K] {n d : ℕ}

theorem isSemilin_projConj
    (D : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    IsSemilin (projU n d K) (TableB.projConj (unitarySU 2 n K d) D) (D : GL (Fin d) K) 1 := by
  intro u v huv
  rw [map_one, MulAut.one_apply] at huv
  refine Eq.trans ?_ (congrArg (projU n d K) (Subtype.ext huv.symm) :
    projU n d K ((unitarySU 2 n K d).normalizerMonoidHom D u) = projU n d K v)
  rfl

theorem exists_unitary_frame63 [Finite K] {h : UnitaryFieldData 2 n K}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))))}
    (hAb : IsElemAbelian 3 Ab) (hAbD : Ab ≤ inndiagU h (by omega)) (hcard : 3 ^ 3 ≤ Nat.card Ab)
    (hV : ∃ V : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))), V ≠ ⊥ ∧
      IsPGroup 2 V ∧ ∀ φ ∈ Ab, ∀ v ∈ V, φ v ∈ V) :
    ∃ P ∈ primeFormUnitary h (idGram K 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer h hM⟩ := by
  classical
  have hd : 3 ≤ 6 := by norm_num
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  have hkerψ := ker_innU_le_center hK hd hdq
  have hlin : ∀ e ∈ Ab, ∃ B ∈ primeFormUnitary h (idGram K 6),
      IsSemilin (projU n 6 K) e B 1 := by
    intro e he
    obtain ⟨B, hB, hsl⟩ := exists_isSemilin h hd hq e
    have hF : fieldFactorU h hd hq e = 1 := by
      have := hAbD he
      rw [← ker_fieldFactorU h hd hq] at this
      exact this
    rw [hF] at hsl
    exact ⟨B, hB, hsl⟩
  have hEA : ∀ e ∈ Ab, ∃ A, (e, A) ∈ SUTorus.suPairs (innU n 6 K) := by
    intro e he
    obtain ⟨B, hB, hsl⟩ := hlin e he
    exact ⟨B, mem_suPairs_innU hB hsl⟩
  have hEC : Ab ⊓ Subgroup.centralizer ((innU n 6 K).range : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨-, hec⟩
    rw [Subgroup.mem_bot]
    ext r
    obtain ⟨u, rfl⟩ := projU_surjective r
    apply hcinj
    have h1 := Subgroup.mem_centralizer_iff.mp hec (innU n 6 K u) ⟨u, rfl⟩
    have h2 : MulAut.conj (e (projU n 6 K u)) = e * MulAut.conj (projU n 6 K u) * e⁻¹ := by
      ext y
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
        MulEquiv.apply_symm_apply]
    rw [MulAut.one_apply, h2]
    change e * innU n 6 K u * e⁻¹ = innU n 6 K u
    rw [← h1, mul_inv_cancel_right]
  set Ĝ := SUTorus.inducedMatrices (innU n 6 K) Ab with hĜdef
  have hĜ : TypeA.PGLTor.IsProjElem 3 Ĝ :=
    SUTorus.isProjElem_inducedMatrices h hd hdq hp hpq hkerψ hAb
  have hcardĜ : Nat.card Ĝ = Nat.card Ab * (Nat.card K - 1) :=
    SUTorus.card_inducedMatrices h hd hdq hp hpq hkerψ hEA hEC
  have hGu : ∀ x ∈ Ĝ, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c * x ∈
      primeFormUnitary h (idGram K 6) := by
    intro x hx
    obtain ⟨e, he, hex⟩ := SUTorus.mem_inducedMatrices.mp hx
    obtain ⟨B, hB, hsl⟩ := hlin e he
    obtain ⟨c, hc⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hd hdq hp hpq hkerψ
      (mem_suPairs_innU hB hsl) hex
    refine ⟨c⁻¹, ?_⟩
    rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    exact hB
  obtain ⟨V, hV1, hV2, hEbV⟩ := hV
  set V' := V.map (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) →*
    MulAut _) with hV'
  have hV'1 : V' ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hcinj]
    exact hV1
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hV'φ : V' ≤ (innU n 6 K).range := by
    rintro _ ⟨v, -, rfl⟩
    obtain ⟨u, rfl⟩ := projU_surjective v
    exact ⟨u, rfl⟩
  have hconjE : ∀ (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))))
      (v : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))),
      α * MulAut.conj v * α⁻¹ = MulAut.conj (α v) := by
    intro α v
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  have hBV : Ab ≤ Subgroup.normalizer (V' : Set (MulAut _)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hconjE]
      exact ⟨e v, hEbV e he v hv, rfl⟩
    · rintro ⟨v, hv, hve⟩
      have hy : y = MulAut.conj (e⁻¹ v) := by
        rw [← hconjE, hve]
        group
      rw [hy]
      exact ⟨e⁻¹ v, hEbV _ (Ab.inv_mem he) v hv, rfl⟩
  obtain ⟨R, hR0, hRi, hRinv⟩ := exists_stable_isotropic h hkerψ hV'1 hV'2 hV'φ hBV
  have hRG : ∀ x ∈ Ĝ, ∀ v ∈ R, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v ∈ R := by
    intro x hx v hv
    obtain ⟨e, he, hex⟩ := SUTorus.mem_inducedMatrices.mp hx
    exact hRinv e x he hex v hv
  have hk2 := two_mul_finrank_le h hRi
  have hk0 : 0 < Module.finrank K R := by
    rcases Nat.eq_zero_or_pos (Module.finrank K R) with h0 | h0
    · exact absurd (Submodule.finrank_eq_zero.mp h0) hR0
    · exact h0
  have hlag : Module.finrank K R = 3 → False := by
    intro hR3
    have h1 := card_le_of_lagrangian h hK hpq hĜ hGu hRi hR3 hRG
    rw [hcardĜ] at h1
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    have h2 : 27 * (Nat.card K - 1) ≤ Nat.card Ab * (Nat.card K - 1) :=
      Nat.mul_le_mul_right _ (by norm_num at hcard; omega)
    omega
  by_contra hnofr
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := fun a ha => mem_conjImage_of_mem_inndiagU h (hAbD ha)
  rcases fieldType_or_heis h hK hpq hAb hAbI hcard hnofr with
    ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ |
    ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3, hz3, hζ3, hζ1, hxy, hxz, hyz,
      hzs⟩
  ·
    have hMG : (M : GL (Fin 6) K) ∈ Ĝ :=
      SUTorus.mem_inducedMatrices.mpr ⟨_, hMA, mem_suPairs_innU hMu (isSemilin_projConj ⟨M, hMN⟩)⟩
    have hRM := hRG M hMG
    set f : Module.End K R := LinearMap.restrict (Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K))
      (fun v hv => by rw [Matrix.toLin'_apply]; exact hRM v hv) with hf
    have hfpow : ∀ (k : ℕ) (v : R), (((f ^ k) v : R) : Fin 6 → K) =
        ((M : Matrix (Fin 6) (Fin 6) K) ^ k) *ᵥ (v : Fin 6 → K) := by
      intro k
      induction k with
      | zero => intro v; simp
      | succ k ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← mulVec_mulVec]
        simp [hf]
    have hf3 : f ^ 3 = (l : K) • (1 : Module.End K R) := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [hfpow, ← Units.val_pow_eq_pow_val, hM3]
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hdet := congrArg LinearMap.det hf3
    rw [map_pow, LinearMap.det_smul, map_one, mul_one] at hdet
    have hl0 : (l : K) ≠ 0 := l.ne_zero
    have hk3 : Module.finrank K R ≠ 3 := fun h3 => hlag h3
    obtain hk | hk : Module.finrank K R = 1 ∨ Module.finrank K R = 2 := by omega
    · rw [hk, pow_one] at hdet
      have hδ : LinearMap.det f ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num)] at hdet
        exact hl0 hdet.symm
      exact hl (Units.mk0 _ hδ) (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet]))
    · rw [hk] at hdet
      have hδ : LinearMap.det f ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num)] at hdet
        exact pow_ne_zero 2 hl0 hdet.symm
      exact hl (Units.mk0 ((l : K) / LinearMap.det f) (div_ne_zero hl0 hδ)) (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow, hdet]
        field_simp))
  ·
    exact not_normalizes_twoSubgroup h hK hpq (U := V') hV'1 hV'2 hxu hyu hzu hxN hyN hzN
      (hBV hxA) (hBV hyA) (hBV hzA) hx3 hz3 hζ3 hζ1 hxy hxz hyz hzs

theorem exists_frame_inndiag63 [Finite K] {h : UnitaryFieldData 2 n K}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {E₀ : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))))}
    (hE₀ : IsElemAbelian 3 E₀) (hE₀D : E₀ ≤ inndiagU h (by omega)) (h27 : 3 ^ 3 ≤ Nat.card E₀)
    (hV : ∃ V : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))), V ≠ ⊥ ∧
      IsPGroup 2 V ∧ ∀ φ ∈ E₀, ∀ v ∈ V, φ v ∈ V) :
    ∃ (Q : GL (Fin 6) K) (hQ : Q ∈ primeFormUnitary h (idGram K 6)), ∀ e ∈ E₀,
      ∃ σ : Fin 6 → Kˣ, σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧ FrameAct h Q hQ e σ := by
  classical
  have hd : 3 ≤ 6 := by norm_num
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨P, hP, hPd⟩ := exists_unitary_frame63 hK hpq hE₀ hE₀D h27 hV
  refine ⟨P, hP, fun e he => ?_⟩
  obtain ⟨M, hM, hMd, heM⟩ := hPd e he
  obtain ⟨u, hu⟩ := exists_unitary_of_gu h hM
  set B := Matrix.GeneralLinearGroup.scalar (Fin 6) u * M with hB
  have hMN := gu_subset_normalizer h hM
  have hsN : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableB.scalar_mem_normalizer _ ⟨u, rfl⟩
  have hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ hsN hMN
  have heB : e = TableB.projConj (unitarySU 2 n K 6) ⟨B, hBN⟩ := by
    rw [heM]
    have e1 : (⟨B, hBN⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
        ⟨_, hsN⟩ * ⟨M, hMN⟩ := rfl
    rw [e1, map_mul, TableB.projConj_of_scalar _ ⟨u, rfl⟩, one_mul]
  have hsl : IsSemilin (projU n 6 K) e B 1 := by
    rw [heB]
    exact isSemilin_projConj ⟨B, hBN⟩
  have hdiag : ((P⁻¹ * B * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
    have e1 : P⁻¹ * B * P = Matrix.GeneralLinearGroup.scalar (Fin 6) u * (P⁻¹ * M * P) := by
      rw [hB, ← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm u P⁻¹]
      simp only [mul_assoc]
    rw [e1, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    intro i j hij
    rw [Matrix.diagonal_mul, hMd hij, mul_zero]
  obtain ⟨τ, hτ⟩ := exists_diagHom_of_isDiag hdiag
  have hfr : FrameAct h P hP e τ := by
    have h1 := hsl.frame h P hP
    rw [map_one, MulAut.one_apply, hτ] at h1
    exact h1
  have hτu : diagHom 6 τ ∈ primeFormUnitary h (idGram K 6) := by
    rw [← hτ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ((primeFormUnitary h (idGram K 6)).inv_mem hP) hu) hP
  have hτn := norm_eq_one_of_diagHom_mem h hτu
  have hpow : ∀ k, τ k ^ 3 = τ ⟨0, by omega⟩ ^ 3 := by
    have h1 := hfr.pow h hτu 3
    rw [hE₀.2 e he, one_pow, semilinNorm_diagHom] at h1
    have hNu : diagHom 6 (fun k => ∏ l ∈ Finset.range 3,
        Units.map (((1 : K ≃+* K) ^ l : K ≃+* K) : K →* K) (τ k)) ∈
        primeFormUnitary h (idGram K 6) := by
      rw [← semilinNorm_diagHom]
      exact semilinNorm_mem h hτu 1 3
    obtain ⟨c, hc⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq P hP hNu h1
    have hent : ∀ k, τ k ^ 3 = c := by
      intro k
      have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin 6) K =>
        (g : Matrix (Fin 6) (Fin 6) K)) hc) k) k
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, coe_diagHom, one_pow] at h2
      have hid : ∀ x : Kˣ, Units.map ((1 : K ≃+* K) : K →* K) x = x := fun x => Units.ext rfl
      simp only [hid, Finset.prod_const, Finset.card_range] at h2
      exact (Units.ext h2).symm
    intro k
    rw [hent k, hent ⟨0, by omega⟩]
  set c := (τ ⟨0, by omega⟩)⁻¹ with hc
  refine ⟨fun k => c * τ k, ?_, fun k => ?_, fun k => ?_, hfr.smul c⟩
  · show c * τ ⟨0, by omega⟩ = 1
    rw [hc]
    exact inv_mul_cancel _
  · show (c * τ k) ^ 3 = 1
    rw [mul_pow, hpow k, hc, inv_pow, inv_mul_cancel]
  · show ((c * τ k : Kˣ) : K) ^ (2 ^ n + 1) = 1
    rw [Units.val_mul, mul_pow, hτn k, mul_one, hc, Units.val_inv_eq_inv_val, inv_pow,
      hτn ⟨0, by omega⟩, inv_one]

end LID63

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitarySU_eq_gramSU)

namespace InndiagSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

@[expose] noncomputable def fieldFactorU (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) →* (K ≃+* K) :=
  (primeFormFieldFactor h (isPrimeFormGram_one (K := K) (n := d)) hd hq).comp
    (MulAut.congr (projEquiv h (by omega))).toMonoidHom

theorem ker_fieldFactorU (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    (fieldFactorU h hd hq).ker = inndiagU h (by omega) := by
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  ext α
  rw [MonoidHom.mem_ker, fieldFactorU, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
  rfl

theorem mem_conjImage_of_mem_inndiagU {hd : 1 ≤ d}
    {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hα : α ∈ inndiagU h hd) :
    α ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
  obtain ⟨B, hB⟩ := (mem_inndiagU h).mp hα
  have e : α = (MulAut.congr (projEquiv h hd)).symm (primeFormConjHom h _ B) := by
    rw [hB, MulEquiv.symm_apply_apply]
  rw [e]
  exact congr_symm_mem h hd B

@[expose] noncomputable def projU (n d : ℕ) (K : Type) [Field K] :
    ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
  LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))

theorem projU_surjective : Function.Surjective (projU n d K) := by
  intro r
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective r
  exact ⟨g, rfl⟩

@[expose] def IsSemilin {R : Type*} [Group R] (θ : ↥(unitarySU 2 n K d) →* R)
    (α : MulAut R) (B : GL (Fin d) K) (φ : K ≃+* K) : Prop :=
  ∀ u v : ↥(unitarySU 2 n K d),
    (v : GL (Fin d) K) = B * glAut φ (u : GL (Fin d) K) * B⁻¹ → α (θ u) = θ v

theorem semilin_mem {B : GL (Fin d) K}
    (hB : B ∈ primeFormUnitary h (idGram K d)) (φ : K ≃+* K) (u : ↥(unitarySU 2 n K d)) :
    B * glAut φ (u : GL (Fin d) K) * B⁻¹ ∈ unitarySU 2 n K d := by
  obtain ⟨x, hx⟩ := u
  change B * glAut φ x * B⁻¹ ∈ unitarySU 2 n K d
  rw [unitarySU_eq_gramSU h] at hx ⊢
  exact conj_mem_gramSU h _ hB (glAut_mem_gramSU h (isPrimeFormGram_one (K := K) (n := d)) φ hx)

theorem exists_isSemilin (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    ∃ B ∈ primeFormUnitary h (idGram K d),
      IsSemilin (projU n d K) α B (fieldFactorU h hd hq α) := by
  have hd1 : 1 ≤ d := by omega
  have hC := isPrimeFormGram_one (K := K) (n := d)
  set E := MulAut.congr (projEquiv h hd1) with hE
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hd hq (E α)
  have hφ : fieldFactorU h hd hq α = φ := by
    change primeFormFieldFactor h hC hd hq (E α) = φ
    rw [hA, primeFormFieldFactor_apply]
  refine ⟨A, A.2, fun u v huv => ?_⟩
  rw [hφ] at huv
  have e : α = E.symm (E α) := (MulEquiv.symm_apply_apply E α).symm
  rw [e, hA, MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (projEquiv h hd1).symm ((primeFormConjHom h _ A * primeFormFieldHom h hC φ)
    (projEquiv h hd1 ((⟨u, u.2⟩ : LargeEvenSUGroup (Fin d) K (2 ^ n)) :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) = _
  rw [projEquiv_mk, MulAut.mul_apply]
  change (projEquiv h hd1).symm (primeFormConjHom h _ A (primeFormFieldAut h hC φ _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk, projEquiv_symm_mk]
  congr 1
  exact Subtype.ext huv.symm

theorem IsSemilin.mul {R : Type*} [Group R] {θ : ↥(unitarySU 2 n K d) →* R}
    {α β : MulAut R} {B C : GL (Fin d) K} {φ ψ : K ≃+* K} (hα : IsSemilin θ α B φ)
    (hβ : IsSemilin θ β C ψ) (hC : C ∈ primeFormUnitary h (idGram K d)) :
    IsSemilin θ (α * β) (B * glAut φ C) (φ * ψ) := by
  intro u v huv
  set w : ↥(unitarySU 2 n K d) := ⟨_, semilin_mem h hC ψ u⟩ with hw
  rw [MulAut.mul_apply, hβ u w rfl]
  refine hα w v ?_
  rw [huv, hw]
  simp only [map_mul, map_inv, MulAut.mul_apply]
  group

@[expose] noncomputable def semilinNorm (B : GL (Fin d) K) (φ : K ≃+* K) : ℕ → GL (Fin d) K
  | 0 => 1
  | m + 1 => semilinNorm B φ m * glAut (φ ^ m) B

theorem semilinNorm_mem {B : GL (Fin d) K} (hB : B ∈ primeFormUnitary h (idGram K d))
    (φ : K ≃+* K) (m : ℕ) : semilinNorm B φ m ∈ primeFormUnitary h (idGram K d) := by
  induction m with
  | zero => exact Subgroup.one_mem _
  | succ m ih =>
    exact Subgroup.mul_mem _ ih
      (glAut_mem_primeFormUnitary h (isPrimeFormGram_one (K := K) (n := d)) _ hB)

theorem IsSemilin.pow {R : Type*} [Group R] {θ : ↥(unitarySU 2 n K d) →* R}
    {α : MulAut R} {B : GL (Fin d) K} {φ : K ≃+* K} (hα : IsSemilin θ α B φ)
    (hB : B ∈ primeFormUnitary h (idGram K d)) (m : ℕ) :
    IsSemilin θ (α ^ m) (semilinNorm B φ m) (φ ^ m) := by
  induction m with
  | zero =>
    intro u v huv
    have hv : v = u := by
      apply Subtype.ext
      rw [huv]
      simp [semilinNorm]
    rw [hv, pow_zero, MulAut.one_apply]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h hα hB

@[expose] noncomputable def frameMk (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
  (projU n d K).comp (TableBUE.conjSU h P hP).symm.toMonoidHom

theorem frameMk_apply (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    (u : ↥(unitarySU 2 n K d)) :
    frameMk h P hP u = projU n d K ((TableBUE.conjSU h P hP).symm u) :=
  rfl

theorem coe_conjSU_symm (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    (u : ↥(unitarySU 2 n K d)) :
    (((TableBUE.conjSU h P hP).symm u : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = P * u * P⁻¹ :=
  rfl

theorem frameMk_surjective (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    Function.Surjective (frameMk h P hP) :=
  projU_surjective.comp (TableBUE.conjSU h P hP).symm.surjective

theorem IsSemilin.frame {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    {B : GL (Fin d) K} {φ : K ≃+* K}
    (hα : IsSemilin (projU n d K) α B φ)
    (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    IsSemilin (frameMk h P hP) α (P⁻¹ * B * glAut φ P) φ := by
  intro u v huv
  rw [frameMk_apply, frameMk_apply]
  refine hα _ _ ?_
  rw [coe_conjSU_symm, coe_conjSU_symm, huv]
  simp only [map_mul, map_inv]
  group

theorem mem_scalars_of_isSemilin_one [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) {N : GL (Fin d) K}
    (hN : N ∈ primeFormUnitary h (idGram K d)) (h1 : IsSemilin (frameMk h P hP) 1 N 1) :
    N ∈ LargeEvenScalars (Fin d) K := by
  set M := P * N * P⁻¹ with hM
  have hMu : M ∈ primeFormUnitary h (idGram K d) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hP hN) (Subgroup.inv_mem _ hP)
  have hMn : M ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := semilin_mem h hMu 1 ⟨g, hg⟩
      simp only [map_one, MulAut.one_apply] at this
      exact this
    · intro hg
      have := semilin_mem h (Subgroup.inv_mem _ hMu) 1 ⟨_, hg⟩
      simp only [map_one, MulAut.one_apply, inv_inv] at this
      have e : M⁻¹ * (M * g * M⁻¹) * M = g := by group
      rw [e] at this
      exact this
  have hc : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ⟨M, hMn⟩ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [TableB.projConj_mk, MulAut.one_apply]
      obtain ⟨u, rfl⟩ := (TableBUE.conjSU h P hP).symm.surjective g
      set v : ↥(unitarySU 2 n K d) := ⟨_, semilin_mem h hN 1 u⟩ with hv
      have e1 : frameMk h P hP u = frameMk h P hP v := by
        have := h1 u v rfl
        rwa [MulAut.one_apply] at this
      have e2 : (LargeEvenSUGroup (Fin d) K (2 ^ n)).normalizerMonoidHom ⟨M, hMn⟩
          ((TableBUE.conjSU h P hP).symm u) = (TableBUE.conjSU h P hP).symm v := by
        apply Subtype.ext
        change M * (P * u * P⁻¹) * M⁻¹ = P * (N * glAut 1 (u : GL (Fin d) K) * N⁻¹) * P⁻¹
        rw [map_one, MulAut.one_apply, hM]
        group
      rw [e2]
      exact e1.symm
  have hs := TableBUE.mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hc
  obtain ⟨c, hcM⟩ := hs
  refine ⟨c, ?_⟩
  have hcc := Subgroup.mem_center_iff.mp (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨c, rfl⟩)
  calc Matrix.GeneralLinearGroup.scalar (Fin d) c
      = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin d) c * P := by
        rw [mul_assoc, ← hcc P, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = N := by
        rw [hcM]
        change P⁻¹ * M * P = N
        rw [hM]
        group

theorem card_le_mul_card_inf_inndiagU [Finite K] [CharP K 2] (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hp : p.Prime)
    {Eh : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hEh : IsElemAbelian p Eh) :
    Nat.card Eh ≤ p * Nat.card (Eh ⊓ inndiagU h (by omega) : Subgroup _) := by
  set F := (fieldFactorU h hd hq).comp Eh.subtype with hF
  have hker : Nat.card F.ker = Nat.card (Eh ⊓ inndiagU h (by omega) : Subgroup _) := by
    have e1 : F.ker = (inndiagU h (by omega)).subgroupOf Eh := by
      rw [hF, ← MonoidHom.comap_ker, ker_fieldFactorU]
      rfl
    rw [e1, ← Subgroup.card_map_of_injective Eh.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hrange : Nat.card F.range ≤ p := by
    have : IsCyclic (K ≃+* K) := AutPSU.isCyclic_ringEquiv (K := K)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F.range)
    have hgp : g ^ p = 1 := by
      obtain ⟨⟨e, he⟩, hge⟩ := g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hge, ← map_pow]
      have : (⟨e, he⟩ : Eh) ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hEh.2 e he)
      rw [this, map_one]
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  calc Nat.card Eh = Nat.card F.ker * Nat.card F.range := (Subgroup.card_ker_mul_card_range F).symm
    _ ≤ Nat.card F.ker * p := Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card (Eh ⊓ inndiagU h (by omega) : Subgroup _) := by rw [hker, mul_comm]

end InndiagSU

end CFSG.StandardType

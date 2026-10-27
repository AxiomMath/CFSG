module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOne
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4CubeScalar
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace S2MathAs3_1615

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

private lemma ltrl6uni_kernel_scalar {d n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))}
    (hM : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) M = 1) :
    (M : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (show 2 ^ n + 1 ≠ 1 by
    have h1 : 1 ≤ n := h.one_le
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
    omega)
  exact TableBUE.mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM

private def ltrl6uni_proj_congr {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {S T : Subgroup (GL ι K)} (h : S = T) : LargeEvenProj S ≃* LargeEvenProj T := by
  subst h
  exact MulEquiv.refl _

private lemma ltrl6uni_projConj_congr {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {S T : Subgroup (GL ι K)} (h : S = T)
    {A : GL ι K} (hA : A ∈ Subgroup.normalizer (S : Set (GL ι K))) :
    ∃ hA' : A ∈ Subgroup.normalizer (T : Set (GL ι K)),
      ∀ x : LargeEvenProj S,
        TableB.projConj T ⟨A, hA'⟩ (ltrl6uni_proj_congr h x) =
          ltrl6uni_proj_congr h (TableB.projConj S ⟨A, hA⟩ x) := by
  subst h
  exact ⟨hA, fun x => rfl⟩

private lemma ltrl6uni_actor {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hψ : Function.Surjective ψ) {e : MulAut L'} (he3 : e ^ 3 = 1)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))}
    (hφI : φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
      (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hφe : ∀ l : L', φ (ψ l) = ψ (e l)) :
    ∃ (S : GL (Fin (lab.rank + 1)) K)
      (hSgu : S ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
      (hSN : S ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
          Set (GL (Fin (lab.rank + 1)) K)))
      (κ : Kˣ), S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) κ ∧
      φ = TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ := by
  have hn1 : 1 ≤ lab.n := hlab.1
  have hUF : UnitaryFieldData 2 lab.n K :=
    CFSG.StandardType.unitaryFieldData_of_card hn1 hK
  have hd3 : 3 ≤ lab.rank + 1 := by
    have h2 : 2 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h.1
    omega
  have hdq : (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
    rintro h
    have hr : lab.rank = 2 := by simpa using congrArg Prod.fst h
    have hle : 2 ≤ lab.n := by
      have h := hlab.2
      rw [htag] at h
      exact h.2 hr
    have h2 : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hle
    have hn : 2 ^ lab.n = 2 := congrArg Prod.snd h
    omega
  have hSnorm : LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n) ⊆
      Subgroup.normalizer
        (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
          Set (GL (Fin (lab.rank + 1)) K)) :=
    TableBUE.gu_subset_normalizer (h := hUF)
  obtain ⟨S, hSgu, hSeq⟩ := TableB.exists_eq_projConj hSnorm hφI
  have hSN : S ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)) := hSnorm hSgu
  have hpow : ∀ k : ℕ, ∀ l : L', (φ ^ k) (ψ l) = ψ ((e ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
        intro l
        rw [pow_succ]
        change (φ ^ k) (φ (ψ l)) = ψ ((e ^ (k + 1)) l)
        rw [hφe l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφ3 : φ ^ 3 = 1 := by
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hpow 3 l, he3]
    rfl
  let A : Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)) := ⟨S, hSN⟩
  have hprojA : TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) A = φ :=
    hSeq.symm
  have hprojA3 :
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) (A ^ 3) = 1 := by
    rw [map_pow, hprojA, hφ3]
  have hmem := ltrl6uni_kernel_scalar hUF hK hd3 hdq hprojA3
  rw [largeEvenScalars_def] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨S, hSgu, hSN, κ, ?_, hSeq⟩
  exact hκ.symm

private lemma ltrl6uni_beta {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2) (hUF : UnitaryFieldData 2 lab.n K)
    (hSU : LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) =
      unitarySU 2 lab.n K (lab.rank + 1))
    {A : GL (Fin (lab.rank + 1)) K}
    (hAgu : A ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hA : A ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K))) :
    ∃ β ∈ InndiagSU.inndiagU (d := lab.rank + 1) hUF (Nat.succ_pos lab.rank),
      ∀ r : LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)),
        β ((ltrl6uni_proj_congr hSU) r) =
          (ltrl6uni_proj_congr hSU)
            (TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
              ⟨A, hA⟩ r) := by
  obtain ⟨hA', hAc⟩ := ltrl6uni_projConj_congr
    (S := LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (T := unitarySU 2 lab.n K (lab.rank + 1)) hSU (A := A) hA
  refine ⟨TableB.projConj (unitarySU 2 lab.n K (lab.rank + 1)) ⟨A, hA'⟩, ?_, ?_⟩
  · have hβIT : TableB.projConj (unitarySU 2 lab.n K (lab.rank + 1)) ⟨A, hA'⟩ ∈
        LargeEvenMatConjImage
          (LargeEvenProjMk (unitarySU 2 lab.n K (lab.rank + 1)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)) := by
      refine ⟨A, hAgu, ?_⟩
      intro h h' hrel
      change TableB.projConj (unitarySU 2 lab.n K (lab.rank + 1)) ⟨A, hA'⟩
          ((h : LargeEvenProj (unitarySU 2 lab.n K (lab.rank + 1)))) =
        ((h' : LargeEvenProj (unitarySU 2 lab.n K (lab.rank + 1))))
      rw [TableB.projConj_mk]
      apply congrArg (fun g : ↥(unitarySU 2 lab.n K (lab.rank + 1)) =>
        (g : LargeEvenProj (unitarySU 2 lab.n K (lab.rank + 1))))
      apply Subtype.ext
      show A * (h : GL (Fin (lab.rank + 1)) K) * A⁻¹ = (h' : GL (Fin (lab.rank + 1)) K)
      rw [hrel]
    have hβI : TableB.projConj (unitarySU 2 lab.n K (lab.rank + 1)) ⟨A, hA'⟩ ∈
        LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)) := hβIT
    exact (InndiagSU.mem_inndiagU (h := hUF) (hd := Nat.succ_pos lab.rank)).mpr
      (InndiagSU.congr_mem_primeFormD (h := hUF) (hd := Nat.succ_pos lab.rank) hK hβI)
  · intro r
    exact hAc r

private lemma ltrl6uni_rescale {lab : LargeEvenLabel} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 lab.n K)
    {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    {e : MulAut L'} {S : GL (Fin (lab.rank + 1)) K}
    (hSgu : S ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hSN : S ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) κ)
    (hφe : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ (ψ l) =
        ψ (e l))
    (c : Kˣ) (hc : c ^ 3 = κ) :
    ∃ (M : GL (Fin (lab.rank + 1)) K)
      (hMN : M ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
          Set (GL (Fin (lab.rank + 1)) K))),
      M ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n) ∧ M ^ 3 = 1 ∧
      ∀ l : L',
        TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨M, hMN⟩ (ψ l) =
          ψ (e l) := by
  set s : GL (Fin (lab.rank + 1)) K :=
    Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) (c⁻¹) with hs
  set M : GL (Fin (lab.rank + 1)) K := s * S with hM
  have hs_mem : s ∈ LargeEvenScalars (Fin (lab.rank + 1)) K := by
    rw [hs, largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hsN : s ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)) :=
    TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) hs_mem
  have hcomm : s * S = S * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs_mem) S).symm
  have hc3 : (c⁻¹ : Kˣ) ^ 3 = κ⁻¹ := by rw [inv_pow, hc]
  have hs3 : s ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) ((c⁻¹ : Kˣ) ^ 3) := by
    rw [hs, ← map_pow]
  have hM3 : M ^ 3 = 1 := by
    rw [hM, Commute.mul_pow hcomm 3, hs3, hS3, hc3, ← map_mul, inv_mul_cancel, map_one]
  have hMN : M ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)) := by
    rw [hM]; exact mul_mem hsN hSN
  have hMgu : M ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.scalar_mul_mem_guSet hUF hSgu c⁻¹
  refine ⟨M, hMN, hMgu, hM3, ?_⟩
  have hMeq : (⟨M, hMN⟩ : Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K))) = ⟨s, hsN⟩ * ⟨S, hSN⟩ := Subtype.ext hM
  have hproj : TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
      ⟨M, hMN⟩ = TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
        ⟨S, hSN⟩ := by
    rw [hMeq, map_mul, TableB.projConj_of_scalar _ hs_mem, one_mul]
  intro l
  rw [hproj]
  exact hφe l

private lemma ltrl6uni_splitLift_of_matrix {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2) (hUF : UnitaryFieldData 2 lab.n K)
    {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    {e : MulAut L'} {M : GL (Fin (lab.rank + 1)) K}
    (hMgu : M ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hMN : M ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)))
    (hM3 : M ^ 3 = 1)
    (hφem : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨M, hMN⟩ (ψ l) =
        ψ (e l)) :
    SplitLift lab (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
      (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) ψ e := by
  have hS := TableBUE.gu_subset_normalizer (d := lab.rank + 1) (h := hUF)
  have hSU : LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) =
      unitarySU 2 lab.n K (lab.rank + 1) := rfl
  obtain ⟨hMN', hcompat⟩ := ltrl6uni_projConj_congr
    (S := LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (T := unitarySU 2 lab.n K (lab.rank + 1)) hSU (A := M) hMN
  refine Or.inr ⟨htag, K, inferInstance, inferInstance, hUF, M, hMN', hM3, hMgu,
    ltrl6uni_proj_congr hSU, ?_, ?_⟩
  · intro l
    rw [hcompat (ψ l), hφem l]
  · intro φ' hφ'
    obtain ⟨A, hAgu, hφ'A⟩ := TableB.exists_eq_projConj hS hφ'
    obtain ⟨β, hβmem, hβeq⟩ := ltrl6uni_beta hlab htag hK hUF hSU hAgu (hS hAgu)
    exact ⟨β, hβmem, fun r => by rw [hβeq r, hφ'A]⟩

private lemma ltrl6uni_noncube {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    {e : MulAut L'} {J : Subgroup L'} {a : MulAut L'}
    (hset : GGRankOneSetup
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) ψ 3 e J 3 a)
    (hnot : ¬ SplitLift lab (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
      (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) ψ e)
    {S : GL (Fin (lab.rank + 1)) K}
    (hSgu : S ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hSN : S ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) κ)
    (hφe : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ (ψ l) =
        ψ (e l)) :
    ∀ c : Kˣ, c ^ 3 ≠ κ := by
  intro c hc
  have hn1 : 1 ≤ lab.n := hlab.1
  have hUF : UnitaryFieldData 2 lab.n K :=
    CFSG.StandardType.unitaryFieldData_of_card hn1 hK
  obtain ⟨M, hMN, hMgu, hM3, hφem⟩ := ltrl6uni_rescale hUF ψ hSgu hSN κ hS3 hφe c hc
  exact hnot (ltrl6uni_splitLift_of_matrix hlab htag hK hUF ψ hMgu hMN hM3 hφem)

private lemma ltrl6uni_label {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {e : MulAut L'} {J : Subgroup L'}
    (hJ : IsComponentOf J (ggFixSub e))
    (hlabJ : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    {S : GL (Fin (lab.rank + 1)) K}
    (hSgu : S ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hSN : S ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) κ)
    (hnc : ∀ c : Kˣ, c ^ 3 ≠ κ)
    (hφe : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ (ψ l) =
        ψ (e l)) :
    lab.rank + 1 = 6 ∧ lab.n = 1 := by
  have hn1 : 1 ≤ lab.n := hlab.1
  have hUF : UnitaryFieldData 2 lab.n K :=
    CFSG.StandardType.unitaryFieldData_of_card hn1 hK
  have hd2 : 2 ≤ lab.rank + 1 := by
    have h2 : 2 ≤ lab.rank := by
      have h := hlab.2
      rw [htag] at h
      exact h.1
    omega
  have hJmap : IsComponentOf (J.map ψ)
      (ggFixSub (TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))
        ⟨S, hSN⟩)) :=
    USixTwo.isComponentOf_map_fix hψ hker hφe hJ
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  have hf : Function.Surjective (ψ.subgroupMap J) := ψ.subgroupMap_surjective J
  have hkerf : (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hψx : ψ (x : L') = 1 := congrArg Subtype.val hx
    have hxc : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hψx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (y : L')
  obtain ⟨φlab⟩ :=
    CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (ψ.subgroupMap J) hf hkerf
  have hlabJmap : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    ggHasLabel_of_mulEquiv φlab hlabJ
  haveI : CharP K 2 := hUF.charP
  exact S2MathAs3_1624.d3Endpoints_of_jobs.2 K lab.n hUF (lab.rank + 1) hd2 S κ hnc
    hSgu hS3 hSN (J.map ψ) hJmap hlabJmap

private lemma ltrl6uni_cube_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {S : Matrix (Fin 6) (Fin 6) K} (hS : S.det = 1) {κ : K}
    (h : S ^ 3 = Matrix.scalar (Fin 6) κ) : κ = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hK]
  let e : K ≃+* CFSG.Fischer.F4 := FiniteField.ringEquivOfCardEq hcard
  have h1 : (e.toRingHom.mapMatrix S).det = 1 := by
    rw [← RingHom.map_det, hS, map_one]
  have h2 : (e.toRingHom.mapMatrix S) ^ 3 = Matrix.scalar (Fin 6) (e κ) := by
    rw [← map_pow e.toRingHom.mapMatrix S 3, h]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  have h3 := CFSG.GGQ2Prime.eq_one_of_det_eq_one_of_pow_three_eq_scalar h1 h2
  exact e.injective (by rw [h3, map_one])

private lemma ltrl6uni_marking {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2) (hUF : UnitaryFieldData 2 lab.n K)
    (hSU : LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) =
      unitarySU 2 lab.n K (lab.rank + 1)) :
    ∀ φ' ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)),
      ∃ β ∈ InndiagSU.inndiagU (d := lab.rank + 1) hUF (Nat.succ_pos lab.rank),
        ∀ r, β ((ltrl6uni_proj_congr hSU) r) = (ltrl6uni_proj_congr hSU) (φ' r) := by
  intro φ' hφ'
  have hS := TableBUE.gu_subset_normalizer (d := lab.rank + 1) (h := hUF)
  obtain ⟨A, hAgu, hφ'A⟩ := TableB.exists_eq_projConj hS hφ'
  obtain ⟨β, hβmem, hβeq⟩ := ltrl6uni_beta hlab htag hK hUF hSU hAgu (hS hAgu)
  exact ⟨β, hβmem, fun r => by rw [hβeq r, hφ'A]⟩

private lemma ltrl6uni_notInner {d n : ℕ} (hd : d = 6) (hn : n = 1) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hUF : UnitaryFieldData 2 n K)
    {L' : Type} [Group L'] (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) {e : MulAut L'} {S : GL (Fin d) K}
    (hSN : S ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ)
    (hnc : ∀ c : Kˣ, c ^ 3 ≠ κ)
    (hφe : ∀ l : L', TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ⟨S, hSN⟩ (ψ l) =
      ψ (e l)) :
    ¬ ∃ r : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
        ∀ l : L', ψ (e l) = r * ψ l * r⁻¹ := by
  subst hd hn
  rintro ⟨r, hr⟩
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hproj : ∀ x : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ⟨S, hSN⟩ x = r * x * r⁻¹ := by
    intro x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hφe l]
    exact hr l
  obtain ⟨T, rfl⟩ := QuotientGroup.mk_surjective r
  have hTN : (T : GL (Fin 6) K) ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1) : Set (GL (Fin 6) K)) := Subgroup.le_normalizer T.2
  have hab : TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ⟨S, hSN⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ⟨(T : GL (Fin 6) K), hTN⟩ := by
    rw [TableB.projConj_of_mem (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (T : GL (Fin 6) K) T.2]
    ext x
    rw [hproj x, MulAut.conj_apply]
  have h1 : TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      ((⟨(T : GL (Fin 6) K), hTN⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1) : Set (GL (Fin 6) K)))⁻¹ * ⟨S, hSN⟩) = 1 := by
    rw [map_mul, map_inv, ← hab, inv_mul_cancel]
  have hscal : (T : GL (Fin 6) K)⁻¹ * S ∈ LargeEvenScalars (Fin 6) K :=
    ltrl6uni_kernel_scalar hUF hK (by norm_num) (by simp) h1
  rw [largeEvenScalars_def] at hscal
  obtain ⟨c, hc⟩ := hscal
  have hSeq : S = (T : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [hc, mul_inv_cancel_left]
  have hTdet : ((T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    have hT' : (T : GL (Fin 6) K) ∈ unitarySU 2 1 K 6 := T.2
    exact ((mem_unitarySU_iff hUF).mp hT').1
  have hc3 : c ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by simp [Nat.card_units, hK4]
    have h := pow_card_eq_one' (G := Kˣ) (x := c)
    rwa [hcard] at h
  have hc3K : (c : K) ^ 3 = 1 := by
    have := congrArg Units.val hc3
    simpa using this
  have hdetS : (S : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [hSeq, Units.val_mul, Matrix.det_mul, hTdet, one_mul,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc (c : K) ^ 6 = ((c : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hc3K]; norm_num
  have hS3' : (S : Matrix (Fin 6) (Fin 6) K) ^ 3 = Matrix.scalar (Fin 6) (κ : K) := by
    have h := congrArg Units.val hS3
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h
    exact h
  have hκ1 : (κ : K) = 1 := ltrl6uni_cube_one hK4 hdetS hS3'
  exact hnc 1 (by rw [one_pow]; exact Units.ext (by rw [Units.val_one]; exact hκ1.symm))

private lemma ltrl6uni_model {d n : ℕ} (hd : d = 6) (hn : n = 1) {K : Type} [Field K]
    [Finite K] (hUF : UnitaryFieldData 2 n K) {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) {e : MulAut L'}
    {S : GL (Fin d) K} (hSgu : S ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hSN : S ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ)
    (hnc : ∀ c : Kˣ, c ^ 3 ≠ κ)
    (hφe : ∀ l : L', TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ⟨S, hSN⟩ (ψ l) =
      ψ (e l))
    (hSU : LargeEvenSUGroup (Fin d) K (2 ^ n) = unitarySU 2 n K d)
    (hmark : ∀ φ' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
      ∃ β ∈ InndiagSU.inndiagU (d := d) hUF (by omega),
        ∀ r, β ((ltrl6uni_proj_congr hSU) r) = (ltrl6uni_proj_congr hSU) (φ' r)) :
    NonsplitUnitaryModel ψ e
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  subst hd hn
  obtain ⟨hS', hcompat⟩ := ltrl6uni_projConj_congr
    (S := LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (T := unitarySU 2 1 K 6) hSU (A := S) hSN
  refine ⟨K, inferInstance, inferInstance, hUF, ltrl6uni_proj_congr hSU,
    TableB.projConj (unitarySU 2 1 K 6) ⟨S, hS'⟩, ?_, ?_, hmark⟩
  · intro l
    rw [hcompat (ψ l), hφe l]
  · exact ⟨S, hSgu, κ, hS3, hnc, rfl⟩

private lemma ltrl6uni_notInnerModel {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hψ : Function.Surjective ψ) {e : MulAut L'}
    (hrank : lab.rank + 1 = 6) (hn : lab.n = 1)
    {S : GL (Fin (lab.rank + 1)) K}
    (hSgu : S ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))
    (hSN : S ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) :
        Set (GL (Fin (lab.rank + 1)) K)))
    (κ : Kˣ) (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) κ)
    (hnc : ∀ c : Kˣ, c ^ 3 ≠ κ)
    (hφe : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ (ψ l) =
        ψ (e l)) :
    (¬ ∃ r : LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)),
        ∀ l : L', ψ (e l) = r * ψ l * r⁻¹) ∧
      NonsplitUnitaryModel ψ e
        (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) := by
  have hn1 : 1 ≤ lab.n := hlab.1
  have hUF : UnitaryFieldData 2 lab.n K :=
    CFSG.StandardType.unitaryFieldData_of_card hn1 hK
  have hSU : LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n) =
      unitarySU 2 lab.n K (lab.rank + 1) := rfl
  exact ⟨ltrl6uni_notInner hrank hn hK hUF ψ hψ hSN κ hS3 hnc hφe,
    ltrl6uni_model hrank hn hUF ψ hSgu hSN κ hS3 hnc hφe hSU
      (ltrl6uni_marking hlab htag hK hUF hSU)⟩

theorem leaf6Unitary_shape {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {e : MulAut L'} {J : Subgroup L'} {a : MulAut L'}
    (hset : GGRankOneSetup
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) ψ 3 e J 3 a)
    (hnot : ¬ SplitLift lab (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) ψ e) :
    lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∧
      (¬ ∃ r : LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)),
        ∀ l : L', ψ (e l) = r * ψ l * r⁻¹) ∧
      NonsplitUnitaryModel ψ e
        (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n))) := by
  have hset' := hset
  obtain ⟨-, -, -, he3, ⟨φ, hφI, hφe⟩, hJ, -, hlabJ, -, -, -, -⟩ := hset
  obtain ⟨S, hSgu, hSN, κ, hS3, hSeq⟩ := ltrl6uni_actor hlab htag hK ψ hψ he3 hφI hφe
  have hφe' : ∀ l : L',
      TableB.projConj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)) ⟨S, hSN⟩ (ψ l) =
        ψ (e l) := by
    intro l
    rw [← hSeq]
    exact hφe l
  have hnc := ltrl6uni_noncube hlab htag hK ψ hψ hker hperf hset' hnot hSgu hSN κ hS3 hφe'
  have hlabel := ltrl6uni_label hlab htag hK ψ hψ hker hJ hlabJ hSgu hSN κ hS3 hnc hφe'
  have hrest := ltrl6uni_notInnerModel hlab htag hK ψ hψ hlabel.1 hlabel.2 hSgu hSN κ hS3 hnc hφe'
  exact ⟨S2MathAs3_1624.twA_label_of_d6_n1 htag rfl hlabel.1 hlabel.2, hrest.1, hrest.2⟩

end S2MathAs3_1615

end

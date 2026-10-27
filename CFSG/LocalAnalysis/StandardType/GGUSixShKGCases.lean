module

public import CFSG.LocalAnalysis.StandardType.GGUSixShSub
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFrameCase
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGHeisCase
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section USixSh

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.LocalAnalysis.GLTheoremA.FQ (fixF)
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni (Induced subfieldHom subfieldEquiv)

@[expose] def GGUSixShPerLineOn {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (Sh : Set (MulAut R)) (A : Subgroup (MulAut L')) : Prop :=
  ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ Sh, ∀ l : L', φ (ψ l) = ψ (a₀ l)) ∨
    ∃ n : L', UnitSixThreeKG.IsWeyl A n ∧
      MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀

theorem ggUSixSh_torusNoLineSh_of_perLineSh {r : ℕ} {R : Type} [Group R] {I Sh : Set (MulAut R)}
    (h : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), CFSG.Open.IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → 3 ^ 3 ≤ Nat.card A →
          GGUSixShPerLineOn ψ Sh A) :
    GGTorusNoLineSh 3 r R I Sh := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _hr h3 _hsc
  refine ⟨{n | UnitSixThreeKG.IsWeyl A n}, fun n hn => hn, fun _ a₀ ha₀ h1 => ?_⟩
  rcases h L' ψ hψ hker hperf A hA hAI h3 a₀ ha₀ h1 with hsh | ⟨n, hn, hmv⟩
  · exact Or.inl hsh
  · exact Or.inr ⟨n, hn, hmv⟩

theorem ggUSixSh_perLineSh_of_frame {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKd : UnitaryFieldData 2 n K) (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {P : GL (Fin 6) K}
    (hP : P ∈ primeFormUnitary hKd (idGram K 6))
    (hframe : ∀ a ∈ A, ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
      ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer hKd hM⟩ (ψ l) =
        ψ (a l))
    (Sh : Set (MulAut (LargeEvenProj (unitarySU 2 n K 6)))) :
    GGUSixShPerLineOn ψ Sh A := by
  obtain ⟨φ, hφs, hφker, hφa, -⟩ := UnitSixThreeKG.exists_model hKd hψ hker hperf hperfSU hP hcov'
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
    DFunLike.coe_injective
  have hPN := LineU.primeForm_mem_normalizer hKd hP
  have hdiag : ∀ a ∈ A, ∃ t : Fin 6 → K, LineU.ActsDiagU φ a t := by
    intro a ha
    obtain ⟨M, hM, hdiagM, hc⟩ := hframe a ha
    have hMN := gu_subset_normalizer hKd hM
    have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    have hdiag' : ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        diagonal (Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      ((Matrix.isDiag_iff_diagonal_diag _).mp hdiagM).symm
    exact ⟨Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K),
      P⁻¹ * M * P, hDN, hdiag', hφa a M (P⁻¹ * M * P) hMN hDN rfl hc⟩
  intro a₀ ha₀ ha₀1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a₀ = 3 := orderOf_eq_prime (hAp a₀ ha₀) ha₀1
  have hΛp : Nat.card (Subgroup.zpowers a₀) = 3 := by rw [Nat.card_zpowers, hord]
  have hΛA : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  obtain ⟨σ, e, heΛ, hmv⟩ := LineU.moved_of_diag hKd (by norm_num) hφs hφker Nat.prime_three hAp
    hdiag hΛA hΛp
  refine Or.inr ⟨φ (LineU.permSU hKd σ),
    LineU.weyl_W_prop hKd (by norm_num) hφker hAp hdiag _ ⟨σ, rfl⟩, fun hmem => hmv ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp heΛ
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hmem k

theorem ggUSixSh_perLineSh_of_heisTriple {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {x y z : GL (Fin 6) K}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hxu : x ∈ primeFormUnitary hKd (idGram K 6)) (hyu : y ∈ primeFormUnitary hKd (idGram K 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram K 6)) {ζ : Kˣ}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hζ : IsPrimitiveRoot ζ 3)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) K)
    (hxA : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ TypeA.inducedSub ψ A)
    (hyA : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ TypeA.inducedSub ψ A)
    (hzA : TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ TypeA.inducedSub ψ A) :
    GGUSixShPerLineOn ψ (ggUSixShSet hKd) A := by
  have hAbcard : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  intro a₀ ha₀ ha₀1
  obtain ⟨x₀, -, hx₀⟩ := hAI a₀ ha₀
  have hx₀Ab : x₀ ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a₀, ha₀, hx₀⟩
  obtain ⟨i, j, k, hM, hi, hj, hk, hx₀eq⟩ := Line63.H5.exists_mono_of_card hKd hpq hAbcard hxN hyN
    hzN hζ hxA hyA hzA hxy hxz hyz hz3 hzs x₀ hx₀Ab
  have hc : ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨x ^ i * y ^ j * z ^ k, hM⟩ (ψ l) =
      ψ (a₀ l) := fun l => by rw [← hx₀eq]; exact hx₀ l
  by_cases hij : i ≠ 0 ∨ j ≠ 0
  · refine Or.inl ⟨TableB.projConj (unitarySU 2 n K 6) ⟨x ^ i * y ^ j * z ^ k, hM⟩,
      ⟨x ^ i * y ^ j * z ^ k, hM,
        mul_mem (mul_mem (pow_mem hxu i) (pow_mem hyu j)) (pow_mem hzu k),
        UnitSixThreeKG.shapeBad_of_mono hKd hpq hxu hyu hzu hx3 hz3 hζ hxy hxz hyz
          (Or.inr hy3) hij hi hj k,
        rfl⟩, hc⟩
  · push Not at hij
    obtain ⟨rfl, rfl⟩ := hij
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : ∀ l, ψ (a₀ l) = ψ l := fun l => by
        rw [← hc l]
        have e : (⟨x ^ 0 * y ^ 0 * z ^ 0, hM⟩ : Subgroup.normalizer
            (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = 1 := by
          apply Subtype.ext
          simp
        rw [e, map_one]
        rfl
      exact absurd (TypeA.mulAut_eq_of_forall ψ hker hperf (a := a₀) (b := 1) h1) ha₀1
    · have hzk : z ^ k ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
        pow_mem hzN k
      have e : (⟨x ^ 0 * y ^ 0 * z ^ k, hM⟩ : Subgroup.normalizer
          (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = ⟨z ^ k, hzk⟩ := by
        apply Subtype.ext
        simp
      rw [e] at hc
      refine Or.inl ⟨TableB.projConj (unitarySU 2 n K 6) ⟨z ^ k, hzk⟩,
        ⟨z ^ k, hzk, pow_mem hzu k,
          UnitSixThreeKG.shapeBad_of_central_pow hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs hk hk0,
          rfl⟩, hc⟩

private lemma ggUSixShCaseAux_zpow_mul_mono {K : Type} [Field K] {X Y Z : GL (Fin 6) K}
    (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y) (r i j k : ℕ) :
    Z ^ r * (X ^ i * Y ^ j * Z ^ k) = (X ^ i * Y ^ j * Z ^ k) * Z ^ r := by
  have hZX : Commute Z X := hXZ.symm
  have hZY : Commute Z Y := hYZ.symm
  have hZZ : Commute Z Z := Commute.refl Z
  have h := ((hZX.pow_right i).pow_left r).mul_right
    (((hZY.pow_right j).pow_left r).mul_right ((hZZ.pow_right k).pow_left r))
  simpa only [mul_assoc] using h.eq

theorem ggUSixSh_perLineSh_of_fieldTriple {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {X Y Z : GL (Fin 6) K}
    (hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hYN : Y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hZN : Z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hXu : X ∈ primeFormUnitary hKd (idGram K 6)) (hYu : Y ∈ primeFormUnitary hKd (idGram K 6))
    (hZu : Z ∈ primeFormUnitary hKd (idGram K 6)) {ζ l : Kˣ}
    (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) (hY3 : Y ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) (hζ : IsPrimitiveRoot ζ 3)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (hZs : Z ∉ LargeEvenScalars (Fin 6) K)
    (hXA : TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ ∈ TypeA.inducedSub ψ A)
    (hYA : TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ ∈ TypeA.inducedSub ψ A)
    (hZA : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ ∈ TypeA.inducedSub ψ A) :
    GGUSixShPerLineOn ψ (ggUSixShSet hKd) A := by
  classical
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  have monoData : ∀ a ∈ A, ∃ (i j k : ℕ) (hM : X ^ i * Y ^ j * Z ^ k ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      i < 3 ∧ j < 3 ∧ k < 3 ∧
      (∀ l : L', TableB.projConj (unitarySU 2 n K 6)
        ⟨X ^ i * Y ^ j * Z ^ k, hM⟩ (ψ l) = ψ (a l)) := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hAI a ha
    have hxAb : x ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hx⟩
    obtain ⟨i, j, k, hM, hi, hj, hk, hxeq⟩ :=
      CFSG.StandardType.Line63.H5.exists_mono_of_card hKd hpq hcardAb hXN hYN hZN hζ
        hXA hYA hZA hXY hXZ hYZ hZ3 hZs x hxAb
    refine ⟨i, j, k, hM, hi, hj, hk, fun l => ?_⟩
    rw [← hxeq]
    exact hx l
  obtain ⟨hZu', w, hwX, hwZ, hwY⟩ :=
    UnitSixThreeKG.exists_weyl_matrix hKd hpq hXu hZu hX3 hZ3 hζ hXY hXZ hYZ hZs
  have hWN : (w : GL (Fin 6) K) ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.le_normalizer w.2
  obtain ⟨φ, hφs, hφker, hφact, hφproj⟩ :=
    UnitSixThreeKG.exists_model hKd hψ hker hperf hperfSU (P := 1) (Subgroup.one_mem _) hcov'
  let n₀ : L' := φ w
  have hWeyl : UnitSixThreeKG.IsWeyl A n₀ := by
    intro a ha
    obtain ⟨i, j, k, hM, hi, hj, hk, hx⟩ := monoData a ha
    have hact : ∀ s : ↥(unitarySU 2 n K 6),
        a (φ s) = φ (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM s) :=
      hφact a (X ^ i * Y ^ j * Z ^ k) (X ^ i * Y ^ j * Z ^ k) hM hM (by simp) hx
    have hWm : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) =
        (X ^ i * Y ^ j * Z ^ k) * Z ^ j * (w : GL (Fin 6) K) :=
      UnitSixThreeKG.weyl_mono hwX hwZ hwY hXZ hYZ i j k
    have h5 : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) * (w : GL (Fin 6) K)⁻¹ =
        (X ^ i * Y ^ j * Z ^ k) * Z ^ j := by
      rw [hWm]
      group
    have h5inv : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k)⁻¹ *
        (w : GL (Fin 6) K)⁻¹ = ((X ^ i * Y ^ j * Z ^ k) * Z ^ j)⁻¹ := by
      rw [← h5]
      group
    have hZju : Z ^ j ∈ unitarySU 2 n K 6 := Subgroup.pow_mem _ hZu' j
    have hconj : w * (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM w)⁻¹ =
        (⟨Z ^ j, hZju⟩ : ↥(unitarySU 2 n K 6)) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
      rw [show (X ^ i * Y ^ j * Z ^ k * (w : GL (Fin 6) K) *
          (X ^ i * Y ^ j * Z ^ k)⁻¹)⁻¹ =
          (X ^ i * Y ^ j * Z ^ k) * (w : GL (Fin 6) K)⁻¹ *
            (X ^ i * Y ^ j * Z ^ k)⁻¹ by group]
      rw [show (w : GL (Fin 6) K) * ((X ^ i * Y ^ j * Z ^ k) *
          (w : GL (Fin 6) K)⁻¹ * (X ^ i * Y ^ j * Z ^ k)⁻¹) =
          (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) * (w : GL (Fin 6) K)⁻¹ *
            (X ^ i * Y ^ j * Z ^ k)⁻¹ by group, h5]
      rw [← ggUSixShCaseAux_zpow_mul_mono hXZ hYZ j i j k]
      group
    have hpow : (φ (w * (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM w)⁻¹)) ^ 3 = 1 := by
      rw [hconj, ← map_pow]
      have hZ3u : (⟨Z ^ j, hZju⟩ : ↥(unitarySU 2 n K 6)) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul, mul_comm j 3, pow_mul,
          hZ3, one_pow]
      rw [hZ3u, map_one]
    have h1 : φ w * (a (φ w))⁻¹ = φ (w * (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM w)⁻¹) := by
      rw [hact w, ← map_inv, ← map_mul]
    constructor
    · change (n₀ * (a n₀)⁻¹) ^ 3 = 1
      rw [show n₀ = φ w from rfl, h1]
      exact hpow
    · intro a' ha'
      obtain ⟨i', j', k', hM', hi', hj', hk', hx'⟩ := monoData a' ha'
      have hact' : ∀ s : ↥(unitarySU 2 n K 6),
          a' (φ s) = φ (LineU.conjN (X ^ i' * Y ^ j' * Z ^ k') hM' s) :=
        hφact a' (X ^ i' * Y ^ j' * Z ^ k') (X ^ i' * Y ^ j' * Z ^ k') hM' hM'
          (by simp) hx'
      change a' (n₀ * (a n₀)⁻¹) = n₀ * (a n₀)⁻¹
      rw [show n₀ = φ w from rfl, h1, hconj, hact' (⟨Z ^ j, hZju⟩ : ↥(unitarySU 2 n K 6))]
      congr 1
      apply Subtype.ext
      rw [LineU.coe_conjN]
      rw [← ggUSixShCaseAux_zpow_mul_mono hXZ hYZ j i' j' k']
      group
  intro a₀ ha₀ hne
  obtain ⟨i, j, k, hM, hi, hj, hk, hx⟩ := monoData a₀ ha₀
  have hunit : X ^ i * Y ^ j * Z ^ k ∈ primeFormUnitary hKd (idGram K 6) :=
    mul_mem (mul_mem (pow_mem hXu i) (pow_mem hYu j)) (pow_mem hZu k)
  by_cases hj0 : j = 0
  · by_cases hi0 : i = 0
    · by_cases hk0 : k = 0
      · have hM0eq : X ^ i * Y ^ j * Z ^ k = 1 := by
          rw [hi0, hj0, hk0]
          simp
        have hsub : (⟨X ^ i * Y ^ j * Z ^ k, hM⟩ :
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = 1 :=
          Subtype.ext hM0eq
        have hp1 : TableB.projConj (unitarySU 2 n K 6)
            ⟨X ^ i * Y ^ j * Z ^ k, hM⟩ = 1 := by
          rw [hsub, map_one]
        have hx1 : ∀ l : L', ψ (a₀ l) = ψ l := by
          intro l
          rw [← hx l, hp1]
          rfl
        have ha1 : a₀ = 1 :=
          TypeA.mulAut_eq_of_forall ψ hker hperf (a := a₀) (b := 1) (fun l => by
            rw [MulAut.one_apply]
            exact hx1 l)
        exact absurd ha1 hne
      · have hM0eq : X ^ i * Y ^ j * Z ^ k = Z ^ k := by
          rw [hi0, hj0]
          simp
        have hshapeZ : UnitSixThreeKG.ShapeBadMat hKd (Z ^ k) :=
          UnitSixThreeKG.shapeBad_of_central_pow hKd hpq hXu hZu hX3 hZ3 hζ hXY hXZ hYZ hZs hk hk0
        have hshape : UnitSixThreeKG.ShapeBadMat hKd (X ^ i * Y ^ j * Z ^ k) := by
          rw [hM0eq]
          exact hshapeZ
        exact Or.inl ⟨_, ⟨X ^ i * Y ^ j * Z ^ k, hM, hunit, hshape, rfl⟩, hx⟩
    · have hshape : UnitSixThreeKG.ShapeBadMat hKd (X ^ i * Y ^ j * Z ^ k) :=
        UnitSixThreeKG.shapeBad_of_mono hKd hpq hXu hYu hZu hX3 hZ3 hζ hXY hXZ hYZ
          (Or.inl hj0) (Or.inl hi0) hi hj k
      exact Or.inl ⟨_, ⟨X ^ i * Y ^ j * Z ^ k, hM, hunit, hshape, rfl⟩, hx⟩
  · refine Or.inr ⟨n₀, hWeyl, ?_⟩
    intro hc
    have hnj : ¬ 3 ∣ j := by
      have hj01 : j = 1 ∨ j = 2 := by omega
      rcases hj01 with rfl | rfl <;> norm_num
    have hMZ : (X ^ i * Y ^ j * Z ^ k) * Z ^ j ∈
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      Subgroup.mul_mem _ hM (Subgroup.pow_mem _ hZN j)
    obtain ⟨kk, hkk⟩ := Subgroup.mem_zpowers_iff.mp hc
    let mm : ℕ := (kk % 3).toNat
    have hmmz : (mm : ℤ) = kk % 3 := by
      dsimp [mm]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have h3a : a₀ ^ 3 = 1 := hA.2 a₀ ha₀
    have hcm : a₀ ^ mm = MulAut.conj n₀ * a₀ * (MulAut.conj n₀)⁻¹ := by
      rw [← hkk, ← zpow_natCast]
      rw [hmmz]
      exact (zpow_eq_zpow_emod' kk h3a).symm
    have hMm : (X ^ i * Y ^ j * Z ^ k) ^ mm ∈
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      Subgroup.pow_mem _ hM mm
    have hWm : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) =
        (X ^ i * Y ^ j * Z ^ k) * Z ^ j * (w : GL (Fin 6) K) :=
      UnitSixThreeKG.weyl_mono hwX hwZ hwY hXZ hYZ i j k
    have h5 : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) * (w : GL (Fin 6) K)⁻¹ =
        (X ^ i * Y ^ j * Z ^ k) * Z ^ j := by
      rw [hWm]
      group
    have h5inv : (w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k)⁻¹ *
        (w : GL (Fin 6) K)⁻¹ = ((X ^ i * Y ^ j * Z ^ k) * Z ^ j)⁻¹ := by
      rw [← h5]
      group
    have hact : ∀ s : ↥(unitarySU 2 n K 6),
        a₀ (φ s) = φ (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM s) :=
      hφact a₀ (X ^ i * Y ^ j * Z ^ k) (X ^ i * Y ^ j * Z ^ k) hM hM (by simp) hx
    have hstep1 : ∀ s : ↥(unitarySU 2 n K 6),
        (MulAut.conj n₀)⁻¹ (φ s) = φ ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w) := by
      intro s
      rw [show (MulAut.conj n₀)⁻¹ = MulAut.conj n₀⁻¹ from
        (map_inv (MulAut.conj : L' →* MulAut L') n₀).symm, MulAut.conj_apply]
      rw [inv_inv]
      rw [show n₀ = φ w from rfl, ← map_inv, ← map_mul, ← map_mul]
    have hstep2 : ∀ s : ↥(unitarySU 2 n K 6),
        a₀ (φ ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w)) =
          φ (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM
            ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w)) := by
      intro s
      exact hact ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w)
    have hstep3 : ∀ s : ↥(unitarySU 2 n K 6),
        (MulAut.conj n₀) (φ (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM
            ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w))) =
          φ (w * LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM
            ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w) * w⁻¹) := by
      intro s
      rw [MulAut.conj_apply]
      change n₀ * φ (LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM
          ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w)) * n₀⁻¹ = _
      rw [show n₀ = φ w from rfl, ← map_inv, ← map_mul, ← map_mul]
    have hstep4 : ∀ s : ↥(unitarySU 2 n K 6),
        w * LineU.conjN (X ^ i * Y ^ j * Z ^ k) hM
            ((w : ↥(unitarySU 2 n K 6))⁻¹ * s * w) * w⁻¹ =
          LineU.conjN ((X ^ i * Y ^ j * Z ^ k) * Z ^ j) hMZ s := by
      intro s
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
      rw [show (w : GL (Fin 6) K) * ((X ^ i * Y ^ j * Z ^ k) *
          ((w : GL (Fin 6) K)⁻¹ * (s : GL (Fin 6) K) * (w : GL (Fin 6) K)) *
            (X ^ i * Y ^ j * Z ^ k)⁻¹) * (w : GL (Fin 6) K)⁻¹ =
          ((w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k) * (w : GL (Fin 6) K)⁻¹) *
            (s : GL (Fin 6) K) *
              ((w : GL (Fin 6) K) * (X ^ i * Y ^ j * Z ^ k)⁻¹ *
                (w : GL (Fin 6) K)⁻¹) by group, h5, h5inv]
    have hcval : ∀ s : ↥(unitarySU 2 n K 6),
        (MulAut.conj n₀ * a₀ * (MulAut.conj n₀)⁻¹) (φ s) =
          φ (LineU.conjN ((X ^ i * Y ^ j * Z ^ k) * Z ^ j) hMZ s) := by
      intro s
      rw [MulAut.mul_apply, MulAut.mul_apply, hstep1, hstep2, hstep3, hstep4]
    have hleft : ∀ l : L',
        TableB.projConj (unitarySU 2 n K 6)
            ⟨(X ^ i * Y ^ j * Z ^ k) * Z ^ j, hMZ⟩ (ψ l) =
          ψ ((MulAut.conj n₀ * a₀ * (MulAut.conj n₀)⁻¹) l) := by
      intro l
      obtain ⟨s, rfl⟩ := hφs l
      rw [hφproj rfl s,
        LineU.projConj_mk_eq ((X ^ i * Y ^ j * Z ^ k) * Z ^ j) hMZ s,
        hcval s, hφproj rfl (LineU.conjN ((X ^ i * Y ^ j * Z ^ k) * Z ^ j) hMZ s)]
    have hMm_eq : TableB.projConj (unitarySU 2 n K 6)
          ⟨(X ^ i * Y ^ j * Z ^ k) ^ mm, hMm⟩ =
        (TableB.projConj (unitarySU 2 n K 6) ⟨X ^ i * Y ^ j * Z ^ k, hM⟩) ^ mm := by
      rw [← map_pow]
      congr 1
    have hright : ∀ l : L',
        TableB.projConj (unitarySU 2 n K 6)
            ⟨(X ^ i * Y ^ j * Z ^ k) ^ mm, hMm⟩ (ψ l) =
          ψ ((MulAut.conj n₀ * a₀ * (MulAut.conj n₀)⁻¹) l) := by
      intro l
      obtain ⟨s, rfl⟩ := hφs l
      rw [hMm_eq, show (MulAut.conj n₀ * a₀ * (MulAut.conj n₀)⁻¹) =
        a₀ ^ mm from hcm.symm]
      exact TypeA.induced_pow ψ hx mm (φ s)
    have hEqZ : TableB.projConj (unitarySU 2 n K 6)
          ⟨(X ^ i * Y ^ j * Z ^ k) * Z ^ j, hMZ⟩ =
        TableB.projConj (unitarySU 2 n K 6)
          ⟨(X ^ i * Y ^ j * Z ^ k) ^ mm, hMm⟩ :=
      TypeA.induced_unique ψ hψ hleft hright
    obtain ⟨c, hc⟩ := CFSG.StandardType.Line63.H5.exists_scalar_mul_of_projConj_eq'
      hKd hpq hMZ hMm hEqZ
    exact absurd hc
      (UnitSixThreeKG.mono_mul_ne hζ.pow_eq_one hX3 hZ3 hY3 hl hXY hXZ hYZ hZs hnj mm c)

theorem ggUSixSh_perLineSh_of_fieldType {K : Type} [Field K] [Finite K] {n : ℕ}
    (hKd : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {M : GL (Fin 6) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {l : Kˣ}
    (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hMA : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ TypeA.inducedSub ψ A) :
    GGUSixShPerLineOn ψ (ggUSixShSet hKd) A := by
  have hAb : CFSG.Open.IsElemAbelian 3 (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ TypeA.inducedSub ψ A, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K 6)) (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  obtain ⟨X, Z, hXN, hZN, ζ, hXu, hZu, hXA, hZA, hX3, hZ3, hζ, hXM, hXZ, hMZ, hZs⟩ :=
    UnitSixThreeKG.exists_fieldStruct hKd hK hpq hAb hAbI hcardAb hMN hMu hM3 hl hMA
  exact ggUSixSh_perLineSh_of_fieldTriple hKd hpq hperfSU hcov' hψ hker hperf hA hAI hcard hXN hMN hZN hXu
    hMu hZu hX3 hZ3 hM3 hl hζ hXM hXZ hMZ hZs hXA hMA hZA

end USixSh

end CFSG.StandardType

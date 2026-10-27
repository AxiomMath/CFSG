module

public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_twisted_param_aux (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) (m : ℕ)
    (hm : Odd m) (Wm : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (i j : Fin ReeTag.F4.tag.rank)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin ReeTag.F4.tag.rank),
      (∑ l, U s l * Wm l k) ≡
        U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      (∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U)) ∧
      (∀ z, Φ z ∈ torusGroup ReeTag.F4.tag L) ∧
      (∀ z, Φ z ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  classical
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    exact (Nat.not_even_iff_odd.2 hm) ⟨c, by omega⟩
  have hm0 : (m : L) ≠ 0 := fun h => hm2 ((CharP.cast_eq_zero_iff L 2 m).1 h)
  have : NeZero m := ⟨fun h => hm2 (by simp [h])⟩
  have : NeZero (m : L) := ⟨hm0⟩
  let φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* (Fin ReeTag.F4.tag.rank → Lˣ) :=
    { toFun := fun z => expTuple (z.1 : Lˣ) (z.2 : Lˣ) U
      map_one' := by
        funext l
        simp [expTuple]
      map_mul' := fun z z' => by
        simpa using expTuple_mul (z.1 : Lˣ) (z.2 : Lˣ) (z'.1 : Lˣ) (z'.2 : Lˣ) U }
  let Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L :=
    (rootDiagUnitHom ReeTag.F4.tag L).comp φ
  have hΦ : ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) :=
    fun z => rfl
  have hroot : ∀ z : (rootsOfUnity m L) × (rootsOfUnity m L),
      (z.1 : Lˣ) ^ m = 1 ∧ (z.2 : Lˣ) ^ m = 1 :=
    fun z => ⟨(mem_rootsOfUnity m _).1 z.1.2, (mem_rootsOfUnity m _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z.1 : Lˣ) ^ U 0 i * (z.2 : Lˣ) ^ U 1 i = 1 := congrFun hb i
    have hB : (z.1 : Lˣ) ^ U 0 j * (z.2 : Lˣ) ^ U 1 j = 1 := congrFun hb j
    obtain ⟨hm1, hm2'⟩ := hroot z
    have h1 := zpow_minor_eq_one hA hB
    have h2 := zpow_minor_eq_one (x := (z.2 : Lˣ)) (y := (z.1 : Lˣ)) (by rwa [mul_comm] at hA)
      (by rwa [mul_comm] at hB)
    have h2' : (z.2 : Lˣ) ^ (U 0 i * U 1 j - U 0 j * U 1 i) = 1 := by
      have : U 1 i * U 0 j - U 1 j * U 0 i = -(U 0 i * U 1 j - U 0 j * U 1 i) := by ring
      rw [this, zpow_neg, inv_eq_one] at h2
      exact h2
    have e1 := zpow_eq_one_of_coprime hm1 h1 hdet
    have e2 := zpow_eq_one_of_coprime hm2' h2' hdet
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  refine ⟨Φ, hinj, hΦ, fun z => ?_, fun z => ?_⟩
  · rw [hΦ]
    exact rootDiagUnit_mem_torusGroup _
  · rw [hΦ, rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF w]
    apply rootChar_smul_eq_of_forall_single
    intro k
    obtain ⟨hm1, hm2'⟩ := hroot z
    rw [rootChar_expTuple, CTTorus.rootChar_single, reeTuple, expTuple]
    have hpow : ∀ (n : ℕ) (x : Lˣ), x ^ n = x ^ (n : ℤ) := fun n x => (zpow_natCast x n).symm
    rw [hpow, mul_zpow, ← zpow_mul, ← zpow_mul]
    congr 1
    · refine zpow_eq_zpow_of_modEq hm1 ?_
      have h0 := hfix 0 k
      simp only [hW] at *
      exact h0
    · refine zpow_eq_zpow_of_modEq hm2' ?_
      have h1 := hfix 1 k
      simp only [hW] at *
      exact h1

theorem exists_twisted_param (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) (m : ℕ)
    (hm : Odd m) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ) (i j : Fin 4)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin 4),
      (∑ l, U s l * Wm l k) ≡
        U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
          (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
            ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      (∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U)) ∧
      (∀ z, Φ z ∈ torusGroup ReeTag.F4.tag L) ∧
      (∀ z, Φ z ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  refine exists_twisted_param_aux hF w m hm Wm U i j hW hdet (fun s k => ?_)
  have h := hfix s k
  have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
  have h1 := congrArg (fun j : Fin 4 => U s j *
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j) e
  have h2 : U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) k)
        = U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) := by
    rw [relExp_vec a (ReeTag.F4.perm k)]
    exact h1.symm
  rw [← h2]
  exact h

structure ParamData (a : ℕ) (L : Type) [Field L] [CharP L 2] [IsAlgClosed L]
    (F : MulAut (adjointGroup ReeTag.F4.tag L)) (w : WeylGroup ReeTag.F4.tag) (m : ℕ)
    (U : Fin 2 → Fin 4 → ℤ) : Prop where
  param : ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
    Function.Injective Φ ∧
    (∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U)) ∧
    (∀ z, Φ z ∈ torusGroup ReeTag.F4.tag L) ∧
    (∀ z, Φ z ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))

@[expose] def uPhi2 (a : ℕ) : Fin 2 → Fin 4 → ℤ :=
  ![![0, -1, 0, 1 - 2 ^ a], ![-1, -1, -2 ^ a, 2]]

@[expose] def mPhi2 (a : ℕ) : ℕ := 2 ^ (2 * a + 1) + 1

theorem torusParam_phi2 (hF : IsReeFrob a F) :
    ParamData a L F wPhi2 (mPhi2 a) (uPhi2 a) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have hm : Odd (2 ^ (2 * a + 1) + 1) := by
    refine Even.add_one ?_
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  refine ⟨exists_twisted_param hF wPhi2 (2 ^ (2 * a + 1) + 1) hm
    (toMat 4 [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]])
    (uPhi2 a) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_⟩
  · exact ⟨-1, 0, by norm_num [uPhi2]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, uPhi2] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] def uPhi4m (a : ℕ) : Fin 2 → Fin 4 → ℤ :=
  ![![-1, 0, 0, 1 - 2 ^ a], ![-1, -1, 1 - 2 ^ a, 1]]

@[expose] def mPhi4m (a : ℕ) : ℕ := 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1

theorem torusParam_phi4m (hF : IsReeFrob a F) :
    ParamData a L F wPhi4m (mPhi4m a) (uPhi4m a) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : Odd (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by
    rw [Nat.odd_iff]
    omega
  have hmc : (((2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 : ℕ)) : ℤ) =
      2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  refine ⟨exists_twisted_param hF wPhi4m (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) hm
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    (uPhi4m a) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_⟩
  · rw [hmc]
    exact ⟨1, 0, by norm_num [uPhi4m]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, hmc, uPhi4m] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] def uPhi4p (a : ℕ) : Fin 2 → Fin 4 → ℤ :=
  ![![-1, 0, 0, -2 ^ a], ![-1, -1, -2 ^ a, 1]]

@[expose] def mPhi4p (a : ℕ) : ℕ := 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1

theorem torusParam_phi4p (hF : IsReeFrob a F) :
    ParamData a L F wPhi4p (mPhi4p a) (uPhi4p a) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  have hm : Odd (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) := by
    rw [Nat.odd_iff]
    omega
  refine ⟨exists_twisted_param hF wPhi4p (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) hm
    (toMat 4 [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]])
    (uPhi4p a) 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_⟩
  · exact ⟨1, 0, by norm_num [uPhi4p]⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, uPhi4p] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

end CFSG.RankThree.PartOne.KEXC

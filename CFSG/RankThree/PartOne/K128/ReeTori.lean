module

public import CFSG.RankThree.PartOne.KLC.TwF4Torus
public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KLC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem torus_hom_m_phi2 (hF : IsReeFrob a F) {m : ℕ} (hm : Odd m)
    (hmM : (m : ℤ) ∣ 2 ^ (2 * a + 1) + 1) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted hF wPhi2 hm
    (toMat 4 [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]])
    ![![0, -1, 0, 1 - 2 ^ a], ![-1, -1, -2 ^ a, 2]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨-1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

theorem torus_hom_m_phi1 (hF : IsReeFrob a F) {m : ℕ} (hm : Odd m)
    (hmM : (m : ℤ) ∣ 2 ^ (2 * a + 1) - 1) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi1) := by
  have hW : wordMat ReeTag.F4.tag [] =
      toMat ReeTag.F4.tag.rank [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted hF wPhi1 hm
    (toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    ![![-1, 0, 0, -2 ^ a], ![0, -1, -2 ^ a, 0]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨1, ?_⟩; ring1)

theorem torus_hom_m_phi4m (hF : IsReeFrob a F) {m : ℕ} (hm : Odd m)
    (hmM : (m : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted hF wPhi4m hm
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    ![![-1, 0, 0, 1 - 2 ^ a], ![-1, -1, 1 - 2 ^ a, 1]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

theorem torus_hom_m_phi4p (hF : IsReeFrob a F) {m : ℕ} (hm : Odd m)
    (hmM : (m : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4p) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted hF wPhi4p hm
    (toMat 4 [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]])
    ![![-1, 0, 0, -2 ^ a], ![-1, -1, -2 ^ a, 1]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] def expTuple1 (ξ : Lˣ) (U : Fin ReeTag.F4.tag.rank → ℤ) :
    Fin ReeTag.F4.tag.rank → Lˣ := fun i => ξ ^ U i

omit [CharP L 2] [IsAlgClosed L] in
theorem rootChar_expTuple1 (ξ : Lˣ) (U v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple1 ξ U) v = ξ ^ (∑ i, U i * v i) := by
  simp only [rootChar, expTuple1, ← zpow_mul]
  rw [KLR.prod_zpow_eq_zpow_sum]

theorem exists_hom_twisted_rank1_aux (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (Wm : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ)
    (U : Fin ReeTag.F4.tag.rank → ℤ) (i : Fin ReeTag.F4.tag.rank)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hunit : IsCoprime (U i) (m : ℤ))
    (hfix : ∀ k : Fin ReeTag.F4.tag.rank, (∑ l, U l * Wm l k) ≡
      U (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  classical
  let φ : (rootsOfUnity m L) →* (Fin ReeTag.F4.tag.rank → Lˣ) :=
    { toFun := fun z => expTuple1 (z : Lˣ) U
      map_one' := by
        funext l
        simp [expTuple1]
      map_mul' := fun z z' => by
        funext l
        simp [expTuple1, mul_zpow] }
  let Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L :=
    (rootDiagUnitHom ReeTag.F4.tag L).comp φ
  have hΦ : ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple1 (z : Lˣ) U) := fun z => rfl
  have hroot : ∀ z : rootsOfUnity m L, (z : Lˣ) ^ m = 1 := fun z => (mem_rootsOfUnity m _).1 z.2
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z : Lˣ) ^ U i = 1 := congrFun hb i
    exact Subtype.ext (zpow_eq_one_of_coprime (hroot z) hA hunit)
  refine ⟨Φ, hinj, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [hΦ]
    exact rootDiagUnit_mem_torusGroup _
  · rintro _ ⟨z, rfl⟩
    rw [hΦ, rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF w]
    apply rootChar_smul_eq_of_forall_single
    intro k
    rw [rootChar_expTuple1, CTTorus.rootChar_single, reeTuple, expTuple1]
    have hpow : ∀ (n : ℕ) (x : Lˣ), x ^ n = x ^ (n : ℤ) := fun n x => (zpow_natCast x n).symm
    rw [hpow, ← zpow_mul]
    refine zpow_eq_zpow_of_modEq (hroot z) ?_
    have h0 := hfix k
    simp only [hW] at *
    exact h0

theorem exists_hom_twisted_rank1 (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 4 → ℤ) (i : Fin 4)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hunit : IsCoprime (U i) (m : ℤ))
    (hfix : ∀ k : Fin 4, (∑ l, U l * Wm l k) ≡
      U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
        (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  refine exists_hom_twisted_rank1_aux hF w Wm U i hW hunit (fun k => ?_)
  have h := hfix k
  have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
  have h1 := congrArg (fun j : Fin 4 => U j *
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j) e
  have h2 : U ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) k)
        = U (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) := by
    rw [relExp_vec a (ReeTag.F4.perm k)]
    exact h1.symm
  rw [← h2]
  exact h

@[expose] noncomputable def wPhi6 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [1, 2, 1, 0]

theorem torus_hom_m_phi6 (hF : IsReeFrob a F) {m : ℕ}
    (hmM : (m : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi6) := by
  have hW : wordMat ReeTag.F4.tag [1, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 1, 0, 0], [-2, 1, 0, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_rank1 hF wPhi6
    (toMat 4 [[-1, 1, 0, 0], [-2, 1, 0, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    ![1 - 2 * (2 ^ a) ^ 2, -1, -(2 ^ a), -2 * (2 ^ a) ^ 3 + 2 * 2 ^ a + 1] 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨-1, 0, by norm_num⟩
  · intro k
    fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] noncomputable def wPhi12m : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [1, 0]

theorem torus_hom_m_phi12m (hF : IsReeFrob a F) {m : ℕ}
    (hmM : (m : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 -
      2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1)) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi12m) := by
  have hW : wordMat ReeTag.F4.tag [1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 1, 0, 0], [-1, 0, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_rank1 hF wPhi12m
    (toMat 4 [[-1, 1, 0, 0], [-1, 0, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    ![1, -2 * (2 ^ a) ^ 2 - 1, -2 * (2 ^ a) ^ 3 + 2 * (2 ^ a) ^ 2 - 2 ^ a + 1, 2 ^ a] 0
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro k
    fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] noncomputable def wPhi12p : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 2, 3, 0, 1, 2, 0, 1, 0]

theorem torus_hom_m_phi12p (hF : IsReeFrob a F) {m : ℕ}
    (hmM : (m : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 +
      2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1)) :
    ∃ Φ : (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi12p) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 2, 3, 0, 1, 2, 0, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-2, -1, 1, 1], [-2, -2, 2, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_rank1 hF wPhi12p
    (toMat 4 [[-1, -1, 1, 0], [-2, -1, 1, 1], [-2, -2, 2, 1], [-2, 0, 1, 0]])
    ![-2 * 2 ^ a - 1, -2 * (2 ^ a) ^ 2 - 2 * 2 ^ a - 1, 2 ^ a + 1, -2 * (2 ^ a) ^ 3 + 2 ^ a] 2
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · obtain ⟨c, hc⟩ := hmM
    refine ⟨-(4 * (2 ^ a) ^ 3 + 2 * 2 ^ a), c, ?_⟩
    simp only [Matrix.cons_val]
    linear_combination (-1 : ℤ) * hc
  · intro k
    fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 (hmM.trans ?_) <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

end CFSG.RankThree.PartOne.K128

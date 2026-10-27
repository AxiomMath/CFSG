module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
import CFSG.GH74.Filter.Lie.TwistedF4
import CFSG.GH74.Filter.Orthogonal.EvenEichler
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3
import CFSG.GH74.SmallRanks
import CFSG.LieType.BorelTits.AllModels
import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC

section SmallGroups

open CFSG.Open CFSG.GH74 CFSG.GH74.SmallRanks

@[expose] def uc22lbAlt6Elt : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem uc22lb_orderOf_alt6Elt : orderOf uc22lbAlt6Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

theorem uc22lb_factorization_two_card_alt6 :
    (Nat.card (alternatingGroup (Fin 6))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact factorization_two_pow_mul_odd (by decide)

theorem uc22lb_twoRank_alt6_le_two : twoRank (alternatingGroup (Fin 6)) ≤ 2 :=
  twoRank_le_two_of_orderOf uc22lbAlt6Elt 2 uc22lb_orderOf_alt6Elt
    uc22lb_factorization_two_card_alt6

@[expose] def uc22lbAlt7Elt : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem uc22lb_orderOf_alt7Elt : orderOf uc22lbAlt7Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

theorem uc22lb_factorization_two_card_alt7 :
    (Nat.card (alternatingGroup (Fin 7))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact factorization_two_pow_mul_odd (by decide)

theorem uc22lb_twoRank_alt7_le_two : twoRank (alternatingGroup (Fin 7)) ≤ 2 :=
  twoRank_le_two_of_orderOf uc22lbAlt7Elt 2 uc22lb_orderOf_alt7Elt
    uc22lb_factorization_two_card_alt7

theorem uc22lb_notSmall_of_big {L : Type} [Group L] [Finite L]
    (h3 : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L)) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsL2Odd L p ∧ ¬ IsL3Odd L p) ∧ ¬ IsAlt L 6 ∧ ¬ IsAlt L 7 := by
  refine ⟨fun p hp hp2 => ⟨fun hl2 => ?_, fun hl3 => ?_⟩, fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · have := twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 hl2
    unfold twoRank at this
    omega
  · have :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pRank_two_le_two_of_PSL3 hp hp2 hl3
    omega
  · have h1 := twoRank_eq_of_mulEquiv e
    have h2 := uc22lb_twoRank_alt6_le_two
    unfold twoRank at h1 h2
    omega
  · have h1 := twoRank_eq_of_mulEquiv e
    have h2 := uc22lb_twoRank_alt7_le_two
    unfold twoRank at h1 h2
    omega

end SmallGroups

section ClassicalEven

open CFSG.Assembly.LowTwoRank CFSG.GH74.Filter CFSG.SectionRank CFSG.SectionRank.ClassicalOdd
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem uc22lb_big_psl {L : Type} [Group L] {m f : ℕ} (hf : 3 ≤ f)
    (h : StatedClassicalModel L .PSL m 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨⟨hp, hf1, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, ?_⟩
  have h1 := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := m) (a := 1) (b := 1) le_rfl
    (by omega) hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  omega

theorem uc22lb_big_psp {L : Type} [Group L] {m f : ℕ} (h : StatedClassicalModel L .PSp m 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨⟨hp, hf1, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, ?_⟩
  have h1 := CFSG.SectionRank.ClassicalOdd.le_pRank_Sp (n := m) hm hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  have : 1 * (2 + 1) ≤ f * (m + 1) := Nat.mul_le_mul hf1 (by omega)
  omega

theorem uc22lb_big_pOmegaPlus {L : Type} [Group L] {m f : ℕ}
    (h : StatedClassicalModel L .POmegaPlus m 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn4 : 4 ≤ m := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card hK
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, ?_⟩
  have h := le_pRank_statedProj_statedOmega hK (coe_quadPlus m K)
    (plusPair K (⟨0, by omega⟩ : Fin m)) (commutator_orthogonalGroup_quadPlus (by omega))
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  have h6 : 1 * 6 ≤ f * (m + m - 2) := Nat.mul_le_mul hf (by omega)
  omega

theorem uc22lb_big_pOmegaMinus {L : Type} [Group L] {m f : ℕ}
    (h : StatedClassicalModel L .POmegaMinus m 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hn4 : 4 ≤ m := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card hK
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, ?_⟩
  have h := le_pRank_statedProj_statedOmega hK (coe_quadMinus m K b c)
    (minusPair K b c (⟨0, by omega⟩ : Fin (m - 1))) (commutator_orthogonalGroup_quadMinus hn4 hirr)
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  have h6 : 1 * 6 ≤ f * (m - 1 + (m - 1 + 2) - 2) := Nat.mul_le_mul hf (by omega)
  omega

end ClassicalEven

section Unitary

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalOdd

variable {m : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] def uc22lbM (u w : Fin m → K) (c d : K) : Matrix (Fin m) (Fin m) K :=
  1 + c • vecMulVec u u + d • vecMulVec w w

theorem uc22lbM_zero (u w : Fin m → K) : uc22lbM u w 0 0 = 1 := by simp [uc22lbM]

theorem uc22lbM_mul (u w : Fin m → K) (huu : u ⬝ᵥ u = 0) (huw : u ⬝ᵥ w = 0) (hwu : w ⬝ᵥ u = 0)
    (hww : w ⬝ᵥ w = 0) (c d c' d' : K) :
    uc22lbM u w c d * uc22lbM u w c' d' = uc22lbM u w (c + c') (d + d') := by
  have h11 : vecMulVec u u * vecMulVec u u = 0 := by
    rw [vecMulVec_mul_vecMulVec, huu, zero_smul, vecMulVec_zero]
  have h12 : vecMulVec u u * vecMulVec w w = 0 := by
    rw [vecMulVec_mul_vecMulVec, huw, zero_smul, vecMulVec_zero]
  have h21 : vecMulVec w w * vecMulVec u u = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwu, zero_smul, vecMulVec_zero]
  have h22 : vecMulVec w w * vecMulVec w w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hww, zero_smul, vecMulVec_zero]
  simp only [uc22lbM, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h11, h12,
    h21, h22, smul_zero, add_zero, add_smul]
  abel

theorem uc22lbM_transpose (u w : Fin m → K) (c d : K) :
    (uc22lbM u w c d)ᵀ = uc22lbM u w c d := by
  ext i j
  simp only [uc22lbM, transpose_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, one_apply]
  rw [mul_comm (u j) (u i), mul_comm (w j) (w i)]
  simp only [eq_comm]

theorem uc22lbM_map_pow {f : ℕ} (u w : Fin m → K) (hu : ∀ i, u i ^ 2 ^ f = u i)
    (hw : ∀ i, w i ^ 2 ^ f = w i) (c d : K) :
    (uc22lbM u w c d).map (· ^ 2 ^ f) = uc22lbM u w (c ^ 2 ^ f) (d ^ 2 ^ f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext i j
  simp only [uc22lbM, map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, one_apply, add_pow_char_pow, mul_pow, hu, hw]
  congr 2
  split_ifs <;> simp

theorem uc22lbM_unitary {f : ℕ} (u w : Fin m → K) (hu : ∀ i, u i ^ 2 ^ f = u i)
    (hw : ∀ i, w i ^ 2 ^ f = w i) (huu : u ⬝ᵥ u = 0) (huw : u ⬝ᵥ w = 0) (hwu : w ⬝ᵥ u = 0)
    (hww : w ⬝ᵥ w = 0) (c d : K) (hc : c ^ 2 ^ f + c = 0) (hd : d ^ 2 ^ f + d = 0) :
    ((uc22lbM u w c d).map (· ^ 2 ^ f))ᵀ * uc22lbM u w c d = 1 := by
  rw [uc22lbM_map_pow u w hu hw, uc22lbM_transpose, uc22lbM_mul u w huu huw hwu hww, hc, hd,
    uc22lbM_zero]

theorem uc22lbM_mulVec (u w : Fin m → K) (huu : u ⬝ᵥ u = 0) (hwu : w ⬝ᵥ u = 0) (c d : K) :
    uc22lbM u w c d *ᵥ u = u := by
  simp only [uc22lbM, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, huu, hwu]
  simp

@[expose] def uc22lbVec (i j : Fin m) : Fin m → K := Pi.single i 1 + Pi.single j 1

theorem uc22lbVec_pow {f : ℕ} {i j : Fin m} (hij : i ≠ j) (k : Fin m) :
    uc22lbVec (K := K) i j k ^ 2 ^ f = uc22lbVec i j k := by
  simp only [uc22lbVec, Pi.add_apply, Pi.single_apply]
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj]

theorem uc22lbVec_dot_self {i j : Fin m} (hij : i ≠ j) :
    uc22lbVec (K := K) i j ⬝ᵥ uc22lbVec i j = 0 := by
  simp only [uc22lbVec, add_dotProduct, dotProduct_add, single_dotProduct, dotProduct_single,
    Pi.add_apply, Pi.single_apply, hij, hij.symm, if_true, if_false]
  simp
  exact CharTwo.add_self_eq_zero (1 : K)

theorem uc22lbVec_dot_disjoint {i j k l : Fin m} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : uc22lbVec (K := K) i j ⬝ᵥ uc22lbVec k l = 0 := by
  simp only [uc22lbVec, add_dotProduct, dotProduct_add, single_dotProduct, dotProduct_single,
    Pi.add_apply, Pi.single_apply, hik, hil, hjk, hjl, hik.symm, hil.symm, hjk.symm, hjl.symm,
    if_true, if_false]
  simp

@[expose] def uc22lbTr (K : Type) [Field K] [CharP K 2] (f : ℕ) : K →+ K where
  toFun c := c ^ 2 ^ f + c
  map_zero' := by simp
  map_add' c d := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simp only [add_pow_char_pow]
    abel

theorem uc22lbTr_apply (f : ℕ) (c : K) : uc22lbTr K f c = c ^ 2 ^ f + c := rfl

theorem uc22lbTr_uc22lbTr [Finite K] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (c : K) :
    uc22lbTr K f (uc22lbTr K f c) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have h := FiniteField.pow_card c
  rw [hc] at h
  have hh : (c ^ 2 ^ f) ^ 2 ^ f = c := by rw [← pow_mul, ← sq]; exact h
  rw [uc22lbTr_apply, uc22lbTr_apply, add_pow_char_pow, hh]
  linear_combination (CharTwo.add_self_eq_zero c) + (CharTwo.add_self_eq_zero (c ^ 2 ^ f))

theorem uc22lb_two_pow_le_card_ker [Finite K] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) :
    2 ^ f ≤ Nat.card (uc22lbTr K f).ker := by
  have h1 := AddSubgroup.card_ker_mul_card_range (uc22lbTr K f)
  have h2 : (uc22lbTr K f).range ≤ (uc22lbTr K f).ker := by
    rintro _ ⟨c, rfl⟩
    exact uc22lbTr_uc22lbTr hK c
  have h3 : Nat.card (uc22lbTr K f).range ≤ Nat.card (uc22lbTr K f).ker :=
    AddSubgroup.card_le_of_le h2
  rw [hK] at h1
  by_contra h
  have h := not_le.1 h
  nlinarith

theorem uc22lb_three_le_pRank_of_family [Finite K] {f : ℕ} {V : Type} [AddCommGroup V] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (hVcard : 8 ≤ Nat.card V) (α β : V →+ K)
    (hα : ∀ v, α v ^ 2 ^ f + α v = 0) (hβ : ∀ v, β v ^ 2 ^ f + β v = 0) (u w : Fin m → K)
    (hu : ∀ i, u i ^ 2 ^ f = u i) (hw : ∀ i, w i ^ 2 ^ f = w i) (huu : u ⬝ᵥ u = 0)
    (huw : u ⬝ᵥ w = 0) (hwu : w ⬝ᵥ u = 0) (hww : w ⬝ᵥ w = 0) (hu0 : u ≠ 0)
    (hinj : Function.Injective fun v => uc22lbM u w (α v) (β v)) :
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedSU m (2 ^ f) K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : Multiplicative V →* GL (Fin m) K :=
    glOfAdd (fun v : V => uc22lbM u w (α v) (β v)) (by simp [uc22lbM_zero]) (fun a b => by
      rw [map_add, map_add, uc22lbM_mul u w huu huw hwu hww])
  have hφ : ∀ a, (φ a : Matrix (Fin m) (Fin m) K) = uc22lbM u w (α a.toAdd) (β a.toAdd) :=
    fun a => rfl
  have hpow : ∀ a : Multiplicative V, a ^ 2 = 1 := fun a => by
    rw [sq]
    exact congrArg Multiplicative.ofAdd (hV2 a.toAdd)
  have hP : IsPGroup 2 (Multiplicative V) := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcard : Nat.card (Multiplicative V) = Nat.card V := Nat.card_congr Multiplicative.toAdd
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := le_pRank_statedProj (H := StatedSU m (2 ^ f) K) Nat.one_lt_two multiplicative_comm hpow
    hk φ (glOfAdd_injective hinj) (fun a => ?_) (v := u) hu0 (fun a => ?_)
  · omega
  · refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine det_eq_one_of_pow_char (p := 2) ?_
      rw [sq, hφ, uc22lbM_mul u w huu huw hwu hww, CharTwo.add_self_eq_zero,
        CharTwo.add_self_eq_zero, uc22lbM_zero]
    · rw [hφ]
      exact uc22lbM_unitary u w hu hw huu huw hwu hww _ _ (hα _) (hβ _)
  · rw [hφ]
    exact uc22lbM_mulVec u w huu hwu _ _

theorem uc22lb_big_psu {L : Type} [Group L] {m f : ℕ} (hmf : (4 ≤ m ∧ 2 ≤ f) ∨ (2 ≤ m ∧ 3 ≤ f))
    (h : StatedClassicalModel L .PSU m 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨⟨hp, hf, hm, hnq⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  have hK' : Nat.card K = (2 ^ f) ^ 2 := hK
  have hfix := uc22lb_two_pow_le_card_ker hK'
  have hmem : ∀ c : (uc22lbTr K f).ker, (c : K) ^ 2 ^ f + (c : K) = 0 := fun c => c.2
  rcases hmf with ⟨hm4, hf2⟩ | ⟨hm2, hf3⟩
  ·
    have hne01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hne23 : (⟨2, by omega⟩ : Fin m) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    refine uc22lb_three_le_pRank_of_family (f := f)
      (V := (uc22lbTr K f).ker × (uc22lbTr K f).ker) (fun v => Prod.ext (Subtype.ext
        (CharTwo.add_self_eq_zero _)) (Subtype.ext (CharTwo.add_self_eq_zero _))) ?_
      (((uc22lbTr K f).ker.subtype).comp (AddMonoidHom.fst _ _))
      (((uc22lbTr K f).ker.subtype).comp (AddMonoidHom.snd _ _)) (fun v => hmem v.1)
      (fun v => hmem v.2) (uc22lbVec ⟨0, by omega⟩ ⟨1, by omega⟩)
      (uc22lbVec ⟨2, by omega⟩ ⟨3, by omega⟩)
      (uc22lbVec_pow hne01) (uc22lbVec_pow hne23) (uc22lbVec_dot_self hne01)
      (uc22lbVec_dot_disjoint (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]))
      (uc22lbVec_dot_disjoint (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]))
      (uc22lbVec_dot_self hne23) ?_ ?_
    · rw [Nat.card_prod]
      nlinarith
    · intro hu
      have := congrFun hu ⟨0, by omega⟩
      simp [uc22lbVec] at this
    · intro a b hab
      have h1 := congrFun (congrFun hab ⟨0, by omega⟩) ⟨0, by omega⟩
      have h2 := congrFun (congrFun hab ⟨2, by omega⟩) ⟨2, by omega⟩
      simp [uc22lbM, uc22lbVec, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply,
        Pi.single_apply, Matrix.one_apply] at h1 h2
      exact Prod.ext h1 h2
  ·
    have hne01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    refine uc22lb_three_le_pRank_of_family (f := f) (V := (uc22lbTr K f).ker)
      (fun v => Subtype.ext (CharTwo.add_self_eq_zero _)) (by omega)
      ((uc22lbTr K f).ker.subtype) 0 hmem (fun v => by simp)
      (uc22lbVec ⟨0, by omega⟩ ⟨1, by omega⟩) 0 (uc22lbVec_pow hne01) (fun i => by simp)
      (uc22lbVec_dot_self hne01) (by simp) (by simp) (by simp) ?_ ?_
    · intro hu
      have := congrFun hu ⟨0, by omega⟩
      simp [uc22lbVec] at this
    · intro a b hab
      have h1 := congrFun (congrFun hab ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [uc22lbM, uc22lbVec, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply,
        Pi.single_apply, Matrix.one_apply] at h1
      exact h1

end Unitary

section Alt9

open Equiv

@[expose] def uc22lbAltX : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22lbAltY : alternatingGroup (Fin 9) :=
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22lbAltZ : alternatingGroup (Fin 9) :=
  ⟨swap 4 5 * swap 6 7, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem uc22lbAlt_xy : uc22lbAltX * uc22lbAltY = uc22lbAltY * uc22lbAltX := by decide +kernel

theorem uc22lbAlt_xz : uc22lbAltX * uc22lbAltZ = uc22lbAltZ * uc22lbAltX := by decide +kernel

theorem uc22lbAlt_yz : uc22lbAltY * uc22lbAltZ = uc22lbAltZ * uc22lbAltY := by decide +kernel

theorem uc22lbAlt_ox : orderOf uc22lbAltX = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem uc22lbAlt_oy : orderOf uc22lbAltY = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem uc22lbAlt_oz : orderOf uc22lbAltZ = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem uc22lbAlt_xne : uc22lbAltX ≠ uc22lbAltY := by decide +kernel

theorem uc22lbAlt_notMem :
    uc22lbAltZ ∉ Subgroup.zpowers uc22lbAltX ⊔ Subgroup.zpowers uc22lbAltY := by
  intro h
  let S : Subgroup (alternatingGroup (Fin 9)) :=
    MulAction.stabilizer (alternatingGroup (Fin 9)) (4 : Fin 9)
  have hx : Subgroup.zpowers uc22lbAltX ≤ S := by
    rw [Subgroup.zpowers_le]
    change uc22lbAltX • (4 : Fin 9) = 4
    decide +kernel
  have hy : Subgroup.zpowers uc22lbAltY ≤ S := by
    rw [Subgroup.zpowers_le]
    change uc22lbAltY • (4 : Fin 9) = 4
    decide +kernel
  have := sup_le hx hy h
  change uc22lbAltZ • (4 : Fin 9) = 4 at this
  revert this
  decide +kernel

theorem uc22lb_big_alt9 {L : Type} [Group L] (e : L ≃* alternatingGroup (Fin 9)) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  haveI : Finite L := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨inferInstance, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e]
  obtain ⟨E₁, hE₁x, hE₁y, hE₁, hE₁card, hE₁le⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 1) (secondRank := 1) (Subgroup.zpowers uc22lbAltX)
      (Subgroup.zpowers uc22lbAltY)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary uc22lbAltX uc22lbAlt_ox)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary uc22lbAltY uc22lbAlt_oy)
      (by rw [Nat.card_zpowers, uc22lbAlt_ox, pow_one])
      (by rw [Nat.card_zpowers, uc22lbAlt_oy, pow_one])
      (by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, rfl⟩
        exact ((Commute.zpow_left (Commute.symm uc22lbAlt_xy) k)).eq)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint _ uc22lbAltY uc22lbAlt_oy (by
        rw [mem_zpowers_iff_mem_range_orderOf, uc22lbAlt_ox, Finset.mem_image]
        rintro ⟨k, hk, hky⟩
        rw [Finset.mem_range] at hk
        interval_cases k
        · rw [pow_zero] at hky
          revert hky
          decide +kernel
        · rw [pow_one] at hky
          exact uc22lbAlt_xne hky))
  have hzE : uc22lbAltZ ∉ E₁ := fun h => uc22lbAlt_notMem (hE₁le h)
  have hcx : Subgroup.zpowers uc22lbAltX ≤
      Subgroup.centralizer (Subgroup.zpowers uc22lbAltZ : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (Commute.symm uc22lbAlt_xz) k)).eq
  have hcy : Subgroup.zpowers uc22lbAltY ≤
      Subgroup.centralizer (Subgroup.zpowers uc22lbAltZ : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (Commute.symm uc22lbAlt_yz) k)).eq
  obtain ⟨E, -, -, hE, hEcard, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 2) (secondRank := 1) E₁ (Subgroup.zpowers uc22lbAltZ) hE₁
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary uc22lbAltZ uc22lbAlt_oz)
      (by rw [hE₁card])
      (by rw [Nat.card_zpowers, uc22lbAlt_oz, pow_one])
      (hE₁le.trans (sup_le hcx hcy))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint E₁ uc22lbAltZ uc22lbAlt_oz hzE)
  exact CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hE (k := 1 + 1 + 1) hEcard

theorem uc22lb_nonab_alt9 : ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
  refine ⟨⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 0 4 * swap 1 5, by rw [Perm.mem_alternatingGroup]; decide⟩, ?_⟩
  decide +kernel

end Alt9

section Nonabelian

theorem uc22lb_nonab_of_big {L : Type} [Group L]
    (hbig : ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L))
    (hBT : ∀ U : Subgroup L, U ≠ ⊥ → IsPGroup 2 U →
      ∃ P : Subgroup L, P ≠ ⊤ ∧ Subgroup.normalizer (U : Set L) ≤ P) :
    ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨hfin, h3⟩ := hbig
  haveI := hfin
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two (⊤ : Subgroup L)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup L) := Nat.pow_le_pow_right (by norm_num) h3
  have hEne : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hE8
    omega
  by_contra hcomm
  have hcomm' : ∀ a b : L, a * b = b * a := fun a b => by
    by_contra hne
    exact hcomm ⟨a, b, hne⟩
  obtain ⟨P, hP, hN⟩ := hBT E hEne (CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE)
  have hnorm : Subgroup.normalizer (E : Set L) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr ⟨fun x hx g => by
      rw [hcomm' g x, mul_inv_cancel_right]
      exact hx⟩
  exact hP (eq_top_iff.mpr (hnorm ▸ hN))

end Nonabelian

section ClassicalFacts

open CFSG.Assembly.LowTwoRank

theorem uc22lb_classical_facts {L : Type} [Group L] {t : StatedLieTag} {m f : ℕ}
    (h : StatedClassicalModel L t m 2 f)
    (hcase : (t = .PSL ∧ 3 ≤ f) ∨ (t = .PSU ∧ ((4 ≤ m ∧ 2 ≤ f) ∨ (2 ≤ m ∧ 3 ≤ f))) ∨
      t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a := by
  have hbig : ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
    rcases hcase with ⟨rfl, hf⟩ | ⟨rfl, hmf⟩ | rfl | rfl | rfl
    · exact uc22lb_big_psl hf h
    · exact uc22lb_big_psu hmf h
    · exact uc22lb_big_psp h
    · exact uc22lb_big_pOmegaPlus h
    · exact uc22lb_big_pOmegaMinus h
  obtain ⟨hfin, h3⟩ := hbig
  refine ⟨hfin, h3, uc22lb_nonab_of_big ⟨hfin, h3⟩ fun U hU hU2 => ?_⟩
  obtain ⟨S, P, hP, hN, -⟩ := CFSG.LieType.BorelTits.holds_of_statedClassicalModel h U hU hU2
  exact ⟨P, hP, hN⟩

theorem uc22lb_alt9_facts {L : Type} [Group L] (e : L ≃* alternatingGroup (Fin 9)) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨hfin, h3⟩ := uc22lb_big_alt9 e
  obtain ⟨a, b, hab⟩ := uc22lb_nonab_alt9
  exact ⟨hfin, h3, e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end ClassicalFacts

@[expose] def ListBExceptional (L : Type) [Group L] : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m n : ℕ), 2 < n ∧
      (t ∈ CFSG.Blueprint.chevalleyExceptionalTags ∨ t = .twistedF4 ∨ t = .twistedB2) ∧
      CFSG.Blueprint.LieModel L t m 2 n) ∨
    CFSG.Blueprint.LieModel L .trialityD4 0 2 1 ∨ CFSG.Blueprint.LieModel L .trialityD4 0 2 2

@[expose] def ListBExceptionalFacts : Prop :=
  ∀ (L : Type) [Group L], ListBExceptional L →
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a

section Exceptional

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.SectionRank CFSG.GH74.Filter.Lie

section Chevalley


theorem uc22lb_big_chevalley {L : Type} [Group L] {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel L t 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  have hfin : Finite L := CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness L t 2 f h
  refine ⟨hfin, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hp, hf, hn⟩, hm⟩ := h
  cases t with
  | G2 => have := three_mul_le_pRank_of_G2Model hm; omega
  | F4 => have := four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm; omega
  | E6 => have := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm; omega
  | E7 => have := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inl rfl))) hm; omega
  | E8 => have := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inr rfl))) hm; omega
  | twistedE6 => have := four_le_pRank_of_twistedE6Model hf hm; omega
  | trialityD4 => have := four_le_pRank_of_trialityD4Model hf hm; omega
  | _ => exact absurd ht (by decide)

theorem uc22lb_borelTits_of_lieModel {L : Type} [Group L] {t : StatedLieTag} {m n : ℕ}
    (h : LieModel L t m 2 n) (U : Subgroup L) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ P : Subgroup L, P ≠ ⊤ ∧ Subgroup.normalizer (U : Set L) ≤ P := by
  obtain ⟨S, P, hP, hN, -⟩ := CFSG.LieType.BorelTits.lieModel_conclusion L t m 2 n h U hU hU2
  exact ⟨P, hP, hN⟩

end Chevalley

section Suzuki


theorem uc22lb_big_suzuki {L : Type} [Group L] {f : ℕ} (hf : 3 ≤ f) (h : SuzukiModel L 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  have hfin : Finite L := CFSG.LieType.Simplicity.fam_suzuki_finiteness L 2 f h
  refine ⟨hfin, ?_⟩
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have := CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_eq_of_mulEquiv hK' e
  have h3 : 3 ≤ CFSG.Open.twoRank L := by omega
  exact h3

end Suzuki

section Ree


theorem uc22lb_big_twistedF4 {L : Type} [Group L] {f : ℕ} (h : ReeTitsModel L .twistedF4 2 f) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
  obtain ⟨hfin, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier L 2 f h
  refine ⟨hfin, ?_⟩
  obtain ⟨⟨-, -, -, -, -, h3⟩, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_natCard_eq_pow hK
  have : CharP K ReeTag.F4.prime := hc
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨e'⟩ := hiso a K hfa hK ⟨e⟩
  have hΓ : ReeTag.F4.reeGamma K a =
      (reeFixed ReeTag.F4 K a).map (adjointGroup ReeTag.F4.tag K).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)
  let e2 : ReeTag.F4.reeGamma K a ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hΓ).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm
  have eL : L ≃* reeFixed ReeTag.F4 K a := e'.trans e2
  have : Finite (reeFixed ReeTag.F4 K a) := Finite.of_equiv L eL.toEquiv
  rw [pRank_top_eq_of_mulEquiv Nat.one_lt_two eL]
  let F : adjointGroup ReeTag.F4.tag K ≃* adjointGroup ReeTag.F4.tag K := ReeTag.F4.reeAut K a
  have hFF : ∀ g, F (F g) = g := ReeTag.F4.reeAut_reeAut a hK'
  let g : Fin 4 → Multiplicative K →* adjointGroup ReeTag.F4.tag K := fun i =>
    rootHom (K := K) (quadF4.root i)
  obtain ⟨hcomm, hinj⟩ := SepWitness.pi_data quadF4_check (K := K)
  have hstab : ∀ i y, F (g i y) ∈ (MonoidHom.noncommPiCoprod g hcomm).range := by
    intro i y
    have h1 : g i y ∈ (rootOperatorFamily ReeTag.F4.tag).rootSubgroup K (quadF4.root i) :=
      (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _
    have h2 := ReeTag.reeAut_mem_X (t := ReeTag.F4) a h1
    rw [dualRootOf_quadF4] at h2
    obtain ⟨c, hc⟩ := ((rootOperatorFamily ReeTag.F4.tag).mem_rootSubgroup).1 h2
    refine ⟨Pi.mulSingle (![1, 0, 3, 2] i) (Multiplicative.ofAdd c), ?_⟩
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    exact hc
  obtain ⟨E, hEF, hEc, hEs, hEcard⟩ := exists_fixed_elemAbelian_of_pi F hFF
    (fun x => CharTwo.add_self_eq_zero x) g hcomm hinj hstab
  have hEΓ : E ≤ reeFixed ReeTag.F4 K a := fun x hx => (mem_reeFixed _ _ _).2 (hEF x hx)
  rw [Fintype.card_fin] at hEcard
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [sq] using hEs x.1 x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hK8 : 2 ^ 3 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have hk2 : k ≤ 2 := by omega
    have h1 : Nat.card E ≤ 2 ^ 2 := by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk2
    have h2 : Nat.card E ^ 2 ≤ (2 ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 3) ^ 4 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left hK8 4
    norm_num at h2 h3
    omega
  have hle : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (reeFixed ReeTag.F4 K a)) :=
    le_pRank_of_injective Nat.one_lt_two
      (fun x y => Subtype.ext (hEc x.1 x.2 y.1 y.2))
      (fun x => Subtype.ext (by simpa [sq] using hEs x.1 x.2)) hk
      (Subgroup.inclusion hEΓ) (Subgroup.inclusion_injective hEΓ) le_top
  omega

theorem listBExceptionalFacts : ListBExceptionalFacts := by
  intro L _ h
  have key : ∀ {t : StatedLieTag} {m n : ℕ}, 2 < n →
      (t ∈ chevalleyExceptionalTags ∨ t = .twistedF4 ∨ t = .twistedB2) →
      LieModel L t m 2 n →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a := by
    intro t m n hn htag hL
    have hbig : ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
      rcases hL with ⟨ht, hcl⟩ | ⟨-, ht, hce⟩ | ⟨-, ht, hree⟩ | ⟨-, ht, hsz⟩
      · exfalso
        rcases htag with htag | htag | htag
        · revert ht htag
          cases t <;> decide
        · subst htag; exact absurd ht (by decide)
        · subst htag; exact absurd ht (by decide)
      · exact uc22lb_big_chevalley ht hce
      · cases t with
        | twistedF4 => exact uc22lb_big_twistedF4 hree
        | twistedG2 =>
          obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := hree
          exact absurd h23 (by omega)
        | Tits =>
          obtain ⟨⟨-, -, -, -, hf1⟩, -⟩ := hree
          exact absurd hf1 (by omega)
        | _ => exact absurd ht (by decide)
      · subst ht
        exact uc22lb_big_suzuki hn hsz
    obtain ⟨hfin, h3⟩ := hbig
    exact ⟨hfin, h3, uc22lb_nonab_of_big ⟨hfin, h3⟩ (uc22lb_borelTits_of_lieModel hL)⟩
  rcases h with ⟨t, m, n, hn, htag, hL⟩ | hL | hL
  · exact key hn htag hL
  · have hce := hL.chevalleyExceptionalModel (by decide)
    obtain ⟨hfin, h3⟩ := uc22lb_big_chevalley (by decide) hce
    exact ⟨hfin, h3, uc22lb_nonab_of_big ⟨hfin, h3⟩ (uc22lb_borelTits_of_lieModel hL)⟩
  · have hce := hL.chevalleyExceptionalModel (by decide)
    obtain ⟨hfin, h3⟩ := uc22lb_big_chevalley (by decide) hce
    exact ⟨hfin, h3, uc22lb_nonab_of_big ⟨hfin, h3⟩ (uc22lb_borelTits_of_lieModel hL)⟩

end Ree

end Exceptional

section Assembly

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem uc22lb_listB_facts (hE : ListBExceptionalFacts) {L : Type} [Group L]
    (h : Asc1930ListB L) :
    ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a := by
  rcases h with ⟨t, m, n, hn, hL⟩ | h | h | h | h | h | h
  · by_cases hexc : t ∈ chevalleyExceptionalTags ∨ t = .twistedF4 ∨ t = .twistedB2
    · exact hE L (Or.inl ⟨t, m, n, hn, hexc, hL⟩)
    · rcases hL with ⟨ht, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, hree⟩ | ⟨-, ht, -⟩
      · have hadm := hcl.1
        cases t with
        | PSL => exact uc22lb_classical_facts hcl (Or.inl ⟨rfl, hn⟩)
        | PSU =>
          have h3 : 3 ≤ m := hadm.2.2.1
          exact uc22lb_classical_facts hcl (Or.inr (Or.inl ⟨rfl, Or.inr ⟨by omega, hn⟩⟩))
        | PSp => exact uc22lb_classical_facts hcl (Or.inr (Or.inr (Or.inl rfl)))
        | POmegaOdd => exact absurd rfl hadm.2.2.2
        | POmegaPlus => exact uc22lb_classical_facts hcl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        | POmegaMinus => exact uc22lb_classical_facts hcl (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        | _ => exact absurd ht (by decide)
      · exact absurd (Or.inl ht) hexc
      · cases t with
        | twistedF4 => exact absurd (Or.inr (Or.inl rfl)) hexc
        | twistedG2 =>
          obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := hree
          exact absurd h23 (by omega)
        | Tits =>
          obtain ⟨⟨-, -, -, -, hf1⟩, -⟩ := hree
          exact absurd hf1 (by omega)
        | _ => exact absurd ht (by decide)
      · exact absurd (Or.inr (Or.inr ht)) hexc
  · exact hE L (Or.inr (Or.inl h))
  · exact hE L (Or.inr (Or.inr h))
  · exact uc22lb_classical_facts (h.statedClassicalModel (by decide))
      (Or.inr (Or.inl ⟨rfl, Or.inl ⟨by norm_num, le_rfl⟩⟩))
  · exact uc22lb_classical_facts (h.statedClassicalModel (by decide))
      (Or.inr (Or.inl ⟨rfl, Or.inl ⟨by norm_num, le_rfl⟩⟩))
  · exact uc22lb_classical_facts (h.statedClassicalModel (by decide))
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · obtain ⟨e⟩ := h
    exact uc22lb_alt9_facts e

theorem listBNonabelian_of (hE : ListBExceptionalFacts) : ListBNonabelian := by
  intro L _ h
  obtain ⟨-, -, hnc⟩ := uc22lb_listB_facts hE h
  exact hnc

theorem listBNotSmall_of (hE : ListBExceptionalFacts) : ListBNotSmall := by
  intro L _ h
  obtain ⟨hfin, h3, -⟩ := uc22lb_listB_facts hE h
  haveI := hfin
  exact uc22lb_notSmall_of_big h3


theorem listBNonabelian : ListBNonabelian :=
  listBNonabelian_of listBExceptionalFacts

theorem listBNotSmall : ListBNotSmall :=
  listBNotSmall_of listBExceptionalFacts

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.UC22

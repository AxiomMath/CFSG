module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Simplicity.TitsElements
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLargeReeTits
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Tits

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.Simplicity.TitsBits CFSG.Assembly.RankThreeEven

@[expose] def wordPow (w : List Letter) : ℕ → List Letter
  | 0 => []
  | k + 1 => w ++ wordPow w k

@[expose] def wordA : List Letter :=
  wordPow (titsG1Word ++ titsZ2Word ++ titsZ1Word) 4

@[expose] def wordB : List Letter :=
  titsG0Word ++ wordA ++ titsG0Word.reverse

@[expose] def wordC : List Letter :=
  wordA ++ wordB ++ wordA.reverse ++ wordB.reverse

@[expose] def wordT (i j k : ℕ) : List Letter :=
  wordPow wordA i ++ wordPow wordB j ++ wordPow wordC k

@[expose] def fingerprint : List ℕ :=
  [1, 3076809556016478, 2335905500814679, 440922216599585, 2329109785049317, 4408776991862355,
    1200955672821761, 452012928109254, 3072160404960781, 159481533567521, 3741566383435331,
    2927388591603301, 3823880046616521, 137443409921, 4209760843463504, 449734651283489,
    1796671810110465, 3889965838471909, 1167965907387393, 2368613626761869, 26485436829406,
    1726441578364929, 26440660159009, 4137368349701357, 1964528365806364, 34695282689,
    2033781878105997]

theorem wordA_cube : evalB (wordPow wordA 3) % 2 ^ 2704 = evalB [] % 2 ^ 2704 := by
  decide +kernel

theorem wordB_cube : evalB (wordPow wordB 3) % 2 ^ 2704 = evalB [] % 2 ^ 2704 := by
  decide +kernel

theorem wordC_cube : evalB (wordPow wordC 3) % 2 ^ 2704 = evalB [] % 2 ^ 2704 := by
  decide +kernel

theorem wordC_comm_wordA :
    evalB (wordC ++ wordA) % 2 ^ 2704 = evalB (wordA ++ wordC) % 2 ^ 2704 := by
  decide +kernel

theorem wordC_comm_wordB :
    evalB (wordC ++ wordB) % 2 ^ 2704 = evalB (wordB ++ wordC) % 2 ^ 2704 := by
  decide +kernel

theorem wordA_flip : evalB (wordA.map Letter.flip) % 2 ^ 2704 = evalB wordA % 2 ^ 2704 := by
  decide +kernel

theorem wordB_flip : evalB (wordB.map Letter.flip) % 2 ^ 2704 = evalB wordB % 2 ^ 2704 := by
  decide +kernel

theorem fingerprint_spec : ∀ i j k : Fin 3,
    evalB (wordT i j k) % 2 ^ 52 =
      fingerprint.getD (9 * (i : ℕ) + 3 * (j : ℕ) + (k : ℕ)) 0 := by
  decide +kernel

theorem fingerprint_injective : ∀ x y : Fin 3 × Fin 3 × Fin 3,
    fingerprint.getD (9 * (x.1 : ℕ) + 3 * (x.2.1 : ℕ) + (x.2.2 : ℕ)) 0 =
      fingerprint.getD (9 * (y.1 : ℕ) + 3 * (y.2.1 : ℕ) + (y.2.2 : ℕ)) 0 → x = y := by
  decide

section Group

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem evalG_wordPow (w : List Letter) (k : ℕ) : evalG K (wordPow w k) = evalG K w ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordPow, evalG_append, ih, pow_succ']

omit [Finite K] in
theorem evalG_eq_evalG_of {w w' : List Letter} (h : evalB w % 2 ^ 2704 = evalB w' % 2 ^ 2704) :
    evalG K w = evalG K w' := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact (evalG_eq_evalG_iff w w').mpr h

theorem evalG_wordA_mem : evalG K wordA ∈ reeFixed ReeTag.F4 K 0 := by
  rw [mem_reeFixed, reeAut_evalG]
  exact evalG_eq_evalG_of wordA_flip

theorem evalG_wordB_mem : evalG K wordB ∈ reeFixed ReeTag.F4 K 0 := by
  rw [mem_reeFixed, reeAut_evalG]
  exact evalG_eq_evalG_of wordB_flip

omit [Finite K] in
theorem evalG_wordC :
    evalG K wordC = evalG K wordA * evalG K wordB * (evalG K wordA)⁻¹ * (evalG K wordB)⁻¹ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [wordC, evalG_append, evalG_append, evalG_append, evalG_inv, evalG_inv]

@[expose] noncomputable def eltA : reeFixed ReeTag.F4 K 0 := ⟨evalG K wordA, evalG_wordA_mem⟩

@[expose] noncomputable def eltB : reeFixed ReeTag.F4 K 0 := ⟨evalG K wordB, evalG_wordB_mem⟩

@[expose] noncomputable def eltC : reeFixed ReeTag.F4 K 0 :=
  eltA * eltB * eltA⁻¹ * eltB⁻¹

theorem coe_eltC : ((eltC : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) =
    evalG K wordC := by
  rw [evalG_wordC]
  rfl

theorem coe_eltA : ((eltA : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) =
    evalG K wordA :=
  rfl

theorem coe_eltB : ((eltB : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) =
    evalG K wordB :=
  rfl

theorem eltC_eq : (eltC : reeFixed ReeTag.F4 K 0) = eltA * eltB * eltA⁻¹ * eltB⁻¹ :=
  rfl

attribute [irreducible] eltA eltB eltC

theorem eltA_cube : (eltA : reeFixed ReeTag.F4 K 0) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, coe_eltA, ← evalG_wordPow]
  exact evalG_eq_evalG_of wordA_cube

theorem eltB_cube : (eltB : reeFixed ReeTag.F4 K 0) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, coe_eltB, ← evalG_wordPow]
  exact evalG_eq_evalG_of wordB_cube

theorem eltC_cube : (eltC : reeFixed ReeTag.F4 K 0) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, coe_eltC, ← evalG_wordPow]
  exact evalG_eq_evalG_of wordC_cube

theorem eltC_comm_eltA : Commute (eltC : reeFixed ReeTag.F4 K 0) eltA := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eltC, coe_eltA, ← evalG_append, ← evalG_append]
  exact evalG_eq_evalG_of wordC_comm_wordA

theorem eltC_comm_eltB : Commute (eltC : reeFixed ReeTag.F4 K 0) eltB := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eltC, coe_eltB, ← evalG_append, ← evalG_append]
  exact evalG_eq_evalG_of wordC_comm_wordB

@[expose] noncomputable def eltT (x : Fin 3 × Fin 3 × Fin 3) : reeFixed ReeTag.F4 K 0 :=
  eltA ^ (x.1 : ℕ) * eltB ^ (x.2.1 : ℕ) * eltC ^ (x.2.2 : ℕ)

theorem coe_eltT (x : Fin 3 × Fin 3 × Fin 3) :
    ((eltT x : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) =
      evalG K (wordT x.1 x.2.1 x.2.2) := by
  rw [eltT, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
    Subgroup.coe_pow, coe_eltC, coe_eltA, coe_eltB, wordT, evalG_append, evalG_append,
    evalG_wordPow, evalG_wordPow, evalG_wordPow]

theorem eltT_injective : Function.Injective (eltT (K := K)) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  intro x y hxy
  have h := congrArg Subtype.val hxy
  rw [coe_eltT, coe_eltT, evalG_eq_evalG_iff] at h
  have h52 := congrArg (· % 2 ^ 52) h
  simp only [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 52 ≤ 2704))] at h52
  rw [fingerprint_spec, fingerprint_spec] at h52
  exact fingerprint_injective x y h52

theorem pow_mod_three {g : reeFixed ReeTag.F4 K 0} (hg : g ^ 3 = 1) (n : ℕ) :
    g ^ n = g ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hg, one_pow, one_mul]

theorem eltB_mul_eltA : (eltB : reeFixed ReeTag.F4 K 0) * eltA = eltC ^ 2 * eltA * eltB := by
  have h : eltC * (eltB * eltA) = (eltA : reeFixed ReeTag.F4 K 0) * eltB := by
    rw [eltC_eq]
    group
  have hc2 : eltC ^ 2 * (eltC : reeFixed ReeTag.F4 K 0) = 1 := by
    rw [← pow_succ, eltC_cube]
  calc (eltB : reeFixed ReeTag.F4 K 0) * eltA = eltC ^ 2 * (eltC * (eltB * eltA)) := by
        rw [← mul_assoc, hc2, one_mul]
    _ = eltC ^ 2 * eltA * eltB := by rw [h, mul_assoc]

theorem eltB_mul_eltA_pow (i : ℕ) :
    (eltB : reeFixed ReeTag.F4 K 0) * eltA ^ i = eltC ^ (2 * i) * eltA ^ i * eltB := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hca : Commute (eltC ^ 2 : reeFixed ReeTag.F4 K 0) eltA :=
      (Commute.pow_left eltC_comm_eltA 2)
    calc (eltB : reeFixed ReeTag.F4 K 0) * eltA ^ (i + 1) = (eltB * eltA ^ i) * eltA := by
          rw [pow_succ, mul_assoc]
      _ = eltC ^ (2 * i) * eltA ^ i * (eltB * eltA) := by rw [ih, mul_assoc]
      _ = eltC ^ (2 * i) * eltA ^ i * (eltC ^ 2 * eltA * eltB) := by rw [eltB_mul_eltA]
      _ = eltC ^ (2 * i) * (eltA ^ i * eltC ^ 2) * eltA * eltB := by group
      _ = eltC ^ (2 * i) * (eltC ^ 2 * eltA ^ i) * eltA * eltB := by
          rw [(Commute.pow_right hca i).eq]
      _ = eltC ^ (2 * (i + 1)) * eltA ^ (i + 1) * eltB := by
          rw [mul_add, mul_one, pow_add, pow_succ]
          group

theorem eltA_mul_eltT (x : Fin 3 × Fin 3 × Fin 3) :
    (eltA : reeFixed ReeTag.F4 K 0) * eltT x = eltT (x.1 + 1, x.2) := by
  show eltA * (eltA ^ (x.1 : ℕ) * eltB ^ (x.2.1 : ℕ) * eltC ^ (x.2.2 : ℕ)) =
    eltA ^ ((x.1 + 1 : Fin 3) : ℕ) * eltB ^ (x.2.1 : ℕ) * eltC ^ (x.2.2 : ℕ)
  have h : (eltA : reeFixed ReeTag.F4 K 0) * eltA ^ (x.1 : ℕ) =
      eltA ^ ((x.1 + 1 : Fin 3) : ℕ) := by
    rw [← pow_succ', pow_mod_three eltA_cube, Fin.val_add, Fin.val_one]
  simp only [← mul_assoc, h]

theorem eltB_mul_eltT (x : Fin 3 × Fin 3 × Fin 3) :
    (eltB : reeFixed ReeTag.F4 K 0) * eltT x = eltT (x.1, x.2.1 + 1, x.2.2 + 2 * x.1) := by
  show eltB * (eltA ^ (x.1 : ℕ) * eltB ^ (x.2.1 : ℕ) * eltC ^ (x.2.2 : ℕ)) =
    eltA ^ (x.1 : ℕ) * eltB ^ ((x.2.1 + 1 : Fin 3) : ℕ) * eltC ^ ((x.2.2 + 2 * x.1 : Fin 3) : ℕ)
  have hcb : Commute (eltC ^ (2 * (x.1 : ℕ)) : reeFixed ReeTag.F4 K 0) (eltB ^ ((x.2.1 : ℕ) + 1)) :=
    Commute.pow_pow eltC_comm_eltB _ _
  have hcc : (eltC : reeFixed ReeTag.F4 K 0) ^ (2 * (x.1 : ℕ)) * eltC ^ (x.2.2 : ℕ) =
      eltC ^ ((x.2.2 + 2 * x.1 : Fin 3) : ℕ) := by
    rw [← pow_add, pow_mod_three eltC_cube]
    congr 1
    simp only [Fin.val_add, Fin.val_mul]
    omega
  have hbb : (eltB : reeFixed ReeTag.F4 K 0) ^ ((x.2.1 : ℕ) + 1) =
      eltB ^ ((x.2.1 + 1 : Fin 3) : ℕ) := by
    rw [pow_mod_three eltB_cube, Fin.val_add, Fin.val_one]
  have hca : Commute (eltC ^ (2 * (x.1 : ℕ)) : reeFixed ReeTag.F4 K 0) (eltA ^ (x.1 : ℕ)) :=
    Commute.pow_pow eltC_comm_eltA _ _
  calc (eltB : reeFixed ReeTag.F4 K 0) * (eltA ^ (x.1 : ℕ) * eltB ^ (x.2.1 : ℕ) *
        eltC ^ (x.2.2 : ℕ)) =
        (eltB * eltA ^ (x.1 : ℕ)) * eltB ^ (x.2.1 : ℕ) * eltC ^ (x.2.2 : ℕ) := by group
    _ = eltC ^ (2 * (x.1 : ℕ)) * eltA ^ (x.1 : ℕ) * eltB * eltB ^ (x.2.1 : ℕ) *
        eltC ^ (x.2.2 : ℕ) := by rw [eltB_mul_eltA_pow]
    _ = eltA ^ (x.1 : ℕ) * (eltC ^ (2 * (x.1 : ℕ)) * eltB ^ ((x.2.1 : ℕ) + 1)) *
        eltC ^ (x.2.2 : ℕ) := by
        rw [hca.eq, pow_succ' eltB]
        group
    _ = eltA ^ (x.1 : ℕ) * eltB ^ ((x.2.1 : ℕ) + 1) *
        (eltC ^ (2 * (x.1 : ℕ)) * eltC ^ (x.2.2 : ℕ)) := by
        rw [hcb.eq]
        group
    _ = _ := by rw [hcc, hbb]

@[expose] noncomputable def sylowS : Subgroup (reeFixed ReeTag.F4 K 0) :=
  Subgroup.closure {eltA, eltB}

theorem eltT_mem (x : Fin 3 × Fin 3 × Fin 3) :
    eltT x ∈ (sylowS : Subgroup (reeFixed ReeTag.F4 K 0)) := by
  have ha : (eltA : reeFixed ReeTag.F4 K 0) ∈ sylowS := Subgroup.subset_closure (by simp)
  have hb : (eltB : reeFixed ReeTag.F4 K 0) ∈ sylowS := Subgroup.subset_closure (by simp)
  have hc : (eltC : reeFixed ReeTag.F4 K 0) ∈ sylowS := by
    rw [eltC_eq]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  exact mul_mem (mul_mem (pow_mem ha _) (pow_mem hb _)) (pow_mem hc _)

theorem mem_range_eltT {g : reeFixed ReeTag.F4 K 0} (hg : g ∈ (sylowS : Subgroup _)) :
    g ∈ Set.range (eltT (K := K)) := by
  refine Subgroup.closure_induction_left (p := fun g _ => g ∈ Set.range (eltT (K := K)))
    ⟨(0, 0, 0), by simp [eltT]⟩ ?_ ?_ hg
  · rintro x hx _ _ ⟨y, rfl⟩
    rcases hx with rfl | rfl
    · exact ⟨_, (eltA_mul_eltT y).symm⟩
    · exact ⟨_, (eltB_mul_eltT y).symm⟩
  · rintro x hx _ _ ⟨y, rfl⟩
    have hinv : ∀ {g : reeFixed ReeTag.F4 K 0}, g ^ 3 = 1 → g⁻¹ = g * g := fun {g} h => by
      rw [inv_eq_iff_mul_eq_one, ← pow_three, h]
    rcases hx with rfl | rfl
    · rw [hinv eltA_cube, mul_assoc, eltA_mul_eltT, eltA_mul_eltT]
      exact ⟨_, rfl⟩
    · rw [hinv eltB_cube, mul_assoc, eltB_mul_eltT, eltB_mul_eltT]
      exact ⟨_, rfl⟩

theorem card_sylowS : Nat.card (sylowS : Subgroup (reeFixed ReeTag.F4 K 0)) = 3 ^ 3 := by
  have hset : ((sylowS : Subgroup (reeFixed ReeTag.F4 K 0)) : Set (reeFixed ReeTag.F4 K 0)) =
      Set.range (eltT (K := K)) :=
    Set.Subset.antisymm (fun g hg => mem_range_eltT hg) (by rintro _ ⟨x, rfl⟩; exact eltT_mem x)
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective eltT_injective]
  simp

theorem eltA_mul_eltB_ne :
    (eltA : reeFixed ReeTag.F4 K 0) * eltB ≠ eltB * eltA := by
  intro h
  have h1 : (eltC : reeFixed ReeTag.F4 K 0) = 1 := by
    rw [eltC_eq, h]
    group
  have h2 : eltT (K := K) ((0, 0, 1) : Fin 3 × Fin 3 × Fin 3) =
      eltT ((0, 0, 0) : Fin 3 × Fin 3 × Fin 3) := by
    simp [eltT, h1]
  exact absurd (eltT_injective (K := K) h2) (by decide)

end Group

section Ranks

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem card_reeFixed (hK : Nat.card K = 2) :
    Nat.card (reeFixed ReeTag.F4 K 0) = 35942400 := by
  have h := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    0 K (by rw [hK]; norm_num)).1
  rw [← LargeReeInvolution.map_reeFixed_eq_reeGamma,
    Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective] at h
  rw [h]
  norm_num

theorem pRank_three_reeFixed (hK : Nat.card K = 2) :
    CFSG.Assembly.pRank 3 (⊤ : Subgroup (reeFixed ReeTag.F4 K 0)) ≤ 2 :=
  pRank_le_two_of_nonabelian Nat.prime_three (by rw [card_reeFixed hK]; norm_num) card_sylowS
    ⟨eltA, Subgroup.subset_closure (by simp), eltB, Subgroup.subset_closure (by simp),
      eltA_mul_eltB_ne⟩

theorem localRank_three_reeFixed (hK : Nat.card K = 2) :
    localRank 3 (reeFixed ReeTag.F4 K 0) ≤ 2 :=
  localRank_le_of_pRank_le Nat.prime_three (pRank_three_reeFixed hK)

theorem localRank_three_commutator (hK : Nat.card K = 2) :
    localRank 3 (commutator (reeFixed ReeTag.F4 K 0)) ≤ 2 :=
  (CFSG.RankThree.PartOne.PlaneAux.localRank_le_of_injective Nat.prime_three
    (commutator (reeFixed ReeTag.F4 K 0)).subtype
    (commutator (reeFixed ReeTag.F4 K 0)).subtype_injective).trans (localRank_three_reeFixed hK)

theorem localRank_three_commutator_quotient_center (hK : Nat.card K = 2) :
    localRank 3 (commutator (reeFixed ReeTag.F4 K 0) ⧸
      Subgroup.center (commutator (reeFixed ReeTag.F4 K 0))) ≤ 2 := by
  have e := (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK)).trans
    (QuotientGroup.quotientBot (G := commutator (reeFixed ReeTag.F4 K 0)))
  rw [localRank_eq_of_mulEquiv e Nat.prime_three]
  exact localRank_three_commutator hK

end Ranks

end CFSG.RankThree.PartTwo.Census.Carrier.Tits

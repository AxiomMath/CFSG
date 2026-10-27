module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bNorm2
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace M22Norm2Aux

def genA : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

def genB : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem genA_mem : genA ∈ CFSG.Blueprint.NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem genB_mem : genB ∈ CFSG.Blueprint.NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

def genG : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 2, 17] * List.formPerm [4, 20, 13] * List.formPerm [5, 11, 16] *
    List.formPerm [6, 7, 8] * List.formPerm [10, 14, 12] * List.formPerm [15, 18, 21]

def genH : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 9, 19] * List.formPerm [4, 20, 13] * List.formPerm [5, 10, 21] *
    List.formPerm [6, 8, 7] * List.formPerm [11, 14, 15] * List.formPerm [12, 18, 16]

def genT1 : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 6] * List.formPerm [4, 18] * List.formPerm [5, 13] * List.formPerm [7, 8] *
    List.formPerm [10, 11] * List.formPerm [12, 15] * List.formPerm [14, 20] * List.formPerm [16, 21]

def genT2 : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 8] * List.formPerm [4, 10] * List.formPerm [5, 12] * List.formPerm [6, 7] *
    List.formPerm [11, 18] * List.formPerm [13, 15] * List.formPerm [14, 21] * List.formPerm [16, 20]

theorem genG_eq : genG = (genB * genA * genB⁻¹ * genA * genB⁻¹ * genA * genB * genA * genB * genA *
    genB * genA * genB * genB * genA * genB⁻¹ * genA * genB * genA * genB * genB * genA * genB *
    genA * genB * genA * genB) := by
  decide +kernel

theorem genH_eq : genH = (genB * genB * genA * genB * genA * genB⁻¹ * genA * genB * genB * genA *
    genB⁻¹ * genA * genB * genA * genB * genA * genB * genB * genA * genB * genA * genB * genA *
    genB⁻¹ * genA * genB⁻¹ * genA) := by
  decide +kernel

theorem genT1_eq : genT1 = (genB * genB * genA * genB⁻¹ * genA * genB * genA * genB⁻¹ * genA *
    genB⁻¹ * genA * genB⁻¹ * genA * genB * genB * genA * genB * genA * genB * genA * genB * genB *
    genA * genB⁻¹ * genA * genB) := by
  decide +kernel

theorem genG_mem : genG ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [genG_eq]
  exact (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem genB_mem genA_mem) (inv_mem genB_mem)) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genA_mem) genB_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem)

theorem genH_mem : genH ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [genH_eq]
  exact (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem genB_mem genB_mem) genA_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) (inv_mem genB_mem)) genA_mem)

theorem genT1_mem : genT1 ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [genT1_eq]
  exact (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem genB_mem genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) (inv_mem genB_mem)) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genA_mem) genB_mem) genB_mem) genA_mem) (inv_mem genB_mem)) genA_mem) genB_mem)

theorem genG_pow3 : genG ^ 3 = 1 := by
  decide +kernel

theorem genH_pow3 : genH ^ 3 = 1 := by
  decide +kernel

theorem genGH_comm : genG * genH = genH * genG := by
  decide +kernel

def gX : CFSG.Blueprint.NativeSporadic.M22 := ⟨genG, genG_mem⟩

def hX : CFSG.Blueprint.NativeSporadic.M22 := ⟨genH, genH_mem⟩

theorem gX_pow3 : gX ^ 3 = 1 :=
  Subtype.ext genG_pow3

theorem hX_pow3 : hX ^ 3 = 1 :=
  Subtype.ext genH_pow3

theorem gX_hX_mul : gX * hX = hX * gX :=
  Subtype.ext genGH_comm

theorem gX_hX_comm : Commute gX hX :=
  gX_hX_mul

theorem key_mul (i j k l : ℕ) :
    gX ^ i * hX ^ j * (gX ^ k * hX ^ l) = gX ^ (i + k) * hX ^ (j + l) := by
  have hcomm : hX ^ j * gX ^ k = gX ^ k * hX ^ j := (gX_hX_comm.symm.pow_pow j k).eq
  rw [pow_add, pow_add]
  calc gX ^ i * hX ^ j * (gX ^ k * hX ^ l) = gX ^ i * (hX ^ j * gX ^ k) * hX ^ l := by
        simp only [mul_assoc]
    _ = gX ^ i * (gX ^ k * hX ^ j) * hX ^ l := by rw [hcomm]
    _ = gX ^ i * gX ^ k * (hX ^ j * hX ^ l) := by simp only [mul_assoc]

def sylowSub : Subgroup CFSG.Blueprint.NativeSporadic.M22 where
  carrier := {x | ∃ i j : ℕ, x = gX ^ i * hX ^ j}
  mul_mem' := by
    rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, key_mul i j k l⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro x ⟨i, j, rfl⟩
    refine ⟨2 * i, 2 * j, inv_eq_of_mul_eq_one_right ?_⟩
    rw [key_mul, show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring, pow_mul, pow_mul,
      gX_pow3, hX_pow3, one_pow, one_pow, one_mul]

def sylowList : List (Equiv.Perm (Fin 22)) :=
  [1, genG, genG ^ 2, genH, genG * genH, genG ^ 2 * genH, genH ^ 2, genG * genH ^ 2,
    genG ^ 2 * genH ^ 2]

def kleinList : List (Equiv.Perm (Fin 22)) := [1, genT1, genT2, genT1 * genT2]

theorem sylowList_mem : ∀ σ ∈ sylowList, σ ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  intro σ hσ
  simp only [sylowList, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact genG_mem
  · exact pow_mem genG_mem 2
  · exact genH_mem
  · exact mul_mem genG_mem genH_mem
  · exact mul_mem (pow_mem genG_mem 2) genH_mem
  · exact pow_mem genH_mem 2
  · exact mul_mem genG_mem (pow_mem genH_mem 2)
  · exact mul_mem (pow_mem genG_mem 2) (pow_mem genH_mem 2)

theorem kleinList_one : (1 : Equiv.Perm (Fin 22)) ∈ kleinList := by
  simp [kleinList]

theorem sylowList_nodup : sylowList.Nodup := by
  decide +kernel

theorem sylowList_exp : ∀ σ ∈ sylowList, ∃ a b : ℕ, a < 3 ∧ b < 3 ∧
    σ = genG ^ a * genH ^ b := by
  intro σ hσ
  simp only [sylowList, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  · exact ⟨2, 0, by norm_num, by norm_num, by simp⟩
  · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  · exact ⟨1, 1, by norm_num, by norm_num, by simp⟩
  · exact ⟨2, 1, by norm_num, by norm_num, by simp⟩
  · exact ⟨0, 2, by norm_num, by norm_num, by simp⟩
  · exact ⟨1, 2, by norm_num, by norm_num, by simp⟩
  · exact ⟨2, 2, by norm_num, by norm_num, by simp⟩

theorem mem_sylowList_of_lt (a b : ℕ) (ha : a < 3) (hb : b < 3) :
    genG ^ a * genH ^ b ∈ sylowList := by
  interval_cases a <;> interval_cases b <;> simp [sylowList]

theorem mem_sylowSub_iff (x : CFSG.Blueprint.NativeSporadic.M22) :
    x ∈ sylowSub ↔ (x : Equiv.Perm (Fin 22)) ∈ sylowList := by
  constructor
  · rintro ⟨i, j, rfl⟩
    show genG ^ i * genH ^ j ∈ sylowList
    rw [pow_eq_pow_mod i genG_pow3, pow_eq_pow_mod j genH_pow3]
    exact mem_sylowList_of_lt _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  · intro hx
    obtain ⟨a, b, -, -, hab⟩ := sylowList_exp _ hx
    exact ⟨a, b, Subtype.ext hab⟩

def subOfList (L : List (Equiv.Perm (Fin 22))) (h1 : (1 : Equiv.Perm (Fin 22)) ∈ L)
    (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) (hinv : ∀ x ∈ L, x⁻¹ ∈ L) :
    Subgroup CFSG.Blueprint.NativeSporadic.M22 where
  carrier := {x | (x : Equiv.Perm (Fin 22)) ∈ L}
  mul_mem' := fun {x y} hx hy => hmul _ hx _ hy
  one_mem' := h1
  inv_mem' := fun {x} hx => hinv _ hx

theorem kleinList_mul_fin : ∀ i j : Fin kleinList.length,
    kleinList.get i * kleinList.get j ∈ kleinList := by
  decide +kernel

theorem kleinList_inv_fin : ∀ i : Fin kleinList.length, (kleinList.get i)⁻¹ ∈ kleinList := by
  decide +kernel

theorem kleinList_sq_fin : ∀ i : Fin kleinList.length, kleinList.get i ^ 2 = 1 := by
  decide +kernel

theorem kleinList_mul : ∀ x ∈ kleinList, ∀ y ∈ kleinList, x * y ∈ kleinList := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
  exact kleinList_mul_fin i j

theorem kleinList_inv : ∀ x ∈ kleinList, x⁻¹ ∈ kleinList := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  exact kleinList_inv_fin i

theorem kleinList_sq : ∀ x ∈ kleinList, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  exact kleinList_sq_fin i

def kleinSub : Subgroup CFSG.Blueprint.NativeSporadic.M22 :=
  subOfList kleinList kleinList_one kleinList_mul kleinList_inv

theorem genT1_ne_one : genT1 ≠ 1 := by
  decide +kernel

theorem genG_kleinNorm : ∀ i : Fin kleinList.length,
    genG * kleinList.get i * genG⁻¹ ∈ kleinList ∧ genG⁻¹ * kleinList.get i * genG ∈ kleinList := by
  decide +kernel

theorem genH_kleinNorm : ∀ i : Fin kleinList.length,
    genH * kleinList.get i * genH⁻¹ ∈ kleinList ∧ genH⁻¹ * kleinList.get i * genH ∈ kleinList := by
  decide +kernel

theorem kleinSub_ne_bot : kleinSub ≠ ⊥ := by
  intro h
  have hmem : (⟨genT1, genT1_mem⟩ : CFSG.Blueprint.NativeSporadic.M22) ∈ kleinSub := by
    show genT1 ∈ kleinList
    decide +kernel
  rw [h, Subgroup.mem_bot] at hmem
  exact genT1_ne_one (congrArg Subtype.val hmem)

theorem kleinSub_isPGroup : IsPGroup 2 kleinSub := by
  intro x
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hx : ((x : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) ∈ kleinList := x.2
  show ((x : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) ^ 2 ^ 1 = 1
  rw [pow_one]
  exact kleinList_sq _ hx

theorem mem_normalizer_kleinSub (x : CFSG.Blueprint.NativeSporadic.M22)
    (hx0 : ∀ i : Fin kleinList.length,
      (x : Equiv.Perm (Fin 22)) * kleinList.get i * (x : Equiv.Perm (Fin 22))⁻¹ ∈ kleinList ∧
      (x : Equiv.Perm (Fin 22))⁻¹ * kleinList.get i * (x : Equiv.Perm (Fin 22)) ∈ kleinList) :
    x ∈ Subgroup.normalizer (kleinSub : Set CFSG.Blueprint.NativeSporadic.M22) := by
  have hx : ∀ m ∈ kleinList,
      (x : Equiv.Perm (Fin 22)) * m * (x : Equiv.Perm (Fin 22))⁻¹ ∈ kleinList ∧
      (x : Equiv.Perm (Fin 22))⁻¹ * m * (x : Equiv.Perm (Fin 22)) ∈ kleinList := by
    intro m hm
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    exact hx0 i
  rw [Subgroup.mem_normalizer_iff]
  intro k
  show (k : Equiv.Perm (Fin 22)) ∈ kleinList ↔
    ((x * k * x⁻¹ : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) ∈ kleinList
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro hk
    exact (hx _ hk).1
  · intro hk
    have h2 := (hx _ hk).2
    rwa [show (x : Equiv.Perm (Fin 22))⁻¹ * ((x : Equiv.Perm (Fin 22)) * (k : Equiv.Perm (Fin 22)) *
      (x : Equiv.Perm (Fin 22))⁻¹) * (x : Equiv.Perm (Fin 22)) = (k : Equiv.Perm (Fin 22)) by group]
      at h2

theorem genG_normalizes :
    gX ∈ Subgroup.normalizer (kleinSub : Set CFSG.Blueprint.NativeSporadic.M22) :=
  mem_normalizer_kleinSub gX genG_kleinNorm

theorem genH_normalizes :
    hX ∈ Subgroup.normalizer (kleinSub : Set CFSG.Blueprint.NativeSporadic.M22) :=
  mem_normalizer_kleinSub hX genH_kleinNorm

theorem sylowSub_le_normalizer :
    sylowSub ≤ Subgroup.normalizer (kleinSub : Set CFSG.Blueprint.NativeSporadic.M22) := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := hx
  exact mul_mem (pow_mem genG_normalizes i) (pow_mem genH_normalizes j)

theorem natCard_of_iff (K : Subgroup CFSG.Blueprint.NativeSporadic.M22)
    (L : List (Equiv.Perm (Fin 22)))
    (hL : ∀ σ ∈ L, σ ∈ CFSG.Blueprint.NativeSporadic.M22)
    (hK : ∀ x : CFSG.Blueprint.NativeSporadic.M22, x ∈ K ↔ (x : Equiv.Perm (Fin 22)) ∈ L)
    (hnd : L.Nodup) : Nat.card K = L.length := by
  have hf : Function.Injective (fun x : K =>
      ((x : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22))) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hr : Set.range (fun x : K =>
      ((x : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22))) =
      (L.toFinset : Set (Equiv.Perm (Fin 22))) := by
    ext σ
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨x, rfl⟩
      exact (hK x.1).1 x.2
    · intro hσ
      exact ⟨⟨⟨σ, hL σ hσ⟩, (hK ⟨σ, hL σ hσ⟩).2 hσ⟩, rfl⟩
  rw [← Nat.card_range_of_injective hf, hr, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem natCard_sylowSub : Nat.card sylowSub = 9 := by
  rw [natCard_of_iff sylowSub sylowList sylowList_mem mem_sylowSub_iff sylowList_nodup]
  rfl

theorem factorization_443520 : (443520 : ℕ).factorization 3 = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : (443520 : ℕ) = 3 ^ 2 * 49280 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end M22Norm2Aux

open M22Norm2Aux in
theorem norm2_M22 :
    Norm2 (CFSG.Blueprint.NativeSporadic.M22) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.M22).factorization 3 = 2 := by
    rw [CFSG.Sporadic.Mathieu.card_M22]
    exact factorization_443520
  let S : Sylow 3 CFSG.Blueprint.NativeSporadic.M22 :=
    Sylow.ofCard sylowSub (by rw [natCard_sylowSub, hfac] <;> norm_num)
  refine Norm2.of_inner CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card S ?_
  intro B hBS _
  exact ⟨kleinSub, kleinSub_ne_bot, kleinSub_isPGroup, le_trans hBS sylowSub_le_normalizer⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

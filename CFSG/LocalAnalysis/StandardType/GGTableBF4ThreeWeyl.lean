module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
open scoped Pointwise

namespace TableBF4

local instance tableBF4ThreeNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def wordActF4 (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  ω.foldr (fun i v => reflect .F4 i v) v

theorem wordProd_smul_F4 (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    (coxeterSystem .F4).wordProd ω • v = wordActF4 ω v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih]
    exact simple_smul i _

@[expose] def word1 : List (Fin Tag.F4.rank) := [1, 0]

@[expose] def word2 : List (Fin Tag.F4.rank) := [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2]

@[expose] def weylW1 : WeylGroup .F4 := (coxeterSystem .F4).wordProd word1

@[expose] def weylW2 : WeylGroup .F4 := (coxeterSystem .F4).wordProd word2

theorem weylW1_pow_three : weylW1 ^ 3 = 1 := by
  refine ext_single fun i => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, weylW1, wordProd_smul_F4,
    wordProd_smul_F4, wordProd_smul_F4]
  revert i
  decide +kernel

theorem weylW2_pow_three : weylW2 ^ 3 = 1 := by
  refine ext_single fun i => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, weylW2, wordProd_smul_F4,
    wordProd_smul_F4, wordProd_smul_F4]
  revert i
  decide +kernel

theorem weylW1_mul_weylW2 : weylW1 * weylW2 = weylW2 * weylW1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, weylW1, weylW2, wordProd_smul_F4, wordProd_smul_F4, wordProd_smul_F4,
    wordProd_smul_F4]
  revert i
  decide +kernel

theorem weylW1_ne_one : weylW1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun w : WeylGroup .F4 => w • (Pi.single 0 1 : Fin Tag.F4.rank → ℤ)) h
  simp only [one_smul, weylW1, wordProd_smul_F4] at h1
  revert h1
  decide +kernel

theorem weylW2_ne_one : weylW2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun w : WeylGroup .F4 => w • (Pi.single 3 1 : Fin Tag.F4.rank → ℤ)) h
  simp only [one_smul, weylW2, wordProd_smul_F4] at h1
  revert h1
  decide +kernel

theorem weylW2_ne_weylW1 : weylW2 ≠ weylW1 := by
  intro h
  have h1 := congrArg (fun w : WeylGroup .F4 => w • (Pi.single 0 1 : Fin Tag.F4.rank → ℤ)) h
  simp only [weylW1, weylW2, wordProd_smul_F4] at h1
  revert h1
  decide +kernel

theorem weylW2_ne_weylW1_sq : weylW2 ≠ weylW1 ^ 2 := by
  intro h
  have h1 := congrArg (fun w : WeylGroup .F4 => w • (Pi.single 0 1 : Fin Tag.F4.rank → ℤ)) h
  simp only [pow_two, mul_smul, weylW1, weylW2, wordProd_smul_F4] at h1
  revert h1
  decide +kernel

theorem orderOf_weylW1 : orderOf weylW1 = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime weylW1_pow_three weylW1_ne_one

theorem orderOf_weylW2 : orderOf weylW2 = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime weylW2_pow_three weylW2_ne_one

@[expose] def weylS : Subgroup (WeylGroup .F4) :=
  Subgroup.zpowers weylW1 ⊔ Subgroup.zpowers weylW2

theorem zpowers_weylW2_le_normalizer :
    Subgroup.zpowers weylW2 ≤ Subgroup.normalizer (Subgroup.zpowers weylW1 : Set (WeylGroup .F4)) := by
  intro y hy
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow (weylW1_mul_weylW2 : Commute weylW1 weylW2) k m).eq

theorem exists_pow_eq_zpow_of_orderOf {w : WeylGroup .F4} (hw : orderOf w = 3) (k : ℤ) :
    ∃ a : ℕ, a < 3 ∧ w ^ k = w ^ a := by
  have h := (zpow_mod_orderOf w k).symm
  rw [hw] at h
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  rw [h, ← zpow_natCast, Int.toNat_of_nonneg h0]
  norm_num

theorem disjoint_zpowers_weylW :
    Disjoint (Subgroup.zpowers weylW1) (Subgroup.zpowers weylW2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card (Subgroup.zpowers weylW1 ⊓ Subgroup.zpowers weylW2 : Subgroup _) ∣ 3 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : Subgroup.zpowers weylW1 ⊓ Subgroup.zpowers weylW2 ≤ _)
    rwa [Nat.card_zpowers, orderOf_weylW2] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · rw [disjoint_iff]
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers weylW1 ⊓ Subgroup.zpowers weylW2 = Subgroup.zpowers weylW2 :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, orderOf_weylW2])
    have hmem : weylW2 ∈ Subgroup.zpowers weylW1 ⊓ Subgroup.zpowers weylW2 := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem.1
    obtain ⟨a, ha, ha'⟩ := exists_pow_eq_zpow_of_orderOf orderOf_weylW1 k
    rw [ha'] at hk
    interval_cases a
    · exact weylW2_ne_one (by rw [← hk, pow_zero])
    · exact weylW2_ne_weylW1 (by rw [← hk, pow_one])
    · exact weylW2_ne_weylW1_sq hk.symm

theorem card_weylS : Nat.card weylS = 9 := by
  rw [weylS, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    zpowers_weylW2_le_normalizer disjoint_zpowers_weylW, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_weylW1, orderOf_weylW2]

theorem exists_eq_of_mem_weylS {w : WeylGroup .F4} (hw : w ∈ weylS) :
    ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ w = weylW1 ^ a * weylW2 ^ b := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left _ _ zpowers_weylW2_le_normalizer
  have hw' : w ∈ (Subgroup.zpowers weylW1 : Set (WeylGroup .F4)) *
      (Subgroup.zpowers weylW2 : Set (WeylGroup .F4)) := by
    rw [← h]
    exact hw
  obtain ⟨x, hx, y, hy, rfl⟩ := hw'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨a, ha, ha'⟩ := exists_pow_eq_zpow_of_orderOf orderOf_weylW1 k
  obtain ⟨b, hb, hb'⟩ := exists_pow_eq_zpow_of_orderOf orderOf_weylW2 m
  exact ⟨a, b, ha, hb, by rw [ha', hb']⟩

theorem weylW1_mem_weylS : weylW1 ∈ weylS :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem weylW2_mem_weylS : weylW2 ∈ weylS :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

@[expose] def torusReflF4 (i : Fin Tag.F4.rank) (a : Fin Tag.F4.rank → ZMod 3) :
    Fin Tag.F4.rank → ZMod 3 :=
  a - (∑ j, ((Tag.F4.cartan j i : ℤ) : ZMod 3) * a j) • Pi.single i 1

@[expose] def torusWordF4 (ω : List (Fin Tag.F4.rank)) (a : Fin Tag.F4.rank → ZMod 3) :
    Fin Tag.F4.rank → ZMod 3 :=
  ω.foldr torusReflF4 a

theorem torusReflF4_eq (i : Fin Tag.F4.rank) (a : Fin Tag.F4.rank → ZMod 3) :
    torusReflF4 i a = a - cartanFunctional .F4 3 i a • Pi.single i 1 := by
  rw [CFSG.RankThree.CentralCover.cartanFunctional_apply]
  rfl

@[expose] def wordAB (a b : ℕ) : List (Fin Tag.F4.rank) :=
  (List.replicate a word1).flatten ++ (List.replicate b word2).flatten

theorem wordProd_replicate (ω : List (Fin Tag.F4.rank)) (a : ℕ) :
    (coxeterSystem .F4).wordProd (List.replicate a ω).flatten =
      (coxeterSystem .F4).wordProd ω ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.flatten_cons, CoxeterSystem.wordProd_append, ih, pow_succ']

theorem wordProd_wordAB (a b : ℕ) :
    (coxeterSystem .F4).wordProd (wordAB a b) = weylW1 ^ a * weylW2 ^ b := by
  rw [wordAB, CoxeterSystem.wordProd_append, wordProd_replicate, wordProd_replicate]
  rfl

theorem card_fix_torusWordF4_le : ∀ a b : Fin 3, (a, b) ≠ (0, 0) →
    (Finset.univ.filter fun x : Fin Tag.F4.rank → ZMod 3 =>
      torusWordF4 (wordAB a b) x = x).card ≤ 9 := by
  decide +kernel

theorem card_fix_word1_word2_le : (Finset.univ.filter fun x : Fin Tag.F4.rank → ZMod 3 =>
    torusWordF4 word1 x = x ∧ torusWordF4 word2 x = x).card ≤ 3 := by
  decide +kernel

section Weyl

variable (K : Type) [Field K]

@[expose] noncomputable def nWordF4 (ω : List (Fin Tag.F4.rank)) : adjointGroup .F4 K :=
  (ω.map fun i => (⟨weylElt .F4 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup .F4 K)).prod

variable {K}

theorem nWordF4_cons (i : Fin Tag.F4.rank) (ω : List (Fin Tag.F4.rank)) :
    nWordF4 K (i :: ω) = ⟨weylElt .F4 K i 1, weylElt_mem_adjointGroup i 1⟩ * nWordF4 K ω := by
  rw [nWordF4, List.map_cons, List.prod_cons]
  rfl

theorem coe_nWordF4 (ω : List (Fin Tag.F4.rank)) :
    ((nWordF4 K ω : adjointGroup .F4 K) : ModGL .F4 K) =
      (ω.map fun i => weylElt .F4 K i 1).prod := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [nWordF4_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]

theorem coe_nWordF4_mem_monomialSubgroup (ω : List (Fin Tag.F4.rank)) :
    ((nWordF4 K ω : adjointGroup .F4 K) : ModGL .F4 K) ∈ monomialSubgroup .F4 K := by
  rw [coe_nWordF4]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_monomialSubgroup i

theorem nWordF4_conj_chevTorus {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (ω : List (Fin Tag.F4.rank))
    (a : Fin Tag.F4.rank → ZMod 3) :
    nWordF4 K ω * chevTorus .F4 ζ hζ (.ofAdd a) * (nWordF4 K ω)⁻¹ =
      chevTorus .F4 ζ hζ (.ofAdd (torusWordF4 ω a)) := by
  induction ω with
  | nil => simp [nWordF4, torusWordF4]
  | cons i ω ih =>
    rw [nWordF4_cons, mul_inv_rev]
    have e : ∀ x y z : adjointGroup .F4 K, x * y * z * (y⁻¹ * x⁻¹) = x * (y * z * y⁻¹) * x⁻¹ :=
      fun x y z => by group
    rw [e, ih, weylElt_conj_chevTorus]
    show _ = chevTorus .F4 ζ hζ (.ofAdd (torusReflF4 i (torusWordF4 ω a)))
    rw [torusReflF4_eq]


theorem weylQuotientHom_nWordF4 (ω : List (Fin Tag.F4.rank)) :
    weylQuotientHom .F4 K ⟨_, coe_nWordF4_mem_monomialSubgroup ω⟩ =
      (coxeterSystem .F4).wordProd ω := by
  apply weylQuotientHom_eq
  show MapsRootLines ((nWordF4 K ω : adjointGroup .F4 K) : ModGL .F4 K) _
  rw [coe_nWordF4]
  exact mapsRootLines_list_prod ω

end Weyl

end TableBF4

end CFSG.StandardType

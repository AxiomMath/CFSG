module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowCyclic
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

namespace TableBExc

section Torsion

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_cube_mem_torusGroup_E6 (u : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnit .E6 (fun l => u l ^ 3) ∈ torusGroup .E6 K := by
  have he : rootDiagUnit .E6 (fun l => u l ^ 3) = ((List.finRange Tag.E6.rank).map fun j =>
      torusElt .E6 K j (∏ i, u i ^ Tag.E6.cartan.adjugate i j)).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_prod_zpow_eq_smul (Matrix.adjugate_mul _),
      det_cartan_E6]
    congr 1
  rw [he]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.subset_closure ⟨(i, _), rfl⟩

theorem pow_mul_eq_self_of_mod {M : Type*} [Monoid M] {p k : ℕ} (hk : 3 * k % p = 1) {x : M}
    (hx : x ^ p = 1) : x ^ (3 * k) = x := by
  rw [← Nat.div_add_mod (3 * k) p, hk, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

theorem fullp_E6 {p : ℕ} (hp1 : 1 < p) (hp3 : Nat.Coprime 3 p) (a : Fin Tag.E6.rank → Kˣ)
    (ha : ∀ i, a i ^ p = 1) : rootDiagUnit .E6 a ∈ torusGroup .E6 K := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hp3 hp1
  have e : a = fun l => (a l ^ k) ^ 3 := by
    funext l
    rw [← pow_mul, mul_comm, pow_mul_eq_self_of_mod hk (ha l)]
  rw [e]
  exact rootDiagUnit_cube_mem_torusGroup_E6 _

@[expose] noncomputable def torusPowEltP {p : ℕ}
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) : adjointGroup τ K :=
  ⟨rootDiagUnit τ fun i => ζ ^ (x i).val,
    torusGroup_le_adjointGroup (hfullp _ fun i => by
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])⟩

theorem coe_torusPowEltP {p : ℕ}
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) :
    (torusPowEltP hfullp hζ x : ModGL τ K) = rootDiagUnit τ fun i => ζ ^ (x i).val :=
  rfl

theorem bijective_torusPowEltP {p : ℕ} [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    (∀ x, torusPowEltP hfullp hζ x ∈ torusPow τ K p) ∧
      Function.Injective (torusPowEltP hfullp hζ) ∧
      ∀ g ∈ torusPow τ K p, ∃ x, torusPowEltP hfullp hζ x = g := by
  refine ⟨fun x => ⟨hfullp _ fun i => by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow],
    Subtype.ext ?_⟩, fun x y hxy => ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_pow, coe_torusPowEltP, rootDiagUnit_pow, OneMemClass.coe_one,
      ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · funext i
    have h := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) hxy
    simp only [coe_torusPowEltP] at h
    exact CFSG.RankThree.Chevalley.eq_of_pow_val_eq_pow_val hζo
      (congrFun (rootDiagUnit_injective h) i)
  · obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg.1
    have hap' : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [← rootDiagUnit_pow, ← ha, rootDiagUnit_one, ← Subgroup.coe_pow, hg.2,
        OneMemClass.coe_one]
    have hap : a ^ p = 1 := rootDiagUnit_injective hap'
    have hai : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun hap i
    choose m hm using fun i =>
      CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo (hai i)
    refine ⟨m, Subtype.ext ?_⟩
    rw [coe_torusPowEltP, ha]
    congr 1
    exact funext hm

theorem card_torusPow_of_fullp [Finite K] {p : ℕ}
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow τ K p) = p ^ τ.rank := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨hmem, hinj, hsurj⟩ := bijective_torusPowEltP hfullp hζo hζ
  let e : (Fin τ.rank → ZMod p) ≃ torusPow τ K p :=
    Equiv.ofBijective (fun x => ⟨torusPowEltP hfullp hζ x, hmem x⟩)
      ⟨fun x y h => hinj (congrArg Subtype.val h), fun g => by
        obtain ⟨x, hx⟩ := hsurj g g.2
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_torusPow_E6 [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow .E6 K p) = p ^ 6 :=
  card_torusPow_of_fullp (fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2
    (Ne.symm hp3))) hp hpq

end Torsion

@[expose] def prodE6 (q : ℕ) : ℕ :=
  geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q * geomSum 5 1 q *
    (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q)

theorem not_dvd_smooth_seven {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (a b c : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h)
    omega

section Orders

variable {K : Type} [Field K]

theorem card_adjointGroup_E6_eq [Finite K] :
    Nat.card (adjointGroup .E6 K) =
      Nat.card (torusGroup .E6 K) * (Nat.card K ^ 36 * prodE6 (Nat.card K)) := by
  classical
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  rw [card_adjointGroup, finsum_eq_sum_of_fintype,
    CFSG.Timmesfeld.ExceptionalOrders.sum_length_E6,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6, prodE6, mul_assoc]

theorem not_dvd_index_torusGroup_E6 [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .E6 K).subgroupOf (adjointGroup .E6 K)).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [index_torusGroup_eq card_adjointGroup_E6_eq]
  have hq1 := cast_eq_one_of_dvd_sub_one hq hpq
  have hW := not_dvd_smooth_seven hp hp7 7 4 1
  rw [← ZMod.natCast_eq_zero_iff] at hW ⊢
  intro h
  apply hW
  rw [← h, prodE6]
  push_cast
  simp only [geomSum_cast hq1, hq1, one_pow]
  norm_num

theorem ggExcToralRankInput_E6_of_seven_le [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput .E6 K p :=
  ggExcToralRankInput_of_not_dvd_index hp (not_dvd_index_torusGroup_E6 hp hp7 hpq)
    (card_torusPow_E6 hp (by omega) hpq)

end Orders

local instance tableBExcE6NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

local instance tableBExcE6FactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def wordE6Five : List (Fin Tag.E6.rank) := [0, 2, 3, 4]

theorem orderOf_wordE6Five : orderOf ((coxeterSystem .E6).wordProd wordE6Five) = 5 :=
  orderOf_wordProd_eq Nat.prime_five _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem card_fix_wordE6Five :
    Nat.card {x : Fin Tag.E6.rank → ZMod 5 // torusWord .E6 5 wordE6Five x = x} ≤ 5 ^ (6 - 2) :=
  card_fix_torusWord_le (τ := .E6) wordE6Five ![0, 2] ![0, 1] (by decide)
    ![![2, 3], ![3, 3]] (by decide +kernel)

section Five

variable {K : Type} [Field K]

theorem ggExcToralRankInput_E6_five [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E6 K 5 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_five_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h5)
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG
  have hGm : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  refine ggExcToralRankInput_of_cyclic Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five det_cartan_E6 (by norm_num))
    (card_torusPow_E6 Nat.prime_five (by norm_num) h5) wordE6Five orderOf_wordE6Five
    (M := Nat.card K ^ 36 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E6_eq, prodE6]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm1, geomSum_cast hq1, one_pow, Nat.cast_one]
    decide
  · calc 5 * Nat.card {x : Fin Tag.E6.rank → ZMod 5 // torusWord .E6 5 wordE6Five x = x}
        ≤ 5 * 5 ^ (6 - 2) := Nat.mul_le_mul_left _ card_fix_wordE6Five
      _ < 5 ^ Tag.E6.rank := by decide

theorem ggExcToralRankInput_E6_of_ne_three [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput .E6 K p := by
  by_cases h7 : 7 ≤ p
  · exact ggExcToralRankInput_E6_of_seven_le hp h7 hpq
  · have h5 : p = 5 := by
      interval_cases p <;> first | omega | exact absurd hp (by decide)
    subst h5
    exact ggExcToralRankInput_E6_five hpq

end Five

end TableBExc

end CFSG.StandardType

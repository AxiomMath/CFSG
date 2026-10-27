module

public import CFSG.RankThree.PartOne.SRC.RankOneAux
public import CFSG.RankThree.PartOne.SLBN.OddSum
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.SLBG2

open Subgroup Matrix CFSG CFSG.SL2MinimalFaithful CFSG.RankThree.PartOne.SRC
open scoped MatrixGroups

theorem eq_one_of_sq_eq_one_of_pow_odd {G : Type*} [Group G] {x : G} {m : ℕ} (hm : Odd m)
    (h2 : x ^ 2 = 1) (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hx
  exact hx

theorem pow_five_of_mem_zpowers {G : Type*} [Group G] {a y : G} (ha : a ^ 5 = 1)
    (hy : y ∈ Subgroup.zpowers a) : y ^ 5 = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ha, _root_.one_zpow]

section ThreeInvolutions

variable {S : Type*} [Group S] {V : Type*} [CommGroup V] [Finite V]

theorem card_le_of_three (hV3 : ∀ x : V, x ^ 3 = 1) (b : Fin 3 → S) (hb2 : ∀ i, b i * b i = 1)
    (hb : b 0 * b 1 * b 2 = 1) (ρ : S →* MulAut V)
    (hfix : ∀ i, Nat.card {v : V | ρ (b i) v = v} ≤ 3) : Nat.card V ≤ 27 := by
  have hsq : ∀ i, ρ (b i) * ρ (b i) = 1 := fun i => by rw [← map_mul, hb2 i, map_one]
  have hp : ρ (b 0) * ρ (b 1) * ρ (b 2) = 1 := by rw [← map_mul, ← map_mul, hb, map_one]
  let F : {v : V | ρ (b 0) v = v} × {v : V | ρ (b 1) v = v} × {v : V | ρ (b 2) v = v} → V :=
    fun m => (m.1 : V) * m.2.1 * m.2.2
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨c₁, c₂, c₃, e₁, e₂, e₃, hx⟩ := CFSG.RankThree.PartOne.SLBN.exists_prod_fixed_three hV3
      (ρ (b 0)) (ρ (b 1)) (ρ (b 2)) (hsq 0) (hsq 1) (hsq 2) hp x
    exact ⟨(⟨c₁, e₁⟩, ⟨c₂, e₂⟩, ⟨c₃, e₃⟩), hx.symm⟩
  have h := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_prod] at h
  calc Nat.card V ≤ Nat.card {v : V | ρ (b 0) v = v} *
        (Nat.card {v : V | ρ (b 1) v = v} * Nat.card {v : V | ρ (b 2) v = v}) := h
    _ ≤ 3 * (3 * 3) := by
      gcongr
      · exact hfix 0
      · exact hfix 1
      · exact hfix 2
    _ = 27 := by norm_num

end ThreeInvolutions

section Cover

variable {K : Type} [Field K] {S : Type} [Group S]

theorem exists_card_25 [Finite K] (hK : Nat.card K = 9) (ι : SL(2, K) × SL(2, K) →* S)
    (hι : ∀ A, ι A = 1 → A ^ 2 = 1) : ∃ P : Subgroup S, Nat.card P = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card (SL(2, K)) := by
    rw [card_specialLinearGroup_fin_two, hK]
    norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 h5
  set PX : Subgroup (SL(2, K) × SL(2, K)) := (Subgroup.zpowers a).prod (Subgroup.zpowers a) with hPX
  have hcard : Nat.card PX = 25 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers a) (Subgroup.zpowers a)).toEquiv,
      Nat.card_prod, Nat.card_zpowers, ha]
  have h5a : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hpow5 : ∀ x : PX, ((x : SL(2, K) × SL(2, K))) ^ 5 = 1 := by
    intro x
    have hx := Subgroup.mem_prod.mp x.2
    exact Prod.ext (by simpa [Prod.pow_fst] using pow_five_of_mem_zpowers h5a hx.1)
      (by simpa [Prod.pow_snd] using pow_five_of_mem_zpowers h5a hx.2)
  let f : PX →* S := ι.comp PX.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι (x : SL(2, K) × SL(2, K)) = 1 := hx
    exact Subtype.ext (eq_one_of_sq_eq_one_of_pow_odd (m := 5) (by decide) (hι _ h1) (hpow5 x))
  refine ⟨PX.map ι, ?_⟩
  have hmap : PX.map ι = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]

@[expose] def uProd : Multiplicative K × Multiplicative K →* SL(2, K) × SL(2, K) :=
  (unipotentHom (F := K)).prodMap (unipotentHom (F := K))

theorem uProd_injective : Function.Injective (uProd (K := K)) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (unipotentHom_injective h1) (unipotentHom_injective h2)

theorem uProd_pow_three [CharP K 3] (x : Multiplicative K × Multiplicative K) : (uProd x) ^ 3 = 1 := by
  have h3 : ∀ s : Multiplicative K, s ^ 3 = 1 := by
    intro s
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    have : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    calc 3 • Multiplicative.toAdd s = (3 : K) * Multiplicative.toAdd s := by
          rw [nsmul_eq_mul]; norm_num
      _ = 0 := by rw [this, zero_mul]
  have hx : x ^ 3 = 1 := Prod.ext (h3 x.1) (h3 x.2)
  rw [← map_pow, hx, map_one]

theorem exists_pair [CharP K 3] (hK : Nat.card K = 9) (ι : SL(2, K) × SL(2, K) →* S)
    (hι : ∀ A, ι A = 1 → A ^ 2 = 1) {b : S} (hb : orderOf b = 2) (hc : ∀ g, ι g * b = b * ι g) :
    ∃ (T E : Subgroup S) (k : ℕ), T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElementaryAbelian 3 E ∧ 4 ≤ k ∧
      Nat.card E = 3 ^ k ∧ E ≤ normalizer (T : Set S) := by
  have hψinj : Function.Injective ((ι.comp uProd)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι (uProd x) = 1 := hx
    have h2 := hι _ h1
    have h3 := uProd_pow_three x
    exact uProd_injective (by rw [map_one]; exact eq_one_of_sq_eq_one_of_pow_odd (m := 3) (by decide) h2 h3)
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    omega
  refine ⟨Subgroup.zpowers b, (ι.comp uProd).range, 4, ?_, ?_, ?_, le_rfl, ?_, ?_⟩
  · intro h
    exact hb1 (by simpa using (Subgroup.zpowers_eq_bot.mp h))
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; simp)
  ·
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · refine ⟨⟨fun x y => ?_⟩⟩
      obtain ⟨x', hx'⟩ := x.2
      obtain ⟨y', hy'⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx', ← hy', ← map_mul, ← map_mul, mul_comm x' y']
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
      obtain ⟨x', hx'⟩ := x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hx', ← map_pow, Subgroup.coe_one]
      show ι (uProd (x' ^ 3)) = 1
      rw [map_pow, uProd_pow_three, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, Nat.card_prod]
    have : Nat.card (Multiplicative K) = 9 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      exact hK
    rw [this]
    norm_num
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hxc : ι (uProd y) ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup S) : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcw : b * ι (uProd y) = ι (uProd y) * b := (hc _).symm
      exact (Commute.zpow_left (show Commute b (ι (uProd y)) from hcw) m).eq
    exact Subgroup.centralizer_le_normalizer _ hxc

end Cover

end CFSG.RankThree.PartOne.SLBG2

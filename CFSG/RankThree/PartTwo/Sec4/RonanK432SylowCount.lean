module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open scoped Pointwise

theorem card_sylow_mem_modEq_one {G : Type} [Group G] [Finite G] {x : G} (hx : x ^ 3 = 1) :
    Nat.card {Q : Sylow 3 G // x ∈ Q} ≡ 1 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) := by
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have h1 := hp.card_modEq_card_fixedPoints (Sylow 3 G)
  have h2 := card_sylow_modEq_one 3 G
  have h3 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) (Sylow 3 G)) =
      Nat.card {Q : Sylow 3 G // x ∈ Q} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun Q => by
      rw [hp.sylow_mem_fixedPoints_iff]
      exact Subgroup.zpowers_le)
  rw [h3] at h1
  exact h1.symm.trans h2

section DoubleCount

variable {G : Type} [Group G] [Finite G]

theorem mem_smul_sylow_iff {P : Sylow 3 G} {g y : G} : y ∈ g • P ↔ g⁻¹ * y * g ∈ P := by
  have h : ((g • P : Sylow 3 G) : Subgroup G) = MulAut.conj g • (P : Subgroup G) :=
    Sylow.coe_subgroup_smul
  show y ∈ ((g • P : Sylow 3 G) : Subgroup G) ↔ _
  rw [h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem mem_iff_conj_mem {X : Set G} (hX : ∀ g y : G, y ∈ X → g * y * g⁻¹ ∈ X) (g y : G) :
    y ∈ X ↔ g * y * g⁻¹ ∈ X :=
  ⟨hX g y, fun h => by simpa [mul_assoc] using hX g⁻¹ _ h⟩

theorem ncard_mul_eq_card_mul (X : Set G) {s t : ℕ}
    (hs : ∀ y ∈ X, Nat.card {Q : Sylow 3 G // y ∈ Q} = s)
    (ht : ∀ Q : Sylow 3 G, Nat.card {y : G // y ∈ X ∧ y ∈ Q} = t) :
    X.ncard * s = Nat.card (Sylow 3 G) * t := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite (Sylow 3 G)
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (y : G) (Q : Sylow 3 G) => y ∈ Q) (s := X.toFinset) (t := Finset.univ)
  have e1 : ∀ y : G, (Finset.bipartiteAbove (fun (y : G) (Q : Sylow 3 G) => y ∈ Q)
      Finset.univ y).card = Nat.card {Q : Sylow 3 G // y ∈ Q} := by
    intro y
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have e2 : ∀ Q : Sylow 3 G, (Finset.bipartiteBelow (fun (y : G) (Q : Sylow 3 G) => y ∈ Q)
      X.toFinset Q).card = Nat.card {y : G // y ∈ X ∧ y ∈ Q} := by
    intro Q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp [Finset.bipartiteBelow]
  rw [Finset.sum_congr rfl (fun y hy => (e1 y).trans (hs y (by simpa using hy))),
    Finset.sum_congr rfl (fun Q _ => (e2 Q).trans (ht Q))] at key
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ] at key
  rw [Set.ncard_eq_toFinset_card' X, key, Nat.card_eq_fintype_card]

theorem card_inter_sylow_eq {X : Set G} (hX : ∀ g y : G, y ∈ X → g * y * g⁻¹ ∈ X)
    (P Q : Sylow 3 G) :
    Nat.card {y : G // y ∈ X ∧ y ∈ Q} = Nat.card {y : G // y ∈ X ∧ y ∈ P} := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  refine Nat.card_congr ((Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun y => ?_).symm)
  show (y ∈ X ∧ y ∈ P) ↔ (g * y * g⁻¹ ∈ X ∧ g * y * g⁻¹ ∈ g • P)
  rw [mem_smul_sylow_iff, ← mem_iff_conj_mem hX]
  simp [mul_assoc]

theorem card_sylow_mem_conj (x g : G) :
    Nat.card {Q : Sylow 3 G // g * x * g⁻¹ ∈ Q} = Nat.card {Q : Sylow 3 G // x ∈ Q} := by
  refine Nat.card_congr ((Equiv.subtypeEquiv (MulAction.toPerm g : Equiv.Perm (Sylow 3 G))
    fun Q => ?_).symm)
  show x ∈ Q ↔ g * x * g⁻¹ ∈ g • Q
  rw [mem_smul_sylow_iff]
  simp [mul_assoc]

theorem class_mul_card_sylow_mem (x : G) (P : Sylow 3 G) :
    (conjugatesOf x).ncard * Nat.card {Q : Sylow 3 G // x ∈ Q} =
      Nat.card (Sylow 3 G) * Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P} := by
  have hX : ∀ g y : G, y ∈ conjugatesOf x → g * y * g⁻¹ ∈ conjugatesOf x := by
    intro g y hy
    exact hy.trans (isConj_iff.2 ⟨g, rfl⟩)
  refine ncard_mul_eq_card_mul (conjugatesOf x) (fun y hy => ?_)
    (fun Q => card_inter_sylow_eq hX P Q)
  obtain ⟨g, rfl⟩ := isConj_iff.1 (show IsConj x y from hy)
  exact card_sylow_mem_conj x g

end DoubleCount

section Numbers

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_27 {g' : ℕ} (hG : Nat.card G = 27 * g') (hg' : g' % 3 = 2) (P : Sylow 3 G) :
    Nat.card P = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg0 : g' ≠ 0 := by omega
  have h3 : ¬ 3 ∣ g' := by omega
  rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul (by norm_num) hg0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3, add_zero,
    show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem ncard_conjugatesOf_mul_card_centralizer (x : G) :
    (conjugatesOf x).ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  rw [← Subgroup.index_centralizer_eq_ncard, mul_comm]
  exact Subgroup.card_mul_index _

theorem mod_nine_of_count {sB d mB tB : ℕ} (hs : sB % 3 = 1) (hd : d % 3 = 2) (hm : mB % 3 = 2)
    (h : 3 * (sB * d) = tB * mB) : tB % 9 = 3 := by
  have h1 : tB % 3 = 0 := by
    have := Nat.mul_mod tB mB 3
    rw [hm] at this
    omega
  obtain ⟨u, rfl⟩ : 3 ∣ tB := Nat.dvd_of_mod_eq_zero h1
  have h2 : sB * d = u * mB := by
    have : 3 * u * mB = 3 * (u * mB) := by ring
    omega
  have h3 : u % 3 = 1 := by
    have e1 := Nat.mul_mod sB d 3
    have e2 := Nat.mul_mod u mB 3
    rw [hs, hd] at e1
    rw [hm] at e2
    omega
  omega

theorem card_class_inter_sylow_mod_nine {g' m : ℕ} (hG : Nat.card G = 27 * g') (hg' : g' % 3 = 2)
    {x : G} (hx : x ^ 3 = 1) (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9 * m)
    (hm : m % 3 = 2) (P : Sylow 3 G) :
    Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P} % 9 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP27 := card_sylow_eq_27 hG hg' P
  have hn1 : Nat.card (Sylow 3 G) % 3 = 1 := card_sylow_modEq_one 3 G
  have hNn : Nat.card (Subgroup.normalizer (P : Set G)) * Nat.card (Sylow 3 G) = Nat.card G := by
    rw [P.card_eq_index_normalizer]
    exact Subgroup.card_mul_index _
  obtain ⟨d, hd⟩ : 27 ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    rw [← hP27]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hnd : Nat.card (Sylow 3 G) * d = g' := by
    rw [hd, hG] at hNn
    have : 27 * (Nat.card (Sylow 3 G) * d) = 27 * g' := by rw [← hNn]; ring
    omega
  have hd3 : d % 3 = 2 := by
    have := Nat.mul_mod (Nat.card (Sylow 3 G)) d 3
    rw [hnd, hn1] at this
    omega
  have hs1 : Nat.card {Q : Sylow 3 G // x ∈ Q} % 3 = 1 := card_sylow_mem_modEq_one hx
  have hdc := class_mul_card_sylow_mem x P
  have hcl := ncard_conjugatesOf_mul_card_centralizer x
  have key : Nat.card G * (Nat.card {Q : Sylow 3 G // x ∈ Q} *
      Nat.card (Subgroup.normalizer (P : Set G))) =
      Nat.card G * (Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P}) := by
    calc Nat.card G * (Nat.card {Q : Sylow 3 G // x ∈ Q} *
          Nat.card (Subgroup.normalizer (P : Set G)))
        = ((conjugatesOf x).ncard * Nat.card (Subgroup.centralizer ({x} : Set G))) *
          (Nat.card {Q : Sylow 3 G // x ∈ Q} * Nat.card (Subgroup.normalizer (P : Set G))) := by
          rw [hcl]
      _ = ((conjugatesOf x).ncard * Nat.card {Q : Sylow 3 G // x ∈ Q}) *
          (Nat.card (Subgroup.centralizer ({x} : Set G)) *
            Nat.card (Subgroup.normalizer (P : Set G))) := by ring
      _ = (Nat.card (Sylow 3 G) * Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P}) *
          (Nat.card (Subgroup.centralizer ({x} : Set G)) *
            Nat.card (Subgroup.normalizer (P : Set G))) := by rw [hdc]
      _ = (Nat.card (Subgroup.normalizer (P : Set G)) * Nat.card (Sylow 3 G)) *
          (Nat.card (Subgroup.centralizer ({x} : Set G)) *
            Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P}) := by ring
      _ = Nat.card G * (Nat.card (Subgroup.centralizer ({x} : Set G)) *
          Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P}) := by rw [hNn]
  have key' := Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  rw [hd, hc] at key'
  refine mod_nine_of_count (sB := Nat.card {Q : Sylow 3 G // x ∈ Q}) (d := d) (mB := m) hs1 hd3
    hm ?_
  have : 9 * (3 * (Nat.card {Q : Sylow 3 G // x ∈ Q} * d)) =
      9 * (Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P} * m) := by
    calc 9 * (3 * (Nat.card {Q : Sylow 3 G // x ∈ Q} * d))
        = Nat.card {Q : Sylow 3 G // x ∈ Q} * (27 * d) := by ring
      _ = 9 * m * Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P} := key'
      _ = 9 * (Nat.card {y : G // y ∈ conjugatesOf x ∧ y ∈ P} * m) := by ring
  omega

end Numbers

end CFSG.RankThree.PartTwo.Sec4.RonanK432

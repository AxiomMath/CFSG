module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Alg
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S42B1

open Equiv

variable {G : Type} [Group G]

theorem eq_one_of_pow_odd_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨e, he⟩ := hQ ⟨x, hx⟩
  have h2 : x ^ (2 ^ e) = 1 := by
    simpa using congrArg Subtype.val he
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h1 : orderOf x ∣ Nat.gcd (2 ^ e) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hxm)
  rw [hcop] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem mem_of_pow_odd_mem {Q K : Subgroup G} (hQ : IsPGroup 2 Q) {q : G} (hq : q ∈ Q)
    {m : ℕ} (hm : Odd m) (hqm : q ^ m ∈ K) : q ∈ K := by
  obtain ⟨e, he⟩ := hQ ⟨q, hq⟩
  have h2 : q ^ (2 ^ e) = 1 := by
    simpa using congrArg Subtype.val he
  have hcop : Nat.Coprime m (orderOf q) :=
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)).symm.coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one h2)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact K.pow_mem hqm u

theorem mem_of_odd_of_le_sup {K Q X : Subgroup G} (hKn : X ≤ Subgroup.normalizer (K : Set G))
    (hQX : Q ≤ X) (hQ : IsPGroup 2 Q) (hX : X ≤ K ⊔ Q) {y : G} (hy : y ∈ X) {m : ℕ}
    (hm : Odd m) (hym : y ^ m = 1) : y ∈ K := by
  obtain ⟨k, hk, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (fun q hq => hKn (hQX hq))).mp (hX hy)
  have hpow : ∀ n : ℕ, ∃ k' ∈ K, (k * q) ^ n = k' * q ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', hn⟩ := ih
      refine ⟨k' * (q ^ n * k * (q ^ n)⁻¹), K.mul_mem hk' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hKn (hQX (Q.pow_mem hq n))) k).mp hk
      · rw [pow_succ, hn]; group
  obtain ⟨k', hk', hn⟩ := hpow m
  rw [hym] at hn
  have hqm : q ^ m ∈ K := by
    have : q ^ m = k'⁻¹ := by
      have h1 : k' * q ^ m = 1 := hn.symm
      exact eq_inv_of_mul_eq_one_right h1
    rw [this]; exact K.inv_mem hk'
  exact K.mul_mem hk (mem_of_pow_odd_mem hQ hq hm hqm)

theorem centralizes_of_comm_mod {P N : Subgroup G} (hP : IsPGroup 2 P) (hNP : N ≤ P) {d : G}
    {m : ℕ} (hm : Odd m) (hdm : d ^ m = 1)
    (hdN : ∀ n ∈ N, d * n * d⁻¹ = n) (hcomm : ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ N) :
    ∀ x ∈ P, d * x * d⁻¹ = x := by
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n, n = d * x * d⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hnN : n ∈ N := hn ▸ hcomm x hx
  have hxd : d * x * d⁻¹ = n * x := by rw [hn]; group
  have hfix : ∀ k : ℕ, d * n ^ k * d⁻¹ = n ^ k := by
    intro k
    have : d * n ^ k * d⁻¹ = (d * n * d⁻¹) ^ k := by rw [conj_pow]
    rw [this, hdN n hnN]
  have hk : ∀ k : ℕ, d ^ k * x * (d ^ k)⁻¹ = n ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc d ^ (k + 1) * x * (d ^ (k + 1))⁻¹
          = d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = d * (n ^ k * x) * d⁻¹ := by rw [ih]
        _ = (d * n ^ k * d⁻¹) * (d * x * d⁻¹) := by group
        _ = n ^ (k + 1) * x := by rw [hfix k, hxd, pow_succ]; exact (mul_assoc _ _ _).symm
  have h1 := hk m
  rw [hdm] at h1
  have h2 : n ^ m = 1 := by
    have : x = n ^ m * x := by simpa using h1
    exact (mul_eq_right.mp this.symm)
  have h3 : n = 1 := eq_one_of_pow_odd_of_isPGroup hP (hNP hnN) hm h2
  rw [hxd, h3, one_mul]

theorem le_centralizer_conjSub {N Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) (h : N ≤ Subgroup.centralizer (Q : Set G)) :
    N ≤ Subgroup.centralizer ((conjSub g Q : Subgroup G) : Set G) :=
  calc N = conjSub g N := (conjSub_eq_of_mem_normalizer hg).symm
    _ ≤ conjSub g (Subgroup.centralizer (Q : Set G)) := conjSub_mono g h
    _ = Subgroup.centralizer ((conjSub g Q : Subgroup G) : Set G) := (conjSub_centralizer g Q).symm

private theorem centralizer_card_dec : ∀ z : Perm (Fin 5), z ^ 8 = 1 → z ≠ 1 →
    (z ^ 2 ≠ 1 ∨ Perm.sign z ≠ 1) → ¬ 8 ∣ Fintype.card {p : Perm (Fin 5) // p * z = z * p} := by
  decide +kernel

theorem exists_double_transposition_of_normal {P N : Subgroup (Perm (Fin 5))}
    (hP : Nat.card P = 8) (hNP : N ≤ P) (hn : P ≤ Subgroup.normalizer (N : Set (Perm (Fin 5))))
    (hN : N ≠ ⊥) : ∃ z ∈ N, z ≠ 1 ∧ z ^ 2 = 1 ∧ Perm.sign z = 1 := by
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (F53B3.O1.inf_centralizer_ne_bot_of_normalized hP2 hNP hn hN)
  obtain ⟨hzN, hzC⟩ := Subgroup.mem_inf.mp hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzP : z ∈ P := hNP hzN
  have hz8 : z ^ 8 = 1 := by
    have := pow_card_eq_one' (G := P) (x := ⟨z, hzP⟩)
    have h' := congrArg Subtype.val this
    simpa [hP] using h'
  have hPC : P ≤ Subgroup.centralizer ({z} : Set (Perm (Fin 5))) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzC p hp
  have hdvd : 8 ∣ Nat.card (Subgroup.centralizer ({z} : Set (Perm (Fin 5)))) :=
    hP ▸ Subgroup.card_dvd_of_le hPC
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set (Perm (Fin 5)))) =
      Fintype.card {p : Perm (Fin 5) // p * z = z * p} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
      rw [Subgroup.mem_centralizer_singleton_iff])
  rw [hcard] at hdvd
  refine ⟨z, hzN, hz1', ?_⟩
  by_contra hcon
  have h2 : z ^ 2 ≠ 1 ∨ Perm.sign z ≠ 1 := by
    by_cases h : z ^ 2 = 1
    · exact Or.inr (fun hs => hcon ⟨h, hs⟩)
    · exact Or.inl h
  exact centralizer_card_dec z hz8 hz1' h2 hdvd

end F53.Stellmacher.S42B1

end CFSG.Quasithin

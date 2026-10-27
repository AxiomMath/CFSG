module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32LocBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.P31A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126L1a S126L1b
  S126L1c S126L19a S126L19b S126E Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem isPGroup_L1_inf_centralizer (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) :
    IsPGroup 2 ↥(S126.Li L F.V1 ⊓ Subgroup.centralizer (V : Set G)) :=
  (S126T2.isPGroup_CL h1222 hH).to_le (inf_le_inf_right _ (S126L19b.L1_le_L F))

theorem L1_eq_closure_three (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) :
    S126.Li L F.V1 =
      Subgroup.closure {x : G | x ∈ S126.Li L F.V1 ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} := by
  refine le_antisymm ?_ ?_
  · rw [S126L19b.L1_eq F]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
    have hxL1 : x ∈ S126.Li L F.V1 := Subgroup.subset_closure ⟨⟨hxL, hxN⟩, m, hm, hxm⟩
    have hx3 : x ^ 3 = 1 := S126L19b.pow_three_of_mem h1222 F hH hxL hxN hm hxm
    exact Subgroup.subset_closure ⟨hxL1, 1, by rw [pow_one]; exact hx3⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxL1, -, -⟩
    exact hxL1

theorem isSolvable_L1 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Group.IsSolvable ↥(S126.Li L F.V1) := by
  obtain ⟨a, ha⟩ := S126L19a.card_inf_eq_pow h1222 hH (S126L19b.L1_le_L F)
  have hcard := S126L19a.card_eq F hH (S126L19b.L1_le_L F)
  change Nat.card (S126.Li L F.V1) =
    Nat.card (S126L19b.L1bar F hH) * Nat.card ↥(S126.Li L F.V1 ⊓
      Subgroup.centralizer (V : Set G)) at hcard
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card (S126L19b.L1bar F hH) → r = 2 ∨ r = 3 := by
    intro r hr hdvd
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := S126L19b.L1bar F hH) r hdvd
    have h24 : ((σ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) ^ 24 = 1 :=
      S126L19a.pow_24 (S126L19b.blocks_of_mem_L1bar F hH σ.2)
    have hσ24 : (σ : S126L19b.L1bar F hH) ^ 24 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h24
    have h24dvd : r ∣ 24 := by
      rw [← hσ]
      exact orderOf_dvd_of_pow_eq_one hσ24
    have h24' : r ∣ 2 ^ 3 * 3 ^ 1 := by
      rw [show (2 : ℕ) ^ 3 * 3 ^ 1 = 24 by norm_num]
      exact h24dvd
    rcases hr.dvd_mul.mp h24' with h2dvd | h3dvd
    · obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2dvd
      interval_cases j
      · rw [hj] at hr
        exact absurd hr (by norm_num)
      · left
        rw [hj]
        norm_num
      · rw [hj] at hr
        exact absurd hr (by norm_num)
      · rw [hj] at hr
        exact absurd hr (by norm_num)
    · have h3 : r = 1 ∨ r = 3 := (Nat.dvd_prime Nat.prime_three).1 h3dvd
      rcases h3 with h1 | h3
      · exact absurd h1 hr.ne_one
      · exact Or.inr h3
  have hfac : Nat.card (S126L19b.L1bar F hH) =
      2 ^ (Nat.card (S126L19b.L1bar F hH)).factorization 2 *
        3 ^ (Nat.card (S126L19b.L1bar F hH)).factorization 3 := by
    have hn0 : Nat.card (S126L19b.L1bar F hH) ≠ 0 := Nat.card_pos.ne'
    have hsub : (Nat.card (S126L19b.L1bar F hH)).factorization.support ⊆ {2, 3} := by
      intro r hr
      rw [Nat.support_factorization] at hr
      have h := hprime r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
      simpa using h
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rw [Finsupp.prod_of_support_subset _ hsub _ (by simp), Finset.prod_pair (by norm_num)]
  set b := (Nat.card (S126L19b.L1bar F hH)).factorization 2
  set c := (Nat.card (S126L19b.L1bar F hH)).factorization 3
  have hfac' : Nat.card (S126L19b.L1bar F hH) = 2 ^ b * 3 ^ c := hfac
  have hcard' : Nat.card (S126.Li L F.V1) = 2 ^ (b + a) * 3 ^ c := by
    calc Nat.card (S126.Li L F.V1)
        = Nat.card (S126L19b.L1bar F hH) *
            Nat.card ↥(S126.Li L F.V1 ⊓ Subgroup.centralizer (V : Set G)) := hcard
      _ = (2 ^ b * 3 ^ c) * 2 ^ a := by rw [hfac', ha]
      _ = 2 ^ (b + a) * 3 ^ c := by rw [pow_add]; ring
  exact CFSG.GH74.GLS.C3.Layer1.Thm1L32.Loc.isSolvable_of_card_two_pow_mul_three_pow hcard'


theorem tau_mem_Q8 : (swap (0 : Fin 8) 1 * swap 4 5) ∈ S126L1c.Q8 := by
  refine ⟨?_, ?_⟩
  · have h : swap (0 : Fin 8) 1 * swap 4 5 =
        S126L1c.g1 * (S126L1c.bsw * S126L1c.g1 * S126L1c.bsw) := by
      decide
    rw [h]
    exact Subgroup.mul_mem _ S126L1c.g1_mem
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ S126L1c.bsw_mem S126L1c.g1_mem)
        S126L1c.bsw_mem)
  · change swap (0 : Fin 8) 1 * swap 4 5 ∈ alternatingGroup (Fin 8)
    rw [Equiv.Perm.mem_alternatingGroup]
    decide

theorem fin4_aux :
    ∀ a : Fin 4 → Fin 4, (∀ j, a (a (a j)) = j) →
      ∀ j : Fin 4, (swap (0 : Fin 4) 1 ∘ a ∘ swap (0 : Fin 4) 1 ∘ a ∘
        swap (0 : Fin 4) 1 ∘ a ∘ swap (0 : Fin 4) 1 ∘ a) j = j := by
  decide +kernel

theorem blocks_of_cube_one {σ : Perm (Fin 8)}
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨
      (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)))
    (h3 : σ ^ 3 = 1) :
    ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4) := by
  rcases hb with h | h
  · exact h
  · exfalso
    have e : (σ ^ 3) 0 = σ (σ (σ 0)) := by
      rw [show σ ^ 3 = σ * σ * σ by rw [pow_succ, pow_succ, pow_one]]
      rfl
    have h1 : 4 ≤ (σ 0).val := (h 0).1 (by decide)
    have h2 : ¬ (σ 0).val < 4 := by omega
    have h3' : ¬ 4 ≤ (σ (σ 0)).val := fun hc => h2 ((h (σ 0)).2 hc)
    have h4 : (σ (σ 0)).val < 4 := by
      have := (σ (σ 0)).isLt
      omega
    have h5 : 4 ≤ (σ (σ (σ 0))).val := (h (σ (σ 0))).1 h4
    rw [← e, h3] at h5
    norm_num at h5

theorem tau_conj_mul_sq {σ : Perm (Fin 8)}
    (hσb : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) (hσ3 : σ ^ 3 = 1) :
    ((swap (0 : Fin 8) 1 * swap 4 5) * σ * (swap (0 : Fin 8) 1 * swap 4 5)⁻¹ * σ) ^ 2 = 1 := by
  let τ : Perm (Fin 8) := swap (0 : Fin 8) 1 * swap (4 : Fin 8) 5
  let L : Fin 4 → Fin 8 := fun j => ⟨j.val, by omega⟩
  let H8 : Fin 4 → Fin 8 := fun j => ⟨j.val + 4, by omega⟩
  let s : Fin 4 → Fin 4 := swap (0 : Fin 4) 1
  let a : Fin 4 → Fin 4 := fun j => ⟨(σ (L j)).val, by
    have h := (hσb (L j)).1 j.isLt
    simpa [L] using h⟩
  let b : Fin 4 → Fin 4 := fun j => ⟨(σ (H8 j)).val - 4, by
    have h1 : ¬ (H8 j).val < 4 := by simp [H8]
    have h2 : ¬ (σ (H8 j)).val < 4 := fun hc => h1 ((hσb (H8 j)).2 hc)
    have h3 : (σ (H8 j)).val < 8 := (σ (H8 j)).isLt
    omega⟩
  have hσL : ∀ j, σ (L j) = L (a j) := by
    intro j
    apply Fin.ext
    rfl
  have hσH : ∀ j, σ (H8 j) = H8 (b j) := by
    intro j
    have h1 : ¬ (H8 j).val < 4 := by simp [H8]
    have h2 : ¬ (σ (H8 j)).val < 4 := fun hc => h1 ((hσb (H8 j)).2 hc)
    have h3 : (σ (H8 j)).val < 8 := (σ (H8 j)).isLt
    apply Fin.ext
    change (σ (H8 j)).val = (b j).val + 4
    have hb : (b j).val = (σ (H8 j)).val - 4 := rfl
    omega
  have hτL : ∀ j, τ (L j) = L (s j) := by
    intro j
    fin_cases j <;> decide
  have hτH : ∀ j, τ (H8 j) = H8 (s j) := by
    intro j
    fin_cases j <;> decide
  have hτinv : τ⁻¹ = τ := by decide
  have ha3 : ∀ j, a (a (a j)) = j := by
    intro j
    have h1 : (σ ^ 3) (L j) = L j := by rw [hσ3]; rfl
    have h2 : (σ ^ 3) (L j) = L (a (a (a j))) := by
      rw [show σ ^ 3 = σ * σ * σ by rw [pow_succ, pow_succ, pow_one]]
      simp only [Equiv.Perm.mul_apply]
      rw [hσL, hσL, hσL]
    rw [h2] at h1
    exact Fin.ext (by simpa [L] using congrArg Fin.val h1)
  have hb3 : ∀ j, b (b (b j)) = j := by
    intro j
    have h1 : (σ ^ 3) (H8 j) = H8 j := by rw [hσ3]; rfl
    have h2 : (σ ^ 3) (H8 j) = H8 (b (b (b j))) := by
      rw [show σ ^ 3 = σ * σ * σ by rw [pow_succ, pow_succ, pow_one]]
      simp only [Equiv.Perm.mul_apply]
      rw [hσH, hσH, hσH]
    rw [h2] at h1
    have h3 := congrArg Fin.val h1
    simp only [H8] at h3
    exact Fin.ext (by omega)
  have hsq_a : ∀ j, (s ∘ a ∘ s ∘ a ∘ s ∘ a ∘ s ∘ a) j = j := fin4_aux a ha3
  have hsq_b : ∀ j, (s ∘ b ∘ s ∘ b ∘ s ∘ b ∘ s ∘ b) j = j := fin4_aux b hb3
  have hstep_a : ∀ x : Fin 4, (τ * σ * τ⁻¹ * σ) (L x) = L ((s ∘ a ∘ s ∘ a) x) := by
    intro x
    rw [hτinv]
    simp only [Equiv.Perm.mul_apply]
    rw [hσL, hτL, hσL, hτL]
    rfl
  have hstep_b : ∀ x : Fin 4, (τ * σ * τ⁻¹ * σ) (H8 x) = H8 ((s ∘ b ∘ s ∘ b) x) := by
    intro x
    rw [hτinv]
    simp only [Equiv.Perm.mul_apply]
    rw [hσH, hτH, hσH, hτH]
    rfl
  have hlow : ∀ (i : Fin 8) (hi : i.val < 4), ((τ * σ * τ⁻¹ * σ) ^ 2) i = i := by
    intro i hi
    set j : Fin 4 := ⟨i.val, hi⟩ with hj
    have hiL : L j = i := Fin.ext rfl
    rw [← hiL]
    calc ((τ * σ * τ⁻¹ * σ) ^ 2) (L j)
        = (τ * σ * τ⁻¹ * σ) ((τ * σ * τ⁻¹ * σ) (L j)) := rfl
      _ = (τ * σ * τ⁻¹ * σ) (L ((s ∘ a ∘ s ∘ a) j)) := by rw [hstep_a]
      _ = L ((s ∘ a ∘ s ∘ a) ((s ∘ a ∘ s ∘ a) j)) := hstep_a _
      _ = L j := by
            congr 1
            simpa [Function.comp_assoc] using hsq_a j
  have hhigh : ∀ (i : Fin 8) (hi : 4 ≤ i.val), ((τ * σ * τ⁻¹ * σ) ^ 2) i = i := by
    intro i hi
    set j : Fin 4 := ⟨i.val - 4, by omega⟩ with hj
    have hjval : j.val = i.val - 4 := by
      have h := congrArg Fin.val hj
      simpa using h
    have hiH : H8 j = i := by
      apply Fin.ext
      simp only [H8, hjval]
      omega
    rw [← hiH]
    calc ((τ * σ * τ⁻¹ * σ) ^ 2) (H8 j)
        = (τ * σ * τ⁻¹ * σ) ((τ * σ * τ⁻¹ * σ) (H8 j)) := rfl
      _ = (τ * σ * τ⁻¹ * σ) (H8 ((s ∘ b ∘ s ∘ b) j)) := by rw [hstep_b]
      _ = H8 ((s ∘ b ∘ s ∘ b) ((s ∘ b ∘ s ∘ b) j)) := hstep_b _
      _ = H8 j := by
            congr 1
            simpa [Function.comp_assoc] using hsq_b j
  change (τ * σ * τ⁻¹ * σ) ^ 2 = 1
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 4
  · simpa using hlow i hi
  · have hi4 : 4 ≤ i.val := by omega
    simpa using hhigh i hi4

theorem pow_two_pow_ne_one_of_order_three {M : Type*} [Monoid M] {g : M}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (k : ℕ) : g ^ 2 ^ k ≠ 1 := by
  intro h
  have h3 : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hdvd : 3 ∣ 2 ^ k := by
    rw [← h3]
    exact orderOf_dvd_of_pow_eq_one h
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

theorem comm_L1_T (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ⁅S126.Li L F.V1, T⁆ = S126.Li L F.V1 := by
  set H : Subgroup G := S126.Li L F.V1 with hHdef
  set N : Subgroup G := ⁅H, T⁆ with hN
  have hTL1 : T ≤ Subgroup.normalizer (H : Set G) := by
    rw [hHdef]
    exact S126L19b.T_le_normalizer_L1 h1222 hH
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hNle : N ≤ H := Subgroup.le_normalizer_iff_commutator_le_left.1 hTL1
  have hNnormal : (N.subgroupOf H).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    rw [hN]
    exact Subgroup.normalizer_commutator_ge_left H T
  obtain ⟨t₁, ⟨ht₁T, -⟩, ht₁act⟩ := S126T2.exists_TL_of_Q8 F hH
    (swap (0 : Fin 8) 1 * swap 4 5) tau_mem_Q8
  have ht₁V : t₁ ∈ Subgroup.normalizer (V : Set G) := hTV ht₁T
  have hgen : H ≤ N := by
    have hclosure : H = Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} := by
      rw [hHdef]
      exact L1_eq_closure_three h1222 F hH
    rw [hclosure]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxH, k, hxk⟩
    have hxLi : x ∈ S126.Li L F.V1 := by simpa [hHdef] using hxH
    have hxL : x ∈ L := S126L19b.L1_le_L F hxLi
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1 hxL
    have hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G) := S126L19b.L1_le_normalizer F hxLi
    set σ : ↥(alternatingGroup (Fin 8)) := S126L19a.psi F hH ⟨x, hxL⟩ with hσdef
    have hσact : ActsAs F x (σ : Perm (Fin 8)) := S126L19a.actsAs_psi F hH ⟨x, hxL⟩
    have hσ3x : x ^ 3 = 1 :=
      S126L19b.pow_three_of_mem h1222 F hH hxL hx1 (Odd.pow (by decide : Odd 3)) hxk
    have hσ3 : (σ : Perm (Fin 8)) ^ 3 = 1 :=
      S126P.pow_eq_one_of_actsAs hσact hxV hσ3x
    have hσb : ∀ i : Fin 8, (i.val < 4 ↔ ((σ : Perm (Fin 8)) i).val < 4) :=
      blocks_of_cube_one (S126L19a.blocks_of_mem_V1 F hx1 hσact) hσ3
    have hσfin : ((swap (0 : Fin 8) 1 * swap 4 5) * (σ : Perm (Fin 8)) *
        (swap (0 : Fin 8) 1 * swap 4 5)⁻¹ * (σ : Perm (Fin 8))) ^ 2 = 1 :=
      tau_conj_mul_sq hσb hσ3
    set c : G := t₁ * x * t₁⁻¹ * x with hcdef
    have hconjH : t₁ * x * t₁⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (hTL1 ht₁T) x).1 hxH
    have hcH : c ∈ H := by
      rw [hcdef]
      exact H.mul_mem hconjH hxH
    have hcLi : c ∈ S126.Li L F.V1 := by simpa [hHdef] using hcH
    have hcL : c ∈ L := S126L19b.L1_le_L F hcLi
    have hcV : c ∈ Subgroup.normalizer (V : Set G) := by
      rw [hcdef]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₁V hxV)
        (Subgroup.inv_mem _ ht₁V)) hxV
    have hcact : ActsAs F c ((swap (0 : Fin 8) 1 * swap 4 5) * (σ : Perm (Fin 8)) *
        (swap (0 : Fin 8) 1 * swap 4 5)⁻¹ * (σ : Perm (Fin 8))) := by
      rw [hcdef]
      exact ((ht₁act.mul hσact hxV).mul ht₁act.inv (Subgroup.inv_mem _ ht₁V)).mul hσact hxV
    have hc2act : ActsAs F (c ^ 2) 1 := by
      have h := hcact.pow hcV 2
      rw [hσfin] at h
      exact h
    have hc2C : c ^ 2 ∈ Subgroup.centralizer (V : Set G) :=
      S126L1b.mem_centralizer_of_mem_L F (L.pow_mem hcL 2) (Subgroup.pow_mem _ hcV 2) hc2act
    obtain ⟨m, hm⟩ := S126T2.isPGroup_CL h1222 hH
      ⟨c ^ 2, Subgroup.mem_inf.2 ⟨L.pow_mem hcL 2, hc2C⟩⟩
    have hc2pow : (c ^ 2) ^ 2 ^ m = 1 := by
      have h := congrArg (fun z : ↥(L ⊓ Subgroup.centralizer (V : Set G)) => ((z : G))) hm
      simpa using h
    have hc_pow : c ^ 2 ^ (m + 1) = 1 := by
      rw [show 2 ^ (m + 1) = 2 * 2 ^ m by ring, pow_mul, hc2pow]
    let Nsub : Subgroup ↥H := N.subgroupOf H
    haveI hNn : Nsub.Normal := hNnormal
    let Q := ↥H ⧸ Nsub
    let φ : ↥H →* Q := QuotientGroup.mk' Nsub
    let xH : ↥H := ⟨x, hxH⟩
    let q : Q := φ xH
    have hq_odd : Odd (orderOf q) := by
      have hq3 : q ^ 3 ^ k = 1 := by
        have hx3' : xH ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hxk)
        calc q ^ 3 ^ k = φ (xH ^ (3 ^ k)) := by
              change (φ xH) ^ 3 ^ k = φ (xH ^ (3 ^ k))
              rw [map_pow]
          _ = φ 1 := by rw [hx3']
          _ = 1 := map_one φ
      exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hq3)
    have hq2 : q ^ 2 = φ (⟨c, hcH⟩ : ↥H) := by
      have hquot : φ (xH ^ 2) = φ (⟨c, hcH⟩ : ↥H) := by
        change QuotientGroup.mk' Nsub (xH ^ 2) = QuotientGroup.mk' Nsub (⟨c, hcH⟩ : ↥H)
        rw [QuotientGroup.mk'_eq_mk']
        let k' : G := t₁ * x * t₁⁻¹ * x⁻¹
        have hk' : k' ∈ N := by
          rw [hN, Subgroup.commutator_comm]
          simpa [k', commutatorElement_def] using Subgroup.commutator_mem_commutator ht₁T hxH
        let kH : ↥H := ⟨k', hNle hk'⟩
        have hkH : kH ∈ Nsub := Subgroup.mem_subgroupOf.2 hk'
        let zH : ↥H := xH⁻¹ * (xH⁻¹ * kH * xH) * xH
        have hz1 : xH⁻¹ * kH * (xH⁻¹)⁻¹ ∈ Nsub := hNn.conj_mem kH hkH xH⁻¹
        have hz2 : xH⁻¹ * (xH⁻¹ * kH * (xH⁻¹)⁻¹) * (xH⁻¹)⁻¹ ∈ Nsub :=
          hNn.conj_mem _ hz1 xH⁻¹
        have hzH : zH ∈ Nsub := by
          simpa [zH] using hz2
        refine ⟨zH, hzH, ?_⟩
        apply Subtype.ext
        simp only [zH, kH, k', xH, hcdef, Subgroup.coe_mul, Subgroup.coe_pow,
          Subgroup.coe_inv, Subtype.coe_mk]
        group
      calc q ^ 2 = φ (xH ^ 2) := by
            change (φ xH) ^ 2 = φ (xH ^ 2)
            rw [map_pow]
        _ = φ (⟨c, hcH⟩ : ↥H) := hquot
    have hq2pow : q ^ 2 ^ (m + 2) = 1 := by
      have hcHpow : (⟨c, hcH⟩ : ↥H) ^ 2 ^ (m + 1) = 1 := by
        apply Subtype.ext
        simpa using hc_pow
      calc q ^ 2 ^ (m + 2) = (q ^ 2) ^ 2 ^ (m + 1) := by
            rw [show 2 ^ (m + 2) = 2 * 2 ^ (m + 1) by ring, pow_mul]
        _ = (φ (⟨c, hcH⟩ : ↥H)) ^ 2 ^ (m + 1) := by rw [hq2]
        _ = φ ((⟨c, hcH⟩ : ↥H) ^ 2 ^ (m + 1)) := by rw [map_pow]
        _ = φ 1 := by rw [hcHpow]
        _ = 1 := map_one φ
    have hq1 : q = 1 := by
      have hcop : Nat.Coprime (orderOf q) (2 ^ (m + 2)) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hq_odd)
      have hd : orderOf q ∣ 1 * 2 ^ (m + 2) := by
        simpa using orderOf_dvd_of_pow_eq_one hq2pow
      have hd1 : orderOf q ∣ 1 := (Nat.Coprime.dvd_mul_right (m := 1) hcop).1 hd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
    have hxNsub : xH ∈ Nsub := by
      have hqone : (xH : Q) = 1 := by
        change q = 1
        exact hq1
      exact (QuotientGroup.eq_one_iff xH).1 hqone
    exact Subgroup.mem_subgroupOf.1 hxNsub
  exact le_antisymm hNle hgen

theorem exists_e9_frame (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∃ x ∈ S126.Li L F.V1, ∃ y ∈ S126.Li L F.V1, ∃ t₁ ∈ T, ∃ t₂ ∈ T,
      t₁ * x * t₁⁻¹ * x ∈ Subgroup.centralizer (V : Set G) ∧
      t₂ * x * t₂⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
      t₂ * y * t₂⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
      (∀ k : ℕ, (x ^ 2) ^ (2 ^ k) ≠ 1) ∧ (∀ k : ℕ, (y * x) ^ (2 ^ k) ≠ 1) ∧
      (∀ k : ℕ, (y * x⁻¹) ^ (2 ^ k) ≠ 1) := by
  obtain ⟨x, hxL1, hxV, hxact⟩ :=
    S126L1b.exists_mem_L1 F S126E.c1_mem S126E.c1_pow_three S126E.c1_block
  obtain ⟨y, hyL1, hyV, hyact⟩ :=
    S126L1b.exists_mem_L1 F S126E.c2_mem S126E.c2_pow_three S126E.c2_block
  obtain ⟨t₁, ⟨ht₁T, ht₁L⟩, ht₁act⟩ := S126T2.exists_TL_of_Q8 F hH
    (swap (0 : Fin 8) 1 * swap (4 : Fin 8) 5) tau_mem_Q8
  obtain ⟨t₂, ⟨ht₂T, ht₂L⟩, ht₂act⟩ := S126T2.exists_TL_of_Q8 F hH S126L1c.bsw
    ⟨S126L1c.bsw_mem, S126L1c.bsw_mem_A8⟩
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have ht₁V : t₁ ∈ Subgroup.normalizer (V : Set G) := hTV ht₁T
  have ht₂V : t₂ ∈ Subgroup.normalizer (V : Set G) := hTV ht₂T
  have hxL : x ∈ L := S126L19b.L1_le_L F hxL1
  have hyL : y ∈ L := S126L19b.L1_le_L F hyL1
  refine ⟨x, hxL1, y, hyL1, t₁, ht₁T, t₂, ht₂T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmemL : t₁ * x * t₁⁻¹ * x ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ht₁L hxL) (L.inv_mem ht₁L)) hxL
    have hmemV : t₁ * x * t₁⁻¹ * x ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₁V hxV)
        (Subgroup.inv_mem _ ht₁V)) hxV
    have hact : ActsAs F (t₁ * x * t₁⁻¹ * x) 1 := by
      have h := ((ht₁act.mul hxact hxV).mul ht₁act.inv
        (Subgroup.inv_mem _ ht₁V)).mul hxact hxV
      rwa [show (swap (0 : Fin 8) 1 * swap (4 : Fin 8) 5) * (S126E.c1 : Perm (Fin 8)) *
          (swap (0 : Fin 8) 1 * swap (4 : Fin 8) 5)⁻¹ * S126E.c1 = 1 by decide] at h
    exact S126L1b.mem_centralizer_of_mem_L F hmemL hmemV hact
  · have hmemL : t₂ * x * t₂⁻¹ * y⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ht₂L hxL) (L.inv_mem ht₂L)) (L.inv_mem hyL)
    have hmemV : t₂ * x * t₂⁻¹ * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₂V hxV)
        (Subgroup.inv_mem _ ht₂V)) (Subgroup.inv_mem _ hyV)
    have hact : ActsAs F (t₂ * x * t₂⁻¹ * y⁻¹) 1 := by
      have h := ((ht₂act.mul hxact hxV).mul ht₂act.inv
        (Subgroup.inv_mem _ ht₂V)).mul hyact.inv (Subgroup.inv_mem _ hyV)
      rwa [show S126L1c.bsw * (S126E.c1 : Perm (Fin 8)) * S126L1c.bsw⁻¹ * S126E.c2⁻¹ = 1
        by decide] at h
    exact S126L1b.mem_centralizer_of_mem_L F hmemL hmemV hact
  · have hmemL : t₂ * y * t₂⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ht₂L hyL) (L.inv_mem ht₂L)) (L.inv_mem hxL)
    have hmemV : t₂ * y * t₂⁻¹ * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₂V hyV)
        (Subgroup.inv_mem _ ht₂V)) (Subgroup.inv_mem _ hxV)
    have hact : ActsAs F (t₂ * y * t₂⁻¹ * x⁻¹) 1 := by
      have h := ((ht₂act.mul hyact hyV).mul ht₂act.inv
        (Subgroup.inv_mem _ ht₂V)).mul hxact.inv (Subgroup.inv_mem _ hxV)
      rwa [show S126L1c.bsw * (S126E.c2 : Perm (Fin 8)) * S126L1c.bsw⁻¹ * S126E.c1⁻¹ = 1
        by decide] at h
    exact S126L1b.mem_centralizer_of_mem_L F hmemL hmemV hact
  · intro k hk
    have hx2 : x ^ 2 ^ (k + 1) = 1 := by
      rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
      exact (pow_mul x 2 (2 ^ k)).trans hk
    have h1 : (S126E.c1 : Perm (Fin 8)) ^ 2 ^ (k + 1) = 1 :=
      S126P.pow_eq_one_of_actsAs hxact hxV hx2
    exact pow_two_pow_ne_one_of_order_three S126E.c1_pow_three (by decide) (k + 1) h1
  · intro k hk
    have h1 : (S126E.c2 * S126E.c1 : Perm (Fin 8)) ^ 2 ^ k = 1 :=
      S126P.pow_eq_one_of_actsAs (hyact.mul hxact hxV)
        (Subgroup.mul_mem _ hyV hxV) hk
    exact pow_two_pow_ne_one_of_order_three
      (by decide : (S126E.c2 * S126E.c1 : Perm (Fin 8)) ^ 3 = 1) (by decide) k h1
  · intro k hk
    have h1 : (S126E.c2 * S126E.c1⁻¹ : Perm (Fin 8)) ^ 2 ^ k = 1 :=
      S126P.pow_eq_one_of_actsAs (hyact.mul hxact.inv (Subgroup.inv_mem _ hxV))
        (Subgroup.mul_mem _ hyV (Subgroup.inv_mem _ hxV)) hk
    exact pow_two_pow_ne_one_of_order_three
      (by decide : (S126E.c2 * S126E.c1⁻¹ : Perm (Fin 8)) ^ 3 = 1) (by decide) k h1

end CFSG.Quasithin.H13.P31A

module

public import CFSG.Quasithin.Background.Asc81cPfCoord
public import Certificates.Certificate7224
public import CFSG.Quasithin.Background.Asc81cPfQuot

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native Check

section Arrays

theorem rep_powA {N : ℕ} {a : Array ℕ} {σ : Equiv.Perm (Fin N)} (h : Rep N a σ) (k : ℕ) :
    Rep N (powA N a k) (σ ^ k) := by
  induction k with
  | zero => simpa [powA] using (rep_idA (n := N))
  | succ k ih =>
    rw [pow_succ']
    exact rep_compA h ih

theorem ord3A_iff {N : ℕ} {a : Array ℕ} {σ : Equiv.Perm (Fin N)} (h : Rep N a σ) :
    ord3A N a = true ↔ σ ^ 3 = 1 :=
  eqA_iff (rep_powA h 3) rep_idA

theorem isInvolA_iff {N : ℕ} {a : Array ℕ} {σ : Equiv.Perm (Fin N)} (h : Rep N a σ) :
    isInvolA N a = true ↔ σ * σ = 1 ∧ σ ≠ 1 := by
  have h1 := eqA_iff (rep_compA h h) (rep_idA (n := N))
  have h2 := eqA_iff h (rep_idA (n := N))
  unfold isInvolA
  constructor
  · intro hi
    rw [Bool.and_eq_true] at hi
    refine ⟨h1.1 hi.1, fun he => ?_⟩
    have := h2.2 he
    simp [this] at hi
  · rintro ⟨ha, hb⟩
    rw [Bool.and_eq_true]
    refine ⟨h1.2 ha, ?_⟩
    cases hc : eqA N a (idA N)
    · rfl
    · exact absurd (h2.1 hc) hb

theorem rep_eq_iff {N : ℕ} {a : Array ℕ} {σ : Equiv.Perm (Fin N)} (h : Rep N a σ) {i : ℕ}
    (hi : i < N) : a[i]! = i ↔ σ ⟨i, hi⟩ = ⟨i, hi⟩ := by
  rw [h ⟨i, hi⟩]
  exact ⟨fun h' => Fin.ext h', fun h' => by rw [h']⟩

end Arrays

variable {W : Type*} [CommGroup W] [Finite W]

section Pick

theorem exists_mem_ne {Γ : Type*} [Group Γ] {S : Subgroup Γ} (h : 1 < Nat.card S) (a : Γ) :
    ∃ c ∈ S, c ≠ a := by
  by_contra hall
  push Not at hall
  have hsub : (S : Set Γ) ⊆ {a} := fun c hc => hall c hc
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h1
  have : Nat.card (S : Set Γ) = Nat.card S := rfl
  omega

theorem exists_mem_ne_ne {Γ : Type*} [Group Γ] {S : Subgroup Γ} (h : 2 < Nat.card S) (a b : Γ) :
    ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
  by_contra hall
  push Not at hall
  have hsub : (S : Set Γ) ⊆ {a, b} := fun c hc => by
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hall c hc hca)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le a ({b} : Set Γ)
  rw [Set.ncard_singleton] at h2
  rw [← Nat.card_coe_set_eq] at h1
  have : Nat.card (S : Set Γ) = Nat.card S := rfl
  omega

end Pick

section Frame

theorem nat_eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b :=
  Nat.eq_of_testBit_eq fun k => by
    have := congrArg (fun x => x.testBit k) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all

variable {Q : Type*} [CommGroup Q] [Finite Q]

omit [Finite Q] in
theorem inv_eq_self_of_sq (hQ : ∀ q : Q, q ^ 2 = 1) (q : Q) : q⁻¹ = q := by
  have h := hQ q
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

omit [Finite Q] in
theorem odd_card_zpowers_of_pow_three {ξ : MulAut Q} (hξ : ξ ^ 3 = 1) :
    Odd (Nat.card (Subgroup.zpowers ξ)) := by
  rw [Nat.card_zpowers]
  have h := orderOf_dvd_of_pow_eq_one hξ
  rcases (Nat.dvd_prime Nat.prime_three).1 h with h1 | h1 <;> rw [h1] <;> decide

theorem trace_eq_one (hQ : ∀ q : Q, q ^ 2 = 1) {ξ : MulAut Q} (hξ : ξ ^ 3 = 1) {v : Q}
    (hv : v ∈ commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ)) : v * ξ v * ξ (ξ v) = 1 := by
  have hodd := odd_card_zpowers_of_pow_three hξ
  have hξm : ξ ∈ Subgroup.zpowers ξ := Subgroup.mem_zpowers ξ
  have h1 : ξ (ξ (ξ v)) = v := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hξ, MulAut.one_apply]
  have hs : v * ξ v * ξ (ξ v) ∈ fixV (Subgroup.zpowers ξ) ⊓ commSub ⊤ (Subgroup.zpowers ξ) := by
    refine ⟨mem_fixV_zpowers ?_, ?_⟩
    · rw [map_mul, map_mul, h1]
      simp only [mul_comm, mul_left_comm]
    · have h2 := commSub_stable' hξm hv
      have h3 := commSub_stable' hξm h2
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hv h2) h3
  rwa [fixV_inf_commSub_eq_bot' hQ hodd, Subgroup.mem_bot] at hs

omit [Finite Q] in
theorem coordMap_two_pow {n : ℕ} (e : Fin n → Q) (k : Fin n) :
    coordMap e ⟨2 ^ (k : ℕ), Nat.pow_lt_pow_right (by norm_num) k.2⟩ = e k := by
  unfold coordMap
  simp only [Nat.testBit_two_pow]
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    have : ¬ ((k : ℕ) = b) := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

omit [Finite Q] in
theorem coordMap_two_pow' {n : ℕ} (e : Fin n → Q) (k : ℕ) (hk : k < n) :
    coordMap e ⟨2 ^ k, Nat.pow_lt_pow_right (by norm_num) hk⟩ = e ⟨k, hk⟩ :=
  coordMap_two_pow e ⟨k, hk⟩

omit [Finite Q] in
theorem coordMap_injective {n : ℕ} {e : Fin n → Q} (he : ∀ k, e k * e k = 1)
    (h1 : ∀ i, coordMap e i = 1 → i = ⟨0, Nat.two_pow_pos n⟩) :
    Function.Injective (coordMap e) := by
  intro i j hij
  have h := coordMap_xor he i j
  rw [hij, ← pow_two] at h
  have h2 : coordMap e (i ^^^ j) = 1 := by
    rw [h]
    have hsq : ∀ k, e k ^ 2 = 1 := fun k => by rw [pow_two]; exact he k
    unfold coordMap
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    split_ifs
    · exact hsq k
    · exact one_pow 2
  have h3 := congrArg Fin.val (h1 _ h2)
  rw [Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow i.2 j.2)] at h3
  exact Fin.ext (nat_eq_of_xor_eq_zero h3)

omit [Finite Q] in
theorem eq_one_of_mul_eq_one {A B : Subgroup Q} (hAB : B ⊓ A = ⊥) {a b : Q} (ha : a ∈ A)
    (hb : b ∈ B) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
  have h2 : a ∈ B ⊓ A := ⟨h1 ▸ B.inv_mem hb, ha⟩
  rw [hAB, Subgroup.mem_bot] at h2
  refine ⟨h2, ?_⟩
  rw [h2, one_mul] at h
  exact h

omit [Finite Q] in
theorem ite_mul_ite_eq_one (hQ' : ∀ q : Q, q⁻¹ = q) {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : b ≠ a) {p q : Bool} (h : (if p then a else 1) * (if q then b else 1) = 1) :
    p = false ∧ q = false := by
  cases p <;> cases q
  · exact ⟨rfl, rfl⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
    exact absurd h hb
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact absurd h ha
  · simp only [↓reduceIte] at h
    exact absurd (by rw [← hQ' a]; exact eq_inv_of_mul_eq_one_right h) hab

theorem fin16_eq_zero (i : Fin 16) (h0 : (i : ℕ).testBit 0 = false) (h1 : (i : ℕ).testBit 1 = false)
    (h2 : (i : ℕ).testBit 2 = false) (h3 : (i : ℕ).testBit 3 = false) : i = ⟨0, by norm_num⟩ := by
  revert h0 h1 h2 h3
  revert i
  decide

theorem fin8_eq_zero (i : Fin 8) (h0 : (i : ℕ).testBit 0 = false) (h1 : (i : ℕ).testBit 1 = false)
    (h2 : (i : ℕ).testBit 2 = false) : i = ⟨0, by norm_num⟩ := by
  revert h0 h1 h2
  revert i
  decide

variable (hQ : ∀ q : Q, q ^ 2 = 1) {ξ : MulAut Q} (hξ : ξ ^ 3 = 1)
include hQ hξ

theorem exists_pair (hA : 1 < Nat.card (commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ))) :
    ∃ e₀ ∈ commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ), e₀ ≠ 1 ∧ ξ e₀ ≠ 1 ∧ ξ e₀ ≠ e₀ ∧
      ξ e₀ ∈ commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ) ∧ ξ (ξ e₀) = e₀ * ξ e₀ := by
  have hodd := odd_card_zpowers_of_pow_three hξ
  obtain ⟨e₀, he₀, he₀1⟩ := exists_mem_ne hA 1
  have hξm : ξ ∈ Subgroup.zpowers ξ := Subgroup.mem_zpowers ξ
  have he₁ := commSub_stable' hξm he₀
  refine ⟨e₀, he₀, he₀1, fun h => he₀1 (ξ.injective (h.trans (map_one ξ).symm)), fun h => ?_, he₁,
    ?_⟩
  · have h1 : e₀ ∈ fixV (Subgroup.zpowers ξ) ⊓ commSub ⊤ (Subgroup.zpowers ξ) :=
      ⟨mem_fixV_zpowers h, he₀⟩
    rw [fixV_inf_commSub_eq_bot' hQ hodd, Subgroup.mem_bot] at h1
    exact he₀1 h1
  · have ht := trace_eq_one hQ hξ he₀
    have h2 : ξ (ξ e₀) = (e₀ * ξ e₀)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [h2, inv_eq_self_of_sq hQ]


theorem exists_frame4 (hcard : Nat.card Q = 16) (hB : Nat.card (fixV (Subgroup.zpowers ξ)) = 4) :
    ∃ φ : Fin (2 ^ 4) → Q, ∃ hφ : Function.Bijective φ, (∀ i j, φ (i ^^^ j) = φ i * φ j) ∧
      Rep (2 ^ 4) (x0 4) (permOf hφ ξ) := by
  have hodd := odd_card_zpowers_of_pow_three hξ
  have hdec := card_fixV_mul_card_commSub hQ hodd
  rw [hB, hcard] at hdec
  have hbot := fixV_inf_commSub_eq_bot' hQ hodd
  have hQ' := inv_eq_self_of_sq hQ
  obtain ⟨e₀, he₀, h01, h11, h10, he₁, hξe₁⟩ := exists_pair hQ hξ (by omega)
  obtain ⟨e₂, he₂, he₂1⟩ := exists_mem_ne (by omega : 1 < Nat.card (fixV (Subgroup.zpowers ξ))) 1
  obtain ⟨e₃, he₃, he₃1, he₃2⟩ :=
    exists_mem_ne_ne (by omega : 2 < Nat.card (fixV (Subgroup.zpowers ξ))) 1 e₂
  set e : Fin 4 → Q := ![e₀, ξ e₀, e₂, e₃] with hedef
  have he : ∀ k, e k * e k = 1 := fun k => by rw [← pow_two]; exact hQ _
  have hφ1 : ∀ i, coordMap e i = 1 → i = ⟨0, Nat.two_pow_pos 4⟩ := by
    intro i hi
    unfold coordMap at hi
    rw [Fin.prod_univ_four] at hi
    change (if (i : ℕ).testBit 0 then e₀ else 1) * (if (i : ℕ).testBit 1 then ξ e₀ else 1) *
      (if (i : ℕ).testBit 2 then e₂ else 1) * (if (i : ℕ).testBit 3 then e₃ else 1) = 1 at hi
    have hA : (if (i : ℕ).testBit 0 then e₀ else 1) * (if (i : ℕ).testBit 1 then ξ e₀ else 1) ∈
        commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ) := by
      refine Subgroup.mul_mem _ ?_ ?_ <;> split_ifs <;>
        first | assumption | exact Subgroup.one_mem _
    have hB' : (if (i : ℕ).testBit 2 then e₂ else 1) * (if (i : ℕ).testBit 3 then e₃ else 1) ∈
        fixV (Subgroup.zpowers ξ) := by
      refine Subgroup.mul_mem _ ?_ ?_ <;> split_ifs <;>
        first | assumption | exact Subgroup.one_mem _
    obtain ⟨hα, hβ⟩ := eq_one_of_mul_eq_one hbot hA hB' (by
      rw [← mul_assoc]
      exact hi)
    obtain ⟨b0, b1⟩ := ite_mul_ite_eq_one hQ' h01 h11 h10 hα
    obtain ⟨b2, b3⟩ := ite_mul_ite_eq_one hQ' he₂1 he₃1 he₃2 hβ
    exact fin16_eq_zero i b0 b1 b2 b3
  have hinj := coordMap_injective he hφ1
  have hφ : Function.Bijective (coordMap e) :=
    hinj.bijective_of_nat_card_le
      (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hxor := coordMap_xor he
  refine ⟨coordMap e, hφ, hxor, ?_⟩
  refine rep_linA _ (permOf_xor hφ hxor ξ) _ fun k hk => ?_
  have hfix : ∀ b ∈ fixV (Subgroup.zpowers ξ), ξ b = b := fun b hb => hb ξ (Subgroup.mem_zpowers ξ)
  interval_cases k
  · have : permOf hφ ξ ⟨2 ^ 0, by norm_num⟩ = ⟨2 ^ 1, by norm_num⟩ := by
      rw [permOf_eq_iff, coordMap_two_pow' e 0 (by norm_num), coordMap_two_pow' e 1 (by norm_num)]
      rfl
    rw [this]
    rfl
  · have : permOf hφ ξ ⟨2 ^ 1, by norm_num⟩ = ⟨2 ^ 0, by norm_num⟩ ^^^ ⟨2 ^ 1, by norm_num⟩ := by
      rw [permOf_eq_iff, hxor, coordMap_two_pow' e 0 (by norm_num),
        coordMap_two_pow' e 1 (by norm_num)]
      exact hξe₁
    rw [this]
    rfl
  · have : permOf hφ ξ ⟨2 ^ 2, by norm_num⟩ = ⟨2 ^ 2, by norm_num⟩ := by
      rw [permOf_eq_iff, coordMap_two_pow' e 2 (by norm_num)]
      exact hfix _ he₂
    rw [this]
    rfl
  · have : permOf hφ ξ ⟨2 ^ 3, by norm_num⟩ = ⟨2 ^ 3, by norm_num⟩ := by
      rw [permOf_eq_iff, coordMap_two_pow' e 3 (by norm_num)]
      exact hfix _ he₃
    rw [this]
    rfl

theorem exists_frame3 (hcard : Nat.card Q = 8) (hB : Nat.card (fixV (Subgroup.zpowers ξ)) = 2) :
    ∃ φ : Fin (2 ^ 3) → Q, ∃ hφ : Function.Bijective φ, (∀ i j, φ (i ^^^ j) = φ i * φ j) ∧
      Rep (2 ^ 3) (x0 3) (permOf hφ ξ) := by
  have hodd := odd_card_zpowers_of_pow_three hξ
  have hdec := card_fixV_mul_card_commSub hQ hodd
  rw [hB, hcard] at hdec
  have hbot := fixV_inf_commSub_eq_bot' hQ hodd
  have hQ' := inv_eq_self_of_sq hQ
  obtain ⟨e₀, he₀, h01, h11, h10, he₁, hξe₁⟩ := exists_pair hQ hξ (by omega)
  obtain ⟨e₂, he₂, he₂1⟩ := exists_mem_ne (by omega : 1 < Nat.card (fixV (Subgroup.zpowers ξ))) 1
  set e : Fin 3 → Q := ![e₀, ξ e₀, e₂] with hedef
  have he : ∀ k, e k * e k = 1 := fun k => by rw [← pow_two]; exact hQ _
  have hφ1 : ∀ i, coordMap e i = 1 → i = ⟨0, Nat.two_pow_pos 3⟩ := by
    intro i hi
    unfold coordMap at hi
    rw [Fin.prod_univ_three] at hi
    change (if (i : ℕ).testBit 0 then e₀ else 1) * (if (i : ℕ).testBit 1 then ξ e₀ else 1) *
      (if (i : ℕ).testBit 2 then e₂ else 1) = 1 at hi
    have hA : (if (i : ℕ).testBit 0 then e₀ else 1) * (if (i : ℕ).testBit 1 then ξ e₀ else 1) ∈
        commSub (⊤ : Subgroup Q) (Subgroup.zpowers ξ) := by
      refine Subgroup.mul_mem _ ?_ ?_ <;> split_ifs <;>
        first | assumption | exact Subgroup.one_mem _
    have hB' : (if (i : ℕ).testBit 2 then e₂ else 1) ∈ fixV (Subgroup.zpowers ξ) := by
      split_ifs <;> first | assumption | exact Subgroup.one_mem _
    obtain ⟨hα, hβ⟩ := eq_one_of_mul_eq_one hbot hA hB' hi
    obtain ⟨b0, b1⟩ := ite_mul_ite_eq_one hQ' h01 h11 h10 hα
    have b2 : (i : ℕ).testBit 2 = false := by
      by_contra hb
      simp only [Bool.not_eq_false] at hb
      simp only [hb, ↓reduceIte] at hβ
      exact he₂1 hβ
    exact fin8_eq_zero i b0 b1 b2
  have hinj := coordMap_injective he hφ1
  have hφ : Function.Bijective (coordMap e) :=
    hinj.bijective_of_nat_card_le
      (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hxor := coordMap_xor he
  refine ⟨coordMap e, hφ, hxor, ?_⟩
  refine rep_linA _ (permOf_xor hφ hxor ξ) _ fun k hk => ?_
  have hfix : ∀ b ∈ fixV (Subgroup.zpowers ξ), ξ b = b := fun b hb => hb ξ (Subgroup.mem_zpowers ξ)
  interval_cases k
  · have : permOf hφ ξ ⟨2 ^ 0, by norm_num⟩ = ⟨2 ^ 1, by norm_num⟩ := by
      rw [permOf_eq_iff, coordMap_two_pow' e 0 (by norm_num), coordMap_two_pow' e 1 (by norm_num)]
      rfl
    rw [this]
    rfl
  · have : permOf hφ ξ ⟨2 ^ 1, by norm_num⟩ = ⟨2 ^ 0, by norm_num⟩ ^^^ ⟨2 ^ 1, by norm_num⟩ := by
      rw [permOf_eq_iff, hxor, coordMap_two_pow' e 0 (by norm_num),
        coordMap_two_pow' e 1 (by norm_num)]
      exact hξe₁
    rw [this]
    rfl
  · have : permOf hφ ξ ⟨2 ^ 2, by norm_num⟩ = ⟨2 ^ 2, by norm_num⟩ := by
      rw [permOf_eq_iff, coordMap_two_pow' e 2 (by norm_num)]
      exact hfix _ he₂
    rw [this]
    rfl

end Frame

theorem c7224_check4 : check4 = true :=
  Certificates.certificate7224.1

theorem c7224_check3 : check3 = true :=
  Certificates.certificate7224.2

section Pre

theorem ord3V_eq_true {n : ℕ} {c : List ℕ} {σ : Equiv.Perm (Fin (2 ^ n))}
    (hσ : ∀ i j, σ (i ^^^ j) = σ i ^^^ σ j)
    (hc : ∀ k (hk : k < n), c.getD k 0 = (σ ⟨2 ^ k, Nat.pow_lt_pow_right (by norm_num) hk⟩ : ℕ))
    (h3 : σ ^ 3 = 1) : ord3V n c = true := by
  unfold ord3V
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hb : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hk
  have e1 := linV_eq σ hσ c hc ⟨2 ^ k, hb⟩
  have e2 := linV_eq σ hσ c hc (σ ⟨2 ^ k, hb⟩)
  have e3 := linV_eq σ hσ c hc (σ (σ ⟨2 ^ k, hb⟩))
  simp only at e1
  rw [e1, e2, e3]
  have h4 : σ (σ (σ ⟨2 ^ k, hb⟩)) = ⟨2 ^ k, hb⟩ := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_three', h3, Equiv.Perm.one_apply]
  rw [h4]
  exact beq_self_eq_true _

theorem fixCount_eq {N : ℕ} {a : Array ℕ} {σ : Equiv.Perm (Fin N)} (h : Rep N a σ) :
    fixCount N a = Fintype.card {i : Fin N // σ i = i} := by
  classical
  rw [Fintype.card_subtype, Fin.univ_def]
  unfold fixCount
  simp only [Finset.card_def, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card]
  congr 1
  refine List.filter_congr fun i _ => ?_
  rw [h i]
  by_cases hi : σ i = i
  · simp [hi]
  · have : (σ i : ℕ) ≠ i := fun h' => hi (Fin.ext h')
    simp [hi, this]

theorem meetTriv_eq_true {N : ℕ} {a b : Array ℕ} {σ τ : Equiv.Perm (Fin N)} (ha : Rep N a σ)
    (hb : Rep N b τ) (h : ∀ i, σ i = i → τ i = i → (i : ℕ) = 0) : meetTriv N a b = true := by
  unfold meetTriv
  rw [allLt_iff]
  intro i hi
  by_cases h1 : a[i]! = i
  · by_cases h2 : b[i]! = i
    · have h3 : i = 0 := h ⟨i, hi⟩ ((rep_eq_iff ha hi).1 h1) ((rep_eq_iff hb hi).1 h2)
      simp [h3]
    · simp [h2]
  · simp [h1]

end Pre

section Crit

omit [Finite W] in
theorem mem_critSub_of_mem_sumL {H : Subgroup (MulAut W)} {n : ℕ}
    (hQ : ∀ q : W ⧸ fixV H, q ^ 2 = 1) {φ : Fin (2 ^ n) → W ⧸ fixV H}
    (hφ : Function.Bijective φ) (hxor : ∀ i j, φ (i ^^^ j) = φ i * φ j) {g₁ g₂ h : H}
    {t₁ t₂ u : Array ℕ} (h₁ : Rep (2 ^ n) t₁ (permOf hφ (quoAct H g₁)))
    (h₂ : Rep (2 ^ n) t₂ (permOf hφ (quoAct H g₂))) (hu : Rep (2 ^ n) u (permOf hφ (quoAct H h)))
    {p : ℕ} (hp : p ∈ sumL (2 ^ n) (fixL (2 ^ n) t₁ t₂) u) :
    ∃ hp' : p < 2 ^ n, φ ⟨p, hp'⟩ ∈ critSub H g₁ g₂ h := by
  simp only [sumL, fixL, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨d, ⟨hd, hd1, hd2⟩, i, hi, rfl⟩ := hp
  have hd1' := (rep_eq_iff h₁ hd).1 hd1
  have hd2' := (rep_eq_iff h₂ hd).1 hd2
  have huj : u[i]! = (permOf hφ (quoAct H h) ⟨i, hi⟩ : ℕ) := hu ⟨i, hi⟩
  have hlt : d ^^^ i ^^^ u[i]! < 2 ^ n := by
    rw [huj]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hd hi) (Fin.isLt _)
  refine ⟨hlt, ?_⟩
  have hfin : (⟨d ^^^ i ^^^ u[i]!, hlt⟩ : Fin (2 ^ n)) =
      ⟨d, hd⟩ ^^^ ⟨i, hi⟩ ^^^ permOf hφ (quoAct H h) ⟨i, hi⟩ := by
    apply Fin.ext
    rw [Fin.xor_val, Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hd hi), ← huj,
      Nat.mod_eq_of_lt hlt]
  rw [hfin, hxor, hxor]
  refine ⟨φ ⟨d, hd⟩, ?_, ?_, φ ⟨i, hi⟩, ?_⟩
  · rw [← coordMap_permOf hφ, hd1']
  · rw [← coordMap_permOf hφ, hd2']
  · rw [coordMap_permOf hφ, mul_assoc, inv_eq_self_of_sq hQ]

theorem index_critSub_le {H : Subgroup (MulAut W)} {n : ℕ} (hn : n = 3 ∨ n = 4)
    (hQ : ∀ q : W ⧸ fixV H, q ^ 2 = 1) (hcard : Nat.card (W ⧸ fixV H) = 2 ^ n)
    {φ : Fin (2 ^ n) → W ⧸ fixV H} (hφ : Function.Bijective φ)
    (hxor : ∀ i j, φ (i ^^^ j) = φ i * φ j) {g₁ g₂ h : H} {t₁ t₂ u : Array ℕ}
    (h₁ : Rep (2 ^ n) t₁ (permOf hφ (quoAct H g₁))) (h₂ : Rep (2 ^ n) t₂ (permOf hφ (quoAct H g₂)))
    (hu : Rep (2 ^ n) u (permOf hφ (quoAct H h)))
    (hb : bigEnough n (sumL (2 ^ n) (fixL (2 ^ n) t₁ t₂) u) = true) :
    (critSub H g₁ g₂ h).index ≤ 4 := by
  have hmem := fun p (hp : p ∈ sumL (2 ^ n) (fixL (2 ^ n) t₁ t₂) u) =>
    mem_critSub_of_mem_sumL hQ hφ hxor h₁ h₂ hu hp
  have hφ0 : φ ⟨0, Nat.two_pow_pos n⟩ = 1 := by
    have h := hxor ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩
    have h0 : (⟨0, Nat.two_pow_pos n⟩ : Fin (2 ^ n)) ^^^ ⟨0, Nat.two_pow_pos n⟩ =
        ⟨0, Nat.two_pow_pos n⟩ := Fin.ext (by simp)
    rw [h0] at h
    exact (mul_eq_left.1 h.symm)
  have hne : ∀ p (hp : p < 2 ^ n), p ≠ 0 → φ ⟨p, hp⟩ ≠ 1 := fun p hp hp0 h => by
    rw [← hφ0] at h
    exact hp0 (congrArg Fin.val (hφ.1 h))
  have hT : Nat.card (critSub H g₁ g₂ h) * (critSub H g₁ g₂ h).index = 2 ^ n := by
    rw [Subgroup.card_mul_index, hcard]
  unfold bigEnough at hb
  split_ifs at hb with h3
  ·
    obtain ⟨p, hp, hp0⟩ := List.any_eq_true.1 hb
    obtain ⟨hp', hpm⟩ := hmem p hp
    have hp0' : p ≠ 0 := by simpa using hp0
    have h2 : 2 ≤ Nat.card (critSub H g₁ g₂ h) := by
      have := Nat.card_le_card_of_injective (fun b : Bool => if b then
        (⟨φ ⟨p, hp'⟩, hpm⟩ : critSub H g₁ g₂ h) else 1) (by
          intro b b' hbb
          cases b <;> cases b' <;> simp only [↓reduceIte] at hbb
          · rfl
          · exact absurd (congrArg Subtype.val hbb).symm (hne p hp' hp0')
          · exact absurd (congrArg Subtype.val hbb) (hne p hp' hp0')
          · rfl)
      simpa using this
    rw [h3, show (2 : ℕ) ^ 3 = 8 by norm_num] at hT
    nlinarith
  ·
    have h4 : n = 4 := by omega
    obtain ⟨p, hp, hpq⟩ := List.any_eq_true.1 hb
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpq
    obtain ⟨hp0, hq⟩ := hpq
    obtain ⟨q, hq, hq0, hqp⟩ := by simpa using List.any_eq_true.1 hq
    obtain ⟨hp', hpm⟩ := hmem p hp
    obtain ⟨hq', hqm⟩ := hmem q hq
    have hφp := hne p hp' hp0
    have hφq := hne q hq' hq0
    have hφpq : φ ⟨p, hp'⟩ ≠ φ ⟨q, hq'⟩ := fun h => hqp (congrArg Fin.val (hφ.1 h)).symm
    have hmul : φ ⟨p, hp'⟩ * φ ⟨q, hq'⟩ ∈ critSub H g₁ g₂ h := Subgroup.mul_mem _ hpm hqm
    let f : Fin 4 → critSub H g₁ g₂ h := ![1, ⟨φ ⟨p, hp'⟩, hpm⟩, ⟨φ ⟨q, hq'⟩, hqm⟩,
      ⟨φ ⟨p, hp'⟩ * φ ⟨q, hq'⟩, hmul⟩]
    have hf : Function.Injective f := by
      have hQ' := inv_eq_self_of_sq hQ
      have e1 : φ ⟨p, hp'⟩ * φ ⟨q, hq'⟩ ≠ 1 := fun h => hφpq (by
        have := eq_inv_of_mul_eq_one_left h
        rw [hQ'] at this
        exact this)
      have e2 : φ ⟨p, hp'⟩ * φ ⟨q, hq'⟩ ≠ φ ⟨p, hp'⟩ := fun h => hφq (mul_eq_left.1 h)
      have e3 : φ ⟨p, hp'⟩ * φ ⟨q, hq'⟩ ≠ φ ⟨q, hq'⟩ := fun h => hφp (mul_eq_right.1 h)
      intro i j hij
      have hv := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;>
        simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Subgroup.coe_one, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk]
          at hv ⊢ <;>
        first
        | rfl
        | exact absurd hv (by tauto)
    have h4c := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h4c
    rw [h4, show (2 : ℕ) ^ 4 = 16 by norm_num] at hT
    nlinarith

theorem false_of_critA (hW : ∀ w : W, w ^ 2 = 1) {G X H : Subgroup (MulAut W)} (hX : Hyp102 G X)
    (hX3 : Nat.card X = 3) (hHG : H ≤ G) (hinj : Function.Injective (quoAct H)) {n : ℕ}
    (hn : n = 3 ∨ n = 4) (hcard : Nat.card (W ⧸ fixV H) = 2 ^ n)
    {φ : Fin (2 ^ n) → W ⧸ fixV H} (hφ : Function.Bijective φ)
    (hxor : ∀ i j, φ (i ^^^ j) = φ i * φ j) {g₁ g₂ h : H} (hh : h ∈ Subgroup.closure {g₁, g₂})
    {t₁ t₂ u : Array ℕ} (h₁ : Rep (2 ^ n) t₁ (permOf hφ (quoAct H g₁)))
    (h₂ : Rep (2 ^ n) t₂ (permOf hφ (quoAct H g₂))) (hu : Rep (2 ^ n) u (permOf hφ (quoAct H h)))
    (hc : critA n t₁ t₂ u = true) : False := by
  have hQ : ∀ q : W ⧸ fixV H, q ^ 2 = 1 := fun q => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW, QuotientGroup.mk_one]
  set M := (permOfHom hφ).comp (quoAct H) with hMdef
  have hM : Function.Injective M := (permOfHom_injective hφ).comp hinj
  have hMa : ∀ g, M g = permOf hφ (quoAct H g) := fun g => rfl
  unfold critA at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hinv, ho1⟩, ho2⟩, hbig⟩ := hc
  obtain ⟨hu2, hu1⟩ := (isInvolA_iff hu).1 hinv
  have hu2' : M (h * h) = 1 := by rw [map_mul]; exact hu2
  have hh2 : h * h = 1 := hM (hu2'.trans (map_one M).symm)
  have hh1 : (h : MulAut W) ≠ 1 := fun h' => hu1 (by
    have : M h = 1 := by rw [show h = 1 from Subtype.ext h', map_one]
    exact this)
  have hodd : ∀ g : H, (permOf hφ (quoAct H g)) ^ 3 = 1 → Odd (orderOf (g : MulAut W)) := by
    intro g hg
    have hg2 : M (g ^ 3) = 1 := by rw [map_pow]; exact hg
    have hg' : g ^ 3 = 1 := hM (hg2.trans (map_one M).symm)
    have : (g : MulAut W) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hg', Subgroup.coe_one]
    have hd := orderOf_dvd_of_pow_eq_one this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1 <;> rw [h1] <;> decide
  have hodd1 := hodd g₁ ((ord3A_iff h₁).1 ho1)
  have hodd2 := hodd g₂ ((ord3A_iff h₂).1 ho2)
  have hidx := index_critSub_le hn hQ hcard hφ hxor h₁ h₂ hu hbig
  have hr := rkIdx_fixV_le_critSub hW (congrArg Subtype.val hh2) hodd1 hodd2 hh
  have hr2 := rkIdx_le_two Subgroup.index_ne_zero_of_finite hidx
  have hord : orderOf (h : MulAut W) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val hh2) hh1
  have hm := mParam_le_of_orderOf_two (hHG h.2) hord
  have h3 := hX.2
  rw [(index_fixV_eq_four hW hX.1 hX3).2] at h3
  omega

end Crit

omit [Finite W] in
theorem rep_evalG_quoAct {H : Subgroup (MulAut W)} {n : ℕ} {φ : Fin (2 ^ n) → W ⧸ fixV H}
    (hφ : Function.Bijective φ) {a b : Array ℕ} {g₁ g₂ : H}
    (ha : Rep (2 ^ n) a (permOf hφ (quoAct H g₁))) (hb : Rep (2 ^ n) b (permOf hφ (quoAct H g₂)))
    (w : List Bool) :
    Rep (2 ^ n) (evalWA (2 ^ n) a b w) (permOf hφ (quoAct H (evalG g₁ g₂ w))) := by
  have e := map_evalG ((permOfHom hφ).comp (quoAct H)) g₁ g₂ w
  simp only [MonoidHom.comp_apply, permOfHom_apply] at e
  rw [e]
  exact rep_evalWA ha hb w

section Closed

theorem pairwise_of_pairwiseNe {N : ℕ} {L : List (Array ℕ)} (h : pairwiseNe N L = true) :
    L.Pairwise fun s t => eqA N s t = false := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons s L ih =>
    unfold pairwiseNe at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    refine List.Pairwise.cons (fun t ht => ?_) (ih h.2)
    have := h.1 t ht
    simpa using this

theorem card_eq_of_closedOK {H : Subgroup (MulAut W)} {N : ℕ} {M : H →* Equiv.Perm (Fin N)}
    (hM : Function.Injective M) {x y : MulAut W} (hxH : x ∈ H) (hyH : y ∈ H) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hcl : H = Subgroup.closure {x, y}) {a b : Array ℕ}
    (ha : Rep N a (M ⟨x, hxH⟩)) (hb : Rep N b (M ⟨y, hyH⟩)) {l : List (List Bool)}
    (hl : closedOK N a b l = true) : Nat.card H = 21 := by
  classical
  unfold closedOK at hl
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hl
  obtain ⟨⟨⟨hlen, hpw⟩, hnil⟩, hclo⟩ := hl
  set ev : List Bool → H := evalG ⟨x, hxH⟩ ⟨y, hyH⟩ with hev
  have hrep : ∀ w, Rep N (evalWA N a b w) (M (ev w)) := fun w => by
    rw [hev, map_evalG]
    exact rep_evalWA ha hb w
  have heq : ∀ w w', eqA N (evalWA N a b w) (evalWA N a b w') = true ↔ ev w = ev w' :=
    fun w w' => (eqA_iff (hrep w) (hrep w')).trans hM.eq_iff
  have hnodup : (l.map ev).Nodup := by
    have h1 := pairwise_of_pairwiseNe hpw
    rw [List.pairwise_map] at h1
    refine List.pairwise_map.2 (h1.imp fun {w w'} h h' => ?_)
    rw [← heq] at h'
    rw [h'] at h
    exact Bool.noConfusion h
  have hnil' : [] ∈ l := List.contains_iff_mem.1 hnil
  have hstep : ∀ w ∈ l, ∀ c : Bool, ∃ w' ∈ l,
      ev w * (if c then ⟨y, hyH⟩ else ⟨x, hxH⟩) = ev w' := by
    intro w hw c
    obtain ⟨⟨w₁, hw₁, e₁⟩, ⟨w₂, hw₂, e₂⟩⟩ := hclo w hw
    cases c
    · exact ⟨w₁, hw₁, by rw [hev, ← evalG_append]; exact (heq _ _).1 e₁⟩
    · exact ⟨w₂, hw₂, by rw [hev, ← evalG_append]; exact (heq _ _).1 e₂⟩
  have hall : ∀ g : MulAut W, g ∈ Subgroup.closure ({x, y} : Set (MulAut W)) →
      ∃ hg : g ∈ H, ∃ w ∈ l, ev w = ⟨g, hg⟩ := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨H.one_mem, [], hnil', rfl⟩
    | mul_right g _ s hs ih =>
      obtain ⟨hgH, w, hw, hwg⟩ := ih
      rcases hs with rfl | rfl
      · obtain ⟨w', hw', e⟩ := hstep w hw false
        refine ⟨H.mul_mem hgH hxH, w', hw', ?_⟩
        rw [← e, hwg]
        rfl
      · obtain ⟨w', hw', e⟩ := hstep w hw true
        refine ⟨H.mul_mem hgH hyH, w', hw', ?_⟩
        rw [← e, hwg]
        rfl
    | mul_inv_cancel g _ s hs ih =>
      obtain ⟨hgH, w, hw, hwg⟩ := ih
      have key : ∀ (c : Bool) (s' : MulAut W) (hs' : s' ∈ H),
          (if c then (⟨y, hyH⟩ : H) else ⟨x, hxH⟩) = ⟨s', hs'⟩ → s' ^ 3 = 1 →
          ∃ hg : g * s'⁻¹ ∈ H, ∃ w ∈ l, ev w = ⟨g * s'⁻¹, hg⟩ := by
        intro c s' hs' hc h3
        obtain ⟨w₁, hw₁, e₁⟩ := hstep w hw c
        obtain ⟨w₂, hw₂, e₂⟩ := hstep w₁ hw₁ c
        have hinv : s'⁻¹ = s' * s' := by
          rw [← pow_two]
          exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])).symm
        refine ⟨H.mul_mem hgH (H.inv_mem hs'), w₂, hw₂, ?_⟩
        rw [← e₂, ← e₁, hwg, hc]
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hinv, mul_assoc]
      rcases hs with rfl | rfl
      · exact key false s hxH rfl hx3
      · exact key true s hyH rfl hy3
  have := finite_mulAut (W := W)
  have : Fintype H := Fintype.ofFinite H
  have hmem : ∀ g : H, g ∈ l.map ev := fun g => by
    obtain ⟨hg, w, hw, hwg⟩ := hall g (hcl ▸ g.2)
    exact List.mem_map.2 ⟨w, hw, by rw [hwg]⟩
  have huniv : (l.map ev).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun g => List.mem_toFinset.2 (hmem g)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← huniv, List.toFinset_card_of_nodup hnodup,
    List.length_map, hlen]

end Closed

section Main

variable {G X Y : Subgroup (MulAut W)}

theorem exists_gen_three (hX3 : Nat.card X = 3) :
    ∃ x ∈ X, orderOf x = 3 ∧ X = Subgroup.zpowers x := by
  obtain ⟨x, hx, hx1⟩ := exists_mem_ne (by omega : 1 < Nat.card X) 1
  have hd : orderOf x ∣ 3 := hX3 ▸ Subgroup.orderOf_dvd_natCard X hx
  have ho : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  refine ⟨x, hx, ho, (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx) ?_).symm⟩
  rw [Nat.card_zpowers, ho, hX3]

theorem card_fixV_quoAct (hW : ∀ w : W, w ^ 2 = 1) {H Z : Subgroup (MulAut W)} (hZ : Hyp101 G Z)
    (hZ3 : Nat.card Z = 3) {z : MulAut W} (hzZ : Z = Subgroup.zpowers z) (hzH : z ∈ H)
    (hZH : Z ≤ H) (hz3 : orderOf z = 3) :
    Nat.card (fixV (Subgroup.zpowers (quoAct H ⟨z, hzH⟩))) * 4 = Nat.card (W ⧸ fixV H) := by
  have hodd : Odd (orderOf ((⟨z, hzH⟩ : H) : MulAut W)) := by
    show Odd (orderOf z)
    rw [hz3]
    decide
  have heq : fixV (Subgroup.zpowers (quoAct H ⟨z, hzH⟩)) =
      (fixV Z).map (QuotientGroup.mk' (fixV H)) := by
    ext q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    constructor
    · intro hq
      have h1 : quoAct H ⟨z, hzH⟩ (w : W ⧸ fixV H) = w := hq _ (Subgroup.mem_zpowers _)
      rw [quoAct_mk_eq_iff hW hodd] at h1
      refine ⟨w, ?_, rfl⟩
      rw [hzZ]
      exact mem_fixV_zpowers h1
    · rintro ⟨w', hw', hw'eq⟩
      have h1 : z w' = w' := hw' z (hzZ ▸ Subgroup.mem_zpowers z)
      have h2 : quoAct H ⟨z, hzH⟩ (w' : W ⧸ fixV H) = w' := by rw [quoAct_mk]; simp [h1]
      have h3 : ((w' : W) : W ⧸ fixV H) = w := hw'eq
      rw [← h3]
      exact mem_fixV_zpowers h2
  have hle : fixV H ≤ fixV Z := fun v hv z hz => hv z (hZH hz)
  have hidx : ((fixV Z).map (QuotientGroup.mk' (fixV H))).index = (fixV Z).index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hle)
  rw [(index_fixV_eq_four hW hZ hZ3).1] at hidx
  have h := ((fixV Z).map (QuotientGroup.mk' (fixV H))).card_mul_index
  rw [hidx, ← heq] at h
  exact h

omit [Finite W] in
theorem eq_one_of_quoAct_fix (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W}
    (hXx : X = Subgroup.zpowers x) (hYy : Y = Subgroup.zpowers y) (hxH : x ∈ X ⊔ Y)
    (hyH : y ∈ X ⊔ Y) (hx3 : orderOf x = 3) (hy3 : orderOf y = 3) {q : W ⧸ fixV (X ⊔ Y)}
    (h1 : quoAct (X ⊔ Y) ⟨x, hxH⟩ q = q) (h2 : quoAct (X ⊔ Y) ⟨y, hyH⟩ q = q) : q = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hox : Odd (orderOf ((⟨x, hxH⟩ : ↥(X ⊔ Y)) : MulAut W)) := by
    show Odd (orderOf x)
    rw [hx3]
    decide
  have hoy : Odd (orderOf ((⟨y, hyH⟩ : ↥(X ⊔ Y)) : MulAut W)) := by
    show Odd (orderOf y)
    rw [hy3]
    decide
  rw [quoAct_mk_eq_iff hW hox] at h1
  rw [quoAct_mk_eq_iff hW hoy] at h2
  have hw : w ∈ fixV (X ⊔ Y) := by
    rw [fixV_sup]
    refine ⟨?_, ?_⟩
    · rw [hXx]
      exact mem_fixV_zpowers h1
    · rw [hYy]
      exact mem_fixV_zpowers h2
  exact (QuotientGroup.eq_one_iff w).2 hw

theorem pair_core (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X) (hX3 : Nat.card X = 3)
    {x y : MulAut W} (hXx : X = Subgroup.zpowers x) (hYy : Y = Subgroup.zpowers y)
    (hxH : x ∈ X ⊔ Y) (hyH : y ∈ X ⊔ Y) (hxo : orderOf x = 3) (hyo : orderOf y = 3)
    (hHG : X ⊔ Y ≤ G) (hcl : X ⊔ Y = Subgroup.closure {x, y})
    (hinj : Function.Injective (quoAct (X ⊔ Y)))
    (hfixη : Nat.card (fixV (Subgroup.zpowers (quoAct (X ⊔ Y) ⟨y, hyH⟩))) * 4 =
      Nat.card (W ⧸ fixV (X ⊔ Y)))
    {n : ℕ} (hn : n = 3 ∨ n = 4) (hcard : Nat.card (W ⧸ fixV (X ⊔ Y)) = 2 ^ n)
    {φ : Fin (2 ^ n) → W ⧸ fixV (X ⊔ Y)} (hφ : Function.Bijective φ)
    (hxor : ∀ i j, φ (i ^^^ j) = φ i * φ j)
    (hrepx : Rep (2 ^ n) (x0 n) (permOf hφ (quoAct (X ⊔ Y) ⟨x, hxH⟩))) {c : List ℕ}
    (hc : ∀ k (hk : k < n), c.getD k 0 =
      (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ k, Nat.pow_lt_pow_right (by norm_num) hk⟩ : ℕ))
    (hck : pairOK n (x0 n) c = true) : Commutes X Y ∨ Nat.card ↥(X ⊔ Y) = 21 := by
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hxorη := permOf_xor hφ hxor (quoAct (X ⊔ Y) ⟨y, hyH⟩)
  have hrepy : Rep (2 ^ n) (linA n c) (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩)) :=
    rep_linA _ hxorη c hc
  have hM : Function.Injective ((permOfHom hφ).comp (quoAct (X ⊔ Y))) :=
    (permOfHom_injective hφ).comp hinj
  have hη3 : permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ^ 3 = 1 := by
    have h1 : (⟨y, hyH⟩ : ↥(X ⊔ Y)) ^ 3 = 1 := Subtype.ext (by simp [hy3])
    rw [← permOfHom_apply, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hord := ord3V_eq_true hxorη hc hη3
  have hfc : fixCount (2 ^ n) (linA n c) = 2 ^ (n - 2) := by
    rw [fixCount_eq hrepy, ← Nat.card_eq_fintype_card]
    have e1 : Nat.card {i : Fin (2 ^ n) // permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) i = i} =
        Nat.card (fixV (Subgroup.zpowers (quoAct (X ⊔ Y) ⟨y, hyH⟩))) := by
      refine Nat.card_congr ((Equiv.subtypeEquiv (Equiv.ofBijective φ hφ)
        (fun i => (permOf_eq_iff hφ _ i i).trans Iff.rfl)).trans
        (Equiv.subtypeEquivRight fun q => ⟨fun h => mem_fixV_zpowers h,
          fun h => h _ (Subgroup.mem_zpowers _)⟩))
    rw [e1]
    rw [hcard] at hfixη
    rcases hn with rfl | rfl
    · have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
      rw [h8] at hfixη
      show _ = 2
      omega
    · have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h16] at hfixη
      show _ = 4
      omega
  have hφ0 : φ ⟨0, Nat.two_pow_pos n⟩ = 1 := by
    have h := hxor ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩
    have h0 : (⟨0, Nat.two_pow_pos n⟩ : Fin (2 ^ n)) ^^^ ⟨0, Nat.two_pow_pos n⟩ =
        ⟨0, Nat.two_pow_pos n⟩ := Fin.ext (by simp)
    rw [h0] at h
    exact (mul_eq_left.1 h.symm)
  have hmt : meetTriv (2 ^ n) (x0 n) (linA n c) = true := by
    refine meetTriv_eq_true hrepx hrepy fun i h1 h2 => ?_
    have h1' := (permOf_eq_iff hφ _ i i).1 h1
    have h2' := (permOf_eq_iff hφ _ i i).1 h2
    have h3 := eq_one_of_quoAct_fix hW hXx hYy hxH hyH hxo hyo h1' h2'
    rw [← hφ0] at h3
    exact congrArg Fin.val (hφ.1 h3)
  unfold pairOK at hck
  simp only [hord, hfc, hmt, Bool.not_true, Bool.false_or, beq_self_eq_true, Bool.and_self,
    Bool.or_eq_true] at hck
  rcases hck with ((hcomm | hplain) | hgen) | hf21
  ·
    left
    have h1 := (eqA_iff (rep_compA hrepx hrepy) (rep_compA hrepy hrepx)).1 hcomm
    have h1' : ((permOfHom hφ).comp (quoAct (X ⊔ Y))) (⟨x, hxH⟩ * ⟨y, hyH⟩) =
        ((permOfHom hφ).comp (quoAct (X ⊔ Y))) (⟨y, hyH⟩ * ⟨x, hxH⟩) := by
      simp only [map_mul, MonoidHom.comp_apply, permOfHom_apply]
      exact h1
    have h2 := congrArg Subtype.val (hM h1')
    simp only [Subgroup.coe_mul] at h2
    intro a ha b hb
    rw [hXx] at ha
    rw [hYy] at hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow h2 i j).eq
  ·
    exfalso
    unfold plainOK at hplain
    obtain ⟨w, -, hw⟩ := List.any_eq_true.1 hplain
    have hrep := rep_evalG_quoAct hφ hrepx hrepy w
    exact false_of_critA (g₁ := ⟨x, hxH⟩) (g₂ := ⟨y, hyH⟩) hW hX hX3 hHG hinj hn hcard hφ hxor
      (evalG_mem_closure _ _ w) hrepx hrepy hrep hw
  ·
    exfalso
    unfold genOK at hgen
    simp only [List.any_eq_true, Bool.and_eq_true] at hgen
    obtain ⟨w₁, -, -, w₂, -, -, w, -, hw⟩ := hgen
    have hrep₁ := rep_evalG_quoAct hφ hrepx hrepy w₁
    have hrep₂ := rep_evalG_quoAct hφ hrepx hrepy w₂
    have hrep := rep_evalG_quoAct hφ hrep₁ hrep₂ w
    exact false_of_critA hW hX hX3 hHG hinj hn hcard hφ hxor (evalG_mem_closure _ _ w)
      hrep₁ hrep₂ hrep hw
  ·
    right
    rw [Bool.and_eq_true] at hf21
    have hf := hf21.2
    unfold f21OK at hf
    exact card_eq_of_closedOK (M := (permOfHom hφ).comp (quoAct (X ⊔ Y))) hM hxH hyH hx3 hy3
      hcl hrepx hrepy hf

theorem ord3_pair (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X)
    (hY : Hyp102 G Y) (hX3 : Nat.card X = 3) (hY3 : Nat.card Y = 3) :
    Commutes X Y ∨ Nat.card ↥(X ⊔ Y) = 21 := by
  by_cases hXY : X = Y
  · left
    subst hXY
    exact commutes_self_of_isCyclic hX.1.2.2.1
  obtain ⟨x, hxX, hxo, hXx⟩ := exists_gen_three hX3
  obtain ⟨y, hyY, hyo, hYy⟩ := exists_gen_three hY3
  have hxH : x ∈ X ⊔ Y := Subgroup.mem_sup_left hxX
  have hyH : y ∈ X ⊔ Y := Subgroup.mem_sup_right hyY
  have hHG : X ⊔ Y ≤ G := sup_le hX.1.1 hY.1.1
  have hcl : X ⊔ Y = Subgroup.closure {x, y} := by
    rw [hXx, hYy, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have hQ : ∀ q : W ⧸ fixV (X ⊔ Y), q ^ 2 = 1 := fun q => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW, QuotientGroup.mk_one]
  have hinj := quoAct_injective hW hX hY hX3 hY3
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hξ3 : quoAct (X ⊔ Y) ⟨x, hxH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxH⟩ : ↥(X ⊔ Y)) ^ 3 = 1 := Subtype.ext (by simp [hx3])
    rw [this, map_one]
  have hfixξ := card_fixV_quoAct hW hX.1 hX3 hXx hxH le_sup_left hxo
  have hfixη := card_fixV_quoAct hW hY.1 hY3 hYy hyH le_sup_right hyo
  have h8 := eight_le_index_fixV_sup hW hX.1 hY.1 hX3 hY3 hXY
  have h16 := index_fixV_sup_le hW hX.1 hY.1 hX3 hY3
  have hcardQ : Nat.card (W ⧸ fixV (X ⊔ Y)) = (fixV (X ⊔ Y)).index :=
    (Subgroup.index_eq_card _).symm
  have hpow : Nat.card (W ⧸ fixV (X ⊔ Y)) = 2 ^ rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) := by
    rw [← card_eq_two_pow hQ ⊤, Subgroup.card_top]
  have hr : rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) = 3 ∨
      rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) = 4 := by
    rw [← hcardQ, hpow] at h8 h16
    have h1 : 3 ≤ rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_of_lt_succ h)
      omega
    have h2 : rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) ≤ 4 := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
      omega
    omega
  rcases hr with hr | hr
  · have hcard : Nat.card (W ⧸ fixV (X ⊔ Y)) = 2 ^ 3 := by rw [hpow, hr]
    obtain ⟨φ, hφ, hxor, hrepx⟩ := exists_frame3 hQ hξ3 (by rw [hcard]; norm_num)
      (by rw [hcard] at hfixξ; omega)
    have hck : pairOK 3 (x0 3)
        [(permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 0, by norm_num⟩ : ℕ),
          (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 1, by norm_num⟩ : ℕ),
          (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 2, by norm_num⟩ : ℕ)] = true := by
      have h := c7224_check3
      simp only [check3, allLt_iff] at h
      exact h _ (Fin.isLt _) _ (Fin.isLt _) _ (Fin.isLt _)
    exact pair_core hW hX hX3 hXx hYy hxH hyH hxo hyo hHG hcl hinj hfixη (Or.inl rfl) hcard hφ
      hxor hrepx (fun k hk => by interval_cases k <;> rfl) hck
  · have hcard : Nat.card (W ⧸ fixV (X ⊔ Y)) = 2 ^ 4 := by rw [hpow, hr]
    obtain ⟨φ, hφ, hxor, hrepx⟩ := exists_frame4 hQ hξ3 (by rw [hcard]; norm_num)
      (by rw [hcard] at hfixξ; omega)
    have hck : pairOK 4 (x0 4)
        [(permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 0, by norm_num⟩ : ℕ),
          (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 1, by norm_num⟩ : ℕ),
          (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 2, by norm_num⟩ : ℕ),
          (permOf hφ (quoAct (X ⊔ Y) ⟨y, hyH⟩) ⟨2 ^ 3, by norm_num⟩ : ℕ)] = true := by
      have h := c7224_check4
      simp only [check4, allLt_iff] at h
      exact h _ (Fin.isLt _) _ (Fin.isLt _) _ (Fin.isLt _) _ (Fin.isLt _)
    exact pair_core hW hX hX3 hXx hYy hxH hyH hxo hyo hHG hcl hinj hfixη (Or.inr rfl) hcard hφ
      hxor hrepx (fun k hk => by interval_cases k <;> rfl) hck

end Main

end Pf

end Asc81c

end CFSG.Quasithin

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.A6S1372L76A
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open
open scoped Matrix

namespace A6L76N3

@[expose] def e0 : Fin 3 → ZMod 2 := ![1, 0, 0]

theorem exists_mulVec_eq_e0 : ∀ x : Fin 3 → ZMod 2, x ≠ 0 →
    ∃ g : SL3.S, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x = e0 := by
  decide +kernel

theorem inX1_iff_mulVec : ∀ A : SL3.S,
    SL3.InX1 A ↔ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e0 = e0 := by
  decide +kernel

@[expose] def blockMat (A : SL3.S) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![(A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2;
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1, (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2]

theorem blockMat_det : ∀ A : SL3.S, SL3.InX1 A → (blockMat A).det = 1 := by
  decide +kernel

theorem blockMat_one : blockMat 1 = 1 := by
  decide +kernel

theorem blockMat_mul (A B : SL3.S) (hA : SL3.InX1 A) :
    blockMat (A * B) = blockMat A * blockMat B := by
  obtain ⟨ha1, ha2⟩ := hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, ha1, ha2]

@[expose] def blockHom : ↥SL3.X1 →* SL22.S2 where
  toFun A := ⟨blockMat A, blockMat_det A A.2⟩
  map_one' := Subtype.ext blockMat_one
  map_mul' A B := Subtype.ext (blockMat_mul A B A.2)

@[expose] def InR (A : SL3.S) : Prop := SL3.InX1 A ∧ blockMat A = 1

instance : DecidablePred InR := fun A => by unfold InR; infer_instance

theorem inR_inv : ∀ A : SL3.S, InR A → InR A⁻¹ := by
  decide +kernel

@[expose] def R : Subgroup SL3.S where
  carrier := {A | InR A}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb =>
    ⟨SL3.inX1_mul a b ha.1 hb.1, by rw [blockMat_mul a b ha.1, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} => inR_inv a

theorem card_R : Nat.card R = 4 := by
  have : Fintype.card {A : SL3.S // InR A} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem index_R : R.index = 42 := by
  have h := R.card_mul_index
  rw [card_R, SL3.card_S] at h
  omega

theorem mul_self_of_inR : ∀ A : SL3.S, InR A → A * A = 1 := by
  decide +kernel

@[expose] def a3 : SL3.S := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide +kernel⟩

theorem a3_facts : a3 ^ 3 = 1 ∧ SL3.InX1 a3 ∧ SL3.InX1 (a3 ^ 2) ∧ ¬ InR a3 ∧ ¬ InR (a3 ^ 2) := by
  decide +kernel

theorem two_pow_mod_three (c : ℕ) : 2 ^ c % 3 = 1 ∨ 2 ^ c % 3 = 2 := by
  induction c with
  | zero => left; rfl
  | succ c ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> simp

theorem a3_pow_two_pow (c : ℕ) : a3 ^ 2 ^ c = a3 ∨ a3 ^ 2 ^ c = a3 ^ 2 := by
  rw [pow_eq_pow_mod (2 ^ c) a3_facts.1]
  rcases two_pow_mod_three c with h | h <;> rw [h]
  · left; exact pow_one a3
  · right; rfl

theorem sl2_word : ∀ r s : SL22.S2, r ^ 3 = 1 → r ≠ 1 → s * s = 1 → s ≠ 1 → ∀ x : SL22.S2,
    x = 1 ∨ x = r ∨ x = r * r ∨ x = s ∨ x = s * r ∨ x = s * (r * r) := by
  decide +kernel

theorem sl2_pow_six : ∀ s : SL22.S2, s ^ 6 = 1 := by
  decide +kernel

theorem sl2_comm_three : ∀ n : SL22.S2, n ≠ 1 → n * n = 1 →
    ∃ g : SL22.S2, (n * (g * n⁻¹ * g⁻¹)) ^ 3 = 1 ∧ n * (g * n⁻¹ * g⁻¹) ≠ 1 := by
  decide +kernel

theorem eq_one_of_pow_two_pow {X : Type*} [Monoid X] {x : X} {j m : ℕ} (hj : x ^ 2 ^ j = 1)
    (hm : x ^ m = 1) (hodd : Odd m) : x = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj) (orderOf_dvd_of_pow_eq_one hm)
  have hcop : Nat.Coprime (2 ^ j) m := (Odd.coprime_two_left hodd).pow_left j
  rwa [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1

theorem mul_self_of_pow_two_pow {X : Type*} [Monoid X] {x : X} {j : ℕ} (hj : x ^ 2 ^ j = 1)
    (h6 : x ^ 6 = 1) : x * x = 1 := by
  have h3 : (x * x) ^ 3 = 1 := by rw [← pow_two, ← pow_mul]; exact h6
  have h2 : (x * x) ^ 2 ^ j = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hj, one_pow]
  exact eq_one_of_pow_two_pow h2 h3 (by decide)

theorem sl2_normal_two (N : Subgroup SL22.S2) (hN : N.Normal) (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hn1
  obtain ⟨j, hj⟩ := h2 ⟨n, hn⟩
  have hj' : n ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hnn := mul_self_of_pow_two_pow hj' (sl2_pow_six n)
  obtain ⟨g, hg3, hg1⟩ := sl2_comm_three n hn1 hnn
  have hmem : n * (g * n⁻¹ * g⁻¹) ∈ N := N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) g)
  obtain ⟨k, hk⟩ := h2 ⟨_, hmem⟩
  have hk' : (n * (g * n⁻¹ * g⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact hg1 (eq_one_of_pow_two_pow hk' hg3 (by decide))

theorem sl3_normal_two (N : Subgroup SL3.S) (hN : N.Normal) (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup SL3.S := A6L76A.isSimpleGroup_sl (le_refl 3) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at h2
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [Subgroup.card_top, SL3.card_S] at hk
    have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : (7 : ℕ) ∣ 168)
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)

theorem quasithinO2QuotientIso_of_isPGroup_ker {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {Q : Type*} [Group Q] (φ : ↥X →* Q) (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 ↥φ.ker) (hQ : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 ↥N → N = ⊥) :
    quasithinO2QuotientIso X Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨φ, hφ, le_antisymm (CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker φ) hk) ?_⟩
  have hN : ((CFSG.Open.pCore 2 ↥X).map φ).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal (G := ↥X) (r := 2)).map _ hφ
  have hP : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥X).map φ) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) (r := 2)).map _
  have h := hQ _ hN hP
  intro x hx
  have : φ x ∈ (CFSG.Open.pCore 2 ↥X).map φ := ⟨x, hx, rfl⟩
  rw [h] at this
  exact this

end A6L76N3

end CFSG.Quasithin.H13.A6

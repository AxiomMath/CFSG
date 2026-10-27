module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N.G2Two

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open

section General

variable {G : Type*} [Group G]

theorem closure_subset_of_mul_mem [Finite G] {S T : Set G} (h1 : (1 : G) ∈ T)
    (hmul : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T) : (Subgroup.closure S : Set G) ⊆ T := by
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left s hs y _ ih => exact hmul s hs y ih
  | inv_mul_cancel s hs y _ ih =>
    have hpow : ∀ n : ℕ, s ^ n * y ∈ T := by
      intro n
      induction n with
      | zero => simpa using ih
      | succ n ihn =>
        rw [pow_succ', mul_assoc]
        exact hmul s hs _ ihn
    have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos s),
        pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem card_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer {g * x * g⁻¹}) = Nat.card (Subgroup.centralizer {x}) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y * g, ?_⟩
      invFun := fun y => ⟨g * y * g⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

theorem card_centralizer_mulEquiv {G' : Type*} [Group G'] (φ : G ≃* G') (x : G) :
    Nat.card (Subgroup.centralizer {φ x}) = Nat.card (Subgroup.centralizer {x}) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨φ.symm y, ?_⟩
      invFun := fun y => ⟨φ y, ?_⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]

theorem centralizer_inv_singleton (x : G) :
    Subgroup.centralizer {x⁻¹} = Subgroup.centralizer {x} := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem factorization_card_centralizer_lt [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {x : G} (hxp : IsPGroup p (Subgroup.zpowers x))
    (hx : ∀ g : G, g⁻¹ * x * g ∈ (P : Subgroup G) →
      (∀ y ∈ (P : Subgroup G), y * (g⁻¹ * x * g) = (g⁻¹ * x * g) * y) → False) :
    (Nat.card (Subgroup.centralizer {x})).factorization p < (Nat.card G).factorization p := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hle : (Nat.card C).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card C) p
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨Q⟩ : Nonempty (Sylow p C) := inferInstance
  set Q' : Subgroup G := (Q : Subgroup C).map C.subtype with hQ'
  have hQ'card : Nat.card Q' = p ^ (Nat.card G).factorization p := by
    rw [hQ', Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, heq]
  set S : Sylow p G := Sylow.ofCard Q' hQ'card with hS
  have hSQ : (S : Subgroup G) = Q' := rfl
  have hQ'C : ∀ y ∈ Q', y * x = x * y := by
    rintro _ ⟨y, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hxQ : x ∈ Q' := by
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have e : x * h * x⁻¹ = h := by
          rw [← hQ'C h hh, mul_inv_cancel_right]
        rw [e]
        exact hh
      · intro hh
        have h1 := hQ'C (x * h * x⁻¹) hh
        have e : h = x * h * x⁻¹ := by
          have h2 : x * h = x * (x * h * x⁻¹) := by
            calc x * h = x * h * x⁻¹ * x := by group
              _ = x * (x * h * x⁻¹) := h1
          exact mul_left_cancel h2
        rw [e]
        exact hh
    have hsup := hxp.to_sup_of_normal_right' S.isPGroup' hnorm
    have heqQ := S.is_maximal' hsup le_sup_right
    have : x ∈ Subgroup.zpowers x ⊔ (S : Subgroup G) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    rw [heqQ] at this
    exact this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hmem : ∀ z : G, z ∈ (S : Subgroup G) ↔ g⁻¹ * z * g ∈ (P : Subgroup G) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  refine hx g ((hmem x).mp hxQ) fun y hy => ?_
  have hgy : g * y * g⁻¹ ∈ (S : Subgroup G) :=
    (hmem _).mpr (by simpa [mul_assoc] using hy)
  have hc := hQ'C _ (hSQ ▸ hgy)
  calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
    _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hc]
    _ = g⁻¹ * x * g * y := by group

end General

@[expose] def mmul (A B : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j +
    A i 4 * B 4 j + A i 5 * B 5 j + A i 6 * B 6 j + A i 7 * B 7 j

theorem mmul_eq (A B : Matrix (Fin 8) (Fin 8) (ZMod 2)) : mmul A B = A * B := by
  ext i j
  simp [mmul, Matrix.mul_apply, Fin.sum_univ_eight]

@[expose] def mpow (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : ℕ → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | 0 => 1
  | n + 1 => mmul A (mpow A n)

theorem mpow_eq (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (n : ℕ) : mpow A n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mpow, ih, mmul_eq, pow_succ']

@[expose] def mword : List (Fin 8) → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | [] => 1
  | i :: v => mmul (mats8 i) (mword v)

theorem mword_eq (v : List (Fin 8)) : mword v = wordEvalM mats8 v := by
  induction v with
  | nil => rfl
  | cons i v ih =>
    rw [mword, ih, mmul_eq]
    rfl

@[expose] def mtr (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : ZMod 2 :=
  A 0 0 + A 1 1 + A 2 2 + A 3 3 + A 4 4 + A 5 5 + A 6 6 + A 7 7

theorem mtr_eq (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : mtr A = A.trace := by
  simp [mtr, Matrix.trace, Fin.sum_univ_eight]

@[expose] def matS : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def matT : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0, 0, 1;
    1, 1, 1, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 1, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    1, 1, 1, 0, 0, 0, 0, 0]

@[expose] def matW : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0, 1, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 1, 1, 1, 1;
    1, 0, 1, 1, 0, 1, 0, 1;
    1, 0, 1, 0, 1, 1, 0, 1;
    0, 1, 0, 1, 1, 1, 1, 0;
    0, 1, 0, 1, 0, 1, 0, 0;
    0, 1, 0, 1, 1, 0, 1, 1]

@[expose] def matMA : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def matMB : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def matSA : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def matSB : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def matM0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def matM0sq : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def matS0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def matS0sq : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 1, 1;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 1, 0]

@[expose] def matP (a b l : Fin 3) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  mmul (mpow matS a) (mmul (mpow matT b) (mpow matW l))

@[expose] def elM : Fin 6 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![1, matMA, matMB, mmul matMA matMB, mmul matMB matMA, mmul matMA (mmul matMB matMA)]

@[expose] def elS : Fin 6 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![1, matSA, matSB, mmul matSA matSB, mmul matSB matSA, mmul matSA (mmul matSB matSA)]

@[expose] def mulA6 : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

@[expose] def mulB6 : Fin 6 → Fin 6 := ![2, 4, 0, 5, 1, 3]

@[expose] def tgtMat : Fin 4 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![matM0, matM0sq, matS0, matS0sq]

@[expose] def conjTable : Fin 3 → Fin 3 → Fin 3 → List (Fin 8) × Fin 4 :=
  ![![![([], 0), ([5, 0, 4, 0, 1], 0), ([5, 0, 4, 0, 1], 1)],
      ![([6, 3, 1], 2), ([5, 0, 4, 7, 0, 1], 1), ([6, 3, 0, 6], 1)],
      ![([6, 3, 1], 3), ([6, 3, 0, 6], 0), ([5, 0, 4, 7, 0, 1], 0)]],
    ![![([3, 6, 3, 2], 1), ([6, 3, 1], 1), ([0, 6, 3], 0)],
      ![([1, 5, 4, 0, 1], 0), ([1, 5, 7, 4], 1), ([0, 6, 5], 1)],
      ![([1, 5, 4, 2, 1], 0), ([6, 1, 5], 0), ([5, 7, 0, 4], 0)]],
    ![![([3, 6, 3, 2], 0), ([0, 6, 5], 0), ([6, 1, 5], 1)],
      ![([1, 5, 4, 2, 1], 1), ([0, 6, 3], 1), ([1, 5, 7, 4], 0)],
      ![([1, 5, 4, 0, 1], 1), ([5, 7, 0, 4], 1), ([6, 3, 1], 0)]]]

abbrev ConjOK (a b l : Fin 3) : Prop :=
  mmul (mword (conjTable a b l).1) (matP a b l) =
    mmul (tgtMat (conjTable a b l).2) (mword (conjTable a b l).1)

theorem word_checks : mword [7, 5, 3] = matS ∧ mword [4, 1, 4, 0] = matT ∧
    mword [5, 1, 4, 3, 1] = matW ∧ mats8 4 = matMA ∧ mats8 2 = matMB ∧
    mword [7, 5, 1, 5, 7] = matSA ∧ mword [3, 6, 0, 6, 3] = matSB ∧
    mmul matMA matMB = matM0 ∧ mmul matM0 matM0 = matM0sq ∧ mmul matSA matSB = matS0 ∧
    mmul matS0 matS0 = matS0sq := by
  decide +kernel

theorem left_s : ∀ a b l : Fin 3, mmul matS (matP a b l) = matP (a + 1) b l := by
  decide +kernel

theorem left_t : ∀ a b l : Fin 3, mmul matT (matP a b l) = matP a (b + 1) l := by
  decide +kernel

theorem left_w :
    ∀ a b l : Fin 3, mmul matW (matP a b l) = matP a (b + 2 * a) (l + 1) := by
  decide +kernel

theorem matP_inj : ∀ a b l a' b' l' : Fin 3, matP a b l = matP a' b' l' →
    a = a' ∧ b = b' ∧ l = l' := by
  decide +kernel

theorem central_t : mmul matT matS = mmul matS matT ∧ mmul matT matW = mmul matW matT := by
  decide +kernel

theorem center_trace : ∀ a b l : Fin 3, mmul (matP a b l) matS = mmul matS (matP a b l) →
    mmul (matP a b l) matT = mmul matT (matP a b l) →
    mmul (matP a b l) matW = mmul matW (matP a b l) → mtr (matP a b l) = 0 → matP a b l = 1 := by
  decide +kernel

theorem trace_w : mtr matW = 0 ∧ matW ≠ 1 := by
  decide +kernel

theorem conj_check0 : ∀ b l : Fin 3, ((0 : Fin 3), b, l) ≠ (0, 0, 0) → ConjOK 0 b l := by
  decide +kernel

theorem conj_check1 : ∀ b l : Fin 3, ConjOK 1 b l := by
  decide +kernel

theorem conj_check2 : ∀ b l : Fin 3, ConjOK 2 b l := by
  decide +kernel

theorem el_closed : ∀ i : Fin 6, mmul matMA (elM i) = elM (mulA6 i) ∧
    mmul matMB (elM i) = elM (mulB6 i) ∧ mmul matSA (elS i) = elS (mulA6 i) ∧
    mmul matSB (elS i) = elS (mulB6 i) := by
  decide +kernel

theorem el_three : ∀ i : Fin 6,
    (mmul (elM i) (mmul (elM i) (elM i)) = 1 → i = 0 ∨ elM i = matM0 ∨ elM i = matM0sq) ∧
    (mmul (elS i) (mmul (elS i) (elS i)) = 1 → i = 0 ∨ elS i = matS0 ∨ elS i = matS0sq) := by
  decide +kernel

theorem cube_checks : mmul matM0 matM0sq = 1 ∧ mmul matS0 matS0sq = 1 ∧ matP 0 0 0 = 1 := by
  decide +kernel

section Cayley


theorem factorization_12096 : (12096 : ℕ).factorization 3 = 3 := by
  rw [show (12096 : ℕ) = 3 ^ 3 * 448 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem finite_cayley : Finite ↥(cayleyGroup (ZMod 2)) :=
  Finite.of_injective (cmat : ↥(cayleyGroup (ZMod 2)) → Matrix (Fin 8) (Fin 8) (ZMod 2))
    fun _ _ h => cmat_injective h

theorem cmat_wordEval_gens8 (v : List (Fin 8)) : cmat (wordEval gens8 v) = mword v := by
  rw [mword_eq]
  exact cmat_wordEval gens8 mats8 cmat_gens8 v

@[expose] noncomputable def pS : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [7, 5, 3]

@[expose] noncomputable def pT : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [4, 1, 4, 0]

@[expose] noncomputable def pW : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [5, 1, 4, 3, 1]

@[expose] noncomputable def pElt (a b l : Fin 3) : ↥(cayleyGroup (ZMod 2)) :=
  pS ^ (a : ℕ) * (pT ^ (b : ℕ) * pW ^ (l : ℕ))

@[expose] noncomputable def P0 : Subgroup ↥(cayleyGroup (ZMod 2)) := Subgroup.closure {pS, pT, pW}

@[expose] noncomputable def mA : ↥(cayleyGroup (ZMod 2)) := gens8 4

@[expose] noncomputable def mB : ↥(cayleyGroup (ZMod 2)) := gens8 2

@[expose] noncomputable def m0 : ↥(cayleyGroup (ZMod 2)) := mA * mB

@[expose] noncomputable def sA : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [7, 5, 1, 5, 7]

@[expose] noncomputable def sB : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [3, 6, 0, 6, 3]

@[expose] noncomputable def s0 : ↥(cayleyGroup (ZMod 2)) := sA * sB

theorem cmat_pS : cmat pS = matS := (cmat_wordEval_gens8 _).trans word_checks.1

theorem cmat_pT : cmat pT = matT := (cmat_wordEval_gens8 _).trans word_checks.2.1

theorem cmat_pW : cmat pW = matW := (cmat_wordEval_gens8 _).trans word_checks.2.2.1

theorem cmat_mA : cmat mA = matMA := (cmat_gens8 4).trans word_checks.2.2.2.1

theorem cmat_mB : cmat mB = matMB := (cmat_gens8 2).trans word_checks.2.2.2.2.1

theorem cmat_sA : cmat sA = matSA := (cmat_wordEval_gens8 _).trans word_checks.2.2.2.2.2.1

theorem cmat_sB : cmat sB = matSB := (cmat_wordEval_gens8 _).trans word_checks.2.2.2.2.2.2.1

theorem cmat_m0 : cmat m0 = matM0 := by
  rw [m0, map_mul, cmat_mA, cmat_mB, ← mmul_eq, word_checks.2.2.2.2.2.2.2.1]

theorem cmat_m0_sq : cmat (m0 * m0) = matM0sq := by
  rw [map_mul, cmat_m0, ← mmul_eq, word_checks.2.2.2.2.2.2.2.2.1]

theorem cmat_s0 : cmat s0 = matS0 := by
  rw [s0, map_mul, cmat_sA, cmat_sB, ← mmul_eq, word_checks.2.2.2.2.2.2.2.2.2.1]

theorem cmat_s0_sq : cmat (s0 * s0) = matS0sq := by
  rw [map_mul, cmat_s0, ← mmul_eq, word_checks.2.2.2.2.2.2.2.2.2.2]

theorem cmat_pElt (a b l : Fin 3) : cmat (pElt a b l) = matP a b l := by
  simp only [pElt, matP, map_mul, map_pow, cmat_pS, cmat_pT, cmat_pW, mmul_eq, mpow_eq]

theorem m0_sq : m0 * m0 = m0⁻¹ :=
  (eq_inv_of_mul_eq_one_left (cmat_injective (by
    rw [map_mul, cmat_m0_sq, cmat_m0, map_one, ← mmul_eq, ← cube_checks.1]
    decide +kernel))).trans rfl

theorem s0_sq : s0 * s0 = s0⁻¹ :=
  (eq_inv_of_mul_eq_one_left (cmat_injective (by
    rw [map_mul, cmat_s0_sq, cmat_s0, map_one, ← mmul_eq, ← cube_checks.2.1]
    decide +kernel))).trans rfl

theorem trace_cmat_conj (g x : ↥(cayleyGroup (ZMod 2))) :
    (cmat (g⁻¹ * x * g)).trace = (cmat x).trace := by
  have h : cmat g * cmat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, Matrix.trace_mul_cycle, h, one_mul]

theorem pElt_mem_P0 (a b l : Fin 3) : pElt a b l ∈ P0 := by
  have hs : pS ∈ P0 := Subgroup.subset_closure (by simp)
  have ht : pT ∈ P0 := Subgroup.subset_closure (by simp)
  have hw : pW ∈ P0 := Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hs _)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ ht _) (Subgroup.pow_mem _ hw _))

theorem exists_pElt_of_mem {y : ↥(cayleyGroup (ZMod 2))} (hy : y ∈ P0) :
    ∃ a b l : Fin 3, y = pElt a b l := by
  have := finite_cayley
  have hsub := closure_subset_of_mul_mem (S := {pS, pT, pW})
    (T := {y | ∃ a b l : Fin 3, cmat y = matP a b l}) ⟨0, 0, 0, by rw [map_one, cube_checks.2.2]⟩
    (by
      rintro x hx y ⟨a, b, l, hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨a + 1, b, l, by rw [map_mul, cmat_pS, hy, ← mmul_eq, left_s]⟩
      · exact ⟨a, b + 1, l, by rw [map_mul, cmat_pT, hy, ← mmul_eq, left_t]⟩
      · exact ⟨a, b + 2 * a, l + 1, by rw [map_mul, cmat_pW, hy, ← mmul_eq, left_w]⟩) hy
  obtain ⟨a, b, l, h⟩ := hsub
  exact ⟨a, b, l, cmat_injective (by rw [h, cmat_pElt])⟩

theorem card_P0 : Nat.card P0 = 27 := by
  let f : Fin 3 × Fin 3 × Fin 3 → P0 := fun x => ⟨pElt x.1 x.2.1 x.2.2, pElt_mem_P0 _ _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b, l⟩ ⟨a', b', l'⟩ h
      have h1 := congrArg (fun y : P0 => cmat (y : ↥(cayleyGroup (ZMod 2)))) h
      simp only [f, cmat_pElt] at h1
      obtain ⟨rfl, rfl, rfl⟩ := matP_inj a b l a' b' l' h1
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨a, b, l, rfl⟩ := exists_pElt_of_mem hy
      exact ⟨(a, b, l), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

@[expose] noncomputable def sylowP0 (hcard : Nat.card ↥(cayleyGroup (ZMod 2)) = 12096) :
    @Sylow 3 ↥(cayleyGroup (ZMod 2)) _ :=
  have := finite_cayley
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard P0 (by rw [card_P0, hcard, factorization_12096]; norm_num)

@[expose] noncomputable def tgt : Fin 4 → ↥(cayleyGroup (ZMod 2)) := ![m0, m0 * m0, s0, s0 * s0]

theorem cmat_tgt (i : Fin 4) : cmat (tgt i) = tgtMat i := by
  fin_cases i
  · exact cmat_m0
  · exact cmat_m0_sq
  · exact cmat_s0
  · exact cmat_s0_sq

theorem conj_check (a b l : Fin 3) (h : (a, b, l) ≠ (0, 0, 0)) : ConjOK a b l := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · exact conj_check0 b l h
  · exact conj_check1 b l
  · exact conj_check2 b l

theorem conj_pElt (a b l : Fin 3) (h : (a, b, l) ≠ (0, 0, 0)) :
    wordEval gens8 (conjTable a b l).1 * pElt a b l =
      tgt (conjTable a b l).2 * wordEval gens8 (conjTable a b l).1 :=
  cmat_injective (by
    rw [map_mul, map_mul, cmat_wordEval_gens8, cmat_pElt, cmat_tgt, ← mmul_eq, ← mmul_eq]
    exact conj_check a b l h)

theorem m0_mem : m0 ∈ Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2))) :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem s0_mem : s0 ∈ Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2))) :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem tgt_mem (i : Fin 4) :
    tgt i ∈ Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2))) ∨
      tgt i ∈ Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2))) := by
  fin_cases i
  · exact Or.inl m0_mem
  · exact Or.inl (Subgroup.mul_mem _ m0_mem m0_mem)
  · exact Or.inr s0_mem
  · exact Or.inr (Subgroup.mul_mem _ s0_mem s0_mem)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {y : G} (hy : IsPGroup p (Subgroup.zpowers y)) :
    ∃ g : G, g⁻¹ * y * g ∈ (S : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S Q
  have hyQ : y ∈ ((g • S : Sylow p G) : Subgroup G) := hQ (Subgroup.mem_zpowers y)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  refine ⟨g, ?_⟩
  have h1 : ((MulAut.conj g)⁻¹ • y : G) = g⁻¹ * y * g := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [← h1]
  exact hyQ

theorem exists_conj_mem_rootSL2 (hcard : Nat.card ↥(cayleyGroup (ZMod 2)) = 12096)
    (y : ↥(cayleyGroup (ZMod 2))) (h3 : y ^ 3 = 1) (h1 : y ≠ 1) :
    ∃ g : ↥(cayleyGroup (ZMod 2)),
      g * y * g⁻¹ ∈ Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2))) ∨
      g * y * g⁻¹ ∈ Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2))) := by
  have := finite_cayley
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy : orderOf y = 3 := orderOf_eq_prime h3 h1
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (sylowP0 hcard) hyp
  obtain ⟨a, b, l, hab⟩ := exists_pElt_of_mem hg
  have hne : (a, b, l) ≠ (0, 0, 0) := by
    intro h0
    simp only [Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl, rfl⟩ := h0
    apply h1
    have e : g⁻¹ * y * g = 1 := by rw [hab]; simp [pElt]
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  set u := wordEval gens8 (conjTable a b l).1
  refine ⟨u * g⁻¹, ?_⟩
  have e : u * g⁻¹ * y * (u * g⁻¹)⁻¹ = tgt (conjTable a b l).2 := by
    have hc := conj_pElt a b l hne
    rw [← hab] at hc
    calc u * g⁻¹ * y * (u * g⁻¹)⁻¹ = u * (g⁻¹ * y * g) * u⁻¹ := by group
      _ = tgt (conjTable a b l).2 * u * u⁻¹ := by rw [hc]
      _ = tgt (conjTable a b l).2 := by group
  rw [e]
  exact tgt_mem _

theorem eq_m0_of_mem {y : ↥(cayleyGroup (ZMod 2))}
    (hy : y ∈ Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2)))) (h3 : y ^ 3 = 1)
    (h1 : y ≠ 1) : y = m0 ∨ y = m0 * m0 := by
  have := finite_cayley
  obtain ⟨i, hi⟩ := closure_subset_of_mul_mem (S := {mA, mB})
    (T := {y | ∃ i : Fin 6, cmat y = elM i}) ⟨0, by rw [map_one]; rfl⟩
    (by
      rintro x hx y ⟨i, hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨mulA6 i, by rw [map_mul, cmat_mA, hy, ← mmul_eq, (el_closed i).1]⟩
      · exact ⟨mulB6 i, by rw [map_mul, cmat_mB, hy, ← mmul_eq, (el_closed i).2.1]⟩) hy
  have hc : mmul (elM i) (mmul (elM i) (elM i)) = 1 := by
    rw [mmul_eq, mmul_eq, ← hi, ← pow_three, ← map_pow, h3, map_one]
  rcases (el_three i).1 hc with rfl | h | h
  · exact absurd (cmat_injective (by rw [hi, map_one]; rfl)) h1
  · exact Or.inl (cmat_injective (by rw [hi, h, cmat_m0]))
  · exact Or.inr (cmat_injective (by rw [hi, h, cmat_m0_sq]))

theorem eq_s0_of_mem {y : ↥(cayleyGroup (ZMod 2))}
    (hy : y ∈ Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2)))) (h3 : y ^ 3 = 1)
    (h1 : y ≠ 1) : y = s0 ∨ y = s0 * s0 := by
  have := finite_cayley
  obtain ⟨i, hi⟩ := closure_subset_of_mul_mem (S := {sA, sB})
    (T := {y | ∃ i : Fin 6, cmat y = elS i}) ⟨0, by rw [map_one]; rfl⟩
    (by
      rintro x hx y ⟨i, hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨mulA6 i, by rw [map_mul, cmat_sA, hy, ← mmul_eq, (el_closed i).2.2.1]⟩
      · exact ⟨mulB6 i, by rw [map_mul, cmat_sB, hy, ← mmul_eq, (el_closed i).2.2.2]⟩) hy
  have hc : mmul (elS i) (mmul (elS i) (elS i)) = 1 := by
    rw [mmul_eq, mmul_eq, ← hi, ← pow_three, ← map_pow, h3, map_one]
  rcases (el_three i).2 hc with rfl | h | h
  · exact absurd (cmat_injective (by rw [hi, map_one]; rfl)) h1
  · exact Or.inl (cmat_injective (by rw [hi, h, cmat_s0]))
  · exact Or.inr (cmat_injective (by rw [hi, h, cmat_s0_sq]))

theorem P0_le_centralizer_pT : P0 ≤ Subgroup.centralizer {pT} := by
  rw [P0, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact cmat_injective (by rw [map_mul, map_mul, cmat_pS, cmat_pT, ← mmul_eq, ← mmul_eq,
      central_t.1])
  · rfl
  · exact cmat_injective (by rw [map_mul, map_mul, cmat_pW, cmat_pT, ← mmul_eq, ← mmul_eq,
      central_t.2])

theorem factorization_card_centralizer_s0 (hcard : Nat.card ↥(cayleyGroup (ZMod 2)) = 12096) :
    (Nat.card (Subgroup.centralizer {s0})).factorization 3 = 3 := by
  have := finite_cayley
  have hc := conj_pElt 0 1 0 (by decide)
  have hpe : pElt 0 1 0 = pT := by simp [pElt]
  rw [hpe] at hc
  have hs0 : s0 = wordEval gens8 [6, 3, 1] * pT * (wordEval gens8 [6, 3, 1])⁻¹ := by
    have : (conjTable 0 1 0).1 = [6, 3, 1] := rfl
    have h2 : tgt (conjTable 0 1 0).2 = s0 := rfl
    rw [this, h2] at hc
    rw [hc, mul_inv_cancel_right]
  rw [hs0, card_centralizer_conj]
  have hpos : Nat.card (Subgroup.centralizer {pT}) ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · have h := (Nat.factorization_le_iff_dvd hpos Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer {pT})) 3
    rwa [hcard, factorization_12096] at h
  · rw [← Nat.prime_three.pow_dvd_iff_le_factorization hpos]
    have h27 := Subgroup.card_dvd_of_le P0_le_centralizer_pT
    rw [card_P0] at h27
    exact h27

theorem card_closure_tw :
    Nat.card (Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2)))) = 9 := by
  have := finite_cayley
  have hmem : ∀ b l : Fin 3,
      pElt 0 b l ∈ Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) := by
    intro b l
    have ht : pT ∈ Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) :=
      Subgroup.subset_closure (by simp)
    have hw : pW ∈ Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) :=
      Subgroup.subset_closure (by simp)
    simp only [pElt, Fin.val_zero, pow_zero, one_mul]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ ht _) (Subgroup.pow_mem _ hw _)
  let f : Fin 3 × Fin 3 → Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) :=
    fun x => ⟨pElt 0 x.1 x.2, hmem _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, l⟩ ⟨b', l'⟩ h
      have h1 := congrArg (fun y : Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) =>
        cmat (y : ↥(cayleyGroup (ZMod 2)))) h
      simp only [f, cmat_pElt] at h1
      obtain ⟨-, rfl, rfl⟩ := matP_inj 0 b l 0 b' l' h1
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨b, l, h⟩ := closure_subset_of_mul_mem (S := {pT, pW})
        (T := {y | ∃ b l : Fin 3, cmat y = matP 0 b l}) ⟨0, 0, by rw [map_one, cube_checks.2.2]⟩
        (by
          rintro x hx y ⟨b, l, hy⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact ⟨b + 1, l, by rw [map_mul, cmat_pT, hy, ← mmul_eq, left_t]⟩
          · refine ⟨b, l + 1, ?_⟩
            rw [map_mul, cmat_pW, hy, ← mmul_eq, left_w]
            simp) hy
      exact ⟨(b, l), Subtype.ext (cmat_injective (by rw [cmat_pElt, h]))⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem closure_tw_le : Subgroup.closure ({pT, pW} : Set ↥(cayleyGroup (ZMod 2))) ≤
    Subgroup.centralizer {pW} := by
  rw [Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact cmat_injective (by rw [map_mul, map_mul, cmat_pW, cmat_pT, ← mmul_eq, ← mmul_eq,
      central_t.2])
  · rfl

theorem factorization_card_centralizer_pW_lt (hcard : Nat.card ↥(cayleyGroup (ZMod 2)) = 12096) :
    (Nat.card (Subgroup.centralizer {pW})).factorization 3 < 3 := by
  have := finite_cayley
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwP : pW ∈ (sylowP0 hcard : Subgroup ↥(cayleyGroup (ZMod 2))) :=
    Subgroup.subset_closure (by simp)
  have hxp : IsPGroup 3 (Subgroup.zpowers pW) :=
    (sylowP0 hcard).isPGroup'.to_le (Subgroup.zpowers_le.mpr hwP)
  have h := factorization_card_centralizer_lt (sylowP0 hcard) hxp ?_
  · rwa [hcard, factorization_12096] at h
  intro g hg hcent
  obtain ⟨a, b, l, hab⟩ := exists_pElt_of_mem hg
  have hcomm : ∀ z ∈ ({pS, pT, pW} : Set ↥(cayleyGroup (ZMod 2))),
      mmul (matP a b l) (cmat z) = mmul (cmat z) (matP a b l) := by
    intro z hz
    have h1 := hcent z (Subgroup.subset_closure hz)
    rw [hab] at h1
    have h2 := congrArg cmat h1
    rw [map_mul, map_mul, cmat_pElt] at h2
    rw [mmul_eq, mmul_eq]
    exact h2.symm
  have htr : mtr (matP a b l) = 0 := by
    rw [mtr_eq, ← cmat_pElt, ← hab, trace_cmat_conj, cmat_pW, ← mtr_eq]
    exact trace_w.1
  have h1 := center_trace a b l
    (by simpa [cmat_pS] using hcomm pS (by simp))
    (by simpa [cmat_pT] using hcomm pT (by simp))
    (by simpa [cmat_pW] using hcomm pW (by simp)) htr
  apply trace_w.2
  have e : g⁻¹ * pW * g = 1 := cmat_injective (by rw [hab, cmat_pElt, h1, map_one])
  have e2 : pW = 1 := by
    calc pW = g * (g⁻¹ * pW * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  rw [← cmat_pW, e2, map_one]

theorem factorization_card_centralizer_m0 (hcard : Nat.card ↥(cayleyGroup (ZMod 2)) = 12096) :
    (Nat.card (Subgroup.centralizer {m0})).factorization 3 = 2 := by
  have := finite_cayley
  have hc := conj_pElt 0 0 1 (by decide)
  have hpe : pElt 0 0 1 = pW := by simp [pElt]
  rw [hpe] at hc
  have hm0 : m0 = wordEval gens8 [5, 0, 4, 0, 1] * pW * (wordEval gens8 [5, 0, 4, 0, 1])⁻¹ := by
    have : (conjTable 0 0 1).1 = [5, 0, 4, 0, 1] := rfl
    have h2 : tgt (conjTable 0 0 1).2 = m0 := rfl
    rw [this, h2] at hc
    rw [hc, mul_inv_cancel_right]
  rw [hm0, card_centralizer_conj]
  have hpos : Nat.card (Subgroup.centralizer {pW}) ≠ 0 := Nat.card_pos.ne'
  have hlt := factorization_card_centralizer_pW_lt hcard
  have hge : 2 ≤ (Nat.card (Subgroup.centralizer {pW})).factorization 3 := by
    rw [← Nat.prime_three.pow_dvd_iff_le_factorization hpos]
    have h9 := Subgroup.card_dvd_of_le closure_tw_le
    rw [card_closure_tw] at h9
    exact h9
  omega

end Cayley

end CFSG.RankThree.PartTwo.Sec8.Hering88N.G2Two

end

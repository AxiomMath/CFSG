module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

theorem perm3_facts : ∀ σ τ : Equiv.Perm (Fin 3), (σ ^ 3 = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ τ ≠ σ ∧
    τ ≠ σ ^ 2) → τ ^ 2 = 1 ∧ σ * τ = τ * σ⁻¹ := by
  decide

theorem perm3_cover : ∀ σ τ : Equiv.Perm (Fin 3), (σ ^ 3 = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ τ ≠ σ ∧
    τ ≠ σ ^ 2) → ∀ ρ : Equiv.Perm (Fin 3),
      ρ ∈ ({1, σ, σ ^ 2, τ, τ * σ, τ * σ ^ 2} : Finset (Equiv.Perm (Fin 3))) := by
  decide

section Linear

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_mul_pow (g x y : G) (i j : ℕ) :
    g * (x ^ i * y ^ j) * g⁻¹ = (g * x * g⁻¹) ^ i * (g * y * g⁻¹) ^ j := by
  rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow, map_pow]

omit [Finite G] in
theorem conj_mul_pow (g x y : G) (j : ℕ) :
    g * (x * y ^ j) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) ^ j := by
  simp

omit [Finite G] in
theorem conj_pow_eq_of_conj_eq {v x : G} (h : v * x * v⁻¹ = x) (m : ℕ) :
    v ^ m * x * (v ^ m)⁻¹ = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc v ^ (m + 1) * x * (v ^ (m + 1))⁻¹ = v ^ m * (v * x * v⁻¹) * (v ^ m)⁻¹ := by
          rw [pow_succ]
          group
      _ = x := by rw [h, ih]

omit [Finite G] in
theorem conj_pow_eq_mul_pow {v x d : G} (hvd : v * d * v⁻¹ = d) {k : ℕ}
    (hvx : v * x * v⁻¹ = x * d ^ k) (m : ℕ) : v ^ m * x * (v ^ m)⁻¹ = x * d ^ (k * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc v ^ (m + 1) * x * (v ^ (m + 1))⁻¹ = v * (v ^ m * x * (v ^ m)⁻¹) * v⁻¹ := by
          rw [pow_succ']
          group
      _ = (v * x * v⁻¹) * (v * d * v⁻¹) ^ (k * m) := by
          rw [ih, ← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow]
      _ = x * d ^ (k * (m + 1)) := by
          rw [hvx, hvd, mul_assoc, ← pow_add]
          congr 2
          ring

omit [Finite G] in
theorem exists_pow_conj_eq {v x d : G} (hd3 : d ^ 3 = 1) (hvd : v * d * v⁻¹ = d) {k : ℕ}
    (hk : k < 3) (hk0 : k ≠ 0) (hvx : v * x * v⁻¹ = x * d ^ k) :
    ∀ β < 3, ∃ m : ℕ, v ^ m * x * (v ^ m)⁻¹ = x * d ^ β := by
  intro β hβ
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exact ⟨β, by rw [conj_pow_eq_mul_pow hvd hvx, one_mul]⟩
  · refine ⟨(2 * β) % 3, ?_⟩
    rw [conj_pow_eq_mul_pow hvd hvx, Item21LateProof.pow_eq_pow_mod_three hd3 (2 * ((2 * β) % 3)),
      show 2 * ((2 * β) % 3) % 3 = β by omega]

theorem exists_basis_repr {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {x δ γ : G} (hxA : x ∈ A)
    (hδA : δ ∈ A) (hγA : γ ∈ A)
    (hB9 : Nat.card (Subgroup.zpowers δ ⊔ Subgroup.zpowers γ : Subgroup G) = 9)
    (hxB : x ∉ Subgroup.zpowers δ ⊔ Subgroup.zpowers γ) :
    ∀ y ∈ A, ∃ m : ℕ, ∃ j : ℕ, ∃ i : ℕ, y = x ^ m * (δ ^ j * γ ^ i) := by
  intro y hy
  have hBA : Subgroup.zpowers δ ⊔ Subgroup.zpowers γ ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hδA) (Subgroup.zpowers_le.mpr hγA)
  obtain ⟨m, -, b, hb, rfl⟩ := Item21LateProof.exists_pow_mul_of_card hcomm h3 hBA
    (by rw [h27, hB9]) hxA hxB y hy
  obtain ⟨j, -, i, -, rfl⟩ := Item21Late2Proof.exists_pow_mul_pow_of_mem_sup
    (hcomm δ hδA γ hγA) (h3 δ hδA) (h3 γ hγA) hb
  exact ⟨m, j, i, rfl⟩

theorem closure_basis_eq_top {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {x δ γ : G} (hxA : x ∈ A)
    (hδA : δ ∈ A) (hγA : γ ∈ A)
    (hB9 : Nat.card (Subgroup.zpowers δ ⊔ Subgroup.zpowers γ : Subgroup G) = 9)
    (hxB : x ∉ Subgroup.zpowers δ ⊔ Subgroup.zpowers γ) :
    Subgroup.closure ({⟨x, hxA⟩, ⟨δ, hδA⟩, ⟨γ, hγA⟩} : Set A) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, j, i, hy⟩ := exists_basis_repr hcomm h3 h27 hxA hδA hγA hB9 hxB y y.2
  have e : y = (⟨x, hxA⟩ : A) ^ m * ((⟨δ, hδA⟩ : A) ^ j * (⟨γ, hγA⟩ : A) ^ i) :=
    Subtype.ext (by simpa using hy)
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _))
  · simp
  · simp
  · simp

theorem conj_eq_of_fix_basis {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {c d a : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (haA : a ∈ A) (hB9 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c) {v : G} (hva : v * a * v⁻¹ = a)
    (hvd : v * d * v⁻¹ = d) (hvc : v * c * v⁻¹ = c) : ∀ y ∈ A, v * y * v⁻¹ = y := by
  intro y hyA
  obtain ⟨m, j, i, rfl⟩ := exists_basis_repr hcomm h3 h27 haA hdA hcA hB9 haB y hyA
  rw [show v * (a ^ m * (d ^ j * c ^ i)) * v⁻¹ =
      (v * a * v⁻¹) ^ m * ((v * d * v⁻¹) ^ j * (v * c * v⁻¹) ^ i) by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply,
      map_mul, map_mul, map_pow, map_pow, map_pow], hva, hvd, hvc]

omit [Finite G] in
theorem mem_trivOnQuot_of_closure {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {φ : MulAut A} {S : Set A}
    (hS : Subgroup.closure S = ⊤) (h : ∀ x ∈ S, ((x⁻¹ * φ x : A) : G) ∈ B) :
    φ ∈ trivOnQuot A B := by
  have hcA : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  let H : Subgroup A :=
    { carrier := {x | ((x⁻¹ * φ x : A) : G) ∈ B}
      mul_mem' := by
        intro x y hx hy
        have e : (x * y)⁻¹ * φ (x * y) = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by
          rw [map_mul, mul_inv_rev]
          calc y⁻¹ * x⁻¹ * (φ x * φ y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by group
            _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by rw [hcA y⁻¹]
            _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by group
        show (((x * y)⁻¹ * φ (x * y) : A) : G) ∈ B
        rw [e, Subgroup.coe_mul]
        exact B.mul_mem hx hy
      one_mem' := by
        show (((1 : A)⁻¹ * φ 1 : A) : G) ∈ B
        simp
      inv_mem' := by
        intro x hx
        have e : x⁻¹⁻¹ * φ x⁻¹ = (x⁻¹ * φ x)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, hcA]
        show ((x⁻¹⁻¹ * φ x⁻¹ : A) : G) ∈ B
        rw [e, Subgroup.coe_inv]
        exact B.inv_mem hx }
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).mpr h
  rw [hS] at hle
  intro x
  exact hle (Subgroup.mem_top x)

theorem mem_trivOnQuot_of_inverts {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {γ δ : G} (hγA : γ ∈ A) (hδA : δ ∈ A)
    (hδ1 : δ ≠ 1) (hγδ : γ ∉ Subgroup.zpowers δ) {w t : G}
    (htN : t ∈ Subgroup.normalizer (A : Set G))
    (hwγ : w * γ * w⁻¹ = γ) (hwδ : w * δ * w⁻¹ = δ)
    (hwA : ∀ y ∈ A, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers δ)
    (hwmove : ∃ y ∈ A, w * y * w⁻¹ ≠ y) (htγ : t * γ * t⁻¹ = γ) (htδ : t * δ * t⁻¹ = δ⁻¹)
    (ht2 : ∀ y ∈ A, t * (t * y * t⁻¹) * t⁻¹ = y)
    (hwt : ∀ y ∈ A, w * (t * y * t⁻¹) * w⁻¹ = t * (w⁻¹ * y * w) * t⁻¹) :
    A.normalizerMonoidHom ⟨t, htN⟩ ∈ trivOnQuot A (Subgroup.zpowers δ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hδ3 := h3 δ hδA
  have hγ3 := h3 γ hγA
  set B := Subgroup.zpowers δ ⊔ Subgroup.zpowers γ with hB
  have hB9 : Nat.card B = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hcomm δ hδA γ hγA) hδ3 hγ3 hδ1 hγδ
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hδA) (Subgroup.zpowers_le.mpr hγA)
  have hwB : ∀ y ∈ B, w * y * w⁻¹ = y := by
    intro y hy
    obtain ⟨j, -, i, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm δ hδA γ hγA) hδ3 hγ3 hy
    rw [conj_pow_mul_pow, hwδ, hwγ]
  obtain ⟨x, hxA, hx⟩ := hwmove
  have hxB : x ∉ B := fun h => hx (hwB x h)
  have hδk : ∀ k : ℕ, δ ^ k ∈ A := fun k => Subgroup.pow_mem _ hδA k
  obtain ⟨k, hk, hkx⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hδ3 (hwA x hxA)
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hx
    rw [pow_zero, inv_mul_eq_one] at hkx
    exact hkx.symm
  have hδk1 : δ ^ k ≠ 1 := by
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · rwa [pow_one]
    · rw [Item21LateProof.sq_eq_inv_of_pow_three hδ3]
      exact inv_ne_one.mpr hδ1
  have hwx : w * x * w⁻¹ = x * δ ^ k := by
    rw [← hkx]
    group
  have hwx' : w⁻¹ * x * w = x * (δ ^ k)⁻¹ := by
    have hwδk : w⁻¹ * δ ^ k * w = δ ^ k := by
      calc w⁻¹ * δ ^ k * w = w⁻¹ * (w * δ ^ k * w⁻¹) * w := by
            rw [hwB _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) k))]
        _ = δ ^ k := by group
    have e : x = (w⁻¹ * x * w) * δ ^ k := by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = w⁻¹ * (x * δ ^ k) * w := by rw [hwx]
        _ = (w⁻¹ * x * w) * (w⁻¹ * δ ^ k * w) := by group
        _ = (w⁻¹ * x * w) * δ ^ k := by rw [hwδk]
    calc w⁻¹ * x * w = (w⁻¹ * x * w) * δ ^ k * (δ ^ k)⁻¹ := by group
      _ = x * (δ ^ k)⁻¹ := by rw [← e]
  have htxA : t * x * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htN x).mp hxA
  obtain ⟨ε, hε, b, hbB, hεb⟩ := Item21LateProof.exists_pow_mul_of_card hcomm h3 hBA
    (by rw [h27, hB9]) hxA hxB _ htxA
  have hbA : b ∈ A := hBA hbB
  have e1 : w * (t * x * t⁻¹) * w⁻¹ = x ^ ε * δ ^ (k * ε) * b := by
    rw [hεb, show w * (x ^ ε * b) * w⁻¹ = (w * x * w⁻¹) ^ ε * (w * b * w⁻¹) by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow],
      hwx, hwB b hbB, (Commute.mul_pow (hcomm x hxA _ (hδk k)) ε), ← pow_mul, mul_comm k ε]
  have e2 : w * (t * x * t⁻¹) * w⁻¹ = (t * x * t⁻¹) * δ ^ k := by
    rw [hwt x hxA, hwx', show t * (x * (δ ^ k)⁻¹) * t⁻¹ =
        (t * x * t⁻¹) * ((t * δ * t⁻¹) ^ k)⁻¹ by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_inv,
        map_pow], htδ, inv_pow, inv_inv]
  rw [e1, hεb] at e2
  have e3 : δ ^ (k * ε) = δ ^ k := by
    have hbδ : b * δ ^ k = δ ^ k * b := hcomm b hbA _ (hδk k)
    rw [mul_assoc, mul_assoc, hbδ] at e2
    exact mul_right_cancel (mul_left_cancel e2)
  have hε1 : ε = 1 := by
    interval_cases ε
    · exfalso
      rw [mul_zero, pow_zero] at e3
      exact hδk1 e3.symm
    · rfl
    · exfalso
      rw [mul_two, pow_add] at e3
      exact hδk1 (mul_eq_left.mp e3)
  rw [hε1, pow_one] at hεb
  obtain ⟨j, -, i, hi, hbji⟩ :=
    Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm δ hδA γ hγA) hδ3 hγ3 hbB
  have e4 : t * (t * x * t⁻¹) * t⁻¹ = x * b * (δ⁻¹ ^ j * γ ^ i) := by
    rw [hεb, show t * (x * b) * t⁻¹ = (t * x * t⁻¹) * (t * b * t⁻¹) by group, hεb, hbji,
      conj_pow_mul_pow, htδ, htγ]
  rw [ht2 x hxA] at e4
  have e5 : b * (δ⁻¹ ^ j * γ ^ i) = 1 := by
    have e6 := e4
    rw [mul_assoc] at e6
    exact (mul_eq_left.mp e6.symm)
  have hγi : γ ^ i * γ ^ i = 1 := by
    rw [hbji] at e5
    have hc : Commute (γ ^ i) (δ⁻¹ ^ j) :=
      Commute.pow_pow (Commute.inv_right (show Commute γ δ from hcomm γ hγA δ hδA)) i j
    calc γ ^ i * γ ^ i = δ ^ j * (γ ^ i * δ⁻¹ ^ j) * γ ^ i := by
          rw [hc.eq, inv_pow]
          group
      _ = 1 := by rw [← e5]; group
  have hi0 : i = 0 := by
    interval_cases i
    · rfl
    · exfalso
      rw [pow_one] at hγi
      have hγ1 : γ ≠ 1 := fun h => hγδ (h ▸ Subgroup.one_mem _)
      apply hγ1
      calc γ = γ ^ 3 * (γ * γ)⁻¹ := by group
        _ = 1 := by rw [hγ3, hγi]; group
    · exfalso
      have hγ1 : γ ≠ 1 := fun h => hγδ (h ▸ Subgroup.one_mem _)
      apply hγ1
      calc γ = γ ^ 2 * γ ^ 2 * (γ ^ 3)⁻¹ := by group
        _ = 1 := by rw [hγi, hγ3]; group
  have hxδ : x⁻¹ * (t * x * t⁻¹) ∈ Subgroup.zpowers δ := by
    rw [hεb, hbji, hi0, pow_zero, mul_one, inv_mul_cancel_left]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) j
  have hxB' : x ∉ Subgroup.zpowers δ ⊔ Subgroup.zpowers γ := hxB
  refine mem_trivOnQuot_of_closure hcomm
    (closure_basis_eq_top hcomm h3 h27 hxA hδA hγA hB9 hxB') ?_
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    exact hxδ
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    show δ⁻¹ * (t * δ * t⁻¹) ∈ Subgroup.zpowers δ
    rw [htδ]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers δ))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers δ))
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    show γ⁻¹ * (t * γ * t⁻¹) ∈ Subgroup.zpowers δ
    rw [htγ, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem le_trivOnQuot_of_perm3 {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {S : Subgroup (MulAut A)}
    (eS : S ≃* Equiv.Perm (Fin 3)) {γ δ : G} (hγA : γ ∈ A) (hδA : δ ∈ A) (hδ1 : δ ≠ 1)
    (hγδ : γ ∉ Subgroup.zpowers δ) {w t : G} (hwN : w ∈ Subgroup.normalizer (A : Set G))
    (htN : t ∈ Subgroup.normalizer (A : Set G)) (hwS : A.normalizerMonoidHom ⟨w, hwN⟩ ∈ S)
    (htS : A.normalizerMonoidHom ⟨t, htN⟩ ∈ S) (hw3 : w ^ 3 = 1) (hwγ : w * γ * w⁻¹ = γ)
    (hwδ : w * δ * w⁻¹ = δ) (hwA : ∀ y ∈ A, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers δ)
    (hwmove : ∃ y ∈ A, w * y * w⁻¹ ≠ y) (htγ : t * γ * t⁻¹ = γ) (htδ : t * δ * t⁻¹ = δ⁻¹) :
    S ≤ trivOnQuot A (Subgroup.zpowers δ) := by
  set W := A.normalizerMonoidHom ⟨w, hwN⟩ with hW
  set T := A.normalizerMonoidHom ⟨t, htN⟩ with hT
  have hWapp : ∀ y : A, ((W y : A) : G) = w * y * w⁻¹ := fun y => rfl
  have hTapp : ∀ y : A, ((T y : A) : G) = t * y * t⁻¹ := fun y => rfl
  have hWi : ∀ y : A, ((W⁻¹ y : A) : G) = w⁻¹ * y * w := by
    intro y
    have e1 : W⁻¹ = A.normalizerMonoidHom ⟨w⁻¹, Subgroup.inv_mem _ hwN⟩ := by
      rw [hW, ← map_inv]
      rfl
    rw [e1, Sec4.normalizerMonoidHom_apply_coe, inv_inv]
  have hWZ : W ∈ trivOnQuot A (Subgroup.zpowers δ) := fun y => by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hWapp]
    exact hwA y y.2
  have hd3 : δ ^ 3 = 1 := h3 δ hδA
  have hδδ : (⟨δ, hδA⟩ : A)⁻¹ ≠ ⟨δ, hδA⟩ := by
    intro h
    have h1 : δ⁻¹ = δ := congrArg Subtype.val h
    have h2 : δ * δ = 1 := by
      calc δ * δ = δ * δ⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel δ
    apply hδ1
    calc δ = δ ^ 3 * (δ * δ)⁻¹ := by group
      _ = 1 := by rw [hd3, h2]; group
  have hWδ : W ⟨δ, hδA⟩ = ⟨δ, hδA⟩ := Subtype.ext (by rw [hWapp]; exact hwδ)
  have hTδ : T ⟨δ, hδA⟩ = (⟨δ, hδA⟩ : A)⁻¹ := Subtype.ext (by rw [hTapp]; exact htδ)
  set σ := eS ⟨W, hwS⟩ with hσ
  set τ := eS ⟨T, htS⟩ with hτ
  have hσ3 : σ ^ 3 = 1 := by
    have e1 : (⟨w, hwN⟩ : Subgroup.normalizer (A : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hw3)
    have hW3' : W ^ 3 = 1 := by
      calc W ^ 3 = A.normalizerMonoidHom (⟨w, hwN⟩ ^ 3) := (map_pow _ _ 3).symm
        _ = 1 := by rw [e1, map_one]
    have hW3 : (⟨W, hwS⟩ : S) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hW3')
    rw [hσ, ← map_pow, hW3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hW1' : (⟨W, hwS⟩ : S) = 1 := eS.injective (by rw [map_one]; exact h)
    have hW1 : W = 1 := congrArg Subtype.val hW1'
    obtain ⟨y, hyA, hy⟩ := hwmove
    apply hy
    have e1 := congrArg (fun φ : MulAut A => ((φ ⟨y, hyA⟩ : A) : G)) hW1
    simpa [hWapp] using e1
  have hτ1 : τ ≠ 1 := by
    intro h
    have hT1' : (⟨T, htS⟩ : S) = 1 := eS.injective (by rw [map_one]; exact h)
    have hT1 : T = 1 := congrArg Subtype.val hT1'
    apply hδδ
    rw [← hTδ, hT1]
    rfl
  have hτσ : τ ≠ σ := by
    intro h
    have hTW : T = W := congrArg Subtype.val (eS.injective h)
    apply hδδ
    rw [← hTδ, hTW, hWδ]
  have hτσ2 : τ ≠ σ ^ 2 := by
    intro h
    have hTW : T = W ^ 2 := by
      have e1 := eS.injective (h.trans (map_pow eS ⟨W, hwS⟩ 2).symm)
      have e2 := congrArg Subtype.val e1
      rwa [Subgroup.coe_pow] at e2
    apply hδδ
    rw [← hTδ, hTW, pow_two, MulAut.mul_apply, hWδ, hWδ]
  have hfacts : σ ^ 3 = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ τ ≠ σ ∧ τ ≠ σ ^ 2 := ⟨hσ3, hσ1, hτ1, hτσ, hτσ2⟩
  obtain ⟨hτ2, hστ⟩ := perm3_facts σ τ hfacts
  have hcov := perm3_cover σ τ hfacts
  have hT2 : T ^ 2 = 1 := by
    have e1 : (⟨T, htS⟩ : S) ^ 2 = 1 := eS.injective (by rw [map_pow, ← hτ, hτ2, map_one])
    have e2 := congrArg Subtype.val e1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at e2
  have hWT : W * T = T * W⁻¹ := by
    have e1 : (⟨W, hwS⟩ : S) * ⟨T, htS⟩ = ⟨T, htS⟩ * (⟨W, hwS⟩ : S)⁻¹ :=
      eS.injective (by rw [map_mul, map_mul, map_inv, ← hσ, ← hτ, hστ])
    have e2 := congrArg Subtype.val e1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at e2
  have ht2 : ∀ y ∈ A, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y hy
    have e1 := congrArg (fun φ : MulAut A => ((φ ⟨y, hy⟩ : A) : G)) hT2
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at e1
    rw [hTapp, hTapp] at e1
    exact e1
  have hwt : ∀ y ∈ A, w * (t * y * t⁻¹) * w⁻¹ = t * (w⁻¹ * y * w) * t⁻¹ := by
    intro y hy
    have e1 := congrArg (fun φ : MulAut A => ((φ ⟨y, hy⟩ : A) : G)) hWT
    simp only [MulAut.mul_apply] at e1
    rw [hWapp, hTapp, hTapp, hWi] at e1
    exact e1
  have hTZ : T ∈ trivOnQuot A (Subgroup.zpowers δ) :=
    mem_trivOnQuot_of_inverts hcomm h3 h27 hγA hδA hδ1 hγδ htN hwγ hwδ hwA hwmove htγ htδ ht2
      hwt
  intro φ hφ
  have hmem := hcov (eS ⟨φ, hφ⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have key : ∀ ψ : S, eS ⟨φ, hφ⟩ = eS ψ → φ = ψ := fun ψ h =>
    congrArg Subtype.val (eS.injective h)
  rcases hmem with h | h | h | h | h | h
  · rw [key 1 (by rw [h, map_one])]
    exact one_mem _
  · rw [key ⟨W, hwS⟩ h]
    exact hWZ
  · rw [key (⟨W, hwS⟩ ^ 2) (by rw [h, map_pow]), Subgroup.coe_pow]
    exact pow_mem hWZ 2
  · rw [key ⟨T, htS⟩ h]
    exact hTZ
  · rw [key (⟨T, htS⟩ * ⟨W, hwS⟩) (by rw [h, map_mul]), Subgroup.coe_mul]
    exact mul_mem hTZ hWZ
  · rw [key (⟨T, htS⟩ * ⟨W, hwS⟩ ^ 2) (by rw [h, map_mul, map_pow]), Subgroup.coe_mul,
      Subgroup.coe_pow]
    exact mul_mem hTZ (pow_mem hWZ 2)

theorem exists_eq_mul_of_mem_trivOnQuot {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27)
    {c d a : G} (hcA : c ∈ A) (hdA : d ∈ A) (haA : a ∈ A)
    (hB9 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c) {w w' : G}
    (hwN : w ∈ Subgroup.normalizer (A : Set G)) (hw'N : w' ∈ Subgroup.normalizer (A : Set G))
    (hwc : w * c * w⁻¹ = c) (hwd : w * d * w⁻¹ = d) {k₁ : ℕ} (hk₁ : k₁ < 3) (hk₁0 : k₁ ≠ 0)
    (hwa : w * a * w⁻¹ = a * d ^ k₁) (hw'a : w' * a * w'⁻¹ = a) (hw'd : w' * d * w'⁻¹ = d)
    {k₂ : ℕ} (hk₂ : k₂ < 3) (hk₂0 : k₂ ≠ 0) (hw'c : w' * c * w'⁻¹ = c * d ^ k₂) {φ : MulAut A}
    (hφ : φ ∈ trivOnQuot A (Subgroup.zpowers d)) (hφd : φ ⟨d, hdA⟩ = ⟨d, hdA⟩) :
    ∃ m₁ m₂ : ℕ, φ = A.normalizerMonoidHom ⟨w' ^ m₂, Subgroup.pow_mem _ hw'N m₂⟩ *
      A.normalizerMonoidHom ⟨w ^ m₁, Subgroup.pow_mem _ hwN m₁⟩ := by
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hclos := closure_basis_eq_top hcomm h3 h27 haA hdA hcA hB9 haB
  obtain ⟨β, hβ, hβe⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hφ ⟨a, haA⟩)
  obtain ⟨α, hα, hαe⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hφ ⟨c, hcA⟩)
  have hφa : ((φ ⟨a, haA⟩ : A) : G) = a * d ^ β := by
    rw [← hβe, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hφc : ((φ ⟨c, hcA⟩ : A) : G) = c * d ^ α := by
    rw [← hαe, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨m₁, hm₁⟩ := exists_pow_conj_eq hd3 hwd hk₁ hk₁0 hwa β hβ
  obtain ⟨m₂, hm₂⟩ := exists_pow_conj_eq hd3 hw'd hk₂ hk₂0 hw'c α hα
  refine ⟨m₁, m₂, ?_⟩
  have hw'm_a : w' ^ m₂ * a * (w' ^ m₂)⁻¹ = a := conj_pow_eq_of_conj_eq hw'a m₂
  have hw'm_d : w' ^ m₂ * d * (w' ^ m₂)⁻¹ = d := conj_pow_eq_of_conj_eq hw'd m₂
  have hwm_d : w ^ m₁ * d * (w ^ m₁)⁻¹ = d := conj_pow_eq_of_conj_eq hwd m₁
  have hwm_c : w ^ m₁ * c * (w ^ m₁)⁻¹ = c := conj_pow_eq_of_conj_eq hwc m₁
  apply MulEquiv.toMonoidHom_injective
  refine MonoidHom.eq_of_eqOn_dense hclos ?_
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  apply Subtype.ext
  simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  rcases hy with rfl | rfl | rfl
  · rw [hφa, Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe, hm₁,
      conj_mul_pow, hw'm_a, hw'm_d]
  · rw [hφd, Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe, hwm_d,
      hw'm_d]
  · rw [hφc, Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe, hwm_c, hm₂]

theorem trivOnQuot_le {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {c d a : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (haA : a ∈ A) (hd1 : d ≠ 1)
    (hB9 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c) {S : Subgroup (MulAut A)} {w w' t : G}
    (hwN : w ∈ Subgroup.normalizer (A : Set G)) (hw'N : w' ∈ Subgroup.normalizer (A : Set G))
    (htN : t ∈ Subgroup.normalizer (A : Set G)) (hwS : A.normalizerMonoidHom ⟨w, hwN⟩ ∈ S)
    (hw'S : A.normalizerMonoidHom ⟨w', hw'N⟩ ∈ S) (htS : A.normalizerMonoidHom ⟨t, htN⟩ ∈ S)
    (hwc : w * c * w⁻¹ = c) (hwd : w * d * w⁻¹ = d)
    (hwA : ∀ y ∈ A, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers d) (hwmove : ∃ y ∈ A, w * y * w⁻¹ ≠ y)
    (hw'a : w' * a * w'⁻¹ = a) (hw'd : w' * d * w'⁻¹ = d)
    (hw'A : ∀ y ∈ A, y⁻¹ * (w' * y * w'⁻¹) ∈ Subgroup.zpowers d)
    (hw'move : ∃ y ∈ A, w' * y * w'⁻¹ ≠ y) (htd : t * d * t⁻¹ = d⁻¹)
    (htZ : A.normalizerMonoidHom ⟨t, htN⟩ ∈ trivOnQuot A (Subgroup.zpowers d)) :
    trivOnQuot A (Subgroup.zpowers d) ≤ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hBA : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr hcA)
  have hcd : c ∉ Subgroup.zpowers d := by
    intro h
    have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ Subgroup.zpowers d :=
      sup_le le_rfl (Subgroup.zpowers_le.mpr h)
    have h1 := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers, orderOf_eq_prime hd3 hd1] at h1
    norm_num at h1
  have hdc9 : Nat.card A = 3 * Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) := by
    rw [h27, hB9]
  obtain ⟨k₁, hk₁, hk₁e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA a haA)
  have hwa : w * a * w⁻¹ = a * d ^ k₁ := by
    rw [← hk₁e]
    group
  have hk₁0 : k₁ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hwa
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hwa hwd hwc y hyA)
  obtain ⟨k₂, hk₂, hk₂e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hw'A c hcA)
  have hw'c : w' * c * w'⁻¹ = c * d ^ k₂ := by
    rw [← hk₂e]
    group
  have hk₂0 : k₂ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw'c
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hw'a hw'd hw'c y hyA)
  have hclos := closure_basis_eq_top hcomm h3 h27 haA hdA hcA hB9 haB
  have hfix : ∀ φ ∈ trivOnQuot A (Subgroup.zpowers d), φ ⟨d, hdA⟩ = ⟨d, hdA⟩ → φ ∈ S := by
    intro φ hφ hφd
    obtain ⟨m₁, m₂, heq⟩ := exists_eq_mul_of_mem_trivOnQuot hcomm h3 h27 hcA hdA haA hB9 haB
      hwN hw'N hwc hwd hk₁ hk₁0 hwa hw'a hw'd hk₂ hk₂0 hw'c hφ hφd
    have hρS : A.normalizerMonoidHom ⟨w ^ m₁, Subgroup.pow_mem _ hwN m₁⟩ ∈ S := by
      have e1 : (⟨w ^ m₁, Subgroup.pow_mem _ hwN m₁⟩ : Subgroup.normalizer (A : Set G)) =
          ⟨w, hwN⟩ ^ m₁ := Subtype.ext (by rw [Subgroup.coe_pow])
      rw [e1, map_pow]
      exact pow_mem hwS m₁
    have hσS : A.normalizerMonoidHom ⟨w' ^ m₂, Subgroup.pow_mem _ hw'N m₂⟩ ∈ S := by
      have e1 : (⟨w' ^ m₂, Subgroup.pow_mem _ hw'N m₂⟩ : Subgroup.normalizer (A : Set G)) =
          ⟨w', hw'N⟩ ^ m₂ := Subtype.ext (by rw [Subgroup.coe_pow])
      rw [e1, map_pow]
      exact pow_mem hw'S m₂
    rw [heq]
    exact mul_mem hσS hρS
  intro φ hφ
  obtain ⟨r, hr, hre⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hφ ⟨d, hdA⟩)
  have hφd : ((φ ⟨d, hdA⟩ : A) : G) = d * d ^ r := by
    rw [← hre, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  interval_cases r
  ·
    exact hfix φ hφ (Subtype.ext (by rw [hφd, pow_zero, mul_one]))
  ·
    set T := A.normalizerMonoidHom ⟨t, htN⟩ with hT
    have hφT : φ * T ∈ S := by
      refine hfix (φ * T) (mul_mem hφ htZ) (Subtype.ext ?_)
      rw [MulAut.mul_apply]
      have e1 : T ⟨d, hdA⟩ = (⟨d, hdA⟩ : A)⁻¹ := Subtype.ext (by
        rw [hT, Sec4.normalizerMonoidHom_apply_coe]
        exact htd)
      rw [e1, map_inv, Subgroup.coe_inv, hφd, pow_one,
        show (d * d)⁻¹ = d * (d ^ 3)⁻¹ by group, hd3, inv_one, mul_one]
    have e2 : φ = (φ * T) * T⁻¹ := by group
    rw [e2]
    exact mul_mem hφT (inv_mem htS)
  ·
    exfalso
    apply hd1
    have e1 : φ ⟨d, hdA⟩ = 1 := Subtype.ext (by
      rw [hφd, show d * d ^ 2 = d ^ 3 by group, hd3, Subgroup.coe_one])
    have e2 : (⟨d, hdA⟩ : A) = 1 := by
      rw [← map_one φ] at e1
      exact φ.injective e1
    exact congrArg Subtype.val e2

omit [Finite G] in
theorem zpowers_eq_of_eq_or_eq_inv {d e : G} (h : d = e ∨ d = e⁻¹) :
    Subgroup.zpowers e = Subgroup.zpowers d := by
  rcases h with rfl | rfl
  · rfl
  · rw [Subgroup.zpowers_inv]

omit [Finite G] in
theorem conj_eq_inv_of_eq_or_eq_inv {d e v : G} (h : d = e ∨ d = e⁻¹)
    (hv : v * e * v⁻¹ = e⁻¹) : v * d * v⁻¹ = d⁻¹ := by
  rcases h with rfl | rfl
  · exact hv
  · rw [inv_inv, show v * e⁻¹ * v⁻¹ = (v * e * v⁻¹)⁻¹ by group, hv, inv_inv]

end Linear

end CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item2119EndProof

theorem item2124_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item2124 := by
  intro G _ _ A E U c L d U₀ a X hE h23
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, hw3, hwd₀, hwA, hwmove⟩, t,
    ⟨htL, htN⟩, htd₀⟩ := Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, hw'3, hw'd', hw'A, hw'move⟩, t',
    ⟨ht'X, ht'N⟩, ht'd'⟩ := Item21Late2Proof.frame_of h45 h66 hcfgX
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A a hpairs'.2.2.1)
  have hfixc : ∀ {y : G}, y ∈ L → y * c * y⁻¹ = c := fun hy => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hy), mul_inv_cancel_right]
  have hfixa : ∀ {y : G}, y ∈ X → y * a * y⁻¹ = a := fun hy => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hy), mul_inv_cancel_right]
  have hd₀ : d = d₀ ∨ d = d₀⁻¹ := hTU d hE.mem_d hd1 hE.type_d
  have hd' : d = d' ∨ d = d'⁻¹ := hTU' d ⟨hdA, hdX⟩ hd1 hdTX
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d := zpowers_eq_of_eq_or_eq_inv hd₀
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d := zpowers_eq_of_eq_or_eq_inv hd'
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  have htd : t * d * t⁻¹ = d⁻¹ := conj_eq_inv_of_eq_or_eq_inv hd₀ htd₀
  have ht'd : t' * d * t'⁻¹ = d⁻¹ := conj_eq_inv_of_eq_or_eq_inv hd' ht'd'
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have haCD := not_mem_sup_of_config2119End hE
  have had : a ∉ Subgroup.zpowers d := fun h => haCD (Subgroup.mem_sup_right h)
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact haCD
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
  obtain ⟨eS⟩ := hcfg.star
  obtain ⟨eSX⟩ := hS3'
  have hwS : A.normalizerMonoidHom ⟨w, hwN⟩ ∈ starOf A L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwL)
  have htS : A.normalizerMonoidHom ⟨t, htN⟩ ∈ starOf A L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htL)
  have hw'S : A.normalizerMonoidHom ⟨w', hw'N⟩ ∈ starOf A X :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw'X)
  have ht'S : A.normalizerMonoidHom ⟨t', ht'N⟩ ∈ starOf A X :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht'X)
  have hLle := le_trivOnQuot_of_perm3 hcomm h3 h27 eS hcA hdA hd1 hcd hwN htN hwS htS hw3
    (hfixc hwL) hwd hwA hwmove (hfixc htL) htd
  have hXle := le_trivOnQuot_of_perm3 hcomm h3 h27 eSX haA hdA hd1 had hw'N ht'N hw'S ht'S hw'3
    (hfixa hw'X) hw'd hw'A hw'move (hfixa ht'X) ht'd
  refine le_antisymm (sup_le hXle hLle) ?_
  exact trivOnQuot_le hcomm h3 h27 hcA hdA haA hd1 hB9 haB hwN hw'N htN
    (Subgroup.mem_sup_right hwS) (Subgroup.mem_sup_left hw'S) (Subgroup.mem_sup_right htS)
    (hfixc hwL) hwd hwA hwmove (hfixa hw'X) hw'd hw'A hw'move htd (hLle htS)

end CFSG.RankThree.PartTwo.Sec21

module

public import Mathlib

public section

namespace CFSG.Quasithin.H13.A6

open Matrix

namespace L32Comm

@[expose] def ut3 (x y z : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, x, y; 0, 1, z; 0, 0, 1]

@[expose] def cols3 (a b c : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => ![a, b, c] j i

theorem trace_core : ∀ a b c : Fin 3 → ZMod 2,
    (cols3 a b c * cols3 a b c * cols3 a b c = 1 ∧ cols3 a b c ≠ 1) →
      ∃ x y z : ZMod 2, trace (ut3 x y z * cols3 a b c * ut3 x (y + x * z) z *
        (cols3 a b c * cols3 a b c)) = 0 := by
  decide +kernel

theorem ut3_mul_inv : ∀ x y z : ZMod 2, ut3 x y z * ut3 x (y + x * z) z = 1 := by
  decide

theorem ut3_mul : ∀ x y z x' y' z' : ZMod 2,
    ut3 x y z * ut3 x' y' z' = ut3 (x + x') (y + y' + x * z') (z + z') := by
  decide

theorem det_ut3 (x y z : ZMod 2) : (ut3 x y z).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [ut3]
  ring

theorem eq_cols3 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    M = cols3 (fun i => M i 0) (fun i => M i 1) (fun i => M i 2) := by
  ext i j
  fin_cases j <;> rfl

theorem eq_one_of_add_three : ∀ t : ZMod 2, t + ((3 : ℕ) : ZMod 2) = 0 → t = 1 := by
  decide

theorem trace_eq_one_of_pow {W : Matrix (Fin 3) (Fin 3) (ZMod 2)} {k : ℕ}
    (hW : W ^ (2 ^ k) = 1) : trace W = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (W + 1) ^ (2 ^ k) = 0 := by
    rw [add_pow_char_pow_of_commute 2 k (Commute.one_right W), hW, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have h2 : IsNilpotent (trace (W + 1)) := isNilpotent_trace_of_isNilpotent ⟨_, h1⟩
  have h3 : trace (W + 1) = 0 := h2.eq_zero
  rw [trace_add, trace_one, Fintype.card_fin] at h3
  exact eq_one_of_add_three _ h3

@[expose] def utSL (x y z : ZMod 2) : SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨ut3 x y z, det_ut3 x y z⟩

theorem utSL_inv (x y z : ZMod 2) : (utSL x y z)⁻¹ = utSL x (y + x * z) z :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (ut3_mul_inv x y z))

@[expose] def U3 : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)) where
  carrier := {g | ∃ x y z : ZMod 2, g = utSL x y z}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, rfl⟩ ⟨x', y', z', rfl⟩
    exact ⟨x + x', y + y' + x * z', z + z', Subtype.ext (ut3_mul x y z x' y' z')⟩
  one_mem' := ⟨0, 0, 0, Subtype.ext (by decide)⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, rfl⟩
    exact ⟨x, y + x * z, z, utSL_inv x y z⟩

theorem card_U3 : Nat.card U3 = 8 := by
  let f : ZMod 2 × ZMod 2 × ZMod 2 → U3 := fun p => ⟨utSL p.1 p.2.1 p.2.2, p.1, p.2.1, p.2.2, rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
    have h' : ut3 x y z = ut3 x' y' z' :=
      congrArg (fun g : U3 => ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    have e1 : x = x' := congrFun (congrFun h' 0) 1
    have e2 : y = y' := congrFun (congrFun h' 0) 2
    have e3 : z = z' := congrFun (congrFun h' 1) 2
    rw [e1, e2, e3]
  have hsurj : Function.Surjective f := by
    rintro ⟨g, x, y, z, rfl⟩
    exact ⟨(x, y, z), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]

theorem exists_conj_U3 (hG : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168)
    {P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))} (hP : Nat.card P = 8) :
    ∃ g : SpecialLinearGroup (Fin 3) (ZMod 2), ∀ u ∈ U3, g * u * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ H : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)), Nat.card H = 8 →
      ¬ 2 ∣ H.index := by
    intro H hH h2
    have := H.card_mul_index
    rw [hH, hG] at this
    omega
  have hU : IsPGroup 2 U3 := IsPGroup.of_card (n := 3) (by rw [card_U3]; norm_num)
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) (ZMod 2))
    (hU.toSylow (hidx _ card_U3)) (hP2.toSylow (hidx _ hP))
  refine ⟨g, fun u hu => ?_⟩
  have h1 : g * u * g⁻¹ ∈ ((g • hU.toSylow (hidx _ card_U3) : Sylow 2 _) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) (hU.toSylow (hidx _ card_U3)) hu
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [hg] at h1
  exact h1

theorem coe_pow_eq_one {g : SpecialLinearGroup (Fin 3) (ZMod 2)} {m : ℕ} (h : g ^ m = 1) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ m = 1 :=
  congrArg (fun A : SpecialLinearGroup (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) h

theorem exists_comm_trace (x : SpecialLinearGroup (Fin 3) (ZMod 2)) (h3 : x ^ 3 = 1)
    (h1 : x ≠ 1) : ∃ u ∈ U3, ∀ k : ℕ, (u * x * u⁻¹ * x⁻¹) ^ (2 ^ k) ≠ 1 := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = M := ⟨_, rfl⟩
  have hM3 : M * M * M = 1 := by
    rw [← hM, ← pow_three']
    exact coe_pow_eq_one h3
  have hM1 : M ≠ 1 := fun h => h1 (Subtype.ext (hM.trans h))
  rw [eq_cols3 M] at hM3 hM1
  obtain ⟨p, q, r, hpqr⟩ := trace_core _ _ _ ⟨hM3, hM1⟩
  rw [← eq_cols3 M] at hpqr
  refine ⟨utSL p q r, ⟨p, q, r, rfl⟩, fun k hk => ?_⟩
  have hxinv : x⁻¹ = x * x :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact h3)
  have hW : ((utSL p q r * x * (utSL p q r)⁻¹ * x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = ut3 p q r * M * ut3 p (q + p * r) r * (M * M) := by
    rw [utSL_inv, hxinv, ← hM]
    rfl
  have h2 := trace_eq_one_of_pow (coe_pow_eq_one hk)
  rw [hW, hpqr] at h2
  exact absurd h2 (by decide)

theorem exists_comm_not_two {Y : Type*} [Group Y] (e : Y ≃* SpecialLinearGroup (Fin 3) (ZMod 2))
    (hY : Nat.card Y = 168) {P : Subgroup Y} (hP : Nat.card P = 8) {a : Y} (h3 : a ^ 3 = 1)
    (h1 : a ≠ 1) : ∃ p ∈ P, ∀ k : ℕ, (p * a * p⁻¹ * a⁻¹) ^ (2 ^ k) ≠ 1 := by
  have hG : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 :=
    (Nat.card_congr e.toEquiv).symm.trans hY
  have hP' : Nat.card (P.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hP
  obtain ⟨g, hg⟩ := exists_conj_U3 hG hP'
  set x := g⁻¹ * e a * g with hx
  have hx3 : x ^ 3 = 1 := by
    have : x = g⁻¹ * e a * g⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, ← map_pow, h3, map_one, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    intro h
    apply h1
    have : e a = 1 := by
      calc e a = g * x * g⁻¹ := by rw [hx]; group
        _ = 1 := by rw [h, mul_one, mul_inv_cancel]
    exact e.injective (this.trans (map_one e).symm)
  obtain ⟨u, hu, hnot⟩ := exists_comm_trace x hx3 hx1
  obtain ⟨p, hp, hpe⟩ := hg u hu
  refine ⟨p, hp, fun k hk => hnot k ?_⟩
  have hpe' : e p = g * u * g⁻¹ := hpe
  have key : e (p * a * p⁻¹ * a⁻¹) = g * (u * x * u⁻¹ * x⁻¹) * g⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpe', hx]
    group
  have h2 : (g * (u * x * u⁻¹ * x⁻¹) * g⁻¹) ^ (2 ^ k) = 1 := by
    rw [← key, ← map_pow, hk, map_one]
  rw [conj_pow] at h2
  calc (u * x * u⁻¹ * x⁻¹) ^ (2 ^ k)
      = g⁻¹ * (g * (u * x * u⁻¹ * x⁻¹) ^ (2 ^ k) * g⁻¹) * g := by group
    _ = 1 := by rw [h2, mul_one, inv_mul_cancel]

section Pair

variable {Q : Type*} [Group Q]

theorem eq_one_of_pow_of_cube {z : Q} {k : ℕ} (hk : z ^ (2 ^ k) = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  have h1 : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h3)
  have h2 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem exists_pow_of_isPGroup {N : Subgroup Q} (hN : IsPGroup 2 N) {n : Q} (hn : n ∈ N) :
    ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem cube_mem_of_conj {X N : Subgroup Q} (hXN : X ≤ Subgroup.normalizer (N : Set Q)) {g : Q}
    (hg : g ∈ X) (hg3 : g ^ 3 = 1) {n : Q} (hn : n ∈ N) : (g * n) ^ 3 ∈ N := by
  have hc : ∀ h ∈ X, h * n * h⁻¹ ∈ N := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (hXN hh) n).mp hn
  have e : (g * n) ^ 3 = (g * n * g⁻¹) * (g ^ 2 * n * (g ^ 2)⁻¹) * (g ^ 3 * n) := by
    rw [pow_three']
    group
  rw [e, hg3, one_mul]
  exact N.mul_mem (N.mul_mem (hc g hg) (hc _ (X.pow_mem hg 2))) hn

theorem mul_comm_of_commutator_eq_bot {A B : Subgroup Q} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
  have hm : a * b * a⁻¹ * b⁻¹ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at hm
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hm, one_mul]

theorem exists_mul_of_mem_sup {A B : Subgroup Q} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : Q} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup Q :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h := hAB a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [_root_.mul_inv_rev, hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem false_of_pair {K₁ X N P : Subgroup Q} {t c : Q}
    (hcomm' : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hinf : K₁ ⊓ K₁.map (MulAut.conj t).toMonoidHom = ⊥)
    (hX' : X ≤ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (htX : t ∈ Subgroup.normalizer (X : Set Q)) (hPX : P ≤ Subgroup.normalizer (X : Set Q))
    (hPK : P ≤ K₁) (hP : Nat.card P = 8) (hK : Nat.card K₁ = 168)
    (e : ↥K₁ ≃* SpecialLinearGroup (Fin 3) (ZMod 2))
    (hXN : X ≤ Subgroup.normalizer (N : Set Q)) (hN : IsPGroup 2 N)
    (hc : c ∈ X) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hdec : ∀ x ∈ X, x ∈ N ∨ c * c * x ∈ N ∨ c * x ∈ N) : False := by
  set K₂ := K₁.map (MulAut.conj t).toMonoidHom with hK₂
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := mul_comm_of_commutator_eq_bot hcomm'
  have hX : ∀ x ∈ X, ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := fun x hx =>
    exists_mul_of_mem_sup hcomm (hX' hx)
  have hint : ∀ y, y ∈ K₁ → y ∈ K₂ → y = 1 := fun y h1 h2 => by
    have : y ∈ K₁ ⊓ K₂ := ⟨h1, h2⟩
    rw [hinf] at this
    exact this
  have hN1 : ∀ n ∈ N, n ^ 3 = 1 → n = 1 := fun n hn h3 => by
    obtain ⟨k, hk⟩ := exists_pow_of_isPGroup hN hn
    exact eq_one_of_pow_of_cube hk h3
  have hconjN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (hXN hg) n).mp hn
  have hE9 : ∀ y ∈ X, y ∈ K₁ → y ^ 3 = 1 → y = 1 := by
    intro y hyX hyK hy3
    by_contra hy1
    set y' := t * y * t⁻¹ with hy'
    have hy'X : y' ∈ X := (Subgroup.mem_normalizer_iff.mp htX y).mp hyX
    have hy'K : y' ∈ K₂ := ⟨y, hyK, by simp [MulAut.conj_apply, hy']⟩
    have hy'3 : y' ^ 3 = 1 := by rw [hy', conj_pow, hy3, mul_one, mul_inv_cancel]
    have hy'1 : y' ≠ 1 := fun h => hy1 (by
      have e1 : y = t⁻¹ * y' * t := by rw [hy']; group
      rw [e1, h]
      group)
    have hcm : Commute y y' := hcomm y hyK y' hy'K
    have hA : y⁻¹ * y' ∈ N → False := fun h => by
      have h3 : (y⁻¹ * y') ^ 3 = 1 := by
        rw [hcm.inv_left.mul_pow, inv_pow, hy3, hy'3, inv_one, one_mul]
      have h4 := hN1 _ h h3
      have hyy : y = y' := by
        calc y = y * (y⁻¹ * y') := by rw [h4, mul_one]
          _ = y' := by group
      exact hy1 (hint y hyK (hyy ▸ hy'K))
    have hB : y * y' ∈ N → False := fun h => by
      have h3 : (y * y') ^ 3 = 1 := by rw [hcm.mul_pow, hy3, hy'3, one_mul]
      have h4 := hN1 _ h h3
      have hyy : y = y'⁻¹ := eq_inv_of_mul_eq_one_left h4
      exact hy1 (hint y hyK (hyy ▸ K₂.inv_mem hy'K))
    rcases hdec y hyX with h | h | h
    · exact hy1 (hN1 y h hy3)
    · rcases hdec y' hy'X with h' | h' | h'
      · exact hy'1 (hN1 y' h' hy'3)
      · apply hA
        have := N.mul_mem (N.inv_mem h) h'
        have e1 : (c * c * y)⁻¹ * (c * c * y') = y⁻¹ * y' := by group
        rwa [e1] at this
      · apply hB
        have h1 := hconjN _ (X.inv_mem (X.mul_mem hc hc)) _ h
        have := N.mul_mem h1 h'
        have e1 : (c * c)⁻¹ * (c * c * y) * (c * c)⁻¹⁻¹ * (c * y') =
            y * c ^ 3 * y' := by group
        rwa [e1, hc3, mul_one] at this
    · rcases hdec y' hy'X with h' | h' | h'
      · exact hy'1 (hN1 y' h' hy'3)
      · apply hB
        have h1 := hconjN _ (X.inv_mem hc) _ h
        have := N.mul_mem h1 h'
        have e1 : c⁻¹ * (c * y) * c⁻¹⁻¹ * (c * c * y') = y * c ^ 3 * y' := by
          rw [pow_three']
          group
        rwa [e1, hc3, mul_one] at this
      · apply hA
        have := N.mul_mem (N.inv_mem h) h'
        have e1 : (c * y)⁻¹ * (c * y') = y⁻¹ * y' := by group
        rwa [e1] at this
  have hE9' : ∀ y ∈ X, y ∈ K₂ → y ^ 3 = 1 → y = 1 := by
    intro y hyX hyK hy3
    obtain ⟨k, hk, rfl⟩ := hyK
    have hk' : (MulAut.conj t).toMonoidHom k = t * k * t⁻¹ := rfl
    rw [hk'] at hyX hy3 ⊢
    have hkX : k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htX) _).mp hyX
      have e1 : t⁻¹ * (t * k * t⁻¹) * t⁻¹⁻¹ = k := by group
      rwa [e1] at this
    have hk3 : k ^ 3 = 1 := by
      have e1 : k ^ 3 = t⁻¹ * (t * k * t⁻¹) ^ 3 * t⁻¹⁻¹ := by
        rw [conj_pow]
        group
      rw [e1, hy3, mul_one, mul_inv_cancel]
    rw [hE9 k hkX hk hk3, mul_one, mul_inv_cancel]
  have hcube : ∀ x ∈ X, x ^ 3 ∈ N := by
    intro x hx
    rcases hdec x hx with h | h | h
    · exact N.pow_mem h 3
    · have e1 : x = (c * c)⁻¹ * (c * c * x) := by group
      rw [e1]
      refine cube_mem_of_conj hXN (X.inv_mem (X.mul_mem hc hc)) ?_ h
      have e2 : (c * c)⁻¹ ^ 3 = (c ^ 3 * c ^ 3)⁻¹ := by group
      rw [e2, hc3, mul_one, inv_one]
    · have e1 : x = c⁻¹ * (c * x) := by group
      rw [e1]
      refine cube_mem_of_conj hXN (X.inv_mem hc) ?_ h
      rw [inv_pow, hc3, inv_one]
  have htwo : ∀ y ∈ X, y ∈ K₁ → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hyX hyK
    obtain ⟨k, hk⟩ := exists_pow_of_isPGroup hN (hcube y hyX)
    refine ⟨k, hE9 _ (X.pow_mem hyX _) (K₁.pow_mem hyK _) ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hk]
  obtain ⟨a, haK, b, hbK, hcab⟩ := hX c hc
  have hab : Commute a b := hcomm a haK b hbK
  have ha3 : a ^ 3 = 1 := by
    have h1 : a ^ 3 * b ^ 3 = 1 := by rw [← hab.mul_pow, ← hcab, hc3]
    have h2 : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hint _ (K₁.pow_mem haK 3) (h2 ▸ K₂.inv_mem (K₂.pow_mem hbK 3))
  have ha1 : a ≠ 1 := by
    intro ha
    rw [ha, one_mul] at hcab
    exact hc1 (hE9' c hc (hcab ▸ hbK) hc3)
  have hPY : Nat.card (P.subgroupOf K₁) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]
    exact hP
  obtain ⟨p, hp, hnot⟩ := exists_comm_not_two e hK hPY (a := ⟨a, haK⟩)
    (Subtype.ext (by simp [ha3])) (fun h => ha1 (congrArg Subtype.val h))
  have hpP : (p : Q) ∈ P := hp
  have hpK : (p : Q) ∈ K₁ := p.2
  have hbp : b * (p : Q)⁻¹ = (p : Q)⁻¹ * b := (hcomm _ (K₁.inv_mem hpK) b hbK).symm
  have hw : (p : Q) * a * (p : Q)⁻¹ * a⁻¹ = (p : Q) * c * (p : Q)⁻¹ * c⁻¹ := by
    rw [hcab]
    calc (p : Q) * a * (p : Q)⁻¹ * a⁻¹ = (p : Q) * a * ((p : Q)⁻¹ * b) * b⁻¹ * a⁻¹ := by group
      _ = (p : Q) * a * (b * (p : Q)⁻¹) * b⁻¹ * a⁻¹ := by rw [hbp]
      _ = (p : Q) * (a * b) * (p : Q)⁻¹ * (a * b)⁻¹ := by group
  have hwX : (p : Q) * a * (p : Q)⁻¹ * a⁻¹ ∈ X := by
    rw [hw]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPX hpP) c).mp hc) (X.inv_mem hc)
  have hwK : (p : Q) * a * (p : Q)⁻¹ * a⁻¹ ∈ K₁ :=
    K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hpK haK) (K₁.inv_mem hpK)) (K₁.inv_mem haK)
  obtain ⟨k, hk⟩ := htwo _ hwX hwK
  exact hnot k (Subtype.ext (by simpa using hk))

end Pair

end L32Comm

end CFSG.Quasithin.H13.A6


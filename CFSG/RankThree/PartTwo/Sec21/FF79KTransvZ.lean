module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTransvL5
public import CFSG.RankThree.PartTwo.Sec21.FF79KFactsZ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 Matrix

@[expose] def qV (c : ZMod 2) (a w : Fin 3 → ZMod 2) : M5 :=
  qM c (a 0) (a 1) (a 2) (w 0) (w 1) (w 2)

theorem qV_mul (c c' : ZMod 2) (a a' w w' : Fin 3 → ZMod 2) :
    qV c a w * qV c' a' w' = qV (c + c' + a ⬝ᵥ w') (a + a') (w + w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qV, qM, Matrix.mul_apply, Fin.sum_univ_five, dotProduct, Fin.sum_univ_three] <;> ring

theorem qV_inj {c c' : ZMod 2} {a a' w w' : Fin 3 → ZMod 2} (h : qV c a w = qV c' a' w') :
    c = c' ∧ a = a' ∧ w = w' := by
  have e := fun i j => congrFun (congrFun h i) j
  have h04 := e 0 4
  have h01 := e 0 1
  have h02 := e 0 2
  have h03 := e 0 3
  have h14 := e 1 4
  have h24 := e 2 4
  have h34 := e 3 4
  simp [qV, qM] at h04 h01 h02 h03 h14 h24 h34
  refine ⟨h04, ?_, ?_⟩
  · funext k; fin_cases k <;> assumption
  · funext k; fin_cases k <;> assumption

theorem qV_comm_iff (c c' : ZMod 2) (a a' w w' : Fin 3 → ZMod 2) :
    qV c a w * qV c' a' w' = qV c' a' w' * qV c a w ↔ a ⬝ᵥ w' + a' ⬝ᵥ w = 0 := by
  rw [qV_mul, qV_mul]
  constructor
  · intro h
    obtain ⟨h1, -, -⟩ := qV_inj h
    rw [CharTwo.add_eq_zero]
    have : a ⬝ᵥ w' = a' ⬝ᵥ w := by
      have := h1
      rw [add_comm c' c] at this
      exact add_left_cancel this
    exact this
  · intro h
    rw [CharTwo.add_eq_zero] at h
    rw [h, add_comm a' a, add_comm w' w, add_comm c' c]

theorem qV_sq (c : ZMod 2) (a w : Fin 3 → ZMod 2) :
    qV c a w * qV c a w = qV (a ⬝ᵥ w) 0 0 := by
  rw [qV_mul]
  have h1 : c + c = 0 := CharTwo.add_self_eq_zero c
  have h2 : a + a = 0 := funext fun k => CharTwo.add_self_eq_zero (a k)
  have h3 : w + w = 0 := funext fun k => CharTwo.add_self_eq_zero (w k)
  rw [h2, h3, h1, zero_add]

theorem qV_zero : qV 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem qV_fourth (c : ZMod 2) (a w : Fin 3 → ZMod 2) : (qV c a w) ^ 4 = 1 := by
  have h : (qV c a w) ^ 4 = qV (a ⬝ᵥ w) 0 0 * qV (a ⬝ᵥ w) 0 0 := by
    rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, qV_sq]
  rw [h, qV_sq]
  have : a ⬝ᵥ w * 0 = 0 := by simp
  simp [dotProduct, qV_zero]


@[expose] def inv3 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![A 1 1 * A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
    -(A 1 0 * A 2 2) + A 1 2 * A 2 0, A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
    A 1 0 * A 2 1 - A 1 1 * A 2 0, -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0]

theorem mul_inv3 {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : A.det = 1) : A * inv3 A = 1 := by
  have : inv3 A = A.adjugate := (Matrix.adjugate_fin_three A).symm
  rw [this, Matrix.mul_adjugate, h, one_smul]

theorem inv3_mul {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : A.det = 1) : inv3 A * A = 1 :=
  mul_eq_one_comm.1 (mul_inv3 h)

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem l3Cent : ∀ W U : Fin 3 → Fin 3 → ZMod 2,
    Matrix.of W * Matrix.of W * Matrix.of W = 1 → Matrix.of W ≠ 1 → (Matrix.of U).det = 1 →
    Matrix.of W * Matrix.of U = Matrix.of U * Matrix.of W →
    Matrix.of U = 1 ∨ Matrix.of U = Matrix.of W ∨ Matrix.of U = Matrix.of W * Matrix.of W := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finA : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
    ∃ B : Fin 3 → Fin 3 → ZMod 2, (Matrix.of B).det = 1 ∧
      u ⬝ᵥ (Matrix.of B *ᵥ v) + (u ᵥ* inv3 (Matrix.of B)) ⬝ᵥ v = 1 := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finB : ∀ u x : Fin 3 → ZMod 2, u ≠ 0 → x ≠ 0 →
    ∃ B : Fin 3 → Fin 3 → ZMod 2, (Matrix.of B).det = 1 ∧ u ⬝ᵥ (Matrix.of B *ᵥ x) = 1 := by
  decide +kernel


theorem conj_qV (c : ZMod 2) (a w : Fin 3 → ZMod 2) (B B' : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : B * B' = 1) :
    invAM 0 B * qV c a w * invAM 0 B' = qV c (a ᵥ* B') (B *ᵥ w) := by
  have e : ∀ i j : Fin 3, B i 0 * B' 0 j + B i 1 * B' 1 j + B i 2 * B' 2 j =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.one_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invAM, qV, qM, Matrix.mul_apply, Fin.sum_univ_five, vecMul, mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    first | ring1 | exact e00 | exact e01 | exact e02 | exact e10 | exact e11 | exact e12 |
      exact e20 | exact e21 | exact e22


theorem Q_coords {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) (hm : invMid (g : M5) = 1) :
    ∃ (c : ZMod 2) (a w : Fin 3 → ZMod 2), (g : M5) = qV c a w :=
  ⟨(g : M5) 0 4, ![(g : M5) 0 1, (g : M5) 0 2, (g : M5) 0 3],
    ![(g : M5) 1 4, (g : M5) 2 4, (g : M5) 3 4], shape_eq hg hm⟩

theorem comm_iff_Q {x y : G52} {c c' : ZMod 2} {a a' w w' : Fin 3 → ZMod 2}
    (hx : (x : M5) = qV c a w) (hy : (y : M5) = qV c' a' w') :
    x * y = y * x ↔ a ⬝ᵥ w' + a' ⬝ᵥ w = 0 := by
  rw [← qV_comm_iff c c' a a' w w', ← hx, ← hy, ← Units.val_mul, ← Units.val_mul]
  exact ⟨fun h => by rw [h], fun h => Units.ext h⟩

theorem act_Q {R : Subgroup G52}
    (hn : ∀ g ∈ Subgroup.centralizer {invT0}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {x : G52} (hx : x ∈ R)
    {c : ZMod 2} {a w : Fin 3 → ZMod 2} (hxm : (x : M5) = qV c a w)
    (B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : B * B' = 1) (h' : B' * B = 1) :
    ∃ y ∈ R, (y : M5) = qV c (a ᵥ* B') (B *ᵥ w) := by
  have hl : invAM 0 B * invAM 0 B' = 1 := by
    rw [invAM_mul, mulVec_zero, add_zero, h, invAM_one]
  let L : G52 := mk5 (invAM 0 B) (invAM 0 B') hl
  have hL : L ∈ Subgroup.centralizer {invT0} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    simp only [L, invT0, coe_mk5]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [invAM, invT0M, Matrix.mul_apply, Fin.sum_univ_five]
  refine ⟨L * x * L⁻¹, hn L hL x hx, ?_⟩
  rw [Units.val_mul, Units.val_mul, hxm]
  have : ((L⁻¹ : G52) : M5) = invAM 0 B' := rfl
  rw [this]
  exact conj_qV c a w B B' h


theorem qV_one_zero : qV 1 0 0 = invT0M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem center_t0 {R : Subgroup G52} (hp : IsPGroup 2 R) (hRC : R ≤ Subgroup.centralizer {invT0})
    (hn : ∀ g ∈ Subgroup.centralizer {invT0}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {r₁ r₂ : G52}
    (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R) (hnc : r₁ * r₂ ≠ r₂ * r₁) {r : G52} (hr : r ∈ R)
    (hc : ∀ x ∈ R, r * x = x * r) : r ∈ Subgroup.zpowers invT0 := by
  have hQ := mid_eq_one hp hRC hn
  obtain ⟨c, u, v, hrm⟩ := Q_coords (hRC hr) (hQ r hr)
  obtain ⟨c₁, u₁, v₁, h₁m⟩ := Q_coords (hRC hr₁) (hQ r₁ hr₁)
  obtain ⟨c₂, u₂, v₂, h₂m⟩ := Q_coords (hRC hr₂) (hQ r₂ hr₂)
  have hω : u₁ ⬝ᵥ v₂ + u₂ ⬝ᵥ v₁ ≠ 0 := fun h => hnc ((comm_iff_Q h₁m h₂m).2 h)
  have one_ne : (1 : ZMod 2) ≠ 0 := by decide
  have ortho : ∀ x ∈ R, ∀ {cx : ZMod 2} {ax wx : Fin 3 → ZMod 2}, (x : M5) = qV cx ax wx →
      u ⬝ᵥ wx + ax ⬝ᵥ v = 0 := fun x hx cx ax wx hxm =>
    (comm_iff_Q hrm hxm).1 (hc x hx)
  have orthoB : ∀ x ∈ R, ∀ {cx : ZMod 2} {ax wx : Fin 3 → ZMod 2}, (x : M5) = qV cx ax wx →
      ∀ B B' : Matrix (Fin 3) (Fin 3) (ZMod 2), B * B' = 1 → B' * B = 1 →
      u ⬝ᵥ (B *ᵥ wx) + (ax ᵥ* B') ⬝ᵥ v = 0 := by
    intro x hx cx ax wx hxm B B' h h'
    obtain ⟨y, hy, hym⟩ := act_Q hn hx hxm B B' h h'
    exact ortho y hy hym
  have pair : ∀ B : Fin 3 → Fin 3 → ZMod 2, (Matrix.of B).det = 1 →
      Matrix.of B * inv3 (Matrix.of B) = 1 ∧ inv3 (Matrix.of B) * Matrix.of B = 1 :=
    fun B hB => ⟨mul_inv3 hB, inv3_mul hB⟩
  have hu0 : u = 0 ∨ v = 0 := by
    by_contra hcon
    obtain ⟨hu', hv'⟩ := not_or.1 hcon
    obtain ⟨B, hB, hB1⟩ := finA u v hu' hv'
    have := orthoB r hr hrm (Matrix.of B) _ (pair B hB).1 (pair B hB).2
    rw [this] at hB1
    exact one_ne hB1.symm
  have hc01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · have hcm : (r : M5) = invT0M ∨ (r : M5) = 1 := by
        rw [hrm, hu, hv]
        rcases hc01 c with rfl | rfl
        · right; exact qV_zero
        · left; exact qV_one_zero
      rcases hcm with h | h
      · have : r = invT0 := Units.ext h
        rw [this]; exact Subgroup.mem_zpowers _
      · have : r = 1 := Units.ext (by rw [h, Units.val_one])
        rw [this]; exact Subgroup.one_mem _
    · exfalso
      have hui : ∀ x ∈ R, ∀ {cx : ZMod 2} {ax wx : Fin 3 → ZMod 2},
          (x : M5) = qV cx ax wx → ax = 0 := by
        intro x hx cx ax wx hxm
        by_contra hax
        obtain ⟨B, hB, hB1⟩ := finB ax v hax hv
        have := orthoB x hx hxm (inv3 (Matrix.of B)) (Matrix.of B) (pair B hB).2 (pair B hB).1
        rw [hu, zero_dotProduct, zero_add, ← dotProduct_mulVec, hB1] at this
        exact one_ne this
      have e1 := hui r₁ hr₁ h₁m
      have e2 := hui r₂ hr₂ h₂m
      apply hω
      rw [e1, e2, zero_dotProduct, zero_dotProduct, add_zero]
  · have hv : v = 0 := hu0.resolve_left hu
    exfalso
    have hvi : ∀ x ∈ R, ∀ {cx : ZMod 2} {ax wx : Fin 3 → ZMod 2},
        (x : M5) = qV cx ax wx → wx = 0 := by
      intro x hx cx ax wx hxm
      by_contra hwx
      obtain ⟨B, hB, hB1⟩ := finB u wx hu hwx
      have := orthoB x hx hxm (Matrix.of B) (inv3 (Matrix.of B)) (pair B hB).1 (pair B hB).2
      rw [hv, dotProduct_zero, add_zero, hB1] at this
      exact one_ne this
    have e1 := hvi r₁ hr₁ h₁m
    have e2 := hvi r₂ hr₂ h₂m
    apply hω
    rw [e1, e2, dotProduct_zero, dotProduct_zero, add_zero]


theorem pow_four_of_mid {g : G52} (hg : g ∈ Subgroup.centralizer {invT0})
    (hm : invMid (g : M5) = 1) : g ^ 4 = 1 := by
  obtain ⟨c, a, w, hgm⟩ := Q_coords hg hm
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, hgm, qV_fourth, Units.val_one])

theorem mid_of_two_elt {d z : G52} (hd : d ∈ Subgroup.centralizer {invT0})
    (hz : z ∈ Subgroup.centralizer {invT0}) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hdn : ∃ n : ℕ, d ^ (2 ^ n) = 1) (hdz : d * z = z * d) : invMid (d : M5) = 1 := by
  set w : GL (Fin 3) (ZMod 2) := piHom ⟨z, hz⟩ with hw
  set u : GL (Fin 3) (ZMod 2) := piHom ⟨d, hd⟩ with hu
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow]
    have : (⟨z, hz⟩ : Subgroup.centralizer {invT0}) ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    have hm : invMid (z : M5) = 1 := by
      have : (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by rw [h]; rfl
      exact this
    have h4 := pow_four_of_mid hz hm
    apply hz1
    calc z = z ^ 4 * (z ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hz3]; group
  have huw : w * u = u * w := by
    rw [hw, hu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdz.symm
  have hu2 : ∃ n : ℕ, u ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hdn
    refine ⟨n, ?_⟩
    rw [hu, ← map_pow]
    have : (⟨d, hd⟩ : Subgroup.centralizer {invT0}) ^ (2 ^ n) = 1 := Subtype.ext hn
    rw [this, map_one]
  have hdet : ((u : Matrix (Fin 3) (Fin 3) (ZMod 2))).det = 1 := by
    have h0 : ((u : Matrix (Fin 3) (Fin 3) (ZMod 2))).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ h0
  have hW3 : (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) * w * w = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', hw3, Units.val_one]
  have hW1 : (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => hw1 (Units.ext (by rw [h]; rfl))
  have hcomm : (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) * u = u * w := by
    have := congrArg Units.val huw
    simpa [Units.val_mul] using this
  have key := l3Cent (fun i j => (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j)
    (fun i j => (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) hW3 hW1 hdet hcomm
  have no3 : ∀ g : GL (Fin 3) (ZMod 2), g ^ 3 = 1 → g ≠ 1 → (∃ n : ℕ, g ^ (2 ^ n) = 1) → False := by
    rintro g hg3 hg1 ⟨n, hn⟩
    have h3 : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    have : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    rw [h3] at this
    have := Nat.prime_three.dvd_of_dvd_pow this
    omega
  rcases key with h | h | h
  · exact h
  · exfalso
    have huw' : u = w := Units.ext h
    rw [huw'] at hu2
    exact no3 w hw3 hw1 hu2
  · exfalso
    have huw' : u = w * w := Units.ext (by rw [Units.val_mul]; exact h)
    have hu3 : u ^ 3 = 1 := by
      rw [huw', ← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hw3, one_pow]
    have hu1 : u ≠ 1 := by
      intro h1
      apply hw1
      rw [huw'] at h1
      calc w = w ^ 3 * (w * w)⁻¹ := by group
        _ = 1 := by rw [hw3, h1]; group
    exact no3 u hu3 hu1 hu2

theorem commDim_eq_one_of_data {y z s : G52} (hs : orderOf s = 2) (hy : orderOf y = 3)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({y} : Set G52))) (hsy : s * y * s⁻¹ = y⁻¹)
    (hz : orderOf z = 3) (hzc : z * y = y * z) (hzy : z ∉ Subgroup.zpowers y)
    (hsz : s * z = z * s) : commDim s = 1 := by
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hle := commDim_le_one_of_data hs hy h7 hsy hz hzc hzy hsz
  rcases inv_commDim_eq_one_or_two hs2 hs1 with h | h
  · exact h
  · omega

theorem transport {s : G52} (hs2 : s ^ 2 = 1) (h1 : commDim s = 1)
    (R : Subgroup G52) (hp : IsPGroup 2 R) (hRC : R ≤ Subgroup.centralizer {s})
    (hn : ∀ g ∈ Subgroup.centralizer {s}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∃ c : G52, c * invT0 * c⁻¹ = s ∧
      (∀ x ∈ Subgroup.centralizer {s}, c⁻¹ * x * c ∈ Subgroup.centralizer {invT0}) ∧
      ∃ R' : Subgroup G52, (∀ x, x ∈ R ↔ c⁻¹ * x * c ∈ R') ∧
        R' ≤ Subgroup.centralizer {invT0} ∧ IsPGroup 2 R' ∧
        (∀ g ∈ Subgroup.centralizer {invT0}, ∀ r ∈ R', g * r * g⁻¹ ∈ R') := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_t0 hs2 h1)
  set f : G52 →* G52 := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfx : ∀ x, f x = c⁻¹ * x * c := fun x => by simp [hf, MulAut.conj_apply]
  have hinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hscomm : ∀ x, x ∈ Subgroup.centralizer {s} → c⁻¹ * x * c ∈ Subgroup.centralizer {invT0} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have : invT0 = c⁻¹ * s * c := by rw [← hc]; group
    rw [this]
    calc c⁻¹ * x * c * (c⁻¹ * s * c) = c⁻¹ * (x * s) * c := by group
      _ = c⁻¹ * (s * x) * c := by rw [hx]
      _ = c⁻¹ * s * c * (c⁻¹ * x * c) := by group
  refine ⟨c, hc, hscomm, R.map f, ?_, ?_, hp.of_equiv (Subgroup.equivMapOfInjective R f hinj), ?_⟩
  · intro x
    constructor
    · intro hx
      exact ⟨x, hx, hfx x⟩
    · rintro ⟨x', hx', hxx⟩
      rw [hfx] at hxx
      have : x = x' := by
        calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
          _ = c * (c⁻¹ * x' * c) * c⁻¹ := by rw [hxx]
          _ = x' := by group
      rw [this]
      exact hx'
  · rintro _ ⟨x, hx, rfl⟩
    rw [hfx]
    exact hscomm x (hRC hx)
  · rintro g hg _ ⟨x, hx, rfl⟩
    have hg' : c * g * c⁻¹ ∈ Subgroup.centralizer {s} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have : s = c * invT0 * c⁻¹ := hc.symm
      rw [this]
      calc c * g * c⁻¹ * (c * invT0 * c⁻¹) = c * (g * invT0) * c⁻¹ := by group
        _ = c * (invT0 * g) * c⁻¹ := by rw [hg]
        _ = c * invT0 * c⁻¹ * (c * g * c⁻¹) := by group
    refine ⟨(c * g * c⁻¹) * x * (c * g * c⁻¹)⁻¹, hn _ hg' x hx, ?_⟩
    rw [hfx, hfx]
    group

theorem ff79KTransvCenter_holds : FF79KTransvCenter := by
  intro s y z hs hy h7 hsy hz hzc hzy hsz R hR hRC hRn r₁ hr₁ r₂ hr₂ hnc r hr hrc
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have h1 := commDim_eq_one_of_data hs hy h7 hsy hz hzc hzy hsz
  obtain ⟨c, hc, -, R', hmem, hR'C, hR'p, hR'n⟩ := transport hs2 h1 R hR hRC hRn
  have hlift : ∀ y' ∈ R', c * y' * c⁻¹ ∈ R := by
    intro y' hy'
    rw [hmem]
    have : c⁻¹ * (c * y' * c⁻¹) * c = y' := by group
    rw [this]
    exact hy'
  have key := center_t0 hR'p hR'C hR'n (r₁ := c⁻¹ * r₁ * c) (r₂ := c⁻¹ * r₂ * c)
    ((hmem r₁).1 hr₁) ((hmem r₂).1 hr₂)
    (by
      intro h
      apply hnc
      have : r₁ * r₂ = c * ((c⁻¹ * r₁ * c) * (c⁻¹ * r₂ * c)) * c⁻¹ := by group
      rw [this, h]
      group)
    (r := c⁻¹ * r * c) ((hmem r).1 hr)
    (by
      intro x' hx'
      have hx := hlift x' hx'
      have := hrc _ hx
      calc c⁻¹ * r * c * x' = c⁻¹ * (r * (c * x' * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x' * c⁻¹) * r) * c := by rw [this]
        _ = x' * (c⁻¹ * r * c) := by group)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 key
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← hc, conj_zpow, hk]
  group

theorem ff79KTransvComm_holds : FF79KTransvComm := by
  intro s y z hs hy h7 hsy hz hzc hzy hsz d hdn hds hdz R hR hRC hRn r hr
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have h1 := commDim_eq_one_of_data hs hy h7 hsy hz hzc hzy hsz
  obtain ⟨c, hc, hcent, R', hmem, hR'C, hR'p, hR'n⟩ := transport hs2 h1 R hR hRC hRn
  have hdC : d ∈ Subgroup.centralizer {s} := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact hds
  have hzC : z ∈ Subgroup.centralizer {s} := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact hsz.symm
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hconj : ∀ x : G52, MulAut.conj c⁻¹ x = c⁻¹ * x * c := fun x => by
    simp [MulAut.conj_apply]
  have hd' := hcent d hdC
  have hz' := hcent z hzC
  have hz3' : (c⁻¹ * z * c) ^ 3 = 1 := by
    rw [← hconj, ← map_pow, hz3, map_one]
  have hz1' : c⁻¹ * z * c ≠ 1 := by
    intro h
    apply hz1
    calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨n, hn⟩ := hdn
  have hdn' : ∃ n : ℕ, (c⁻¹ * d * c) ^ (2 ^ n) = 1 :=
    ⟨n, by rw [← hconj, ← map_pow, hn, map_one]⟩
  have hdz' : c⁻¹ * d * c * (c⁻¹ * z * c) = c⁻¹ * z * c * (c⁻¹ * d * c) := by
    calc c⁻¹ * d * c * (c⁻¹ * z * c) = c⁻¹ * (d * z) * c := by group
      _ = c⁻¹ * (z * d) * c := by rw [hdz]
      _ = c⁻¹ * z * c * (c⁻¹ * d * c) := by group
  have hmid := mid_of_two_elt hd' hz' hz3' hz1' hdn' hdz'
  have hr' := (hmem r).1 hr
  have hQ := mid_eq_one hR'p hR'C hR'n _ hr'
  have key := comm_mem_t0 hd' (hR'C hr') hmid hQ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 key
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← hc, conj_zpow, hk]
  group

end CFSG.RankThree.PartTwo.Sec21.FF79

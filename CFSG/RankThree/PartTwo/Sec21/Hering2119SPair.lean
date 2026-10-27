module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SCoord
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SLin

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

section PairLinear

variable {V : Type*} [AddCommGroup V] [Module F3 V]

structure QRelE (I J : V ≃ₗ[F3] V) : Prop where
  II : ∀ v, I (I v) = -v
  JJ : ∀ v, J (J v) = -v
  IJ : ∀ v, I (J v) = -J (I v)

@[expose] def q8 (I J : V ≃ₗ[F3] V) : List (V ≃ₗ[F3] V) :=
  [1, I, I * I, I * I * I, J, I * J, I * I * J, I * I * I * J]

theorem QRelE.toQRel {I J : V ≃ₗ[F3] V} (h : QRelE I J) :
    QRel (I : V →ₗ[F3] V) (J : V →ₗ[F3] V) := ⟨h.II, h.JJ, h.IJ⟩

@[expose] noncomputable def mt (b : Basis (Fin 2 × Fin 2) F3 V) (f : V ≃ₗ[F3] V) : Mat4 :=
  LinearMap.toMatrix b b (f : V →ₗ[F3] V)

theorem mt_mul (b : Basis (Fin 2 × Fin 2) F3 V) (f g : V ≃ₗ[F3] V) :
    mt b (f * g) = mt b f * mt b g := by
  have : ((f * g : V ≃ₗ[F3] V) : V →ₗ[F3] V) = (f : V →ₗ[F3] V) * (g : V →ₗ[F3] V) :=
    LinearMap.ext fun _ => rfl
  rw [mt, this, LinearMap.toMatrix_mul]
  rfl

theorem mt_one (b : Basis (Fin 2 × Fin 2) F3 V) : mt b (1 : V ≃ₗ[F3] V) = 1 := by
  have : (((1 : V ≃ₗ[F3] V)) : V →ₗ[F3] V) = (1 : V →ₗ[F3] V) := LinearMap.ext fun _ => rfl
  rw [mt, this, LinearMap.toMatrix_one]

theorem mt_inj (b : Basis (Fin 2 × Fin 2) F3 V) {f g : V ≃ₗ[F3] V} (h : mt b f = mt b g) :
    f = g := by
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h)

theorem mt_q8_gen {α : Type*} (b : Basis (Fin 2 × Fin 2) F3 V) (ρ : α → Mat4) (m : α → α → α)
    (e : α) (hmul : ∀ x y, ρ x * ρ y = ρ (m x y)) (hone : ρ e = 1) {I J : V ≃ₗ[F3] V}
    {x z : α} (hI : mt b I = ρ x) (hJ : mt b J = ρ z) :
    ∀ y ∈ q8 I J, ∃ w ∈ q8g m e x z, mt b y = ρ w := by
  intro y hy
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [q8g, List.mem_cons, List.not_mem_nil, or_false]
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨e, Or.inl rfl, by rw [mt_one, hone]⟩
  · exact ⟨x, Or.inr (Or.inl rfl), hI⟩
  · exact ⟨m x x, Or.inr (Or.inr (Or.inl rfl)), by rw [mt_mul, hI, hmul]⟩
  · exact ⟨m (m x x) x, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by
      rw [mt_mul, mt_mul, hI, hmul, hmul]⟩
  · exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hJ⟩
  · exact ⟨m x z, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by
      rw [mt_mul, hI, hJ, hmul]⟩
  · exact ⟨m (m x x) z, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by
      rw [mt_mul, mt_mul, hI, hJ, hmul, hmul]⟩
  · exact ⟨m (m (m x x) x) z,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by
      rw [mt_mul, mt_mul, mt_mul, hI, hJ, hmul, hmul, hmul]⟩

theorem q8g_mat2 : q8g (· * ·) (1 : Mat2) I2m0 J2m0 = Q8list := rfl

theorem toMatrix_mul_eq (b : Basis (Fin 2 × Fin 2) F3 V) (f g : V →ₗ[F3] V) :
    LinearMap.toMatrix b b (f * g) = LinearMap.toMatrix b b f * LinearMap.toMatrix b b g :=
  LinearMap.toMatrix_mul b f g

theorem g1_form (b : Basis (Fin 2 × Fin 2) F3 V) {I₀ J₀ : V ≃ₗ[F3] V} (ε₀ ε₁ : V →ₗ[F3] V)
    (g₁ : V ≃ₗ[F3] V) (hI₀ : mt b I₀ = kr 1 I2m0) (hJ₀ : mt b J₀ = kr 1 J2m0)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (hg₁ : ∀ v, g₁ v = v + ε₁ v)
    (hε₁ : ∀ v, ε₁ (ε₁ v) = 0) (hc : ∀ v, ε₀ (ε₁ v) = ε₁ (ε₀ v))
    (hind : ∀ c : F3, ε₁ ≠ c • ε₀)
    (hN₀ : ∃ y ∈ q8 I₀ J₀, g₁ * I₀ = y * g₁) (hN₀' : ∃ y ∈ q8 I₀ J₀, g₁ * J₀ = y * g₁) :
    ∃ A ∈ nilp8, LinearMap.toMatrix b b ε₁ = kr 1 A := by
  have hcomm : LinearMap.toMatrix b b ε₁ * kr nU 1 = kr nU 1 * LinearMap.toMatrix b b ε₁ := by
    rw [← hε₀, ← toMatrix_mul_eq, ← toMatrix_mul_eq]
    congr 1
    exact LinearMap.ext fun v => (hc v).symm
  obtain ⟨P', R', hPR⟩ := eq_of_comm_nU _ hcomm
  have hE1 : LinearMap.toMatrix b b ε₁ = rhoU (P', R') := hPR
  have hsq : rhoU (pmul (P', R') (P', R')) = rhoU (0, 0) := by
    rw [← rhoU_mul, ← hE1]
    have : (ε₁ * ε₁ : V →ₗ[F3] V) = 0 := LinearMap.ext fun v => hε₁ v
    rw [← toMatrix_mul_eq, this, map_zero]
    simp [rhoU, kr_zero_right]
  have hsq' := rhoU_inj hsq
  simp only [pmul, Prod.mk.injEq] at hsq'
  obtain ⟨hP'sq, hP'R'⟩ := hsq'
  have hmg : mt b g₁ = rhoU (1 + P', R') := by
    have : (g₁ : V →ₗ[F3] V) = LinearMap.id + ε₁ := LinearMap.ext fun v => hg₁ v
    rw [mt, this, map_add, LinearMap.toMatrix_id, hE1, ← rhoU_one, ← rhoU_add]
    congr 1
    simp [Prod.ext_iff]
  have hnorm : ∀ (x : V ≃ₗ[F3] V) (q' : Mat2) (hx : mt b x = kr 1 q'),
      (∃ y ∈ q8 I₀ J₀, g₁ * x = y * g₁) →
      ∃ q ∈ Q8list, (1 + P') * q' = q * (1 + P') ∧ R' * q' = q * R' := by
    intro x q' hx ⟨y, hy, hxy⟩
    obtain ⟨w, hw, hyw⟩ := mt_q8_gen b (fun q : Mat2 => kr 1 q) (· * ·) (1 : Mat2)
      (fun x y => kr_mul 1 1 x y ▸ by rw [one_mul]) (by simp [kr_one]) hI₀ hJ₀ y hy
    refine ⟨w, by rw [← q8g_mat2]; exact hw, ?_⟩
    have h1 := congrArg (mt b) hxy
    rw [mt_mul, mt_mul, hmg, hyw, hx] at h1
    have e1 : rhoU (1 + P', R') * rhoU (q', 0) = rhoU (w, 0) * rhoU (1 + P', R') := by
      have h2 : ∀ q : Mat2, kr 1 q = rhoU (q, 0) := fun q => by simp [rhoU, kr_zero_right]
      rw [h2, h2] at h1
      exact h1
    rw [rhoU_mul, rhoU_mul] at e1
    have e2 := rhoU_inj e1
    simp only [pmul, Prod.mk.injEq] at e2
    simp only [mul_zero, add_zero, zero_mul] at e2
    exact ⟨e2.1, by simpa using e2.2⟩
  obtain ⟨q1, hq1, h11, h12⟩ := hnorm I₀ I2m0 hI₀ hN₀
  obtain ⟨q2, hq2, h21, h22⟩ := hnorm J₀ J2m0 hJ₀ hN₀'
  have hind' : ∀ c : F3, ¬ (1 + P' = 1 ∧ R' = c • 1) := by
    rintro c ⟨h1, h2⟩
    apply hind c
    have hP0 : P' = 0 := by simpa using h1
    apply (LinearMap.toMatrix b b).injective
    rw [hE1, map_smul, hε₀, hP0, h2]
    simp [rhoU, kr_zero_right, kr_smul_right]
  have e1P : (1 + P' - 1 : Mat2) = P' := by abel
  have key := classify_g1 (1 + P') (mem_allMat2 _) R' (mem_allMat2 _) ⟨q1, hq1, h11, h12⟩
    ⟨q2, hq2, h21, h22⟩ (by rw [e1P]; exact hP'sq)
    (by rw [e1P]; exact hP'R') hind'
  obtain ⟨hR0, hP1⟩ := key
  have hP'ne : P' ≠ 0 := fun h => hP1 (by rw [h, add_zero])
  refine ⟨P', mem_nilp8 P' hP'sq hP'ne, ?_⟩
  rw [hE1]
  simp [rhoU, hR0, kr_zero_right]

theorem mt_neg_id (b : Basis (Fin 2 × Fin 2) F3 V) (f : V ≃ₗ[F3] V) (hf : ∀ v, f v = -v) :
    mt b f = -1 := by
  have : (f : V →ₗ[F3] V) = -LinearMap.id := LinearMap.ext fun v => by simp [hf]
  rw [mt, this, map_neg, LinearMap.toMatrix_id]

theorem t1_data (b : Basis (Fin 2 × Fin 2) F3 V) {A : Mat2} (hA : A ∈ nilp8)
    (ε₁ : V →ₗ[F3] V) (g₀ I₁ J₁ : V ≃ₗ[F3] V)
    (hε₁ : LinearMap.toMatrix b b ε₁ = kr 1 A) (hg₀ : mt b g₀ = kr uU 1)
    (hIε : ∀ v, I₁ (ε₁ v) = ε₁ (I₁ v)) (hJε : ∀ v, J₁ (ε₁ v) = ε₁ (J₁ v))
    (hQ : QRelE I₁ J₁) (hN : ∃ y ∈ q8 I₁ J₁, g₀ * I₁ = y * g₀)
    (hN' : ∃ y ∈ q8 I₁ J₁, g₀ * J₁ = y * g₀) :
    ∃ a1 b1 a2 b2 : Mat2, mt b I₁ = rhoA A (a1, b1) ∧ mt b J₁ = rhoA A (a2, b2) ∧
      a1 ∈ Q6 ∧ a2 ∈ Q6 ∧ a1 * a2 = -(a2 * a1) ∧
      ((b1 = 0 ∧ b2 = 0) ∨ ∃ y : F3, y ≠ 0 ∧ b1 = y • (nU * a1 - a1 * nU) ∧
        b2 = y • (nU * a2 - a2 * nU)) := by
  have hAA : A * A = 0 := nilp8_sq A hA
  have hcommE : ∀ x : V ≃ₗ[F3] V, (∀ v, x (ε₁ v) = ε₁ (x v)) →
      mt b x * kr 1 A = kr 1 A * mt b x := by
    intro x hx
    rw [← hε₁, mt, ← toMatrix_mul_eq, ← toMatrix_mul_eq]
    congr 1
    exact LinearMap.ext fun v => (hx v)
  obtain ⟨p, hp⟩ := exists_rhoA hA _ (hcommE I₁ hIε)
  obtain ⟨p', hp'⟩ := exists_rhoA hA _ (hcommE J₁ hJε)
  obtain ⟨a1, b1⟩ := p
  obtain ⟨a2, b2⟩ := p'
  have rel_sq : ∀ (x : V ≃ₗ[F3] V) (q : Mat2 × Mat2), mt b x = rhoA A q → (∀ v, x (x v) = -v) →
      pmul q q = (-1, 0) := by
    intro x q hq hx
    have h1 : mt b (x * x) = -1 := mt_neg_id b _ (fun v => hx v)
    rw [mt_mul, hq, rhoA_mul hAA, ← rhoA_neg_one A] at h1
    exact rhoA_inj hA h1
  have hI2 := rel_sq I₁ (a1, b1) hp hQ.II
  have hJ2 := rel_sq J₁ (a2, b2) hp' hQ.JJ
  have hIJ : pmul (a1, b1) (a2, b2) = -pmul (a2, b2) (a1, b1) := by
    have h1 : mt b (I₁ * J₁) = - mt b (J₁ * I₁) := by
      have e1 : ((I₁ * J₁ : V ≃ₗ[F3] V) : V →ₗ[F3] V) =
          -((J₁ * I₁ : V ≃ₗ[F3] V) : V →ₗ[F3] V) := LinearMap.ext fun v => hQ.IJ v
      rw [mt, e1, map_neg]; rfl
    rw [mt_mul, mt_mul, hp, hp', rhoA_mul hAA, rhoA_mul hAA, ← rhoA_neg] at h1
    exact rhoA_inj hA h1
  simp only [pmul, Prod.mk.injEq, Prod.neg_mk] at hI2 hJ2 hIJ
  obtain ⟨hI2a, hI2b⟩ := hI2
  obtain ⟨hJ2a, hJ2b⟩ := hJ2
  obtain ⟨hIJa, hIJb⟩ := hIJ
  have hmg0 : mt b g₀ = rhoA A (uU, 0) := by
    rw [hg₀]; simp [rhoA, kr_zero_left]
  have hnorm : ∀ (x : V ≃ₗ[F3] V) (q : Mat2 × Mat2), mt b x = rhoA A q →
      (∃ y ∈ q8 I₁ J₁, g₀ * x = y * g₀) →
      ∃ w ∈ q8p (a1, b1) (a2, b2), (uU * q.1, uU * q.2) = (w.1 * uU, w.2 * uU) := by
    intro x q hq ⟨y, hy, hxy⟩
    obtain ⟨w, hw, hyw⟩ := mt_q8_gen b (rhoA A) pmul ((1 : Mat2), (0 : Mat2))
      (fun x y => rhoA_mul hAA x y) (rhoA_one A) hp hp' y hy
    refine ⟨w, hw, ?_⟩
    have h1 := congrArg (mt b) hxy
    rw [mt_mul, mt_mul, hmg0, hyw, hq, rhoA_mul hAA, rhoA_mul hAA] at h1
    have e := rhoA_inj hA h1
    simp only [pmul, Prod.mk.injEq] at e
    simp only [zero_mul, mul_zero, add_zero, zero_add] at e
    exact Prod.ext e.1 e.2
  obtain ⟨w1, hw1, hw1e⟩ := hnorm I₁ (a1, b1) hp hN
  obtain ⟨w2, hw2, hw2e⟩ := hnorm J₁ (a2, b2) hp' hN'
  have ha1 : a1 ∈ Q6 := mem_Q6 a1 hI2a
  have ha2 : a2 ∈ Q6 := mem_Q6 a2 hJ2a
  refine ⟨a1, b1, a2, b2, hp, hp', ha1, ha2, hIJa, ?_⟩
  exact classify_dec a1 ha1 b1 (mem_allMat2 _) hI2b a2 ha2 hIJa b2 (mem_allMat2 _) hJ2b hIJb
    ⟨w1, hw1, hw1e⟩ ⟨w2, hw2, hw2e⟩

theorem mt_q8_gen' {α : Type*} (b : Basis (Fin 2 × Fin 2) F3 V) (ρ : α → Mat4) (m : α → α → α)
    (e : α) (hmul : ∀ x y, ρ x * ρ y = ρ (m x y)) (hone : ρ e = 1) {I J : V ≃ₗ[F3] V}
    {x z : α} (hI : mt b I = ρ x) (hJ : mt b J = ρ z) :
    ∀ w ∈ q8g m e x z, ∃ g ∈ q8 I J, mt b g = ρ w := by
  intro w hw
  simp only [q8g, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, by rw [mt_one, hone]⟩
  · exact ⟨I, Or.inr (Or.inl rfl), hI⟩
  · exact ⟨I * I, Or.inr (Or.inr (Or.inl rfl)), by rw [mt_mul, hI, hmul]⟩
  · exact ⟨I * I * I, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by
      rw [mt_mul, mt_mul, hI, hmul, hmul]⟩
  · exact ⟨J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hJ⟩
  · exact ⟨I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by
      rw [mt_mul, hI, hJ, hmul]⟩
  · exact ⟨I * I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by
      rw [mt_mul, mt_mul, hI, hJ, hmul, hmul]⟩
  · exact ⟨I * I * I * J,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by
      rw [mt_mul, mt_mul, mt_mul, hI, hJ, hmul, hmul, hmul]⟩

theorem q8_mem {H : Subgroup (V ≃ₗ[F3] V)} {I J : V ≃ₗ[F3] V} (hI : I ∈ H) (hJ : J ∈ H) :
    ∀ y ∈ q8 I J, y ∈ H := by
  intro y hy
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact hI
  · exact H.mul_mem hI hI
  · exact H.mul_mem (H.mul_mem hI hI) hI
  · exact hJ
  · exact H.mul_mem hI hJ
  · exact H.mul_mem (H.mul_mem hI hI) hJ
  · exact H.mul_mem (H.mul_mem (H.mul_mem hI hI) hI) hJ

theorem Q6_getD_mem : ∀ k < 6, Q6.getD k 0 ∈ Q6 := by
  intro k hk
  have hlen : k < Q6.length := by simpa [Q6] using hk
  rw [List.getD_eq_getElem (hn := hlen)]
  exact List.getElem_mem hlen

theorem letters0 (b : Basis (Fin 2 × Fin 2) F3 V) {H : Subgroup (V ≃ₗ[F3] V)}
    {I₀ J₀ : V ≃ₗ[F3] V} (hI₀H : I₀ ∈ H) (hJ₀H : J₀ ∈ H) (hI₀ : mt b I₀ = kr 1 I2m0)
    (hJ₀ : mt b J₀ = kr 1 J2m0) : ∀ i : ℕ, i < 6 → ∃ g ∈ H, mt b g = kr 1 (Q6.getD i 0) := by
  intro i hi
  have hmul : ∀ x y : Mat2, kr 1 x * kr 1 y = kr 1 (x * y) := fun x y => by
    rw [kr_mul, one_mul]
  have hone : kr 1 (1 : Mat2) = 1 := kr_one
  have hmem := q8_mem hI₀H hJ₀H
  have hq := mt_q8_gen' b (fun q : Mat2 => kr 1 q) (· * ·) (1 : Mat2) hmul hone hI₀ hJ₀
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := Q6_getD
  interval_cases i
  · obtain ⟨g, hg, hmg⟩ := hq I2m0 (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e0]⟩
  · obtain ⟨g, hg, hmg⟩ := hq (I2m0 * I2m0 * I2m0) (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e1]⟩
  · obtain ⟨g, hg, hmg⟩ := hq J2m0 (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e2]⟩
  · obtain ⟨g, hg, hmg⟩ := hq (I2m0 * I2m0 * J2m0) (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e3]⟩
  · obtain ⟨g, hg, hmg⟩ := hq (I2m0 * J2m0) (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e4]⟩
  · obtain ⟨g, hg, hmg⟩ := hq (I2m0 * I2m0 * I2m0 * J2m0) (by simp [q8g])
    exact ⟨g, hmem g hg, by rw [hmg, e5]⟩

theorem letters1 (b : Basis (Fin 2 × Fin 2) F3 V) {A : Mat2} (hA : A ∈ nilp8) {y : F3}
    {H : Subgroup (V ≃ₗ[F3] V)} {I₁ J₁ : V ≃ₗ[F3] V} (hI₁H : I₁ ∈ H) (hJ₁H : J₁ ∈ H)
    {a1 b1 a2 b2 : Mat2} (hI₁ : mt b I₁ = rhoA A (a1, b1)) (hJ₁ : mt b J₁ = rhoA A (a2, b2))
    (ha1 : a1 ∈ Q6) (ha2 : a2 ∈ Q6) (hanti : a1 * a2 = -(a2 * a1))
    (hb1 : b1 = y • (nU * a1 - a1 * nU)) (hb2 : b2 = y • (nU * a2 - a2 * nU)) :
    ∀ i : ℕ, 6 ≤ i → i < 12 → ∃ g ∈ H, mt b g = letter A y i := by
  intro i hi6 hi12
  have hAA := nilp8_sq A hA
  have hmem := q8_mem hI₁H hJ₁H
  have hq := mt_q8_gen' b (rhoA A) pmul ((1 : Mat2), (0 : Mat2)) (fun x y => rhoA_mul hAA x y)
    (rhoA_one A) hI₁ hJ₁
  set a := Q6.getD (i - 6) 0 with ha
  have haQ : a ∈ Q6 := Q6_getD_mem (i - 6) (by omega)
  obtain ⟨w, hw, hwa⟩ := q8_cover a1 ha1 a2 ha2 hanti a haQ
  have hw' : ∃ w' ∈ q8g pmul ((1 : Mat2), (0 : Mat2)) (a1, b1) (a2, b2), w'.1 = a := by
    have hmap := q8g_fst (· * ·) pmul Prod.fst (fun x y => rfl) ((1 : Mat2), (0 : Mat2))
      (a1, b1) (a2, b2)
    have : w ∈ (q8g pmul ((1 : Mat2), (0 : Mat2)) (a1, b1) (a2, b2)).map Prod.fst := by
      rw [hmap]; exact hw
    obtain ⟨w', hw'1, hw'2⟩ := List.mem_map.mp this
    exact ⟨w', hw'1, by rw [hw'2, hwa]⟩
  obtain ⟨w', hw'1, hw'2⟩ := hw'
  have hsnd : w'.2 = y • (nU * w'.1 - w'.1 * nU) := by
    have := bad_pairs a1 ha1 a2 ha2 y w'
    rw [← hb1, ← hb2] at this
    exact this hw'1
  obtain ⟨g, hg, hmg⟩ := hq w' hw'1
  refine ⟨g, hmem g hg, ?_⟩
  rw [hmg]
  have hlet : letter A y i = rhoA A (a, y • (nU * a - a * nU)) := by
    simp only [letter, if_neg (by omega : ¬ i < 6), rhoA]
    rfl
  rw [hlet]
  congr 1
  exact Prod.ext hw'2 (by rw [hsnd, hw'2])

theorem bad_case (b : Basis (Fin 2 × Fin 2) F3 V) {A : Mat2} (hA : A ∈ nilp8) {y : F3}
    (hy : y ≠ 0) {H : Subgroup (V ≃ₗ[F3] V)} {I₀ J₀ I₁ J₁ : V ≃ₗ[F3] V} (hI₀H : I₀ ∈ H)
    (hJ₀H : J₀ ∈ H) (hI₁H : I₁ ∈ H) (hJ₁H : J₁ ∈ H) (hI₀ : mt b I₀ = kr 1 I2m0)
    (hJ₀ : mt b J₀ = kr 1 J2m0) {a1 b1 a2 b2 : Mat2} (hI₁ : mt b I₁ = rhoA A (a1, b1))
    (hJ₁ : mt b J₁ = rhoA A (a2, b2)) (ha1 : a1 ∈ Q6) (ha2 : a2 ∈ Q6)
    (hanti : a1 * a2 = -(a2 * a1)) (hb1 : b1 = y • (nU * a1 - a1 * nU))
    (hb2 : b2 = y • (nU * a2 - a2 * nU)) :
    ∃ g ∈ H, ∃ X : Mat2, mt b g = 1 + kr nU X ∧ ∀ c : F3, X ≠ c • 1 := by
  obtain ⟨e, he, hA', hy'⟩ := badTable_complete A hA y hy
  have hok := badTable_ok e he
  have hlt := badTable_lt e he
  have hL : ∀ i : ℕ, i < 12 → ∃ g ∈ H, mt b g = letter A y i := by
    intro i hi
    by_cases h6 : i < 6
    · obtain ⟨g, hg, hmg⟩ := letters0 b hI₀H hJ₀H hI₀ hJ₀ i h6
      exact ⟨g, hg, by rw [hmg]; simp only [letter, if_pos h6]⟩
    · exact letters1 b hA hI₁H hJ₁H hI₁ hJ₁ ha1 ha2 hanti hb1 hb2 i (by omega) hi
  have hw : ∀ w : List ℕ, (∀ i ∈ w, i < 12) → ∃ g ∈ H, mt b g = wordVal A y w := by
    intro w
    induction w with
    | nil =>
      intro _
      exact ⟨1, H.one_mem, by simp [wordVal, mt_one]⟩
    | cons i w ih =>
      intro hall
      obtain ⟨g, hg, hmg⟩ := ih (fun j hj => hall j (List.mem_cons_of_mem i hj))
      obtain ⟨g', hg', hmg'⟩ := hL i (hall i (List.mem_cons_self))
      exact ⟨g' * g, H.mul_mem hg' hg, by
        rw [mt_mul, hmg, hmg']; simp [wordVal]⟩
  obtain ⟨g, hg, hmg⟩ := hw e.2.2 hlt
  obtain ⟨hok1, hok2⟩ := hok
  rw [hA', hy'] at hok1 hok2
  exact ⟨g, hg, Xof (wordVal A y e.2.2), by rw [hmg]; exact hok1, hok2⟩

theorem kr_inj_right_nU (X Y : Mat2) (h : kr nU X = kr nU Y) : X = Y := by
  ext i j
  have := congrFun (congrFun h (1, i)) (0, j)
  simpa [kr_apply] using this

theorem uequiv_of_mt (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (hε : ∀ v, ε₀ (ε₀ v) = 0) (g : V ≃ₗ[F3] V)
    (X : Mat2) (hg : mt b g = 1 + kr nU X) (hX : ∀ c : F3, X ≠ c • 1) :
    ∃ ν : LinearMap.range ε₀ →ₗ[F3] LinearMap.range ε₀, uEquiv ε₀ hε ν = g ∧
      ∀ c : F3, ν ≠ c • (LinearMap.id : LinearMap.range ε₀ →ₗ[F3] LinearMap.range ε₀) := by
  set S : V →ₗ[F3] V := Matrix.toLin b b (kr 1 X) with hS
  set T : V →ₗ[F3] V := (g : V →ₗ[F3] V) - LinearMap.id with hT
  have hmT : LinearMap.toMatrix b b T = kr nU X := by
    rw [hT, map_sub, LinearMap.toMatrix_id]
    have : LinearMap.toMatrix b b (g : V →ₗ[F3] V) = 1 + kr nU X := hg
    rw [this]; abel
  have hmS : LinearMap.toMatrix b b S = kr 1 X := LinearMap.toMatrix_toLin b b _
  have hT1 : T = ε₀ * S := by
    apply (LinearMap.toMatrix b b).injective
    rw [hmT, LinearMap.toMatrix_mul, hε₀, hmS, kr_mul, one_mul, mul_one]
  have hT2 : T = S * ε₀ := by
    apply (LinearMap.toMatrix b b).injective
    rw [hmT, LinearMap.toMatrix_mul, hε₀, hmS, kr_mul, one_mul, mul_one]
  obtain ⟨ν, hν⟩ := exists_factor ε₀ T (fun v => ⟨S v, by rw [hT1]; rfl⟩)
    (fun v hv => by rw [hT2]; show S (ε₀ v) = 0; rw [hv, map_zero])
  refine ⟨ν, ?_, ?_⟩
  · apply LinearEquiv.ext
    intro v
    rw [uEquiv_apply, hν]
    simp [hT]
  · intro c hc
    have hTc : T = c • ε₀ := by
      apply LinearMap.ext
      intro v
      have := hν v
      rw [hc] at this
      simpa using this.symm
    have : kr nU X = kr nU (c • 1) := by
      rw [← hmT, hTc, map_smul, hε₀, kr_smul_right]
    exact hX c (kr_inj_right_nU _ _ this)

theorem coord_mul (b : Basis (Fin 2 × Fin 2) F3 V) (f : V →ₗ[F3] V) (M : Mat4)
    (hf : LinearMap.toMatrix b b f = M) (x : V) (a : Fin 2 × Fin 2) :
    b.repr (f x) a = ∑ c, M a c * b.repr x c := by
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b f x) a
  rw [hf] at this
  rw [← this]
  rfl

theorem repr_eps_zero (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (x : V) (j : Fin 2) :
    b.repr (ε₀ x) (0, j) = 0 := by
  rw [coord_mul b ε₀ _ hε₀]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply]

theorem card_range_eq_nine [Finite V] (hV : Nat.card V = 81) (ε : V →ₗ[F3] V)
    (hε : ∀ v, ε (ε v) = 0) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε) :
    Nat.card (LinearMap.range ε) = 9 := by
  have h := AddSubgroup.card_ker_mul_card_range ε.toAddMonoidHom
  have h1 : Nat.card (ε.toAddMonoidHom).range = Nat.card (LinearMap.range ε) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [LinearMap.mem_range]; rfl)
  have h2 : Nat.card (ε.toAddMonoidHom).ker = Nat.card (LinearMap.range ε) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro hv
      exact hk v hv
    · rintro ⟨w, rfl⟩
      exact hε w
  rw [h1, h2] at h
  have h3 : Nat.card (LinearMap.range ε) * Nat.card (LinearMap.range ε) = 9 * 9 := by
    rw [h, hV]
  exact Nat.mul_self_inj.mp h3

end PairLinear

section Main

variable {V : Type*} [AddCommGroup V] [Module F3 V]

theorem comm_of_eps {g₀ : V ≃ₗ[F3] V} {ε₀ : V →ₗ[F3] V} (hg₀ : ∀ v, g₀ v = v + ε₀ v)
    (x : V ≃ₗ[F3] V) : (∀ v, x (ε₀ v) = ε₀ (x v)) ↔ x * g₀ = g₀ * x := by
  constructor
  · intro h
    ext v
    show x (g₀ v) = g₀ (x v)
    rw [hg₀, hg₀, map_add, h]
  · intro h v
    have := congrArg (fun f : V ≃ₗ[F3] V => f v) h
    simp only [LinearEquiv.mul_apply] at this
    rw [hg₀, hg₀, map_add] at this
    exact add_left_cancel this

theorem rhoA_zero_snd (A a : Mat2) : rhoA A (a, 0) = kr a 1 := by
  simp [rhoA, kr_zero_left]

theorem kr_comm_one (a q : Mat2) : kr 1 q * kr a 1 = kr a 1 * kr 1 q := by
  rw [kr_mul, kr_mul, one_mul, mul_one, mul_one, one_mul]

theorem pow3_g (g : V ≃ₗ[F3] V) (ε : V →ₗ[F3] V) (hg : ∀ v, g v = v + ε v)
    (hε : ∀ v, ε (ε v) = 0) : g * g * g = 1 := by
  ext v
  show g (g (g v)) = v
  have h3 : ∀ x : V, x + x + x = 0 := fun x => by
    have h : (1 : F3) + 1 + 1 = 0 := by decide
    calc x + x + x = ((1 : F3) + 1 + 1) • x := by simp only [add_smul, one_smul]
      _ = 0 := by rw [h, zero_smul]
  have e1 : g (g v) = v + ε v + ε v := by
    rw [hg (g v), hg v, map_add, hε, add_zero]
  have e2 : g (g (g v)) = v + (ε v + ε v + ε v) := by
    rw [hg (g (g v)), e1]
    simp only [map_add, hε, add_zero]
    abel
  rw [e2, h3, add_zero]

theorem coord_second_block (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (x x' : V)
    (h : ∀ j, b.repr (ε₀ x) (1, j) = b.repr (ε₀ x') (1, j)) : ε₀ x = ε₀ x' := by
  apply b.repr.injective
  ext ⟨a, j⟩
  fin_cases a
  · simp only [Fin.zero_eta]
    rw [repr_eps_zero b ε₀ hε₀ x j, repr_eps_zero b ε₀ hε₀ x' j]
  · exact h j

theorem second_block_ne (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (x : V) (h0 : ε₀ x ≠ 0) :
    (fun j => b.repr (ε₀ x) (1, j)) ≠ 0 := by
  intro h
  apply h0
  have : ε₀ x = ε₀ 0 := coord_second_block b ε₀ hε₀ x 0 (fun j => by
    rw [map_zero]; simpa using congrFun h j)
  rw [this, map_zero]

theorem second_block_act (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ h : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (q : Mat2)
    (hh : LinearMap.toMatrix b b h = kr 1 q) (x : V) (j : Fin 2) :
    b.repr (h (ε₀ x)) (1, j) = ∑ k, q j k * b.repr (ε₀ x) (1, k) := by
  rw [coord_mul b h _ hh]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply]

theorem second_block_act0 (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ h : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (q : Mat2)
    (hh : LinearMap.toMatrix b b h = kr 1 q) (x : V) (j : Fin 2) :
    b.repr (h (ε₀ x)) (0, j) = 0 := by
  rw [coord_mul b h _ hh]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply,
    repr_eps_zero b ε₀ hε₀]

theorem comm_of_mt (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (x : V ≃ₗ[F3] V)
    (h : mt b x * kr nU 1 = kr nU 1 * mt b x) : ∀ v, x (ε₀ v) = ε₀ (x v) := by
  have : ((x : V →ₗ[F3] V) * ε₀) = ε₀ * (x : V →ₗ[F3] V) := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hε₀]
    exact h
  intro v
  exact congrArg (fun f : V →ₗ[F3] V => f v) this

theorem eps_basis (b : Basis (Fin 2 × Fin 2) F3 V) (ε₀ : V →ₗ[F3] V)
    (hε₀ : LinearMap.toMatrix b b ε₀ = kr nU 1) (j k : Fin 2) :
    b.repr (ε₀ (b (0, j))) (1, k) = if k = j then 1 else 0 := by
  rw [coord_mul b ε₀ _ hε₀]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply, Basis.repr_self,
    Finsupp.single_apply]

theorem pair_linear [Finite V] (hV : Nat.card V = 81) (H : Subgroup (V ≃ₗ[F3] V))
    (g₀ g₁ I₀ J₀ I₁ J₁ : V ≃ₗ[F3] V) (ε₀ ε₁ : V →ₗ[F3] V)
    (hg₀ : ∀ v, g₀ v = v + ε₀ v) (hg₁ : ∀ v, g₁ v = v + ε₁ v)
    (hg₀H : g₀ ∈ H) (hg₁H : g₁ ∈ H) (hI₀H : I₀ ∈ H) (hJ₀H : J₀ ∈ H) (hI₁H : I₁ ∈ H)
    (hJ₁H : J₁ ∈ H) (hε₀ : ∀ v, ε₀ (ε₀ v) = 0) (hk₀ : ∀ v, ε₀ v = 0 → v ∈ LinearMap.range ε₀)
    (hε₁ : ∀ v, ε₁ (ε₁ v) = 0) (hc : ∀ v, ε₀ (ε₁ v) = ε₁ (ε₀ v))
    (hind : ∀ c : F3, ε₁ ≠ c • ε₀) (hQ₀ : QRelE I₀ J₀) (hQ₁ : QRelE I₁ J₁)
    (hI₀ε : ∀ v, I₀ (ε₀ v) = ε₀ (I₀ v)) (hJ₀ε : ∀ v, J₀ (ε₀ v) = ε₀ (J₀ v))
    (hI₁ε : ∀ v, I₁ (ε₁ v) = ε₁ (I₁ v)) (hJ₁ε : ∀ v, J₁ (ε₁ v) = ε₁ (J₁ v))
    (hN₀ : ∃ y ∈ q8 I₀ J₀, g₁ * I₀ = y * g₁) (hN₀' : ∃ y ∈ q8 I₀ J₀, g₁ * J₀ = y * g₁)
    (hN₁ : ∃ y ∈ q8 I₁ J₁, g₀ * I₁ = y * g₀) (hN₁' : ∃ y ∈ q8 I₁ J₁, g₀ * J₁ = y * g₀)
    (hbound : ∀ X : Subgroup (V ≃ₗ[F3] V), X ≤ H → IsPGroup 3 X → g₀ ∈ X →
      (∀ x ∈ X, x * g₀ = g₀ * x) → Nat.card X ≤ 81) :
    I₀ * I₁ = I₁ * I₀ ∧ I₀ * J₁ = J₁ * I₀ ∧ J₀ * I₁ = I₁ * J₀ ∧ J₀ * J₁ = J₁ * J₀ := by
  classical
  have hε0ne : ∃ v, ε₀ v ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton V := ⟨fun x y => by
      obtain ⟨w, hw⟩ := hk₀ x (h x)
      obtain ⟨w', hw'⟩ := hk₀ y (h y)
      rw [← hw, ← hw', h w, h w']⟩
    have : Nat.card V = 1 := Nat.card_of_subsingleton 0
    omega
  have hCH : CoordHyp (I₀ : V →ₗ[F3] V) (J₀ : V →ₗ[F3] V) ε₀ :=
    ⟨hQ₀.toQRel, hI₀ε, hJ₀ε, hε₀⟩
  obtain ⟨b, hbI, hbJ, hbε⟩ := hCH.exists_coord hV hε0ne
  have hmI₀ : mt b I₀ = kr 1 I2m0 := hbI
  have hmJ₀ : mt b J₀ = kr 1 J2m0 := hbJ
  obtain ⟨A, hA, hε₁m⟩ := g1_form b ε₀ ε₁ g₁ hmI₀ hmJ₀ hbε hg₁ hε₁ hc hind hN₀ hN₀'
  have hmg₀ : mt b g₀ = kr uU 1 := by
    have : (g₀ : V →ₗ[F3] V) = LinearMap.id + ε₀ := LinearMap.ext fun v => hg₀ v
    rw [mt, this, map_add, LinearMap.toMatrix_id, hbε, uU, kr_add_left, kr_one]
  obtain ⟨a1, b1, a2, b2, hmI₁, hmJ₁, ha1, ha2, hanti, hcase⟩ :=
    t1_data b hA ε₁ g₀ I₁ J₁ hε₁m hmg₀ hI₁ε hJ₁ε hQ₁ hN₁ hN₁'
  rcases hcase with ⟨rfl, rfl⟩ | ⟨y, hy, hb1, hb2⟩
  ·
    rw [rhoA_zero_snd] at hmI₁ hmJ₁
    refine ⟨mt_inj b ?_, mt_inj b ?_, mt_inj b ?_, mt_inj b ?_⟩ <;>
      rw [mt_mul, mt_mul] <;> simp only [hmI₀, hmJ₀, hmI₁, hmJ₁, kr_comm_one]
  ·
    exfalso
    obtain ⟨g, hgH, X, hgm, hX⟩ := bad_case b hA hy hI₀H hJ₀H hI₁H hJ₁H hmI₀ hmJ₀ hmI₁ hmJ₁
      ha1 ha2 hanti hb1 hb2
    obtain ⟨ν, hν, hνns⟩ := uequiv_of_mt b ε₀ hbε hε₀ g X hgm hX
    set H' : Subgroup (V ≃ₗ[F3] V) := H ⊓ Subgroup.centralizer ({g₀} : Set (V ≃ₗ[F3] V))
      with hH'
    have hmemH' : ∀ x, x ∈ H → (∀ v, x (ε₀ v) = ε₀ (x v)) → x ∈ H' := fun x hx hcx =>
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ((comm_of_eps hg₀ x).mp hcx)⟩
    have hcommH' : ∀ x ∈ H', ∀ v, x (ε₀ v) = ε₀ (x v) := fun x hx =>
      (comm_of_eps hg₀ x).mpr (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
    have hgc : ∀ v, g (ε₀ v) = ε₀ (g v) := by
      apply comm_of_mt b ε₀ hbε g
      rw [hgm]
      simp only [add_mul, mul_add, one_mul, mul_one, kr_mul, nU_mul_nU, kr_zero_left]
    have hgH' : g ∈ H' := hmemH' g hgH hgc
    have hνH' : uEquiv ε₀ hε₀ ν ∈ H' := by rw [hν]; exact hgH'
    have hg₀H' : g₀ ∈ H' := hmemH' g₀ hg₀H (fun v => by
      rw [hg₀ (ε₀ v), hg₀ v, map_add])
    have hg₁H' : g₁ ∈ H' := hmemH' g₁ hg₁H (fun v => by
      rw [hg₁ (ε₀ v), hg₁ v, map_add, hc])
    have hq8 : ∀ q ∈ Q8list, ∃ h ∈ H', mt b h = kr 1 q := by
      intro q hq
      have hmul : ∀ x y : Mat2, kr 1 x * kr 1 y = kr 1 (x * y) := fun x y => by
        rw [kr_mul, one_mul]
      obtain ⟨h, hh, hmh⟩ := mt_q8_gen' b (fun q : Mat2 => kr 1 q) (· * ·) (1 : Mat2) hmul kr_one
        hmI₀ hmJ₀ q (by rw [q8g_mat2]; exact hq)
      refine ⟨h, hmemH' h (q8_mem hI₀H hJ₀H h hh) (comm_of_mt b ε₀ hbε h ?_), hmh⟩
      rw [hmh, kr_mul, kr_mul, one_mul, mul_one, mul_one, one_mul]
    have hW := card_range_eq_nine hV ε₀ hε₀ hk₀
    have htrans : ∀ w w' : V, w ∈ LinearMap.range ε₀ → w' ∈ LinearMap.range ε₀ → w ≠ 0 →
        w' ≠ 0 → ∃ h ∈ H', h w = w' := by
      intro w w' hw hw' hw0 hw'0
      obtain ⟨x, rfl⟩ := hw
      obtain ⟨x', rfl⟩ := hw'
      have hc0 := second_block_ne b ε₀ hbε x hw0
      have hc'0 := second_block_ne b ε₀ hbε x' hw'0
      obtain ⟨q, hq, hqc⟩ := trans_dec _ _ hc0 hc'0
      obtain ⟨h, hh, hmh⟩ := hq8 q hq
      refine ⟨h, hh, ?_⟩
      have hhm : LinearMap.toMatrix b b (h : V →ₗ[F3] V) = kr 1 q := hmh
      apply b.repr.injective
      ext ⟨a, j⟩
      fin_cases a
      · exact (second_block_act0 b ε₀ (h : V →ₗ[F3] V) hbε q hhm x j).trans
          (repr_eps_zero b ε₀ hbε x' j).symm
      · have := congrFun hqc j
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
        refine (second_block_act b ε₀ (h : V →ₗ[F3] V) hbε q hhm x j).trans ?_
        simpa [Fin.sum_univ_two] using this
    have hord3 : ∃ s ∈ H', s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε₀, s w ≠ w := by
      refine ⟨g₁, hg₁H', ?_, ?_⟩
      · have := pow3_g g₁ ε₁ hg₁ hε₁
        have e : g₁ ^ 3 = g₁ ^ 2 * g₁ := pow_succ g₁ 2
        rw [e, pow_two]
        exact this
      · obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          apply nilp8_ne A hA
          ext i j
          exact hcon i j
        refine ⟨ε₀ (b (0, j)), ⟨_, rfl⟩, fun hEq => ?_⟩
        have h1 : ε₁ (ε₀ (b (0, j))) = 0 := by
          have := hg₁ (ε₀ (b (0, j)))
          rw [hEq] at this
          exact (add_eq_left.mp this.symm)
        have h2 := coord_mul b ε₁ _ hε₁m (ε₀ (b (0, j))) (1, i)
        rw [h1] at h2
        simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply,
          eps_basis b ε₀ hbε, repr_eps_zero b ε₀ hbε] at h2
        exact hij (by fin_cases j <;> simp at h2 <;> first | exact h2 | exact h2.symm)
    obtain ⟨X', hX'H', hX'3, hX'card, hg₀X', hX'comm⟩ :=
      na_core' ε₀ hε₀ hW hk₀ H' hcommH' g₀ hg₀ hg₀H' htrans hord3 ν hνH' hνns
    have := hbound X' (hX'H'.trans inf_le_left) hX'3 hg₀X' hX'comm
    omega

end Main

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

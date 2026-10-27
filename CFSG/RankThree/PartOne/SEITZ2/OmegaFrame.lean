module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure OmegaFrame (Q : QuadraticForm K V) (b c : K) where
  e : Fin 3 → V
  f : Fin 3 → V
  t : Fin 2 → V
  Q_e : ∀ i, Q (e i) = 0
  Q_f : ∀ i, Q (f i) = 0
  Q_t₀ : Q (t 0) = 1
  Q_t₁ : Q (t 1) = c
  polar_ee : ∀ i j, polar Q (e i) (e j) = 0
  polar_ff : ∀ i j, polar Q (f i) (f j) = 0
  polar_ef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0
  polar_et : ∀ i s, polar Q (e i) (t s) = 0
  polar_ft : ∀ i s, polar Q (f i) (t s) = 0
  polar_t : polar Q (t 0) (t 1) = b
  b_ne : b ≠ 0
  expand : ∀ v, v = ∑ i, polar Q v (f i) • e i + ∑ i, polar Q v (e i) • f i +
    (b⁻¹ * polar Q v (t 1)) • t 0 + (b⁻¹ * polar Q v (t 0)) • t 1

@[expose] def Phi (Q : QuadraticForm K V) (u w x y : V) : K :=
  polar Q x u * polar Q y w + polar Q x w * polar Q y u

section PhiLemmas

variable (Q : QuadraticForm K V) (u w : V)

theorem Phi_add_left (x x' y : V) :
    Phi Q u w (x + x') y = Phi Q u w x y + Phi Q u w x' y := by
  unfold Phi
  simp only [polar_add_left]
  ring

theorem Phi_add_right (x y y' : V) :
    Phi Q u w x (y + y') = Phi Q u w x y + Phi Q u w x y' := by
  unfold Phi
  simp only [polar_add_left]
  ring

theorem Phi_smul_left (a : K) (x y : V) : Phi Q u w (a • x) y = a * Phi Q u w x y := by
  unfold Phi
  simp only [polar_smul_left_eq]
  ring

theorem Phi_smul_right (a : K) (x y : V) : Phi Q u w x (a • y) = a * Phi Q u w x y := by
  unfold Phi
  simp only [polar_smul_left_eq]
  ring

theorem Phi_comm (x y : V) : Phi Q u w x y = Phi Q u w y x := by
  unfold Phi
  ring

theorem Phi_self [CharP K 2] (x : V) : Phi Q u w x x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold Phi
  linear_combination (polar Q x u * polar Q x w) * h2

@[expose] noncomputable def PhiLin (Q : QuadraticForm K V) (u w : V) : V →ₗ[K] V →ₗ[K] K :=
  LinearMap.mk₂ K (Phi Q u w) (Phi_add_left Q u w) (Phi_smul_left Q u w) (Phi_add_right Q u w)
    (Phi_smul_right Q u w)

theorem PhiLin_apply (x y : V) : PhiLin Q u w x y = Phi Q u w x y := rfl

end PhiLemmas

theorem mem_of_sq_mem [Finite K] [CharP K 2] {k : Subfield K} {x : K} (hx : x ^ 2 ∈ k) :
    x ∈ k := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let f : k → k := fun z => ⟨(z : K) ^ 2, k.pow_mem z.2 2⟩
  have hinj : Function.Injective f := by
    intro z z' hzz
    have h1 : (z : K) ^ 2 = (z' : K) ^ 2 := congrArg Subtype.val hzz
    have h3 : ((z : K) + z') ^ 2 = 0 := by
      linear_combination h1 + ((z' : K) ^ 2 + (z : K) * z') * h2
    have h4 : (z : K) + z' = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    apply Subtype.ext
    linear_combination h4 - (z' : K) * h2
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj ⟨x ^ 2, hx⟩
  have h1 : (y : K) ^ 2 = x ^ 2 := congrArg Subtype.val hy
  have h3 : (x + (y : K)) ^ 2 = 0 := by
    linear_combination h1 + (x ^ 2 + x * y) * h2
  have h4 : x + (y : K) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  have : x = y := by linear_combination h4 - (y : K) * h2
  rw [this]
  exact y.2

section Rational

variable {Q : QuadraticForm K V} {b c : K} (F : OmegaFrame Q b c)

@[expose] def OmegaFrame.vec : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → V := Sum.elim F.e (Sum.elim F.f F.t)

@[expose] def OmegaFrame.coef (v : V) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K :=
  Sum.elim (fun i => polar Q v (F.f i)) (Sum.elim (fun i => polar Q v (F.e i))
    ![b⁻¹ * polar Q v (F.t 1), b⁻¹ * polar Q v (F.t 0)])

theorem OmegaFrame.expand' (v : V) : v = ∑ α, F.coef v α • F.vec α := by
  conv_lhs => rw [F.expand v]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, OmegaFrame.coef, OmegaFrame.vec,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

@[expose] def OmegaFrame.IsRat (k : Subfield K) (v : V) : Prop := ∀ α, F.coef v α ∈ k

variable {F} {k : Subfield K}

theorem OmegaFrame.IsRat.add {x y : V} (hx : F.IsRat k x) (hy : F.IsRat k y) :
    F.IsRat k (x + y) := by
  intro α
  have := k.add_mem (hx α) (hy α)
  rcases α with i | i | s
  · simpa [OmegaFrame.coef, polar_add_left] using this
  · simpa [OmegaFrame.coef, polar_add_left] using this
  · fin_cases s
    · simpa [OmegaFrame.coef, polar_add_left, mul_add] using this
    · simpa [OmegaFrame.coef, polar_add_left, mul_add] using this

theorem OmegaFrame.IsRat.smul {x : V} (hx : F.IsRat k x) {a : K} (ha : a ∈ k) :
    F.IsRat k (a • x) := by
  intro α
  have := k.mul_mem ha (hx α)
  rcases α with i | i | s
  · simpa [OmegaFrame.coef, polar_smul_left_eq] using this
  · simpa [OmegaFrame.coef, polar_smul_left_eq] using this
  · fin_cases s
    · simpa [OmegaFrame.coef, polar_smul_left_eq, mul_left_comm] using this
    · simpa [OmegaFrame.coef, polar_smul_left_eq, mul_left_comm] using this

theorem OmegaFrame.polar_t_self [CharP K 2] (s : Fin 2) : polar Q (F.t s) (F.t s) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [polar_self_eq_two_mul, h2, zero_mul]

theorem OmegaFrame.isRat_e [CharP K 2] (j : Fin 3) : F.IsRat k (F.e j) := by
  intro α
  rcases α with i | i | s
  · simp only [OmegaFrame.coef, Sum.elim_inl, F.polar_ef]
    split_ifs <;> simp
  · simp [OmegaFrame.coef, F.polar_ee]
  · fin_cases s <;> simp [OmegaFrame.coef, F.polar_et]

theorem OmegaFrame.isRat_f [CharP K 2] (j : Fin 3) : F.IsRat k (F.f j) := by
  intro α
  rcases α with i | i | s
  · simp [OmegaFrame.coef, F.polar_ff]
  · simp only [OmegaFrame.coef, Sum.elim_inl, Sum.elim_inr]
    rw [polar_comm, F.polar_ef]
    split_ifs <;> simp
  · fin_cases s <;> simp [OmegaFrame.coef, F.polar_ft]

theorem OmegaFrame.isRat_t [CharP K 2] (s : Fin 2) : F.IsRat k (F.t s) := by
  have hb0 := F.b_ne
  have hbt : polar Q (F.t 1) (F.t 0) = b := by rw [polar_comm, F.polar_t]
  intro α
  rcases α with i | i | s'
  · simp only [OmegaFrame.coef, Sum.elim_inl]
    rw [polar_comm, F.polar_ft]
    exact k.zero_mem
  · simp only [OmegaFrame.coef, Sum.elim_inl, Sum.elim_inr]
    rw [polar_comm, F.polar_et]
    exact k.zero_mem
  · fin_cases s <;> fin_cases s' <;>
      simp [OmegaFrame.coef, F.polar_t, hbt, F.polar_t_self, hb0, k.zero_mem, k.one_mem]

theorem Phi_mem_of_frame (u w : V) (hΦ : ∀ α β, Phi Q u w (F.vec α) (F.vec β) ∈ k) {x y : V}
    (hx : F.IsRat k x) (hy : F.IsRat k y) : Phi Q u w x y ∈ k := by
  have key : Phi Q u w x y =
      ∑ α, ∑ β, F.coef x α * (F.coef y β * Phi Q u w (F.vec α) (F.vec β)) := by
    calc Phi Q u w x y = PhiLin Q u w x y := rfl
      _ = _ := by
        conv_lhs => rw [F.expand' x, F.expand' y]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          PhiLin_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  rw [key]
  refine Subfield.sum_mem _ fun α _ => Subfield.sum_mem _ fun β _ => ?_
  exact k.mul_mem (hx α) (k.mul_mem (hy β) (hΦ α β))

theorem Phi_plucker [CharP K 2] (u w a₁ a₂ a₃ a₄ : V) :
    Phi Q u w a₁ a₂ * Phi Q u w a₃ a₄ + Phi Q u w a₁ a₃ * Phi Q u w a₂ a₄ +
      Phi Q u w a₁ a₄ * Phi Q u w a₂ a₃ = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold Phi
  set u₁ := polar Q a₁ u
  set u₂ := polar Q a₂ u
  set u₃ := polar Q a₃ u
  set u₄ := polar Q a₄ u
  set w₁ := polar Q a₁ w
  set w₂ := polar Q a₂ w
  set w₃ := polar Q a₃ w
  set w₄ := polar Q a₄ w
  linear_combination (u₁ * u₂ * w₃ * w₄ + u₁ * u₃ * w₂ * w₄ + u₁ * u₄ * w₂ * w₃ +
    u₂ * u₃ * w₁ * w₄ + u₂ * u₄ * w₁ * w₃ + u₃ * u₄ * w₁ * w₂) * h2

theorem Phi_relation (u w : V) :
    ∑ i, Phi Q u w (F.e i) (F.f i) + b⁻¹ * Phi Q u w (F.t 0) (F.t 1) = polar Q u w := by
  conv_rhs => rw [F.expand u]
  simp only [polar_add_left, polar_smul_left_eq, Fin.sum_univ_three, Phi]
  rw [polar_comm Q u (F.f 0), polar_comm Q u (F.f 1), polar_comm Q u (F.f 2),
    polar_comm Q u (F.e 0), polar_comm Q u (F.e 1), polar_comm Q u (F.e 2),
    polar_comm Q u (F.t 0), polar_comm Q u (F.t 1)]
  ring

theorem map_add₃ (x y z : V) : Q (x + y + z) =
    Q x + Q y + Q z + polar Q x y + polar Q x z + polar Q y z := by
  rw [QuadraticMap.map_add Q (x + y) z, QuadraticMap.map_add Q x y, polar_add_left]
  ring

theorem OmegaFrame.aux_Q [CharP K 2] (j : Fin 3) (s : Fin 2) :
    Q ((![1, c] s) • F.e j + F.f j + F.t s) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQt : Q (F.t s) = ![1, c] s := by fin_cases s <;> simp [F.Q_t₀, F.Q_t₁]
  rw [map_add₃, map_smul_eq_sq, F.Q_e, F.Q_f, hQt, polar_smul_left_eq, polar_smul_left_eq,
    F.polar_ef, F.polar_et, F.polar_ft]
  simp
  linear_combination (![1, c] s) * h2

theorem OmegaFrame.aux_isRat [CharP K 2] {k : Subfield K} (hc : c ∈ k) (j : Fin 3) (s : Fin 2) :
    F.IsRat k ((![1, c] s) • F.e j + F.f j + F.t s) := by
  have ha : (![1, c] s) ∈ k := by fin_cases s <;> simp [k.one_mem, hc]
  exact (((F.isRat_e j).smul ha).add (F.isRat_f j)).add (F.isRat_t s)

theorem OmegaFrame.aux_polar_e (j i : Fin 3) (hij : i ≠ j) (s : Fin 2) :
    polar Q (F.e i) ((![1, c] s) • F.e j + F.f j + F.t s) = 0 := by
  simp [polar_add_right, F.polar_ee, F.polar_ef, F.polar_et, hij]

theorem OmegaFrame.aux_polar_f (j i : Fin 3) (hij : i ≠ j) (s : Fin 2) :
    polar Q (F.f i) ((![1, c] s) • F.e j + F.f j + F.t s) = 0 := by
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_comm Q (F.f i) (F.e j),
    F.polar_ef, F.polar_ff, F.polar_ft]
  simp [Ne.symm hij]

theorem phi_frame_mem [Finite K] [CharP K 2] {k : Subfield K} (hb : b ∈ k) (hc : c ∈ k)
    {u w : V} (huw : polar Q u w = 0)
    (H : ∀ x y, F.IsRat k x → F.IsRat k y → Q x = 0 → Q y = 0 → polar Q x y = 0 →
      Phi Q u w x y ∈ k) :
    ∀ α β, Phi Q u w (F.vec α) (F.vec β) ∈ k := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb0 := F.b_ne
  have P1 : ∀ i j, Phi Q u w (F.e i) (F.e j) ∈ k := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Phi_self]
      exact k.zero_mem
    · exact H _ _ (F.isRat_e i) (F.isRat_e j) (F.Q_e i) (F.Q_e j) (F.polar_ee i j)
  have P2 : ∀ i j, Phi Q u w (F.f i) (F.f j) ∈ k := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Phi_self]
      exact k.zero_mem
    · exact H _ _ (F.isRat_f i) (F.isRat_f j) (F.Q_f i) (F.Q_f j) (F.polar_ff i j)
  have P3 : ∀ i j, i ≠ j → Phi Q u w (F.e i) (F.f j) ∈ k := by
    intro i j hij
    exact H _ _ (F.isRat_e i) (F.isRat_f j) (F.Q_e i) (F.Q_f j) (by rw [F.polar_ef]; simp [hij])
  have P3' : ∀ i j, i ≠ j → Phi Q u w (F.f i) (F.e j) ∈ k := fun i j hij => by
    rw [Phi_comm]
    exact P3 j i (Ne.symm hij)
  have hcoef : ∀ s : Fin 2, (![1, c] s) ∈ k := by
    intro s
    fin_cases s <;> simp [k.one_mem, hc]
  have exists_ne : ∀ i : Fin 3, ∃ j : Fin 3, i ≠ j := by
    intro i
    fin_cases i
    exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
  have P4 : ∀ i s, Phi Q u w (F.e i) (F.t s) ∈ k := by
    intro i s
    obtain ⟨j, hij⟩ := exists_ne i
    have hH := H (F.e i) _ (F.isRat_e i) (F.aux_isRat hc j s) (F.Q_e i) (F.aux_Q j s)
      (F.aux_polar_e j i hij s)
    rw [Phi_add_right, Phi_add_right, Phi_smul_right] at hH
    have := k.sub_mem hH (k.add_mem (k.mul_mem (hcoef s) (P1 i j)) (P3 i j hij))
    convert this using 1
    ring
  have P5 : ∀ i s, Phi Q u w (F.f i) (F.t s) ∈ k := by
    intro i s
    obtain ⟨j, hij⟩ := exists_ne i
    have hH := H (F.f i) _ (F.isRat_f i) (F.aux_isRat hc j s) (F.Q_f i) (F.aux_Q j s)
      (F.aux_polar_f j i hij s)
    rw [Phi_add_right, Phi_add_right, Phi_smul_right] at hH
    have := k.sub_mem hH (k.add_mem (k.mul_mem (hcoef s) (P3' i j hij)) (P2 i j))
    convert this using 1
    ring
  have hS : Phi Q u w (F.e 0) (F.f 0) + Phi Q u w (F.e 1) (F.f 1) + Phi Q u w (F.e 2) (F.f 2) +
      b⁻¹ * Phi Q u w (F.t 0) (F.t 1) = 0 := by
    have := Phi_relation (F := F) u w
    rw [huw, Fin.sum_univ_three] at this
    exact this
  have hCC : ∀ i j, i ≠ j →
      Phi Q u w (F.e i) (F.f i) * Phi Q u w (F.e j) (F.f j) ∈ k := by
    intro i j hij
    have hp := Phi_plucker (Q := Q) u w (F.e i) (F.f i) (F.e j) (F.f j)
    have : Phi Q u w (F.e i) (F.f i) * Phi Q u w (F.e j) (F.f j) =
        -(Phi Q u w (F.e i) (F.e j) * Phi Q u w (F.f i) (F.f j) +
          Phi Q u w (F.e i) (F.f j) * Phi Q u w (F.f i) (F.e j)) := by
      linear_combination hp
    rw [this]
    exact k.neg_mem (k.add_mem (k.mul_mem (P1 i j) (P2 i j))
      (k.mul_mem (P3 i j hij) (P3' i j hij)))
  have hCT : ∀ i, Phi Q u w (F.e i) (F.f i) * Phi Q u w (F.t 0) (F.t 1) ∈ k := by
    intro i
    have hp := Phi_plucker (Q := Q) u w (F.e i) (F.f i) (F.t 0) (F.t 1)
    have : Phi Q u w (F.e i) (F.f i) * Phi Q u w (F.t 0) (F.t 1) =
        -(Phi Q u w (F.e i) (F.t 0) * Phi Q u w (F.f i) (F.t 1) +
          Phi Q u w (F.e i) (F.t 1) * Phi Q u w (F.f i) (F.t 0)) := by
      linear_combination hp
    rw [this]
    exact k.neg_mem (k.add_mem (k.mul_mem (P4 i 0) (P5 i 1)) (k.mul_mem (P4 i 1) (P5 i 0)))
  have hbi : b⁻¹ ∈ k := k.inv_mem hb
  have hC0 : Phi Q u w (F.e 0) (F.f 0) ∈ k := by
    apply mem_of_sq_mem
    have : Phi Q u w (F.e 0) (F.f 0) ^ 2 = -(Phi Q u w (F.e 0) (F.f 0) *
        Phi Q u w (F.e 1) (F.f 1) + Phi Q u w (F.e 0) (F.f 0) * Phi Q u w (F.e 2) (F.f 2) +
        b⁻¹ * (Phi Q u w (F.e 0) (F.f 0) * Phi Q u w (F.t 0) (F.t 1))) := by
      linear_combination (Phi Q u w (F.e 0) (F.f 0)) * hS
    rw [this]
    exact k.neg_mem (k.add_mem (k.add_mem (hCC 0 1 (by decide)) (hCC 0 2 (by decide)))
      (k.mul_mem hbi (hCT 0)))
  have hC1 : Phi Q u w (F.e 1) (F.f 1) ∈ k := by
    apply mem_of_sq_mem
    have : Phi Q u w (F.e 1) (F.f 1) ^ 2 = -(Phi Q u w (F.e 1) (F.f 1) *
        Phi Q u w (F.e 0) (F.f 0) + Phi Q u w (F.e 1) (F.f 1) * Phi Q u w (F.e 2) (F.f 2) +
        b⁻¹ * (Phi Q u w (F.e 1) (F.f 1) * Phi Q u w (F.t 0) (F.t 1))) := by
      linear_combination (Phi Q u w (F.e 1) (F.f 1)) * hS
    rw [this]
    exact k.neg_mem (k.add_mem (k.add_mem (hCC 1 0 (by decide)) (hCC 1 2 (by decide)))
      (k.mul_mem hbi (hCT 1)))
  have hC2 : Phi Q u w (F.e 2) (F.f 2) ∈ k := by
    apply mem_of_sq_mem
    have : Phi Q u w (F.e 2) (F.f 2) ^ 2 = -(Phi Q u w (F.e 2) (F.f 2) *
        Phi Q u w (F.e 0) (F.f 0) + Phi Q u w (F.e 2) (F.f 2) * Phi Q u w (F.e 1) (F.f 1) +
        b⁻¹ * (Phi Q u w (F.e 2) (F.f 2) * Phi Q u w (F.t 0) (F.t 1))) := by
      linear_combination (Phi Q u w (F.e 2) (F.f 2)) * hS
    rw [this]
    exact k.neg_mem (k.add_mem (k.add_mem (hCC 2 0 (by decide)) (hCC 2 1 (by decide)))
      (k.mul_mem hbi (hCT 2)))
  have P6 : ∀ i, Phi Q u w (F.e i) (F.f i) ∈ k := by
    intro i
    fin_cases i
    exacts [hC0, hC1, hC2]
  have P7 : Phi Q u w (F.t 0) (F.t 1) ∈ k := by
    have : Phi Q u w (F.t 0) (F.t 1) = -(b * (Phi Q u w (F.e 0) (F.f 0) +
        Phi Q u w (F.e 1) (F.f 1) + Phi Q u w (F.e 2) (F.f 2))) := by
      have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
      linear_combination b * hS - (Phi Q u w (F.t 0) (F.t 1)) * hbb
    rw [this]
    exact k.neg_mem (k.mul_mem hb (k.add_mem (k.add_mem (P6 0) (P6 1)) (P6 2)))
  intro α β
  rcases α with i | i | s <;> rcases β with j | j | s'
  · exact P1 i j
  · show Phi Q u w (F.e i) (F.f j) ∈ k
    by_cases hij : i = j
    · subst hij
      exact P6 i
    · exact P3 i j hij
  · exact P4 i s'
  · show Phi Q u w (F.f i) (F.e j) ∈ k
    by_cases hij : i = j
    · subst hij
      rw [Phi_comm]
      exact P6 i
    · exact P3' i j hij
  · exact P2 i j
  · exact P5 i s'
  · show Phi Q u w (F.t s) (F.e j) ∈ k
    rw [Phi_comm]
    exact P4 j s
  · show Phi Q u w (F.t s) (F.f j) ∈ k
    rw [Phi_comm]
    exact P5 j s
  · show Phi Q u w (F.t s) (F.t s') ∈ k
    fin_cases s <;> fin_cases s'
    · rw [Phi_self]
      exact k.zero_mem
    · exact P7
    · rw [Phi_comm]
      exact P7
    · rw [Phi_self]
      exact k.zero_mem

theorem OmegaFrame.polar_fe (i j : Fin 3) :
    polar Q (F.f i) (F.e j) = if j = i then 1 else 0 := by
  rw [polar_comm, F.polar_ef]

theorem OmegaFrame.polar_te (s : Fin 2) (i : Fin 3) : polar Q (F.t s) (F.e i) = 0 := by
  rw [polar_comm, F.polar_et]

theorem OmegaFrame.polar_tf (s : Fin 2) (i : Fin 3) : polar Q (F.t s) (F.f i) = 0 := by
  rw [polar_comm, F.polar_ft]

@[expose] def OmegaFrame.tau (F : OmegaFrame Q b c) (s : Fin 2) : V :=
  (![1, c] s) • F.e 1 + F.f 1 + F.t s

theorem OmegaFrame.tau_Q [CharP K 2] (s : Fin 2) : Q (F.tau s) = 0 := F.aux_Q 1 s

theorem OmegaFrame.tau_isRat [CharP K 2] {k : Subfield K} (hc : c ∈ k) (s : Fin 2) :
    F.IsRat k (F.tau s) := F.aux_isRat hc 1 s

theorem OmegaFrame.polar_e_tau (i : Fin 3) (hi : i ≠ 1) (s : Fin 2) :
    polar Q (F.e i) (F.tau s) = 0 := F.aux_polar_e 1 i hi s

theorem OmegaFrame.polar_f_tau (i : Fin 3) (hi : i ≠ 1) (s : Fin 2) :
    polar Q (F.f i) (F.tau s) = 0 := F.aux_polar_f 1 i hi s

theorem OmegaFrame.polar_e1_tau (s : Fin 2) : polar Q (F.e 1) (F.tau s) = 1 := by
  unfold OmegaFrame.tau
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, F.polar_ee, F.polar_ef, F.polar_et]
  simp

end Rational

end Frame

end CFSG.RankThree.PartOne.SEITZ2

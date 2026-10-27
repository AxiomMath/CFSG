module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod

public section

namespace Certificates.FzJ36

abbrev Q8 : Type := QuaternionGroup 2

abbrev N3 : Type := Q8 × Q8 × Q8

@[expose] def swapAut : MulAut N3 where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def act : Multiplicative (ZMod 2) →* MulAut N3 where
  toFun e := if e = 1 then 1 else swapAut
  map_one' := by simp
  map_mul' a b := by
    have h : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hmul : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    have hs : swapAut * swapAut = 1 := MulEquiv.ext fun _ => rfl
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
      simp [hne, hmul, hs]

abbrev Model : Type := N3 ⋊[act] Multiplicative (ZMod 2)

instance : Fintype Model :=
  Fintype.ofEquiv (N3 × Multiplicative (ZMod 2))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun s => (s.left, s.right)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[expose] def zeta : Model := ⟨(QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2), 1⟩

@[expose] def xt : Model := ⟨(1, 1, QuaternionGroup.a 1), 1⟩

@[expose] def KEq (g h : Model) : Prop := g = h ∨ g = h * zeta

instance (g h : Model) : Decidable (KEq g h) := by unfold KEq; infer_instance

private lemma zmod2 (e : Multiplicative (ZMod 2)) :
    e = 1 ∨ e = Multiplicative.ofAdd 1 := by
  revert e
  decide

private lemma q8_a2_central (q : Q8) :
    (QuaternionGroup.a 2 : Q8) * q = q * QuaternionGroup.a 2 := by
  rcases q with i | i
  · rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  · rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, sub_eq_add_neg]
    congr 1

private lemma zeta_left_central (n : N3) : n * zeta.left = zeta.left * n := by
  obtain ⟨q1, q2, q3⟩ := n
  ext <;> simp [zeta, q8_a2_central]

private lemma swapAut_a2 :
    swapAut (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2)
      = (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2) := rfl

private lemma act_zeta (e : Multiplicative (ZMod 2)) :
    act e (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2)
      = (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  rcases zmod2 e with rfl | rfl
  · simp [act]
  · have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    simp [act, hne, swapAut_a2]

theorem zeta_mul_zeta : zeta * zeta = 1 := by
  decide

theorem zeta_central (g : Model) : g * zeta = zeta * g := by
  obtain ⟨n, e⟩ := g
  apply SemidirectProduct.ext
  · simpa [zeta, act_zeta e, map_one, MulAut.one_apply] using zeta_left_central n
  · simp [SemidirectProduct.mul_right, zeta]

theorem zeta_ne_one : zeta ≠ 1 := by
  decide

theorem card_model : Nat.card Model = 1024 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (SemidirectProduct.equivProd (φ := act))]
  simp only [Fintype.card_prod, QuaternionGroup.card]
  have h2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := ZMod.card 2
  rw [h2]

theorem KEq.refl (g : Model) : KEq g g := Or.inl rfl

theorem KEq.symm {g h : Model} (hgh : KEq g h) : KEq h g := by
  rcases hgh with rfl | hgh
  · exact Or.inl rfl
  · right
    rw [hgh, mul_assoc, zeta_mul_zeta, mul_one]

theorem KEq.trans {g h k : Model} (h₁ : KEq g h) (h₂ : KEq h k) : KEq g k := by
  rcases h₁ with rfl | h₁
  · rcases h₂ with rfl | h₂
    · exact Or.inl rfl
    · exact Or.inr h₂
  · rcases h₂ with rfl | h₂
    · exact Or.inr h₁
    · left
      rw [h₁, h₂, mul_assoc, zeta_mul_zeta, mul_one]

theorem KEq.mul {g g' h h' : Model} (h₁ : KEq g g') (h₂ : KEq h h') : KEq (g * h) (g' * h') := by
  rcases h₁ with hg | hg <;> rcases h₂ with hh | hh
  · exact Or.inl (by rw [hg, hh])
  · right
    rw [hg, hh, ← mul_assoc]
  · right
    rw [hg, hh, mul_assoc, mul_assoc, zeta_central h']
  · left
    rw [hg, hh]
    calc (g' * zeta) * (h' * zeta) = g' * (zeta * (h' * zeta)) := by rw [mul_assoc]
      _ = g' * ((zeta * h') * zeta) := by rw [mul_assoc]
      _ = g' * ((h' * zeta) * zeta) := by rw [zeta_central h']
      _ = g' * (h' * (zeta * zeta)) := by rw [mul_assoc]
      _ = g' * (h' * 1) := by rw [zeta_mul_zeta]
      _ = g' * h' := by rw [mul_one]

theorem KEq.mul_zeta (g : Model) : KEq (g * zeta) g := Or.inr rfl

@[expose] def MJ (u : Model) : Prop :=
  ∃ y v w : Model, KEq (y * u) (u * y) ∧ KEq (v * u) (u * v) ∧ KEq (w * u) (u * w) ∧
    ¬ KEq (y * y) 1 ∧ ¬ KEq (y * y) (u * u) ∧ KEq (v * v) (u * u) ∧ KEq (w * w) (u * u) ∧
    KEq (w * v * w⁻¹) v⁻¹ ∧ KEq (y * v) (v * y) ∧ KEq (y * w) (w * y)

private def kq (g h : Model) : Bool := decide (KEq g h)

private lemma kq_eq_true {g h : Model} : kq g h = true ↔ KEq g h := by
  simp [kq]

private def allQ8 (_ : Unit := ()) : List Q8 :=
  [QuaternionGroup.a 0, QuaternionGroup.a 1, QuaternionGroup.a 2, QuaternionGroup.a 3,
   QuaternionGroup.xa 0, QuaternionGroup.xa 1, QuaternionGroup.xa 2, QuaternionGroup.xa 3]

private lemma zmod4 (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

private lemma allQ8_mem (q : Q8) : q ∈ allQ8 () := by
  rcases q with i | i <;> rcases zmod4 i with rfl | rfl | rfl | rfl <;> simp [allQ8]

private def allModel (_ : Unit := ()) : List Model :=
  let l := allQ8 ()
  l.flatMap fun q1 => l.flatMap fun q2 => l.flatMap fun q3 =>
    [⟨(q1, q2, q3), 1⟩, ⟨(q1, q2, q3), Multiplicative.ofAdd 1⟩]

private lemma allModel_mem (g : Model) : g ∈ allModel () := by
  obtain ⟨⟨q1, q2, q3⟩, e⟩ := g
  rcases zmod2 e with rfl | rfl <;>
    exact List.mem_flatMap.mpr ⟨q1, allQ8_mem q1,
      List.mem_flatMap.mpr ⟨q2, allQ8_mem q2,
        List.mem_flatMap.mpr ⟨q3, allQ8_mem q3, by simp⟩⟩⟩

private def centList (u : Model) : List Model :=
  (allModel ()).filter fun g => kq (g * u) (u * g)

private def sqrtList (u : Model) : List Model :=
  (centList u).filter fun v => kq (v * v) (u * u)

private def centListOf (u v : Model) : List Model :=
  (centList u).filter fun y => kq (y * v) (v * y)

private def cvPairs (u : Model) : List (Model × List Model) :=
  (sqrtList u).map fun v => (v, centListOf u v)

def fzJCheck (u : Model) (_ : Unit := ()) : Bool :=
  (cvPairs u).all fun p =>
    (sqrtList u).all fun w =>
      !(kq (w * p.1 * w⁻¹) p.1⁻¹) ||
        p.2.all fun y =>
          !(kq (y * w) (w * y)) || (kq (y * y) 1 || kq (y * y) (u * u))

theorem fzJCheck_sound (u : Model) (h : fzJCheck u () = true) : ¬ MJ u := by
  rintro ⟨y, v, w, hyu, hvu, hwu, hy1, hy2, hv2, hw2, hwv, hyv, hyw⟩
  simp only [fzJCheck] at h
  have hyC : y ∈ centList u := by
    rw [centList, List.mem_filter]
    exact ⟨allModel_mem y, (kq_eq_true).mpr hyu⟩
  have hvS : v ∈ sqrtList u := by
    rw [sqrtList, List.mem_filter]
    exact ⟨by
      rw [centList, List.mem_filter]
      exact ⟨allModel_mem v, (kq_eq_true).mpr hvu⟩, (kq_eq_true).mpr hv2⟩
  have hwS : w ∈ sqrtList u := by
    rw [sqrtList, List.mem_filter]
    exact ⟨by
      rw [centList, List.mem_filter]
      exact ⟨allModel_mem w, (kq_eq_true).mpr hwu⟩, (kq_eq_true).mpr hw2⟩
  have hp : (v, centListOf u v) ∈ cvPairs u := by
    rw [cvPairs, List.mem_map]
    exact ⟨v, hvS, rfl⟩
  have h1 := List.all_eq_true.mp h (v, centListOf u v) hp
  have h2 := List.all_eq_true.mp h1 w hwS
  rw [Bool.or_eq_true_iff, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact absurd ((kq_eq_true).mpr hwv) (by rw [h2]; decide)
  have hyCv : y ∈ centListOf u v := by
    rw [centListOf, List.mem_filter]
    exact ⟨hyC, (kq_eq_true).mpr hyv⟩
  have h3 := List.all_eq_true.mp h2 y hyCv
  rw [Bool.or_eq_true_iff, Bool.not_eq_true'] at h3
  rcases h3 with h3 | h3
  · exact absurd ((kq_eq_true).mpr hyw) (by rw [h3]; decide)
  rw [Bool.or_eq_true_iff] at h3
  rcases h3 with h3 | h3
  · exact hy1 ((kq_eq_true).mp h3)
  · exact hy2 ((kq_eq_true).mp h3)

@[expose] def gens : List Model :=
  [⟨(QuaternionGroup.a 1, 1, 1), 1⟩, ⟨(QuaternionGroup.xa 0, 1, 1), 1⟩,
    ⟨(1, QuaternionGroup.a 1, 1), 1⟩, ⟨(1, QuaternionGroup.xa 0, 1), 1⟩,
    ⟨(1, 1, QuaternionGroup.a 1), 1⟩, ⟨(1, 1, QuaternionGroup.xa 0), 1⟩,
    ⟨1, Multiplicative.ofAdd 1⟩]

theorem model_center_sq (g : Model) (hg : ∀ h ∈ gens, KEq (g * h) (h * g)) : KEq (g * g) 1 := by
  revert g
  decide +kernel

@[expose] def R3Z (g : Model) : Prop :=
  ∃ (q : Q8) (i j : Fin 2),
    KEq g ⟨(QuaternionGroup.a 2 ^ (i : ℕ), QuaternionGroup.a 2 ^ (j : ℕ), q), 1⟩

@[expose] def P36 (n : N3) : Prop :=
  KEq ((⟨n, 1⟩ : Model) * ⟨n, 1⟩) (xt * xt) ∧ ¬ R3Z ⟨n, 1⟩

private instance r3zDecidable (g : Model) : Decidable (R3Z g) := by
  unfold R3Z
  infer_instance

private instance p36Decidable (n : N3) : Decidable (P36 n) := by
  unfold P36
  infer_instance

theorem JHolds (n : N3) (hn : P36 n) : MJ ⟨n, 1⟩ := by
  refine ⟨⟨(n.1, 1, 1), 1⟩, ⟨(1, 1, QuaternionGroup.a 1), 1⟩,
    ⟨(1, 1, QuaternionGroup.xa 0), 1⟩, ?_⟩
  revert n
  decide +kernel

end Certificates.FzJ36

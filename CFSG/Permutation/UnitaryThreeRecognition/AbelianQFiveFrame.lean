module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveBasis
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveSetup

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f : ℕ} (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω] (h5 : p ^ f = 5)
  (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
  {t : G} (ht : t ∈ pairStab G a b) (hot : orderOf t = 8)
  {z₀ v₀ : G} (hz₀ : z₀ ∈ centQ Q j) (hz₀1 : z₀ ≠ 1) (hv₀ : v₀ ∈ AbelianQ.invSub Q j hQab)
  (hv₀1 : v₀ ≠ 1)
include S h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1

omit [Finite G] [Finite Ω] h5 hot hz₀ hz₀1 hv₀1 in
theorem v₁_mem : t * v₀ * t⁻¹ ∈ AbelianQ.invSub Q j hQab :=
  AbelianQ.conj_mem_invSub S.root S.hb S.hcomm S.hj ht.1 hv₀

omit [Finite G] [Finite Ω] h5 hot hz₀1 hv₀1 in
theorem coord5_mem (m : ZMod 5 × ZMod 5 × ZMod 5) : coord5 z₀ v₀ (t * v₀ * t⁻¹) m ∈ Q := by
  have hz : z₀ ∈ Q := (mem_centQ.mp hz₀).1
  have hv : v₀ ∈ Q := hv₀.1
  have hv1 : t * v₀ * t⁻¹ ∈ Q := (S.v₁_mem hQab ht hv₀).1
  exact Q.mul_mem (Q.mul_mem (Q.pow_mem hz _) (Q.pow_mem hv _)) (Q.pow_mem hv1 _)

omit hot hz₀1 hv₀1 in
theorem coord5_add' (m m' : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ (t * v₀ * t⁻¹) (m + m') =
      coord5 z₀ v₀ (t * v₀ * t⁻¹) m * coord5 z₀ v₀ (t * v₀ * t⁻¹) m' := by
  have hz : z₀ ∈ Q := (mem_centQ.mp hz₀).1
  have hv : v₀ ∈ Q := hv₀.1
  have hv1 : t * v₀ * t⁻¹ ∈ Q := (S.v₁_mem hQab ht hv₀).1
  exact coord5_add (S.pow_five_eq_one h5 hz) (S.pow_five_eq_one h5 hv) (S.pow_five_eq_one h5 hv1)
    (hQab _ hz _ hv) (hQab _ hz _ hv1) (hQab _ hv _ hv1) m m'

omit hz₀ hz₀1 in
theorem vpart_eq_one {x y : ZMod 5} (h : pow5 v₀ x * pow5 (t * v₀ * t⁻¹) y = 1) :
    x = 0 ∧ y = 0 := by
  have hv : v₀ ∈ Q := hv₀.1
  have hv1 : t * v₀ * t⁻¹ ∈ Q := (S.v₁_mem hQab ht hv₀).1
  have h5v : v₀ ^ 5 = 1 := S.pow_five_eq_one h5 hv
  have h5v1 : (t * v₀ * t⁻¹) ^ 5 = 1 := S.pow_five_eq_one h5 hv1
  by_cases hy : y = 0
  · subst hy
    rw [pow5_zero, mul_one] at h
    exact ⟨(S.pow5_eq_one_iff h5 hv hv₀1 x).mp h, rfl⟩
  · exfalso
    obtain ⟨y', hy'⟩ : ∃ y' : ZMod 5, y * y' = 1 := by
      revert hy; generalize y = y0; revert y0; decide
    set e : ZMod 5 := -x * y' with hedef
    have hv1e : t * v₀ * t⁻¹ = pow5 v₀ e := by
      have h1 : pow5 (t * v₀ * t⁻¹) y = (pow5 v₀ x)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [← pow5_neg h5v] at h1
      have h2 : pow5 (pow5 (t * v₀ * t⁻¹) y) y' = pow5 (pow5 v₀ (-x)) y' := by rw [h1]
      rw [← pow5_mul h5v1, ← pow5_mul h5v, hy', pow5_one] at h2
      rw [h2]
    have hk : ∀ k : ℕ, t ^ k * v₀ * (t ^ k)⁻¹ = pow5 v₀ (e ^ k) := by
      intro k
      induction k with
      | zero => simp [pow5_one]
      | succ k ih =>
        calc t ^ (k + 1) * v₀ * (t ^ (k + 1))⁻¹ = t ^ k * (t * v₀ * t⁻¹) * (t ^ k)⁻¹ := by
              rw [pow_succ]; group
          _ = t ^ k * pow5 v₀ e * (t ^ k)⁻¹ := by rw [hv1e]
          _ = pow5 (t ^ k * v₀ * (t ^ k)⁻¹) e := conj_pow5 _ _ _
          _ = pow5 v₀ (e ^ (k + 1)) := by rw [ih, ← pow5_mul h5v, pow_succ]
    have he0 : e ≠ 0 := by
      intro he
      rw [he, pow5_zero] at hv1e
      apply hv₀1
      calc v₀ = t⁻¹ * (t * v₀ * t⁻¹) * t := by group
        _ = 1 := by rw [hv1e]; group
    have he4 : e ^ 4 = 1 := by revert he0; generalize e = e'; revert e'; decide
    have hj4 := S.pow_four_eq ht hot
    have h4 := hk 4
    rw [hj4, he4, pow5_one] at h4
    have hinv : j * v₀ * j⁻¹ = v₀⁻¹ := hv₀.2
    rw [h4] at hinv
    apply hv₀1
    apply AbelianQ.eq_one_of_mul_self_eq_one (S.odd_card_Q h5) hv
    calc v₀ * v₀ = v₀⁻¹ * v₀ := by rw [← hinv]
      _ = 1 := inv_mul_cancel v₀

theorem coord5_eq_one {m : ZMod 5 × ZMod 5 × ZMod 5}
    (h : coord5 z₀ v₀ (t * v₀ * t⁻¹) m = 1) : m = 0 := by
  have hz : z₀ ∈ Q := (mem_centQ.mp hz₀).1
  have hv1 := S.v₁_mem hQab ht hv₀
  set y := pow5 v₀ m.2.1 * pow5 (t * v₀ * t⁻¹) m.2.2 with hydef
  have hyV : y ∈ AbelianQ.invSub Q j hQab :=
    (AbelianQ.invSub Q j hQab).mul_mem ((AbelianQ.invSub Q j hQab).pow_mem hv₀ _)
      ((AbelianQ.invSub Q j hQab).pow_mem hv1 _)
  have hzc : pow5 z₀ m.1 = y⁻¹ := by
    have : pow5 z₀ m.1 * y = 1 := by rw [hydef, ← mul_assoc]; exact h
    exact eq_inv_of_mul_eq_one_left this
  have hzZ : pow5 z₀ m.1 ∈ centQ Q j := (centQ Q j).pow_mem hz₀ _
  have hzV : pow5 z₀ m.1 ∈ AbelianQ.invSub Q j hQab := by
    rw [hzc]; exact (AbelianQ.invSub Q j hQab).inv_mem hyV
  have hz1 := AbelianQ.eq_one_of_mem_centQ_of_mem_invSub (S.odd_card_Q h5) hzZ hzV
  have hc : m.1 = 0 := (S.pow5_eq_one_iff h5 hz hz₀1 m.1).mp hz1
  have hy1 : y = 1 := by rw [hz1] at hzc; exact inv_eq_one.mp hzc.symm
  obtain ⟨hx, hy⟩ := S.vpart_eq_one h5 hQab ht hot hv₀ hv₀1 hy1
  exact Prod.ext hc (Prod.ext hx hy)

omit hot hz₀1 hv₀1 in
theorem coord5_neg' (m : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ (t * v₀ * t⁻¹) (-m) = (coord5 z₀ v₀ (t * v₀ * t⁻¹) m)⁻¹ := by
  have h := S.coord5_add' h5 hQab ht hz₀ hv₀ (-m) m
  rw [neg_add_cancel, coord5_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem coord5_injective : Function.Injective (coord5 z₀ v₀ (t * v₀ * t⁻¹)) := by
  intro m m' h
  have h1 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (m - m') = 1 := by
    rw [sub_eq_add_neg, S.coord5_add' h5 hQab ht hz₀ hv₀, S.coord5_neg' h5 hQab ht hz₀ hv₀, h,
      mul_inv_cancel]
  exact sub_eq_zero.mp (S.coord5_eq_one h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1 h1)

theorem coord5_surjective {x : G} (hx : x ∈ Q) :
    ∃ m, coord5 z₀ v₀ (t * v₀ * t⁻¹) m = x := by
  classical
  let φ : (ZMod 5 × ZMod 5 × ZMod 5) → Q := fun m => ⟨_, S.coord5_mem hQab ht hz₀ hv₀ m⟩
  have hinj : Function.Injective φ := fun m m' h =>
    S.coord5_injective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1 (congrArg Subtype.val h)
  have hcard : Nat.card (ZMod 5 × ZMod 5 × ZMod 5) = Nat.card Q := by
    rw [S.card_Q_eq h5, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have hbij := (Function.Injective.bijective_of_nat_card_le hinj hcard.ge)
  obtain ⟨m, hm⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨m, congrArg Subtype.val hm⟩

omit hz₀1 in
theorem coord5_mem_centQ_iff (m : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ (t * v₀ * t⁻¹) m ∈ centQ Q j ↔ m.2 = 0 := by
  have hv1 := S.v₁_mem hQab ht hv₀
  constructor
  · intro hm
    set y := pow5 v₀ m.2.1 * pow5 (t * v₀ * t⁻¹) m.2.2 with hydef
    have hyV : y ∈ AbelianQ.invSub Q j hQab :=
      (AbelianQ.invSub Q j hQab).mul_mem ((AbelianQ.invSub Q j hQab).pow_mem hv₀ _)
        ((AbelianQ.invSub Q j hQab).pow_mem hv1 _)
    have hyZ : y ∈ centQ Q j := by
      have : y = (pow5 z₀ m.1)⁻¹ * coord5 z₀ v₀ (t * v₀ * t⁻¹) m := by
        rw [coord5, hydef]; group
      rw [this]
      exact (centQ Q j).mul_mem ((centQ Q j).inv_mem ((centQ Q j).pow_mem hz₀ _)) hm
    have hy1 := AbelianQ.eq_one_of_mem_centQ_of_mem_invSub (S.odd_card_Q h5) hyZ hyV
    obtain ⟨hx, hy⟩ := S.vpart_eq_one h5 hQab ht hot hv₀ hv₀1 hy1
    exact Prod.ext hx hy
  · intro hm
    have e : coord5 z₀ v₀ (t * v₀ * t⁻¹) m = pow5 z₀ m.1 := by
      rw [coord5, hm]; simp [pow5_zero]
    rw [e]
    exact (centQ Q j).pow_mem hz₀ _

omit hot hv₀1 in
theorem coord5_mem_invSub_iff (m : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ (t * v₀ * t⁻¹) m ∈ AbelianQ.invSub Q j hQab ↔ m.1 = 0 := by
  have hv1 := S.v₁_mem hQab ht hv₀
  have hz : z₀ ∈ Q := (mem_centQ.mp hz₀).1
  have hyV : pow5 v₀ m.2.1 * pow5 (t * v₀ * t⁻¹) m.2.2 ∈ AbelianQ.invSub Q j hQab :=
    (AbelianQ.invSub Q j hQab).mul_mem ((AbelianQ.invSub Q j hQab).pow_mem hv₀ _)
      ((AbelianQ.invSub Q j hQab).pow_mem hv1 _)
  constructor
  · intro hm
    have hzV : pow5 z₀ m.1 ∈ AbelianQ.invSub Q j hQab := by
      have : pow5 z₀ m.1 = coord5 z₀ v₀ (t * v₀ * t⁻¹) m *
          (pow5 v₀ m.2.1 * pow5 (t * v₀ * t⁻¹) m.2.2)⁻¹ := by rw [coord5]; group
      rw [this]
      exact (AbelianQ.invSub Q j hQab).mul_mem hm ((AbelianQ.invSub Q j hQab).inv_mem hyV)
    have h1 := AbelianQ.eq_one_of_mem_centQ_of_mem_invSub (S.odd_card_Q h5)
      ((centQ Q j).pow_mem hz₀ _) hzV
    exact (S.pow5_eq_one_iff h5 hz hz₀1 m.1).mp h1
  · intro hm
    have e : coord5 z₀ v₀ (t * v₀ * t⁻¹) m =
        pow5 v₀ m.2.1 * pow5 (t * v₀ * t⁻¹) m.2.2 := by
      rw [coord5, hm, pow5_zero, one_mul]
    rw [e]
    exact hyV

end StdHyp

end CFSG.UnitaryThreeRecognition

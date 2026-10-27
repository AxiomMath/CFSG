module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.External

section Coordinates

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

theorem mem_coord_of_conj_eq_neg (h2 : (2 : K) ≠ 0) {a c : K} (hc : J.conj c = -c) :
    c - a * J.conj a / 2 + J.conj (c - a * J.conj a / 2) + a * J.conj a = 0 := by
  rw [map_sub, map_div₀, map_mul, J.conj_involutive, map_ofNat, hc]
  linear_combination (-(a * J.conj a)) * inv_mul_cancel₀ h2

theorem exists_mulEquiv_coord {H : Type*} [Group H] (h2 : (2 : K) ≠ 0) (a c : H → K)
    (ha : ∀ x y, a (x * y) = a x + a y)
    (hc : ∀ x y, c (x * y) = c x + c y + (a y * J.conj (a x) - a x * J.conj (a y)) / 2)
    (hcc : ∀ x, J.conj (c x) = -c x)
    (hinj : ∀ x, a x = 0 → c x = 0 → x = 1)
    (hsurj : ∀ a₀ c₀, J.conj c₀ = -c₀ → ∃ x, a x = a₀ ∧ c x = c₀) :
    ∃ φ : H ≃* Coord J, ∀ x, (φ x : K × K) = (a x, c x - a x * J.conj (a x) / 2) := by
  let F : H →* Coord J :=
    { toFun := fun x => ⟨(a x, c x - a x * J.conj (a x) / 2), mem_coord_of_conj_eq_neg J h2 (hcc x)⟩
      map_one' := by
        have ha1 : a 1 = 0 := by
          have := ha 1 1
          rw [mul_one] at this
          linear_combination -this
        have hc1 : c 1 = 0 := by
          have := hc 1 1
          rw [mul_one, ha1, map_zero] at this
          linear_combination -this
        apply Subtype.ext
        change (a 1, c 1 - a 1 * J.conj (a 1) / 2) = _
        rw [coord_one_val, ha1, hc1]
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        rw [coord_mul_val]
        apply Prod.ext
        · exact ha x y
        · simp only
          rw [ha, hc, map_add]
          field_simp
          ring }
  have hF : ∀ x, (F x : K × K) = (a x, c x - a x * J.conj (a x) / 2) := fun x => rfl
  have hinjF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h := congrArg Subtype.val hx
    rw [hF, coord_one_val, Prod.mk.injEq] at h
    obtain ⟨h1, h2'⟩ := h
    rw [h1, zero_mul, zero_div, sub_zero] at h2'
    exact hinj x h1 h2'
  have hsurjF : Function.Surjective F := by
    rintro ⟨⟨a₀, b₀⟩, hz⟩
    have hc₀ : J.conj (b₀ + a₀ * J.conj a₀ / 2) = -(b₀ + a₀ * J.conj a₀ / 2) := by
      rw [map_add, map_div₀, map_mul, J.conj_involutive, map_ofNat]
      linear_combination hz + (J.conj a₀ * a₀) * inv_mul_cancel₀ h2
    obtain ⟨x, hxa, hxc⟩ := hsurj a₀ _ hc₀
    refine ⟨x, Subtype.ext ?_⟩
    rw [hF, hxa, hxc]
    simp
  exact ⟨MulEquiv.ofBijective F ⟨hinjF, hsurjF⟩, hF⟩

theorem eq_hermitianTorusAction {k : Kˣ} {z w : Coord J} (s : K)
    (hs : s = k * (J.conj (k : K))⁻¹ ^ 2) (h1 : (w : K × K).1 = (z : K × K).1 * s)
    (h2 : (w : K × K).2 = (z : K × K).2 * (s * J.conj s)) :
    w = hermitianTorusAction J k z := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hck : J.conj (k : K) ≠ 0 := (_root_.map_ne_zero J.conj).2 hk
  apply Subtype.ext
  apply Prod.ext
  · rw [h1, hs, hermitianTorusAction_fst]
    ring
  · rw [h2, hs, hermitianTorusAction_snd, map_mul, map_pow, map_inv₀, J.conj_involutive]
    field_simp

end Coordinates

section Cyclic

variable {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]

theorem eq_range_powMonoidHom (H : Subgroup G) (n : ℕ)
    (hH : Nat.card H = Nat.card G / Nat.gcd (Nat.card G) n) :
    H = (powMonoidHom n : G →* G).range := by
  set m := Nat.card G / Nat.gcd (Nat.card G) n with hm
  have hmdvd : m ∣ Nat.card G := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hker : Nat.card (powMonoidHom m : G →* G).ker = m := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hmdvd]
  have hHle : H ≤ (powMonoidHom m : G →* G).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← hH]
    have := pow_card_eq_one' (x := (⟨x, hx⟩ : H))
    rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one] at this
    exact this
  have hRle : (powMonoidHom n : G →* G).range ≤ (powMonoidHom m : G →* G).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul]
    have hN : Nat.card G ∣ n * m := by
      rw [hm, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
      exact Dvd.intro _ rfl
    obtain ⟨r, hr⟩ := hN
    rw [hr, pow_mul, pow_card_eq_one', one_pow]
  have hR : Nat.card (powMonoidHom n : G →* G).range = m := by
    rw [IsCyclic.card_powMonoidHom_range]
  rw [Subgroup.eq_of_le_of_card_ge hHle (by rw [hker, hH]),
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hker, hR])]

end Cyclic

end CFSG.UnitaryThreeRecognition.Heisenberg

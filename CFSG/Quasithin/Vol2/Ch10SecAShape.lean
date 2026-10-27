module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin.H13

@[expose] def IsShapeGroup (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∨
    (∃ n : ℕ, CFSG.Blueprint.SuzukiModel X 2 n) ∨
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

theorem isShapeGroup_of_shape701 {G : Type} [Group G] {L : Subgroup G} (h : Shape701 L) :
    IsShapeGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  h

theorem IsShapeGroup.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X)
    (h : IsShapeGroup X) : IsShapeGroup Y := by
  rcases h with ⟨n, hn, K, _, _, hK, ⟨e'⟩⟩ | ⟨n, h2, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ | he
  · exact Or.inl ⟨n, hn, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, h2, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.trans e'⟩⟩)
  · obtain ⟨e'⟩ := he
    exact Or.inr (Or.inr ⟨e.trans e'⟩)

@[expose] def ShapeCard (N : ℕ) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ N = 2 ^ n * (4 ^ n - 1)) ∨
    (∃ a : ℕ, 1 ≤ a ∧ N = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1)) ∨
    N = 168

theorem card_SL_two_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ n * (4 ^ n - 1) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← Nat.card_eq_fintype_card, hK]
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpos : 0 < 2 ^ n - 1 := by
    have h := Finite.one_lt_card (α := K)
    rw [hK] at h
    omega
  have h1 : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by rw [Nat.mul_sub_one, sq]
  rw [h1, h4, show (4 ^ n - 1) * (2 ^ n * (2 ^ n - 1)) = 2 ^ n * (4 ^ n - 1) * (2 ^ n - 1) by
    ring, Nat.mul_div_cancel _ hpos]

theorem card_SL_three_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem shapeCard_of_isShapeGroup
    {X : Type} [Group X] (h : IsShapeGroup X) :
    ShapeCard (Nat.card X) := by
  rcases h with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨n, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ | he
  · exact Or.inl ⟨n, hn, by rw [Nat.card_congr e.toEquiv, card_SL_two_pow hK]⟩
  · subst hf
    exact Or.inr (Or.inl ⟨a, ha, by rw [Nat.card_congr e.toEquiv,
      CFSG.LieType.Ree.suzuki_order hK]⟩)
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (by rw [Nat.card_congr e.toEquiv, card_SL_three_zmod_two]))

theorem two_pow_mul_odd_inj {n a u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ n * u = 2 ^ a * v) : n = a ∧ u = v := by
  have key : ∀ {n a u v : ℕ}, Odd u → 2 ^ n * u = 2 ^ a * v → n ≤ a → n = a := by
    intro n a u v hu h hle
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases k with _ | k
    · rfl
    · exfalso
      rw [h', pow_succ] at hu
      exact (Nat.not_even_iff_odd.mpr hu) ⟨2 ^ k * v, by ring⟩
  have hna : n = a := by
    rcases le_total n a with hle | hle
    · exact key hu h hle
    · exact (key hv h.symm hle).symm
  subst hna
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem three_not_dvd_card_suzuki (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  set q := 2 ^ (2 * a + 1) with hqdef
  have h4 : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hq : q % 3 = 2 := by
    rw [hqdef, pow_succ, pow_mul, Nat.mul_mod, show 2 ^ 2 = 4 by norm_num, h4]
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h1 : (q - 1) % 3 = 1 := by omega
  have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have h3 : (q ^ 2 + 1) % 3 = 2 := by omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod (q ^ 2), h1, h2, h3]
  norm_num

theorem not_shapeCard_of {a b : ℕ} (hb : Odd b) (h3 : 3 ∣ b) (hne : 2 ≤ a → b ≠ 4 ^ a - 1)
    (h168 : a = 3 → b ≠ 21) : ¬ ShapeCard (2 ^ a * b) := by
  rintro (⟨n, hn, h⟩ | ⟨c, -, h⟩ | h)
  · have hodd : Odd (4 ^ n - 1) := by
      have he : Even (4 ^ n) := (Nat.even_pow.mpr ⟨by decide, by omega⟩)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) he odd_one
    obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj hb hodd h
    exact hne hn rfl
  · exact three_not_dvd_card_suzuki c (h ▸ dvd_mul_of_dvd_right h3 _)
  · obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj hb (by decide : Odd 21)
      (h.trans (by norm_num : (168 : ℕ) = 2 ^ 3 * 21))
    exact h168 rfl rfl

theorem nonempty_mulEquiv_of_surjective {Γ X : Type} [Group Γ] [Group X] (hΓ : IsSimpleGroup Γ)
    [Nontrivial X] (π : Γ →* X) (hπ : Function.Surjective π) : Nonempty (Γ ≃* X) := by
  refine ⟨MulEquiv.ofBijective π ⟨?_, hπ⟩⟩
  rcases hΓ.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).mp h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨g, rfl⟩ := hπ x
    exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

end CFSG.Quasithin.Vol2.Ch10.SecA

module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Matrix

namespace E9

@[expose] def A4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def B4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def a4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨A4, by decide⟩

@[expose] def b4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨B4, by decide⟩

theorem coe_a4 : (a4 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = A4 := rfl

theorem coe_b4 : (b4 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = B4 := rfl

theorem a4_cube : a4 ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_a4, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem b4_cube : b4 ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_b4, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem a4_comm : a4 * b4 = b4 * a4 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_a4, coe_b4]
  decide

@[expose] def f9 (q : Fin 3 × Fin 3) : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  a4 ^ (q.1 : ℕ) * b4 ^ (q.2 : ℕ)

theorem f9_injective_mat : ∀ q r : Fin 3 × Fin 3,
    A4 ^ (q.1 : ℕ) * B4 ^ (q.2 : ℕ) = A4 ^ (r.1 : ℕ) * B4 ^ (r.2 : ℕ) → q = r := by
  decide

theorem f9_injective : Function.Injective f9 := by
  intro q r h
  have h' := congrArg Subtype.val h
  simp only [f9, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_a4,
    coe_b4] at h'
  exact f9_injective_mat q r h'

theorem pow_mod_three {g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)} (hg : g ^ 3 = 1) (k : ℕ) :
    g ^ k = g ^ (k % 3) := by
  conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hg, one_pow, mul_one]

@[expose] def e9 : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) where
  carrier := Set.range f9
  mul_mem' := by
    rintro _ _ ⟨q, rfl⟩ ⟨r, rfl⟩
    refine ⟨(⟨(q.1 + r.1 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(q.2 + r.2 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f9]
    rw [← pow_mod_three a4_cube, ← pow_mod_three b4_cube, pow_add, pow_add]
    have hc : Commute a4 b4 := a4_comm
    calc a4 ^ (q.1 : ℕ) * a4 ^ (r.1 : ℕ) * (b4 ^ (q.2 : ℕ) * b4 ^ (r.2 : ℕ)) =
        a4 ^ (q.1 : ℕ) * (a4 ^ (r.1 : ℕ) * b4 ^ (q.2 : ℕ)) * b4 ^ (r.2 : ℕ) := by group
      _ = a4 ^ (q.1 : ℕ) * (b4 ^ (q.2 : ℕ) * a4 ^ (r.1 : ℕ)) * b4 ^ (r.2 : ℕ) := by
        rw [((hc.pow_left _).pow_right _).eq]
      _ = _ := by group
  one_mem' := ⟨(0, 0), by simp [f9]⟩
  inv_mem' := by
    rintro _ ⟨q, rfl⟩
    refine ⟨(⟨(3 - q.1 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(3 - q.2 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f9]
    rw [← pow_mod_three a4_cube, ← pow_mod_three b4_cube]
    have hc : Commute a4 b4 := a4_comm
    rw [_root_.mul_inv_rev, ← ((hc.pow_left _).pow_right _).inv_inv.eq]
    have ha : a4 ^ (3 - (q.1 : ℕ)) = (a4 ^ (q.1 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel q.1.isLt.le, a4_cube]
    have hb : b4 ^ (3 - (q.2 : ℕ)) = (b4 ^ (q.2 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel q.2.isLt.le, b4_cube]
    rw [ha, hb]

theorem card_e9 : Nat.card e9 = 9 := by
  have h : (e9 : Set _) = Set.range f9 := rfl
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective f9_injective, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem e9_elem : IsElemAbelian 3 e9 := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨q, hq⟩ := x.2
    obtain ⟨r, hr⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hq, ← hr, f9]
    have hc : Commute a4 b4 := a4_comm
    have h1 : Commute (a4 ^ (q.1 : ℕ) * b4 ^ (q.2 : ℕ)) (a4 ^ (r.1 : ℕ) * b4 ^ (r.2 : ℕ)) :=
      Commute.mul_left (Commute.mul_right ((Commute.refl a4).pow_pow _ _)
          ((hc.pow_left _).pow_right _))
        (Commute.mul_right ((hc.symm.pow_left _).pow_right _) ((Commute.refl b4).pow_pow _ _))
    exact h1.eq
  · obtain ⟨q, rfl⟩ := hx
    simp only [f9]
    have hc : Commute a4 b4 := a4_comm
    rw [((hc.pow_left _).pow_right _).mul_pow, ← pow_mul, ← pow_mul, mul_comm (q.1 : ℕ),
      mul_comm (q.2 : ℕ), pow_mul, pow_mul, a4_cube, b4_cube, one_pow, one_pow, mul_one]

theorem e9_comm {x y : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)} (hx : x ∈ e9) (hy : y ∈ e9) :
    x * y = y * x :=
  congrArg Subtype.val (e9_elem.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)

variable {G : Type} [Group G] [Finite G]

theorem exists_e9 {Y : Subgroup G} (ψ : ↥Y →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) :
    ∃ P : Subgroup G, P ≤ Y ∧ Nat.card P = 9 ∧ IsElemAbelian 3 P ∧
      ∀ y : ↥Y, (y : G) ∈ P → ψ y = 1 → y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup ↥Y := e9.comap ψ with hQ
  let ψQ : ↥Q →* ↥e9 := (ψ.comp Q.subtype).codRestrict e9 fun q => q.2
  have hψQ : Function.Surjective ψQ := by
    rintro ⟨e, he⟩
    obtain ⟨y, hy⟩ := hψ e
    exact ⟨⟨y, show ψ y ∈ e9 by rw [hy]; exact he⟩, Subtype.ext hy⟩
  have h9 : 3 ^ 2 ∣ Nat.card Q := by
    have := Subgroup.card_dvd_of_surjective hψQ
    rw [card_e9] at this
    exact this
  obtain ⟨P'', hP''⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set P' : Subgroup ↥Y := P''.map Q.subtype with hP'
  have hP'Q : P' ≤ Q := Subgroup.map_subtype_le P''
  have hcardP' : Nat.card P' = 9 := by
    rw [hP', Subgroup.card_map_of_injective Q.subtype_injective, hP'']
    norm_num
  have hinj : ∀ y ∈ P', ψ y = 1 → y = 1 := by
    intro y hy h1
    have h9' : y ^ 9 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hcardP' ▸ Subgroup.orderOf_dvd_natCard P' hy)
    obtain ⟨k, hk⟩ := hker ⟨y, h1⟩
    have h2 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.gcd (2 ^ k) 9 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h2, h9'⟩
    rwa [hcop, pow_one] at this
  have hcomm' : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := by
    intro a ha b hb
    have h1 : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
      have hc : ψ a * ψ b = ψ b * ψ a := e9_comm (hP'Q ha) (hP'Q hb)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 := hinj _ (P'.mul_mem (P'.mul_mem (P'.mul_mem ha hb) (P'.inv_mem ha)) (P'.inv_mem hb))
      h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  have hpow' : ∀ a ∈ P', a ^ 3 = 1 := by
    intro a ha
    refine hinj _ (P'.pow_mem ha 3) ?_
    rw [map_pow]
    exact e9_elem.2 _ (hP'Q ha)
  refine ⟨P'.map Y.subtype, Subgroup.map_subtype_le P', ?_, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩,
    ?_⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hcardP']
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, Subgroup.coe_subtype,
      ← Subgroup.coe_mul, hcomm' a ha b hb, Subgroup.coe_mul]
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hpow' a ha, Subgroup.coe_one]
  · intro y hy h1
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    have : a = y := Subtype.ext hay
    rw [← this] at h1 ⊢
    exact hinj a ha h1

end E9

end CFSG.Quasithin.H13

module

public import CFSG.Monster.Schur.TripleCentral
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Certificate9700
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Monster.Schur

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

@[expose] def twistExp (j k : ℤ) (w : List (ℕ × Bool)) : ℤ :=
  (w.map fun l => (if l.2 then 1 else -1) * (if l.1 = 0 then j else k)).sum

section Twist

variable {E : Type*} [Group E] {z : E}

theorem wordProd_cons {x : ℕ → E} (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    wordProd x (l :: w) = (if l.2 then x l.1 else (x l.1)⁻¹) * wordProd x w := by
  simp [wordProd]

theorem twistExp_cons (j k : ℤ) (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    twistExp j k (l :: w) =
      (if l.2 then 1 else -1) * (if l.1 = 0 then j else k) + twistExp j k w := by
  simp [twistExp]

theorem img2_twist (x y : E) (j k : ℤ) (i : ℕ) :
    img2 (x * z ^ j) (y * z ^ k) i = img2 x y i * z ^ (if i = 0 then j else k) := by
  unfold img2
  split_ifs <;> rfl

theorem wordProd_twist (hz : ∀ g : E, g * z = z * g) (x y : E) (j k : ℤ)
    (w : List (ℕ × Bool)) :
    wordProd (img2 (x * z ^ j) (y * z ^ k)) w = wordProd (img2 x y) w * z ^ twistExp j k w := by
  have hc : ∀ (g : E) (m : ℤ), z ^ m * g = g * z ^ m := fun g m =>
    (Commute.zpow_left (show Commute g z from hz g).symm m).eq
  have mt : ∀ (a b : E) (m e : ℤ), (a * z ^ m) * (b * z ^ e) = (a * b) * z ^ (m + e) := by
    intro a b m e
    calc (a * z ^ m) * (b * z ^ e) = a * (z ^ m * b) * z ^ e := by simp only [mul_assoc]
      _ = a * (b * z ^ m) * z ^ e := by rw [hc b m]
      _ = (a * b) * (z ^ m * z ^ e) := by simp only [mul_assoc]
      _ = (a * b) * z ^ (m + e) := by rw [zpow_add]
  have inv_t : ∀ (a : E) (m : ℤ), (a * z ^ m)⁻¹ = a⁻¹ * z ^ (-m) := by
    intro a m
    rw [mul_inv_rev, ← zpow_neg, hc a⁻¹ (-m)]
  induction w with
  | nil => simp [wordProd, twistExp]
  | cons l w ih =>
    rw [wordProd_cons, wordProd_cons, twistExp_cons, ih, img2_twist]
    cases hl : l.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [inv_t, mt, neg_one_mul]
    · simp only [↓reduceIte]
      rw [mt, one_mul]

end Twist

theorem twistExp_r2 (j k : ℤ) : twistExp j k m12R2 = 5 * j + 6 * k := by
  simp [twistExp, m12R2]
  ring

theorem twistExp_r3 (j k : ℤ) : twistExp j k m12R3 = 6 * j + 4 * k := by
  simp [twistExp, m12R3]
  ring

section Lifts

variable {E G : Type*} [Group E] [Group G] (π : E →* G)

theorem map_img2 (a b : E) (i : ℕ) : π (img2 a b i) = img2 (π a) (π b) i := by
  unfold img2
  split_ifs <;> rfl

theorem exists_good_lifts (hπ : Function.Surjective π) (hk : Nat.card π.ker = 3)
    (hzc : π.ker ≤ Subgroup.center E) (h1 h2 : G)
    (hr2 : wordProd (img2 h1 h2) m12R2 = 1) (hr3 : wordProd (img2 h1 h2) m12R3 = 1) :
    ∃ a b : E, π a = h1 ∧ π b = h2 ∧ wordProd (img2 a b) m12R2 = 1 ∧
      wordProd (img2 a b) m12R3 = 1 := by
  obtain ⟨z, hz, hz1, hz3, hall⟩ := exists_ker_gen3 π hk
  have hzcomm : ∀ g : E, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 (hzc hz) g)
  obtain ⟨a0, ha0⟩ := hπ h1
  obtain ⟨b0, hb0⟩ := hπ h2
  have hmap : ∀ w, π (wordProd (img2 a0 b0) w) = wordProd (img2 h1 h2) w := by
    intro w
    rw [map_wordProd π, ← ha0, ← hb0]
    congr 1
    funext i
    exact map_img2 π a0 b0 i
  have hker : ∀ w, wordProd (img2 h1 h2) w = 1 → wordProd (img2 a0 b0) w ∈ π.ker := by
    intro w hw
    rw [MonoidHom.mem_ker, hmap]
    exact hw
  have hpow : ∀ t ∈ π.ker, ∃ c : ℕ, t = z ^ c := by
    intro t ht
    rcases hall t ht with h | h | h
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; simp⟩
    · exact ⟨2, h⟩
  obtain ⟨c2, hc2⟩ := hpow _ (hker _ hr2)
  obtain ⟨c3, hc3⟩ := hpow _ (hker _ hr3)
  have hz3' : ∀ m : ℤ, z ^ (3 * m) = 1 := by
    intro m
    rw [zpow_mul]
    have : z ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hz3
    rw [this, one_zpow]
  refine ⟨a0 * z ^ (c2 : ℤ), b0 * z ^ (-(c3 : ℤ)), ?_, ?_, ?_, ?_⟩
  · rw [map_mul, zpow_natCast, map_pow, (MonoidHom.mem_ker.1 hz), one_pow, mul_one, ha0]
  · rw [map_mul, zpow_neg, map_inv, zpow_natCast, map_pow, (MonoidHom.mem_ker.1 hz), one_pow,
      inv_one, mul_one, hb0]
  · rw [wordProd_twist hzcomm, twistExp_r2, hc2, ← zpow_natCast, ← zpow_add]
    have : (c2 : ℤ) + (5 * (c2 : ℤ) + 6 * (-(c3 : ℤ))) = 3 * (2 * (c2 : ℤ) - 2 * (c3 : ℤ)) := by
      ring
    rw [this, hz3']
  · rw [wordProd_twist hzcomm, twistExp_r3, hc3, ← zpow_natCast, ← zpow_add]
    have : (c3 : ℤ) + (6 * (c2 : ℤ) + 4 * (-(c3 : ℤ))) = 3 * (2 * (c2 : ℤ) - (c3 : ℤ)) := by
      ring
    rw [this, hz3']

end Lifts

theorem bound_m12Rels :
    Finite (PG 3 m12Rels) ∧ Nat.card (PG 3 m12Rels) ≤ 95040 :=
  Certificates.certificate9700

section Universal

theorem lift_mk3 {E : Type*} [Group E] (img : ℕ → E) (w : List (Fin 3 × Bool)) :
    FreeGroup.lift (fun i : Fin 3 => img i.val) (FreeGroup.mk w) =
      wordProd img (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

theorem wordProd_append {E : Type*} [Group E] (x : ℕ → E) (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp [wordProd]

@[expose] def img3 {E : Type*} (a b ζ : E) (i : ℕ) : E :=
  if i = 0 then a else if i = 1 then b else ζ

theorem wordProd_img3 {E : Type*} [Group E] (a b ζ : E) (w : List (ℕ × Bool))
    (hw : ∀ l ∈ w, l.1 < 2) : wordProd (img3 a b ζ) w = wordProd (img2 a b) w := by
  unfold wordProd
  congr 1
  apply List.map_congr_left
  intro l hl
  have h2 := hw l hl
  have : img3 a b ζ l.1 = img2 a b l.1 := by
    unfold img3 img2
    split_ifs <;> first | rfl | omega
  rw [this]

theorem exists_complement_m12 {E G : Type} [Group E] [Finite E] [Group G] (π : E →* G)
    (hπ : Function.Surjective π) (hk : Nat.card π.ker = 3) (hzc : π.ker ≤ Subgroup.center E)
    (h1 h2 : G) (hr1 : wordProd (img2 h1 h2) m12R1 = 1) (hr2 : wordProd (img2 h1 h2) m12R2 = 1)
    (hr3 : wordProd (img2 h1 h2) m12R3 = 1)
    (hbound : Finite (PG 3 m12Rels) ∧ Nat.card (PG 3 m12Rels) ≤ 95040)
    (hcard : 95040 ≤ Nat.card (Subgroup.closure ({h1, h2} : Set G))) :
    ∃ S : Subgroup E, S ⊓ π.ker = ⊥ ∧ S.map π = Subgroup.closure ({h1, h2} : Set G) := by
  obtain ⟨z, hz, hz1, hz3, hall⟩ := exists_ker_gen3 π hk
  obtain ⟨a, b, ha, hb, hr2', hr3'⟩ := exists_good_lifts π hπ hk hzc h1 h2 hr2 hr3
  have hmap : ∀ w, π (wordProd (img2 a b) w) = wordProd (img2 h1 h2) w := by
    intro w
    rw [map_wordProd π, ← ha, ← hb]
    congr 1
    funext i
    exact map_img2 π a b i
  set ζ := wordProd (img2 a b) m12R1 with hζ
  have hζk : ζ ∈ π.ker := by rw [MonoidHom.mem_ker, hζ, hmap]; exact hr1
  have hζc : ∀ g : E, g * ζ = ζ * g := fun g => Subgroup.mem_center_iff.1 (hzc hζk) g
  have hζ3 : ζ * (ζ * ζ) = 1 := by
    rw [← pow_three]
    rcases hall ζ hζk with h | h | h
    · rw [h]; simp
    · rw [h]; exact hz3
    · rw [h, ← pow_mul, mul_comm, pow_mul, hz3, one_pow]
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 3) | r ∈ m12Rels.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin 3 => img3 a b ζ i.val) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_mk3]
    simp only [m12Rels, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [wordProd, img3] using hζ3
    · have := hζc a
      simp only [wordProd, img3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      simp
      rw [← mul_assoc ζ a, ← this]
      group
    · have := hζc b
      simp only [wordProd, img3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      simp
      rw [← mul_assoc ζ b, ← this]
      group
    · have e4 : ([(1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
          (2, false)] : List (Fin 3 × Bool)).map (fun l => (l.1.val, l.2)) =
          m12R1 ++ [(2, false)] := by decide
      rw [e4, wordProd_append, wordProd_img3 a b ζ m12R1 (by simp [m12R1]), ← hζ]
      simp [wordProd, img3]
    · have e5 : ([(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (1, true),
          (1, true), (1, true), (1, true), (1, true)] : List (Fin 3 × Bool)).map
          (fun l => (l.1.val, l.2)) = m12R2 := by decide
      rw [e5, wordProd_img3 a b ζ m12R2 (by simp [m12R2])]
      exact hr2'
    · have e6 : ([(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (0, true),
          (1, true), (0, true), (0, true), (1, true), (1, true)] : List (Fin 3 × Bool)).map
          (fun l => (l.1.val, l.2)) = m12R3 := by decide
      rw [e6, wordProd_img3 a b ζ m12R3 (by simp [m12R3])]
      exact hr3'
  set ρ : PG 3 m12Rels →* E := PresentedGroup.toGroup hrel with hρ
  have hρof : ∀ i : Fin 3, ρ (PresentedGroup.of i) = img3 a b ζ i.val := fun i =>
    PresentedGroup.toGroup.of hrel
  obtain ⟨hfin, hle⟩ := hbound
  have hS_le : Nat.card ρ.range ≤ 95040 :=
    (Nat.card_le_card_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective).trans hle
  have hπζ : π ζ = 1 := hζk
  have hrange : (π.comp ρ).range = Subgroup.closure ({h1, h2} : Set G) := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · show π (ρ (PresentedGroup.of 0)) ∈ _
        rw [hρof]
        simpa [img3, ha] using Subgroup.subset_closure (by simp : h1 ∈ ({h1, h2} : Set G))
      · show π (ρ (PresentedGroup.of 1)) ∈ _
        rw [hρof]
        simpa [img3, hb] using Subgroup.subset_closure (by simp : h2 ∈ ({h1, h2} : Set G))
      · show π (ρ (PresentedGroup.of 2)) ∈ _
        rw [hρof]
        simp [img3, hπζ]
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨PresentedGroup.of 0, by simp [hρof, img3, ha]⟩
      · exact ⟨PresentedGroup.of 1, by simp [hρof, img3, hb]⟩
  have hmapS : ρ.range.map π = Subgroup.closure ({h1, h2} : Set G) := by
    rw [← MonoidHom.range_comp]
    exact hrange
  refine ⟨ρ.range, ?_, hmapS⟩
  set φ : ρ.range →* G := π.comp ρ.range.subtype with hφ
  have hφr : φ.range = Subgroup.closure ({h1, h2} : Set G) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapS
  have hcardφ := Subgroup.card_ker_mul_card_range φ
  rw [hφr] at hcardφ
  have hCpos : 0 < Nat.card (Subgroup.closure ({h1, h2} : Set G)) := by omega
  have hker1 : Nat.card φ.ker ≤ 1 := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card (Subgroup.closure ({h1, h2} : Set G)))
      _ hCpos
    rw [one_mul]
    calc Nat.card φ.ker * Nat.card (Subgroup.closure ({h1, h2} : Set G)) = Nat.card ρ.range :=
          hcardφ
      _ ≤ 95040 := hS_le
      _ ≤ _ := hcard
  have hkerbot : φ.ker = ⊥ := by
    have : Nat.card φ.ker = 1 := le_antisymm hker1 Nat.card_pos
    exact Subgroup.eq_bot_of_card_eq _ this
  rw [eq_bot_iff]
  intro x hx
  have hxk : (⟨x, hx.1⟩ : ρ.range) ∈ φ.ker := hx.2
  rw [hkerbot, Subgroup.mem_bot] at hxk
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxk)

end Universal

end CFSG.Monster.Schur

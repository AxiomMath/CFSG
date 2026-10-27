module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G8
public import CFSG.Quasithin.Vol2.Ch10SecQ9H8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix Equiv

@[expose] def fixSet (A : Subgroup SL4) : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {v | ∀ a ∈ A, a • v = v}
  add_mem' := fun ha hb a hA => by rw [smul_add, ha a hA, hb a hA]
  zero_mem' := fun a _ => smul_zero a
  neg_mem' := fun ha a hA => by rw [smul_neg, ha a hA]

theorem mem_fixSet {A : Subgroup SL4} {v : Fin 4 → ZMod 2} : v ∈ fixSet A ↔ ∀ a ∈ A, a • v = v :=
  Iff.rfl

theorem smul_mem_fixSet {A : Subgroup SL4} {x : SL4}
    (hx : x ∈ Subgroup.normalizer (A : Set SL4)) {v : Fin 4 → ZMod 2} (hv : v ∈ fixSet A) :
    x • v ∈ fixSet A := by
  intro a ha
  have h : x⁻¹ * a * x ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) a).mp ha
    simpa using this
  calc a • x • v = x • (x⁻¹ * a * x) • v := by rw [← mul_smul, ← mul_smul]; group
    _ = x • v := by rw [hv _ h]

theorem card_fixSet_cases {A : Subgroup SL4} (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) :
    Nat.card (fixSet A) = 2 ∨ Nat.card (fixSet A) = 4 ∨ Nat.card (fixSet A) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hA.card_modEq_card_fixedPoints (Fin 4 → ZMod 2)
  have he : MulAction.fixedPoints A (Fin 4 → ZMod 2) = (fixSet A : Set (Fin 4 → ZMod 2)) := by
    ext v
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixSet, Subtype.forall]
    rfl
  rw [he, card_vec4] at h1
  have h1' : 16 ≡ Nat.card (fixSet A) [MOD 2] := h1
  have hdvd : Nat.card (fixSet A) ∣ 16 := by
    rw [← card_vec4]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  have hne : Nat.card (fixSet A) ≠ 16 := by
    intro h16
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    apply ha1
    apply Subtype.ext
    apply ext_mulVec
    intro x
    have htop : fixSet A = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [h16, card_vec4])
    have hx : x ∈ fixSet A := by rw [htop]; trivial
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    exact hx a ha
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (fixSet A) ∣ 2 ^ 4 from hdvd)
  unfold Nat.ModEq at h1'
  interval_cases i <;> rw [he] at h1' hne ⊢ <;> simp_all

theorem smul_eq_of_pow_smul_eq {G α : Type*} [Group G] [MulAction G α] {g : G}
    (hg : orderOf g = 7) {m : ℕ} (hm0 : 0 < m) (hm7 : m < 7) {x : α} (h : g ^ m • x = x) :
    g • x = x := by
  have h1 : ∀ b : ℕ, (g ^ m) ^ b • x = x := fun b => by
    induction b with
    | zero => rw [pow_zero, one_smul]
    | succ b ih => rw [pow_succ, mul_smul, h, ih]
  have h2 := h1 (m ^ 5)
  have hm : m * m ^ 5 % 7 = 1 := by interval_cases m <;> norm_num
  rwa [← pow_mul, ← pow_mod_orderOf, hg, hm, pow_one] at h2

theorem seven_translates {k : SL4} (hk : orderOf k = 7) {w : Fin 4 → ZMod 2} (hw : k • w ≠ w) :
    Function.Injective (fun i : Fin 7 => k ^ (i : ℕ) • w) ∧ ∀ i : Fin 7, k • k ^ (i : ℕ) • w ≠
      k ^ (i : ℕ) • w := by
  constructor
  · intro i j hij
    by_contra hne
    simp only at hij
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · have h1 : k ^ ((j : ℕ) - i) • (k ^ (i : ℕ) • w) = k ^ (i : ℕ) • w := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel h.le, hij]
      have h2 := smul_eq_of_pow_smul_eq hk (by omega) (by omega) h1
      rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h2
      exact hw (smul_left_cancel _ h2)
    · have h1 : k ^ ((i : ℕ) - j) • (k ^ (j : ℕ) • w) = k ^ (j : ℕ) • w := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel h.le, hij]
      have h2 := smul_eq_of_pow_smul_eq hk (by omega) (by omega) h1
      rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h2
      exact hw (smul_left_cancel _ h2)
  · intro i h
    rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h
    exact hw (smul_left_cancel _ h)

theorem pow_smul_mem {k : SL4} {W : AddSubgroup (Fin 4 → ZMod 2)} (hkW : ∀ v, v ∈ W ↔ k • v ∈ W)
    {w : Fin 4 → ZMod 2} (hw : w ∈ W) (m : ℕ) : k ^ m • w ∈ W := by
  induction m with
  | zero => rwa [pow_zero, one_smul]
  | succ m ih => rw [pow_succ', mul_smul]; exact (hkW _).mp ih

theorem card_fixed_le_two {k : SL4} (hk : orderOf k = 7) {W : AddSubgroup (Fin 4 → ZMod 2)}
    (hfix : ∀ w ∈ W, k • w = w) : Nat.card W ≤ 2 := by
  exact (Nat.card_le_card_of_injective (fun w => (⟨w.1, hfix w.1 w.2⟩ : {v // ρ4 k v = v}))
    fun x y h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h').trans (card_fix_seven hk).le

theorem false_of_card_four {k : SL4} (hk : orderOf k = 7) {W : AddSubgroup (Fin 4 → ZMod 2)}
    (hW : Nat.card W = 4) (hkW : ∀ v, v ∈ W ↔ k • v ∈ W) : False := by
  by_cases hfix : ∀ w ∈ W, k • w = w
  · have := card_fixed_le_two hk hfix
    omega
  obtain ⟨w, hw, hne⟩ : ∃ w ∈ W, k • w ≠ w := by
    by_contra hc
    exact hfix fun w hw => by
      by_contra h
      exact hc ⟨w, hw, h⟩
  have hinj := (seven_translates hk hne).1
  have := Nat.card_le_card_of_injective (fun i : Fin 7 => (⟨k ^ (i : ℕ) • w,
    pow_smul_mem hkW hw i⟩ : ↥W)) fun i j h => hinj (congrArg Subtype.val h)
  rw [Nat.card_fin, hW] at this
  omega

theorem false_of_card_eight {k : SL4} (hk : orderOf k = 7) {W : AddSubgroup (Fin 4 → ZMod 2)}
    (hW : Nat.card W = 8) (hkW : ∀ v, v ∈ W ↔ k • v ∈ W) {v : Fin 4 → ZMod 2} (hv : v ≠ 0)
    (hvW : v ∈ W) (hkv : k • v = v) : False := by
  by_cases hfix : ∀ w ∈ W, k • w = w
  · have := card_fixed_le_two hk hfix
    omega
  obtain ⟨w, hw, hne⟩ : ∃ w ∈ W, k • w ≠ w := by
    by_contra hc
    exact hfix fun w hw => by
      by_contra h
      exact hc ⟨w, hw, h⟩
  obtain ⟨hinj, hmov⟩ := seven_translates hk hne
  let f : Fin 7 ⊕ Fin 2 → ↥W := fun x => match x with
    | .inl i => ⟨k ^ (i : ℕ) • w, pow_smul_mem hkW hw i⟩
    | .inr j => if (j : ℕ) = 0 then 0 else ⟨v, hvW⟩
  have hf : Function.Injective f := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (hinj (congrArg Subtype.val h))
    · exfalso
      have h' := congrArg Subtype.val h
      fin_cases j' <;> simp only [f] at h' <;> simp at h'
      · exact hmov i (by rw [h', smul_zero])
      · exact hmov i (by rw [h', hkv])
    · exfalso
      have h' := congrArg Subtype.val h
      fin_cases j <;> simp only [f] at h' <;> simp at h'
      · exact hmov i' (by rw [← h', smul_zero])
      · exact hmov i' (by rw [← h', hkv])
    · fin_cases j <;> fin_cases j'
      · rfl
      · exfalso
        apply hv
        have h' := congrArg Subtype.val h
        simpa [f] using h'.symm
      · exfalso
        apply hv
        have h' := congrArg Subtype.val h
        simpa [f] using h'
      · rfl
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin, hW] at this
  omega

theorem additive_eq_dot {n : ℕ} {φ : (Fin n → ZMod 2) → ZMod 2}
    (hφ : ∀ x y, φ (x + y) = φ x + φ y) (x : Fin n → ZMod 2) :
    φ x = (fun j => φ (Pi.single j 1)) ⬝ᵥ x := by
  have hφ0 : φ 0 = 0 := by
    have h := hφ 0 0
    rw [add_zero] at h
    calc φ 0 = φ 0 + φ 0 + φ 0 := by rw [add_assoc, zmod2_add_self, add_zero]
      _ = 0 := by rw [← h, zmod2_add_self]
  set Φ : (Fin n → ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' φ hφ
  have hx : x = ∑ j, x j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsc : ∀ j, φ (x j • Pi.single j (1 : ZMod 2)) = x j * φ (Pi.single j 1) := fun j => by
    rcases zmod2_cases (x j) with h | h <;> rw [h]
    · rw [zero_smul, zero_mul, hφ0]
    · rw [one_smul, one_mul]
  conv_lhs => rw [hx]
  rw [show φ (∑ j, x j • Pi.single j (1 : ZMod 2)) = Φ (∑ j, x j • Pi.single j (1 : ZMod 2))
    from rfl, map_sum]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [show Φ _ = φ _ from rfl, hsc j, mul_comm]

theorem exists_hyperplane {W : AddSubgroup (Fin 4 → ZMod 2)} (hW : Nat.card W = 8) :
    ∃ u : Fin 4 → ZMod 2, u ≠ 0 ∧ ∀ x, x ∈ W ↔ u ⬝ᵥ x = 0 := by
  classical
  have hidx : W.index = 2 := by
    have h := W.card_mul_index
    rw [hW, card_vec4] at h
    omega
  obtain ⟨a, ha⟩ := AddSubgroup.index_eq_two_iff.mp hidx
  set φ : (Fin 4 → ZMod 2) → ZMod 2 := fun x => if x ∈ W then 0 else 1 with hφ
  have hnot : ∀ x y, x ∉ W → y ∉ W → x + y ∈ W := fun x y hx hy => by
    have hxa : x + a ∈ W := ((ha x).resolve_right fun h => hx h.1) |>.1
    have hya : y + a ∈ W := ((ha y).resolve_right fun h => hy h.1) |>.1
    have := W.add_mem hxa hya
    rwa [add_add_add_comm, add_self_vec, add_zero] at this
  have hadd : ∀ x y, φ (x + y) = φ x + φ y := fun x y => by
    by_cases hx : x ∈ W <;> by_cases hy : y ∈ W
    · simp [hφ, hx, hy, W.add_mem hx hy]
    · have : x + y ∉ W := fun h => hy (by
        have h' := W.add_mem h hx
        rwa [add_comm x y, add_assoc, add_self_vec, add_zero] at h')
      simp [hφ, hx, hy, this]
    · have : x + y ∉ W := fun h => hx (by
        have h' := W.add_mem h hy
        rwa [add_assoc, add_self_vec, add_zero] at h')
      simp [hφ, hx, hy, this]
    · simp only [hφ, hx, hy, hnot x y hx hy, ↓reduceIte]
      decide
  have hdot := additive_eq_dot hadd
  refine ⟨fun j => φ (Pi.single j 1), ?_, fun x => ?_⟩
  · intro h0
    obtain ⟨x, hx⟩ : ∃ x, x ∉ W := by
      by_contra hc
      have : W = ⊤ := eq_top_iff.mpr fun x _ => by
        by_contra h
        exact hc ⟨x, h⟩
      have h16 := congrArg (fun H : AddSubgroup (Fin 4 → ZMod 2) => Nat.card H) this
      simp only [AddSubgroup.card_top, card_vec4, hW] at h16
      omega
    have := hdot x
    rw [h0, zero_dotProduct] at this
    simp [hφ, hx] at this
  · rw [← hdot]
    by_cases hx : x ∈ W <;> simp [hφ, hx]

theorem vecMul_eq_of_preserves {n : ℕ} {u : Fin n → ZMod 2} {g : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : ∀ x, u ⬝ᵥ x = 0 ↔ u ⬝ᵥ (g *ᵥ x) = 0) : u ᵥ* g = u := by
  funext j
  have h := hg (Pi.single j 1)
  rw [dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at h
  rcases zmod2_cases (u j) with h0 | h1
  · rw [h0]
    exact h.mp h0
  · rw [h1]
    rcases zmod2_cases ((u ᵥ* g) j) with h0' | h1'
    · exact absurd (h.mpr h0') (by rw [h1]; decide)
    · exact h1'

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

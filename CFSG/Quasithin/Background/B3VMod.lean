module

public import CFSG.Quasithin.Background.B3One

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

noncomputable def toV (n : ℕ) (k : Mod) (m : ℕ) : Mod.V n k :=
  if h : inWk n k m = true then
    (QuotientGroup.mk ⟨vecOfNat n m, (vecOfNat_mem_W k m).2 h⟩ : Mod.V n k)
  else 1

theorem toV_of_inW {k : Mod} {m : ℕ} (h : inWk n k m = true) :
    toV n k m = (QuotientGroup.mk ⟨vecOfNat n m, (vecOfNat_mem_W k m).2 h⟩ : Mod.V n k) := by
  unfold toV
  simp only [h, ↓reduceDIte]

theorem inWk_xor {k : Mod} {a b : ℕ} (ha : inWk n k a = true) (hb : inWk n k b = true) :
    inWk n k (a ^^^ b) = true := by
  rw [← vecOfNat_mem_W, vecOfNat_xor]
  exact (k.W n).mul_mem ((vecOfNat_mem_W k a).2 ha) ((vecOfNat_mem_W k b).2 hb)

theorem inWk_actM {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    inWk n k (actM n (tab σ) m) = true := by
  rw [← vecOfNat_mem_W, vecOfNat_actM]
  exact k.isInv_W n σ _ ((vecOfNat_mem_W k m).2 hm)

theorem toV_xor {k : Mod} {a b : ℕ} (ha : inWk n k a = true) (hb : inWk n k b = true) :
    toV n k (a ^^^ b) = toV n k a * toV n k b := by
  rw [toV_of_inW (inWk_xor ha hb), toV_of_inW ha, toV_of_inW hb, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact vecOfNat_xor a b

theorem act_toV {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    Mod.act n k σ (toV n k m) = toV n k (actM n (tab σ) m) := by
  rw [toV_of_inW hm, toV_of_inW (inWk_actM σ hm), act_mk]
  congr 1
  apply Subtype.ext
  exact (vecOfNat_actM σ m).symm

theorem toV_eq_one_iff {k : Mod} {m : ℕ} (hm : inWk n k m = true) :
    toV n k m = 1 ↔ inNk n k m = true := by
  rw [toV_of_inW hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← vecOfNat_mem_N]

theorem toV_ratio {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    Mod.act n k σ (toV n k m) * (toV n k m)⁻¹ = toV n k (actM n (tab σ) m ^^^ m) := by
  rw [act_toV σ hm, toV_xor (inWk_actM σ hm) hm]
  have h2 : (toV n k m)⁻¹ = toV n k m := by
    have := V_sq (n := n) k (toV n k m)
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  rw [h2]

theorem toV_surj (k : Mod) (v : Mod.V n k) :
    ∃ m, m < 2 ^ n ∧ inWk n k m = true ∧ toV n k m = v := by
  induction v using QuotientGroup.induction_on with
  | H w =>
    obtain ⟨m, hm⟩ := (vecEquiv n).surjective (w : U n)
    have hmW : inWk n k m.val = true := by
      rw [← vecOfNat_mem_W]
      have h1 : vecOfNat n m.val = (w : U n) := hm
      rw [h1]
      exact w.2
    refine ⟨m.val, m.isLt, hmW, ?_⟩
    rw [toV_of_inW hmW]
    congr 1
    apply Subtype.ext
    exact hm

theorem card_S_cnt (k : Mod) (S : Subgroup (Mod.V n k)) (p : ℕ → Bool)
    (hp : ∀ m, inWk n k m = true → (toV n k m ∈ S ↔ p m = true)) :
    Nat.card S * cN n k =
      ((List.range (2 ^ n)).filter (fun m => inWk n k m && p m)).length := by
  classical
  let π : ↥(k.W n) →* Mod.V n k := QuotientGroup.mk' ((k.N n).subgroupOf (k.W n))
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 := Subgroup.card_mul_index (S.comap π)
  have h2 := Subgroup.card_mul_index S
  have h3 := card_V_mul (n := n) k
  have h4 : (S.comap π).index = S.index := Subgroup.index_comap_of_surjective S hsurj
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hcomap : Nat.card ↥(S.comap π) = Nat.card S * cN n k := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h4] at h1
    calc Nat.card ↥(S.comap π) * S.index = Nat.card ↥(k.W n) := h1
      _ = Nat.card (Mod.V n k) * cN n k := h3.symm
      _ = (Nat.card S * S.index) * cN n k := by rw [h2]
      _ = Nat.card S * cN n k * S.index := by ring
  rw [← hcomap]
  have h5 : Nat.card ↥(S.comap π) =
      Nat.card {m : Fin (2 ^ n) // (inWk n k m.val && p m.val) = true} := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(vecEquiv n).symm (w.1 : U n), ?_⟩
        invFun := fun m => ⟨⟨vecEquiv n m.1, ?_⟩, ?_⟩
        left_inv := fun w => ?_
        right_inv := fun m => ?_ }
    · have hw : π w.1 ∈ S := w.2
      have hv : vecOfNat n ((vecEquiv n).symm (w.1 : U n)).val = (w.1 : U n) := by
        have := (vecEquiv n).apply_symm_apply (w.1 : U n)
        exact this
      have hin : inWk n k ((vecEquiv n).symm (w.1 : U n)).val = true := by
        rw [← vecOfNat_mem_W, hv]
        exact w.1.2
      simp only [Bool.and_eq_true]
      refine ⟨hin, (hp _ hin).1 ?_⟩
      rw [toV_of_inW hin]
      have : (⟨vecOfNat n ((vecEquiv n).symm (w.1 : U n)).val, (vecOfNat_mem_W k _).2 hin⟩ :
          ↥(k.W n)) = w.1 := Subtype.ext hv
      rw [this]
      exact hw
    · have hm := m.2
      simp only [Bool.and_eq_true] at hm
      exact (vecOfNat_mem_W k m.1.val).2 hm.1
    · have hm := m.2
      simp only [Bool.and_eq_true] at hm
      show π ⟨vecEquiv n m.1, _⟩ ∈ S
      have : π ⟨vecEquiv n m.1, (vecOfNat_mem_W k m.1.val).2 hm.1⟩ = toV n k m.1.val := by
        rw [toV_of_inW hm.1]
        rfl
      rw [this]
      exact (hp _ hm.1).2 hm.2
    · apply Subtype.ext
      apply Subtype.ext
      exact (vecEquiv n).apply_symm_apply _
    · apply Subtype.ext
      exact (vecEquiv n).symm_apply_apply _
  rw [h5]
  exact card_subtype_range (2 ^ n) (fun m => inWk n k m && p m)

end CFSG.Quasithin.B3

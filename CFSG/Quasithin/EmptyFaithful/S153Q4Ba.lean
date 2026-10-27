module

public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

structure ZCtx (W : Type) [CommGroup W] (z : MulAut W) : Prop where
  sq : ∀ w : W, w * w = 1
  cube : z ^ 3 = 1
  fpf : ∀ w : W, z w = w → w = 1

section Points

variable {W : Type} [CommGroup W] {z : MulAut W}

theorem ZCtx.apply_z3 (C : ZCtx W z) (w : W) : z (z (z w)) = w := by
  have h := congrArg (fun f : MulAut W => f w) C.cube
  simpa [pow_succ, MulAut.mul_apply] using h

theorem ZCtx.inv_eq (C : ZCtx W z) (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_right (C.sq w)

theorem ZCtx.z_ne (C : ZCtx W z) {w : W} (hw : w ≠ 1) : z w ≠ w := fun h => hw (C.fpf w h)

theorem ZCtx.zz_ne (C : ZCtx W z) {w : W} (hw : w ≠ 1) : z (z w) ≠ w := by
  intro h
  apply hw
  apply C.fpf
  have h2 : z (z (z w)) = z w := by rw [h]
  rw [C.apply_z3] at h2
  exact h2.symm

private theorem aut_ne_one (g : MulAut W) {w : W} (hw : w ≠ 1) : g w ≠ 1 := by
  intro h
  apply hw
  apply g.injective
  rw [h, map_one]

private theorem four_card (C : ZCtx W z) {w : W} (hw1 : w ≠ 1) :
    ({1, w, z w, z (z w)} : Set W).ncard = 4 := by
  have h1 : (1 : W) ≠ w := fun h => hw1 h.symm
  have h2 : (1 : W) ≠ z w := fun h => aut_ne_one z hw1 h.symm
  have h3 : (1 : W) ≠ z (z w) := fun h => aut_ne_one z (aut_ne_one z hw1) h.symm
  have h4 : w ≠ z w := fun h => C.z_ne hw1 h.symm
  have h5 : w ≠ z (z w) := fun h => C.zz_ne hw1 h.symm
  have h6 : z w ≠ z (z w) := fun h => C.z_ne hw1 (z.injective h).symm
  have e3 : ({z w, z (z w)} : Set W).ncard = 2 := Set.ncard_pair h6
  have e2 : ({w, z w, z (z w)} : Set W).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h4, h5]), e3]
  rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3]), e2]

private theorem four_sub {S : Subgroup W} (hS : ∀ w ∈ S, z w ∈ S) {w : W} (hw : w ∈ S) :
    ({1, w, z w, z (z w)} : Set W) ⊆ (S : Set W) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact S.one_mem
  · exact hw
  · exact hS _ hw
  · exact hS _ (hS _ hw)

theorem ZCtx.four_le [Finite W] (C : ZCtx W z) {S : Subgroup W} (hS : ∀ w ∈ S, z w ∈ S) {w : W}
    (hw : w ∈ S) (hw1 : w ≠ 1) : 4 ≤ Nat.card ↥S := by
  have h := Set.ncard_le_ncard (four_sub hS hw) (Set.toFinite _)
  rw [four_card C hw1] at h
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem pt_exists_ne_one {o : Subgroup W} (ho : IsPt z o) : ∃ w ∈ o, w ≠ 1 := by
  by_contra h
  have h0 : o = ⊥ := (Subgroup.eq_bot_iff_forall o).2 fun x hx => by
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have h4 := ho.1
  rw [h0, Subgroup.card_bot] at h4
  omega

theorem ZCtx.pt_elems [Finite W] (C : ZCtx W z) {o : Subgroup W} (ho : IsPt z o) {w : W}
    (hw : w ∈ o) (hw1 : w ≠ 1) {x : W} (hx : x ∈ o) : x = 1 ∨ x = w ∨ x = z w ∨ x = z (z w) := by
  have hEq : ({1, w, z w, z (z w)} : Set W) = (o : Set W) := by
    apply Set.eq_of_subset_of_ncard_le (four_sub ho.2 hw) _ (Set.toFinite _)
    rw [four_card C hw1, ← Nat.card_coe_set_eq]
    exact ho.1.le
  have hx' : x ∈ ({1, w, z w, z (z w)} : Set W) := by rw [hEq]; exact hx
  simpa using hx'

theorem ZCtx.pt_eq_of_mem [Finite W] (C : ZCtx W z) {o o' : Subgroup W} (ho : IsPt z o)
    (ho' : IsPt z o') {w : W} (hw : w ∈ o) (hw' : w ∈ o') (hw1 : w ≠ 1) : o = o' := by
  have hinv : ∀ x ∈ o ⊓ o', z x ∈ o ⊓ o' := fun x hx => ⟨ho.2 x hx.1, ho'.2 x hx.2⟩
  have h4 : 4 ≤ Nat.card ↥(o ⊓ o') := C.four_le hinv ⟨hw, hw'⟩ hw1
  have e1 : o ⊓ o' = o := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ho.1]; exact h4)
  have e2 : o ⊓ o' = o' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [ho'.1]; exact h4)
  rw [← e1, e2]

theorem ZCtx.pt_inf_eq_bot [Finite W] (C : ZCtx W z) {o o' : Subgroup W} (ho : IsPt z o)
    (ho' : IsPt z o') (h : o ≠ o') : o ⊓ o' = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  exact h (C.pt_eq_of_mem ho ho' hx.1 hx.2 hx1)

theorem card_sup_of_inf_eq_bot [Finite W] {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  let φ : ↥A × ↥B →* W :=
    (A.subtype.comp (MonoidHom.fst _ _)) * (B.subtype.comp (MonoidHom.snd _ _))
  have hφ : ∀ x : ↥A × ↥B, φ x = (x.1 : W) * (x.2 : W) := fun x => rfl
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (x.1 : W) * (x.2 : W) = 1 := by rw [← hφ]; exact hx
    have hb : (x.1 : W) ∈ B := by
      have : (x.1 : W) = (x.2 : W)⁻¹ := eq_inv_of_mul_eq_one_left hx'
      rw [this]; exact B.inv_mem x.2.2
    have h1 : (x.1 : W) = 1 := by
      have : (x.1 : W) ∈ A ⊓ B := ⟨x.1.2, hb⟩
      rw [h] at this
      exact this
    have h2 : (x.2 : W) = 1 := by
      rw [h1, one_mul] at hx'
      exact hx'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hrange : φ.range = A ⊔ B := by
    ext x
    rw [Subgroup.mem_sup]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hc := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Subgroup.card_bot, one_mul, Nat.card_prod] at hc
  exact hc

theorem ZCtx.card_sup_pts [Finite W] (C : ZCtx W z) {o o' : Subgroup W} (ho : IsPt z o)
    (ho' : IsPt z o') (h : o ≠ o') : Nat.card ↥(o ⊔ o') = 16 := by
  rw [card_sup_of_inf_eq_bot (C.pt_inf_eq_bot ho ho' h), ho.1, ho'.1]

private theorem card_filter_mem [Fintype W] [DecidableEq W] (H : Subgroup W) [DecidablePred (· ∈ H)] :
    (Finset.univ.filter (· ∈ H)).card = Nat.card ↥H := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem line_pts [Finite W] {V : Subgroup W} (hV : Nat.card ↥V = 16) {m : ℕ}
    (o : Fin m → Subgroup W) (hc : ∀ i, Nat.card ↥(o i) = 4) (hle : ∀ i, o i ≤ V)
    (hd : ∀ i j, i ≠ j → o i ⊓ o j = ⊥) : m ≤ 5 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  let S : Fin m → Finset W := fun i => (Finset.univ.filter (· ∈ o i)).erase 1
  have hS : ∀ i, (S i).card = 3 := by
    intro i
    have h1 : (1 : W) ∈ Finset.univ.filter (· ∈ o i) := by simp
    simp only [S]
    rw [Finset.card_erase_of_mem h1, card_filter_mem, hc i]
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (S i) (S j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    have : x ∈ o i ⊓ o j := ⟨hxi.2, hxj.2⟩
    rw [hd i j hij] at this
    exact hxi.1 this
  have hsub : Finset.univ.biUnion S ⊆ (Finset.univ.filter (· ∈ V)).erase 1 := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, S, Finset.mem_erase,
      Finset.mem_filter] at hx ⊢
    obtain ⟨i, hi1, hi⟩ := hx
    exact ⟨hi1, hle i hi⟩
  have hV' : ((Finset.univ.filter (· ∈ V)).erase 1).card = 15 := by
    have h1 : (1 : W) ∈ Finset.univ.filter (· ∈ V) := by simp
    rw [Finset.card_erase_of_mem h1, card_filter_mem, hV]
  have := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, hV'] at this
  simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

theorem ZCtx.mem_zpowers (C : ZCtx W z) {g : MulAut W} (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z ∨ g = z * z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h3 : z ^ (3 : ℤ) = 1 := by exact_mod_cast C.cube
  have hm : z ^ m = z ^ (m % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod m 3, zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rw [hm]
  have h0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
  have h1 : m % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hr : m % 3
  · left; simp
  · right; left; simp
  · right; right; simp [pow_two]

theorem ZCtx.zpowers_sq (C : ZCtx W z) {g : MulAut W} (hg : g ∈ Subgroup.zpowers z)
    (hgg : g * g = 1) : g = 1 := by
  rcases C.mem_zpowers hg with h | h | h
  · exact h
  · subst h
    have h3 := C.cube
    rw [pow_succ, pow_two, hgg, one_mul] at h3
    exact h3
  · subst h
    have h4 : z ^ 4 = 1 := by
      have : z ^ 4 = z * z * (z * z) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [this]; exact hgg
    have h43 : z ^ 4 = z * z ^ 3 := pow_succ' z 3
    rw [h4, C.cube, mul_one] at h43
    rw [← h43, one_mul]

end Points

section Finite

def S3 : Fin 3 → Perm (Fin 6)
  | 0 => swap 0 1 * swap 2 3
  | 1 => swap 0 3 * swap 1 2
  | 2 => swap 0 2 * swap 1 3

def tau : Perm (Fin 6) := swap 0 1 * swap 1 2

theorem S3_mem (a : Fin 3) : S3 a ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; revert a; decide

theorem tau_mem : tau ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem S3_sq (a : Fin 3) : S3 a * S3 a = 1 := by revert a; decide
theorem S3_four (a : Fin 3) : S3 a 4 = 4 := by revert a; decide
theorem S3_five (a : Fin 3) : S3 a 5 = 5 := by revert a; decide
theorem S3_zero_ne (a : Fin 3) : S3 a 0 ≠ 0 := by revert a; decide
theorem S3_zero_ne_four (a : Fin 3) : S3 a 0 ≠ 4 := by revert a; decide
theorem S3_zero_ne_five (a : Fin 3) : S3 a 0 ≠ 5 := by revert a; decide
theorem S3_zero_inj {a b : Fin 3} (h : S3 a 0 = S3 b 0) : a = b := by
  revert a b; decide
theorem tau_four : tau 4 = 4 := by decide
theorem tau_five : tau 5 = 5 := by decide
theorem tau_cube : tau * tau * tau = 1 := by decide
theorem tau_conj (a : Fin 3) : tau * S3 a * tau⁻¹ = S3 (a + 1) := by revert a; decide
theorem fin3_add_one_ne (a : Fin 3) : a + 1 ≠ a := by revert a; decide

end Finite

end Q4B

end S153Q

end CFSG.Quasithin

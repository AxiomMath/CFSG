module

public import CFSG.Timmesfeld.Exceptional.DeepQ
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Timmesfeld.Exceptional.DeepAllNearInputs
public import Certificates.Certificate8053

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.CosetTable

theorem allNear_card_le :
    (Finite (PG 7 (relsAN ++ [prodAN])) ∧ Nat.card (PG 7 (relsAN ++ [prodAN])) ≤ 1) ∧
    (Finite (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ∧
      Nat.card (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ≤ 1) :=
  Certificates.certificate8053

theorem allNear_collapse
    {K : Type*} [Group K] {p w : K} {y : Fin 5 → K} (hp : p * p = 1)
    (hw : w * w = 1) (hpw : (p * w) ^ 3 = 1) (hy : ∀ i, y i * y i = 1)
    (hpy : ∀ i, Commute p (y i)) (hyw : ∀ i, (y i * w) ^ 4 = 1)
    (hpyw : ∀ i, (p * y i * w) ^ 3 = 1) (hwxp : ∀ i, (w * (y i * w) ^ 2 * p) ^ 3 = 1)
    (hyy : ∀ i j, i < j → (y i * y j) ^ 2 = p)
    (hxx : ∀ i j, i < j → ((y i * w) ^ 2 * (y j * w) ^ 2) ^ 2 = w)
    (hyx : ∀ i j, i ≠ j → (y i * (y j * w) ^ 2) ^ 3 = 1)
    (hprod : y 0 * y 1 * y 2 * y 3 * y 4 = 1 ∨ y 0 * y 1 * y 2 * y 3 * y 4 = p) : p = 1 := by
  set x : Fin 7 → K := ![p, w, y 0, y 1, y 2, y 3, y 4] with hx
  have hx0 : signedProd x [letAN 0] = p := by simp [x, letAN, signedProd]
  have hx0' : signedProd x [letAN 0 false] = p⁻¹ := by simp [x, letAN, signedProd]
  have hx1 : signedProd x [letAN 1] = w := by simp [x, letAN, signedProd]
  have hx1' : signedProd x [letAN 1 false] = w⁻¹ := by simp [x, letAN, signedProd]
  have hxy : ∀ (i : ℕ) (hi : i < 5), signedProd x (wyAN i) = y ⟨i, hi⟩ := by
    intro i hi
    interval_cases i <;> simp [x, wyAN, letAN, signedProd]
  have hxx' : ∀ (i : ℕ) (hi : i < 5), signedProd x (wxAN i) = (y ⟨i, hi⟩ * w) ^ 2 := by
    intro i hi
    rw [show wxAN i = wyAN i ++ [letAN 1] ++ wyAN i ++ [letAN 1] from rfl, signedProd_append,
      signedProd_append, signedProd_append, hxy i hi, hx1, sq]
    group
  have hrel : ∀ r ∈ relsAN, signedProd x r = 1 := by
    intro r hr
    simp only [relsAN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_range] at hr
    rcases hr with ((rfl | rfl | rfl) | ⟨i, hi, hr⟩) | ⟨i, hi, j, hj, hr⟩
    · rw [repAN, signedProd_replicate, hx0, sq, hp]
    · rw [repAN, signedProd_replicate, hx1, sq, hw]
    · rw [repAN, signedProd_replicate, show [letAN 0, letAN 1] = [letAN 0] ++ [letAN 1] from rfl,
        signedProd_append, hx0, hx1, hpw]
    · rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [repAN, signedProd_replicate, hxy i hi, sq, hy]
      · rw [signedProd_append, signedProd_append, signedProd_append, hx0, hxy i hi]
        have hc := (hpy ⟨i, hi⟩).eq
        calc p * y ⟨i, hi⟩ * p * y ⟨i, hi⟩ = p * (y ⟨i, hi⟩ * p) * y ⟨i, hi⟩ := by group
          _ = p * (p * y ⟨i, hi⟩) * y ⟨i, hi⟩ := by rw [hc]
          _ = 1 := by rw [← mul_assoc, hp, one_mul, hy]
      · rw [repAN, signedProd_replicate, signedProd_append, hxy i hi, hx1, hyw]
      · rw [repAN, signedProd_replicate, signedProd_append, signedProd_append, hx0, hxy i hi, hx1,
          hpyw]
      · rw [repAN, signedProd_replicate, signedProd_append, signedProd_append, hx1, hxx' i hi, hx0,
          hwxp]
    · rcases hr with hr | hr
      · split_ifs at hr with hij
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [signedProd_append, repAN, signedProd_replicate, signedProd_append, hxy i hi,
              hxy j hj, hx0', hyy ⟨i, hi⟩ ⟨j, hj⟩ hij, mul_inv_cancel]
          · rw [signedProd_append, repAN, signedProd_replicate, signedProd_append, hxx' i hi,
              hxx' j hj, hx1', hxx ⟨i, hi⟩ ⟨j, hj⟩ hij, mul_inv_cancel]
        · simp at hr
      · split_ifs at hr with hij
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rw [hr, repAN, signedProd_replicate, signedProd_append, hxy i hi, hxx' j hj]
          exact hyx ⟨i, hi⟩ ⟨j, hj⟩ fun e => hij (congrArg Fin.val e)
        · simp at hr
  have hxp : signedProd x prodAN = y 0 * y 1 * y 2 * y 3 * y 4 := by
    rw [show prodAN = [letAN 2, letAN 3, letAN 4, letAN 5, letAN 6] from rfl]
    simp [x, letAN, signedProd, mul_assoc]
  obtain ⟨⟨hf1, hc1⟩, ⟨hf2, hc2⟩⟩ := allNear_card_le
  rcases hprod with h1 | h1
  · have hx' : ∀ r ∈ relsAN ++ [prodAN], signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hrel r hr
      · rw [List.mem_singleton.1 hr, hxp, h1]
    have : Subsingleton (PG 7 (relsAN ++ [prodAN])) := Finite.card_le_one_iff_subsingleton.1 hc1
    rw [← hx0, show signedProd x [letAN 0] = x 0 by simp [signedProd, letAN], ← pgHom_of _ x hx' 0,
      Subsingleton.elim (PresentedGroup.of 0) 1, map_one]
  · have hx' : ∀ r ∈ relsAN ++ [prodAN ++ [letAN 0 false]], signedProd x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hrel r hr
      · rw [List.mem_singleton.1 hr, signedProd_append, hxp, h1, hx0', mul_inv_cancel]
    have : Subsingleton (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) :=
      Finite.card_le_one_iff_subsingleton.1 hc2
    rw [← hx0, show signedProd x [letAN 0] = x 0 by simp [signedProd, letAN], ← pgHom_of _ x hx' 0,
      Subsingleton.elim (PresentedGroup.of 0) 1, map_one]

theorem allNearCollapse :
    ∀ (G : Type) [Group G] (w p : G) (s : Fin 5 → G), w * w = 1 → p * p = 1 →
      (w * p) ^ 3 = 1 → (∀ i, s i * s i = 1) → (∀ i, Commute w (s i)) →
      (∀ i, (s i * p) ^ 4 = 1) → (∀ i, (w * s i * p) ^ 3 = 1) →
      (∀ i, (p * (s i * p) ^ 2 * w) ^ 3 = 1) → (∀ i j, i < j → (s i * s j) ^ 2 = w) →
      (∀ i j, i < j → ((s i * p) ^ 2 * (s j * p) ^ 2) ^ 2 = p) →
      (∀ i j, i ≠ j → (s i * (s j * p) ^ 2) ^ 3 = 1) →
      (s 0 * s 1 * s 2 * s 3 * s 4 = 1 ∨ s 0 * s 1 * s 2 * s 3 * s 4 = w) → w = 1 :=
  fun _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    allNear_collapse h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end CFSG.Timmesfeld.Moufang.Deep

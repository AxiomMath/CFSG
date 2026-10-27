module

public import CFSG.Monster.GMS.S342
public import CFSG.Monster.GMS.S347
public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

@[expose] def OddExhaustive (a z₀ : G) : Prop :=
  ∀ x y : G, IsConj a x → IsConj a y → y ≠ x → Odd (orderOf (x * y)) → y ∈ oddNbr a z₀ x

@[expose] def OddTypesSeparated (a z₀ : G) : Prop :=
  ∀ x y y' : G, IsConj a x → y ∈ oddNbr a z₀ x → y' ∈ oddNbr a z₀ x → OddNbrType z₀ x y 0 →
    OddNbrType z₀ x y' 1 → ¬ IsConj (x * y) (x * y')

theorem isConj_pow_of_isConj {u v : G} (h : IsConj u v) (n : ℕ) : IsConj (u ^ n) (v ^ n) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by rw [← hc, conj_pow]⟩

theorem orderOf_eq_of_isConj {u v : G} (h : IsConj u v) : orderOf u = orderOf v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact SemiconjBy.orderOf_eq c (show c * u = v * c by rw [← hc]; group)

theorem mem_tableVIISet_iff_of_isConj {a z₀ x y y' : G} (hy : IsConj a y) (hy' : IsConj a y')
    (h : IsConj (x * y) (x * y')) (K : TableVIIClass) :
    y ∈ tableVIISet a z₀ x K ↔ y' ∈ tableVIISet a z₀ x K := by
  have ho := orderOf_eq_of_isConj h
  cases K with
  | two_A =>
    simp only [tableVIISet, twoANbr, Set.mem_ofPred_eq]
    exact ⟨fun h1 => ⟨hy', h1.2.trans h⟩, fun h1 => ⟨hy, h1.2.trans h.symm⟩⟩
  | two_B =>
    simp only [tableVIISet, twoBNbr, Set.mem_ofPred_eq]
    exact ⟨fun h1 => ⟨hy', h1.2.trans h⟩, fun h1 => ⟨hy, h1.2.trans h.symm⟩⟩
  | four_A =>
    simp only [tableVIISet, fourANbr, Set.mem_ofPred_eq]
    exact ⟨fun h1 => ⟨hy', ho ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 2)⟩,
      fun h1 => ⟨hy, ho.symm ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 2).symm⟩⟩
  | four_B =>
    simp only [tableVIISet, fourBNbr, Set.mem_ofPred_eq]
    exact ⟨fun h1 => ⟨hy', ho ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 2)⟩,
      fun h1 => ⟨hy, ho.symm ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 2).symm⟩⟩
  | six_A =>
    simp only [tableVIISet, sixANbr, Set.mem_ofPred_eq]
    exact ⟨fun h1 => ⟨hy', ho ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 3)⟩,
      fun h1 => ⟨hy, ho.symm ▸ h1.2.1, h1.2.2.trans (isConj_pow_of_isConj h 3).symm⟩⟩

theorem orderOf_mul_of_oddNbrType {a z₀ x y : G} (hy : y ∈ oddNbr a z₀ x) {k : Fin 3}
    (hk : OddNbrType z₀ x y k) : orderOf (x * y) = oddTypeOrder k := by
  obtain ⟨-, -, -, w, hw, hwB⟩ := hy
  exact (s348_card hk hw hwB).1

theorem mul_self_of_isConj {u x : G} (hu : orderOf u = 2) (hx : IsConj u x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
    _ = 1 := by rw [hu2]; group

theorem eq_of_mul_eq_one_of_mul_self {x y : G} (hx : x * x = 1) (h : x * y = 1) : y = x :=
  mul_left_cancel (h.trans hx.symm)

variable [Finite G] {d₀ : B} {a z₀ : G}

theorem three_i_even
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x y y' : G}
    (hx : IsConj a x) (hy : IsConj a y) (hy' : IsConj a y') (hev : Even (orderOf (x * y)))
    (h : IsConj (x * y) (x * y')) : ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * y * g⁻¹ = y' := by
  obtain ⟨K, hK, -⟩ := table7_classify I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hy hev
  have hK' := (mem_tableVIISet_iff_of_isConj hy hy' h K).1 hK
  exact table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair
    hG hx hK hK'

theorem three_i_oddNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hsep : OddTypesSeparated a z₀) {x y y' : G} (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x)
    (hy' : y' ∈ oddNbr a z₀ x) (h : IsConj (x * y) (x * y')) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * y * g⁻¹ = y' := by
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy
  obtain ⟨k', hk', -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy'
  have ho : oddTypeOrder k = oddTypeOrder k' := by
    rw [← orderOf_mul_of_oddNbrType hy hk, ← orderOf_mul_of_oddNbrType hy' hk']
    exact orderOf_eq_of_isConj h
  have hkk : k = k' := by
    by_contra hne
    have h01 : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
      revert ho hne
      fin_cases k <;> fin_cases k' <;> simp [oddTypeOrder]
    rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsep x y y' hx hy hy' hk hk' h
    · exact hsep x y' y hx hy' hy hk' hk h.symm
  subst hkk
  exact s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy hy' hk hk'

theorem three_i
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hex : OddExhaustive a z₀)
    (hsep : OddTypesSeparated a z₀) {x y y' : G} (hx : IsConj a x) (hy : IsConj a y)
    (hy' : IsConj a y') (h : IsConj (x * y) (x * y')) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * y * g⁻¹ = y' := by
  have hx2 : x * x = 1 := mul_self_of_isConj hG.1.1 hx
  rcases Nat.even_or_odd (orderOf (x * y)) with hev | hodd
  · exact three_i_even I hG hx hy hy' hev h
  · by_cases hxy : y = x
    · rw [hxy, hx2] at h
      have h1 : x * y' = 1 := isConj_one_right.1 h
      exact ⟨1, one_mem _, by rw [eq_of_mul_eq_one_of_mul_self hx2 h1, hxy]; group⟩
    · have hodd' : Odd (orderOf (x * y')) := orderOf_eq_of_isConj h ▸ hodd
      have hxy' : y' ≠ x := by
        intro he
        rw [he, hx2] at h
        exact hxy (eq_of_mul_eq_one_of_mul_self hx2 (isConj_one_left.1 h))
      exact three_i_oddNbr I hG hsep hx (hex x y hx hy hxy hodd) (hex x y' hx hy' hxy' hodd') h

end CFSG.Monster.Existence

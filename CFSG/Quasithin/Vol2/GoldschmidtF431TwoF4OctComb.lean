module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

@[expose] def octS (i j : ℤ) : Set (Fin F4.tag.rank → ℤ) :=
  {α | ∃ k : ℤ, i ≤ k ∧ k ≤ j ∧ α ∈ octPos k}

@[expose] def octPosKeys : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8]

theorem mem_octPosKeys_iff {k : ℤ} : k ∈ octPosKeys ↔ 1 ≤ k ∧ k ≤ 8 := by
  simp only [octPosKeys, List.mem_cons, List.not_mem_nil, or_false]
  omega

@[expose] def octOmega (x y : Fin F4.tag.rank → ℤ) : ℤ :=
  2 * (x ⟨1, by decide⟩ * y ⟨0, by decide⟩ - x ⟨0, by decide⟩ * y ⟨1, by decide⟩) +
  (x ⟨2, by decide⟩ * y ⟨3, by decide⟩ - x ⟨3, by decide⟩ * y ⟨2, by decide⟩) +
  (x ⟨2, by decide⟩ * y ⟨0, by decide⟩ - x ⟨0, by decide⟩ * y ⟨2, by decide⟩) +
  (x ⟨1, by decide⟩ * y ⟨3, by decide⟩ - x ⟨3, by decide⟩ * y ⟨1, by decide⟩)

theorem octOmega_self (x : Fin F4.tag.rank → ℤ) : octOmega x x = 0 := by
  simp only [octOmega]
  ring

theorem octOmega_right (a b : ℕ) (α β : Fin F4.tag.rank → ℤ) :
    octOmega α (a • α + b • β) = b * octOmega α β := by
  have h : ∀ i, (a • α + b • β) i = a * α i + b * β i := fun i => by simp
  simp only [octOmega, h]
  ring

theorem octOmega_left (a b : ℕ) (α β : Fin F4.tag.rank → ℤ) :
    octOmega (a • α + b • β) β = a * octOmega α β := by
  have h : ∀ i, (a • α + b • β) i = a * α i + b * β i := fun i => by simp
  simp only [octOmega, h]
  ring

theorem octLP_omega : ∀ k ∈ octPosKeys, ∀ x ∈ octLP k, ∀ l ∈ octPosKeys, ∀ y ∈ octLP l,
    (k < l → 0 < octOmega x y) ∧ (k = l → octOmega x y = 0) ∧ (l < k → octOmega x y < 0) := by
  decide +kernel

theorem largeReeBlockTable_pos_octLP : ∀ i : Fin 16,
    (∀ x ∈ largeReeBlockTable i, 0 < height x) →
      ∃ k ∈ octPosKeys, largeReeBlockTable i ⊆ octLP k ∧ octLP k ⊆ largeReeBlockTable i := by
  decide +kernel

section Certs

theorem mem_octPos_iff (k : ℤ) (x : Fin F4.tag.rank → ℤ) : x ∈ octPos k ↔ x ∈ octLP k := by
  rw [octPos_eq]
  rfl

theorem octPos_isRoot {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) :
    ∀ α ∈ octPos k, IsRoot F4.tag α ∧ 0 < height α := by
  intro α hα
  have hα' : α ∈ octBlock k := by
    rw [octBlock_pos (by omega)]
    exact hα
  refine ⟨isRoot_of_mem_octBlock (octKeys_of_pos h1 h8) hα', ?_⟩
  exact height_octLP_pos k (mem_octPosKeys_iff.2 ⟨h1, h8⟩) α ((mem_octPos_iff k α).1 hα)

theorem octPos_mem_posBlocks {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) :
    octPos k ∈ largeReePosBlocks := by
  refine ⟨?_, fun α hα => octPos_isRoot h1 h8 α hα⟩
  have h := octBlock_mem_largeReeBlocks (octKeys_of_pos h1 h8)
  rwa [octBlock_pos (by omega)] at h

theorem octPos_range : ∀ Q ∈ largeReePosBlocks, ∃ k : ℤ, 1 ≤ k ∧ k ≤ 8 ∧ Q = octPos k := by
  intro Q hQ
  have hQ' := hQ.1
  rw [largeReeBlocks_eq_range] at hQ'
  obtain ⟨i, rfl⟩ := hQ'
  obtain ⟨k, hk, h1, h2⟩ := largeReeBlockTable_pos_octLP i (fun x hx => (hQ.2 hx).2)
  obtain ⟨hk1, hk8⟩ := mem_octPosKeys_iff.1 hk
  refine ⟨k, hk1, hk8, ?_⟩
  rw [octPos_eq]
  exact (setOf_mem_eq_of_subset h2 h1).symm

theorem octPos_disjoint {k k' : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) (h1' : 1 ≤ k') (h8' : k' ≤ 8)
    (hne : k ≠ k') : Disjoint (octPos k) (octPos k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h := octLP_omega k (mem_octPosKeys_iff.2 ⟨h1, h8⟩) x ((mem_octPos_iff k x).1 hx)
    k' (mem_octPosKeys_iff.2 ⟨h1', h8'⟩) x ((mem_octPos_iff k' x).1 hx')
  rw [octOmega_self] at h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lt_irrefl _ (h.1 hlt)
  · exact lt_irrefl _ (h.2.2 hgt)

theorem octS_one_eight : octS 1 8 = {α | IsRoot F4.tag α ∧ 0 < height α} := by
  ext α
  constructor
  · rintro ⟨k, h1, h8, hα⟩
    exact octPos_isRoot h1 h8 α hα
  · rintro ⟨hr, hp⟩
    have hU : α ∈ ⋃₀ largeReeBlocks := by
      rw [sUnion_largeReeBlocks]
      exact hr
    obtain ⟨Q', hQ', hα⟩ := hU
    have hpos : Q' ∈ largeReePosBlocks := by
      refine ⟨hQ', fun β hβ => ⟨isRoot_of_mem_largeReeBlocks hQ' hβ, ?_⟩⟩
      rcases largeReeBlocks_sign hQ' with h | h
      · exact h β hβ
      · exact absurd (h α hα) (by omega)
    obtain ⟨k, h1, h8, rfl⟩ := octPos_range Q' hpos
    exact ⟨k, h1, h8, hα⟩

theorem oct_between {k₁ k₂ : ℤ} {α β : Fin F4.tag.rank → ℤ} {a b : ℕ} (h1 : 1 ≤ k₁)
    (h12 : k₁ ≤ k₂) (h8 : k₂ ≤ 8) (hα : α ∈ octPos k₁) (hβ : β ∈ octPos k₂) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hr : IsRoot F4.tag (a • α + b • β)) :
    ∃ k : ℤ, (k₁ = k₂ → k = k₁) ∧ (k₁ < k₂ → k₁ < k ∧ k < k₂) ∧ a • α + b • β ∈ octPos k := by
  obtain ⟨-, hαh⟩ := octPos_isRoot h1 (h12.trans h8) α hα
  obtain ⟨-, hβh⟩ := octPos_isRoot (h1.trans h12) h8 β hβ
  have hγ : a • α + b • β ∈ octS 1 8 := by
    rw [octS_one_eight]
    refine ⟨hr, ?_⟩
    rw [height_nsmul_add_nsmul]
    have h1' : (0 : ℤ) < a := by exact_mod_cast ha
    have h2' : (0 : ℤ) < b := by exact_mod_cast hb
    have := mul_pos h1' hαh
    have := mul_pos h2' hβh
    linarith
  obtain ⟨r, hr1, hr8, hγr⟩ := hγ
  have T12 := octLP_omega k₁ (mem_octPosKeys_iff.2 ⟨h1, h12.trans h8⟩) α
    ((mem_octPos_iff k₁ α).1 hα) k₂ (mem_octPosKeys_iff.2 ⟨h1.trans h12, h8⟩) β
    ((mem_octPos_iff k₂ β).1 hβ)
  have T1r := octLP_omega k₁ (mem_octPosKeys_iff.2 ⟨h1, h12.trans h8⟩) α
    ((mem_octPos_iff k₁ α).1 hα) r (mem_octPosKeys_iff.2 ⟨hr1, hr8⟩) _
    ((mem_octPos_iff r _).1 hγr)
  have Tr2 := octLP_omega r (mem_octPosKeys_iff.2 ⟨hr1, hr8⟩) _ ((mem_octPos_iff r _).1 hγr)
    k₂ (mem_octPosKeys_iff.2 ⟨h1.trans h12, h8⟩) β ((mem_octPos_iff k₂ β).1 hβ)
  rw [octOmega_right] at T1r
  rw [octOmega_left] at Tr2
  refine ⟨r, fun hk => ?_, fun hlt => ?_, hγr⟩
  · rw [T12.2.1 hk, mul_zero] at T1r
    rcases lt_trichotomy k₁ r with h | h | h
    · exact absurd (T1r.1 h) (lt_irrefl _)
    · exact h.symm
    · exact absurd (T1r.2.2 h) (lt_irrefl _)
  · have hw : 0 < octOmega α β := T12.1 hlt
    have hbw : 0 < (b : ℤ) * octOmega α β := mul_pos (by exact_mod_cast hb) hw
    have haw : 0 < (a : ℤ) * octOmega α β := mul_pos (by exact_mod_cast ha) hw
    refine ⟨?_, ?_⟩
    · rcases lt_trichotomy k₁ r with h | h | h
      · exact h
      · have := T1r.2.1 h
        omega
      · have := T1r.2.2 h
        omega
    · rcases lt_trichotomy r k₂ with h | h | h
      · exact h
      · have := Tr2.2.1 h
        omega
      · have := Tr2.2.2 h
        omega

theorem oct_between_any {k₁ k₂ : ℤ} {α β : Fin F4.tag.rank → ℤ} {a b : ℕ} (h1 : 1 ≤ k₁)
    (h8 : k₁ ≤ 8) (h1' : 1 ≤ k₂) (h8' : k₂ ≤ 8) (hα : α ∈ octPos k₁) (hβ : β ∈ octPos k₂)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot F4.tag (a • α + b • β)) :
    ∃ k : ℤ, (k₁ = k₂ → k = k₁) ∧ (k₁ < k₂ → k₁ < k ∧ k < k₂) ∧
      (k₂ < k₁ → k₂ < k ∧ k < k₁) ∧ a • α + b • β ∈ octPos k := by
  rcases le_total k₁ k₂ with h | h
  · obtain ⟨k, e1, e2, hk⟩ := oct_between h1 h h8' hα hβ ha hb hr
    exact ⟨k, e1, e2, fun h' => absurd h' (not_lt.2 h), hk⟩
  · have hr' : IsRoot F4.tag (b • β + a • α) := by rwa [add_comm] at hr
    obtain ⟨k, e1, e2, hk⟩ := oct_between h1' h h8 hβ hα hb ha hr'
    refine ⟨k, fun h' => (e1 h'.symm).trans h'.symm, fun h' => absurd h' (not_lt.2 h), e2, ?_⟩
    rwa [add_comm] at hk

theorem octS_closed {i j : ℤ} {α β : Fin F4.tag.rank → ℤ} {a b : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j)
    (h8 : j ≤ 8) (hα : α ∈ octS i j) (hβ : β ∈ octS i j) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot F4.tag (a • α + b • β)) : a • α + b • β ∈ octS i j := by
  obtain ⟨k₁, hi₁, hj₁, hα'⟩ := hα
  obtain ⟨k₂, hi₂, hj₂, hβ'⟩ := hβ
  obtain ⟨k, e1, e2, e3, hk⟩ :=
    oct_between_any (by omega) (by omega) (by omega) (by omega) hα' hβ' ha hb hr
  refine ⟨k, ?_, ?_, hk⟩ <;>
  · rcases lt_trichotomy k₁ k₂ with h | h | h
    · have := e2 h
      omega
    · have := e1 h
      omega
    · have := e3 h
      omega

theorem octS_ideal_left {i j : ℤ} {α β : Fin F4.tag.rank → ℤ} {a b : ℕ} (h2 : 2 ≤ i)
    (hij : i ≤ j) (h8 : j ≤ 8) (hα : α ∈ octS (i - 1) j) (hβ : β ∈ octS i j) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hr : IsRoot F4.tag (a • α + b • β)) : a • α + b • β ∈ octS i j := by
  obtain ⟨k₁, hi₁, hj₁, hα'⟩ := hα
  obtain ⟨k₂, hi₂, hj₂, hβ'⟩ := hβ
  obtain ⟨k, e1, e2, e3, hk⟩ :=
    oct_between_any (by omega) (by omega) (by omega) (by omega) hα' hβ' ha hb hr
  refine ⟨k, ?_, ?_, hk⟩ <;>
  · rcases lt_trichotomy k₁ k₂ with h | h | h
    · have := e2 h
      omega
    · have := e1 h
      omega
    · have := e3 h
      omega

theorem octS_ideal_right {i j : ℤ} {α β : Fin F4.tag.rank → ℤ} {a b : ℕ} (h1 : 1 ≤ i)
    (hij : i ≤ j) (h7 : j ≤ 7) (hα : α ∈ octS i (j + 1)) (hβ : β ∈ octS i j) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hr : IsRoot F4.tag (a • α + b • β)) : a • α + b • β ∈ octS i j := by
  obtain ⟨k₁, hi₁, hj₁, hα'⟩ := hα
  obtain ⟨k₂, hi₂, hj₂, hβ'⟩ := hβ
  obtain ⟨k, e1, e2, e3, hk⟩ :=
    oct_between_any (by omega) (by omega) (by omega) (by omega) hα' hβ' ha hb hr
  refine ⟨k, ?_, ?_, hk⟩ <;>
  · rcases lt_trichotomy k₁ k₂ with h | h | h
    · have := e2 h
      omega
    · have := e1 h
      omega
    · have := e3 h
      omega

end Certs

end CFSG.Quasithin.H13.F431.TwoF4

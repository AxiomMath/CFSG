module

public import CFSG.Sporadic.Recognition.LyonsAS44M11
public import CFSG.Sporadic.Recognition.LyonsAS44Q8

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS
open CFSG.Semidihedral.GL2Recognition.SharpFourM11

section Classes

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

section Basic

variable (S : LyStd ρ x₁ x₂ x₃)

include S

omit [Finite G] in
theorem x₁_ne_one : (x₁ : G) ≠ 1 := by
  intro h
  have h3 := orderOf_x₁ S
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

omit [Finite G] in
theorem ne_one_of_mem_SG {u : G} (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u) : u ≠ 1 := by
  intro h
  rw [h] at hu
  exact x₁_ne_one S (isConj_one_left.1 hu.2)

omit [Finite G] in
theorem ptOf_eq_iff {u v : G} (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v) :
    ptOf (x₁ : G) A u hu.1 hu.2 = ptOf (x₁ : G) A v hv.1 hv.2 ↔ v = u ∨ v = u⁻¹ := by
  rw [ptOf, ptOf, Subtype.mk.injEq]
  exact eq_comm.trans (zpowers_eq_iff (pow_three_of_isConj_x₁ S hu.2) (ne_one_of_mem_SG S hu))

omit [Finite G] in
theorem conj_eq_or_inv_of_actPerm {k : ↥(normAG (x₁ : G) A)} {u w : G}
    (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hw : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w)
    (h : actPerm (x₁ : G) A k (ptOf (x₁ : G) A u hu.1 hu.2) = ptOf (x₁ : G) A w hw.1 hw.2) :
    (k : G) * u * (k : G)⁻¹ = w ∨ (k : G) * u * (k : G)⁻¹ = w⁻¹ := by
  have h1 : conjSub (k : G) (zpowers u) = zpowers w := congrArg Subtype.val h
  rw [conjSub_zpowers] at h1
  exact (zpowers_eq_iff (pow_three_of_isConj_x₁ S hw.2) (ne_one_of_mem_SG S hw)).1 h1

omit [Finite G] in
theorem ptOf_ne {a b : G} (ha : a ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) a)
    (hb : b ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) b) (h1 : b ≠ a) (h2 : b ≠ a⁻¹) :
    ptOf (x₁ : G) A a ha.1 ha.2 ≠ ptOf (x₁ : G) A b hb.1 hb.2 := by
  intro h
  rcases (ptOf_eq_iff S ha hb).1 h with h | h
  · exact h1 h
  · exact h2 h

end Basic

omit [Finite G] in
theorem exists_eq_toGamma (γ : ↥(gammaG (x₁ : G) A)) :
    ∃ k : ↥(normAG (x₁ : G) A), toGamma (x₁ : G) A k = γ := by
  obtain ⟨γ', k, rfl⟩ := γ
  exact ⟨k, rfl⟩

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

omit [Finite G] F in
theorem six_ne : (x₂ : G) ≠ (x₁ : G) ∧ (x₂ : G) ≠ (x₁ : G)⁻¹ ∧ (x₃ : G) ≠ (x₁ : G) ∧
    (x₃ : G) ≠ (x₁ : G)⁻¹ ∧ (x₃ : G) ≠ (x₂ : G) ∧ (x₃ : G) ≠ (x₂ : G)⁻¹ := by
  have hsix := D.injective_six S
  exact ⟨by simpa using hsix.ne (show (2 : Fin 6) ≠ 0 by decide),
    by simpa using hsix.ne (show (2 : Fin 6) ≠ 1 by decide),
    by simpa using hsix.ne (show (4 : Fin 6) ≠ 0 by decide),
    by simpa using hsix.ne (show (4 : Fin 6) ≠ 1 by decide),
    by simpa using hsix.ne (show (4 : Fin 6) ≠ 2 by decide),
    by simpa using hsix.ne (show (4 : Fin 6) ≠ 3 by decide)⟩

theorem nat_card_pts_ge : 7 ≤ Nat.card ↥(ptsAG (x₁ : G) A) := by
  rw [D.nat_card_pts S F]; norm_num

theorem exists_conj_triple {u v w : G}
    (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v)
    (hw : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w)
    (huv : v ≠ u ∧ v ≠ u⁻¹) (huw : w ≠ u ∧ w ≠ u⁻¹) (hvw : w ≠ v ∧ w ≠ v⁻¹) :
    ∃ k : ↥(normAG (x₁ : G) A),
      ((k : G) * u * (k : G)⁻¹ = x₁ ∨ (k : G) * u * (k : G)⁻¹ = (x₁ : G)⁻¹) ∧
      ((k : G) * v * (k : G)⁻¹ = x₂ ∨ (k : G) * v * (k : G)⁻¹ = (x₂ : G)⁻¹) ∧
      ((k : G) * w * (k : G)⁻¹ = x₃ ∨ (k : G) * w * (k : G)⁻¹ = (x₃ : G)⁻¹) := by
  obtain ⟨h20, h21, h30, h31, h32, h33⟩ := D.six_ne S
  have hx₂ : (x₂ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₂ : G) :=
    ⟨D.x₂_mem_AG S F, D.isConj_x₁_x₂ S⟩
  have hx₃ : (x₃ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₃ : G) :=
    ⟨D.x₃_mem_AG S F, (D.isConj_x₁_x₂ S).trans (isConj_x₂_x₃ D S)⟩
  have hx₁ : (x₁ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₁ : G) :=
    ⟨x_mem_preimQ A, IsConj.refl _⟩
  have hsh : SharplyFourTransitive ↥(gammaG (x₁ : G) A) ↥(ptsAG (x₁ : G) A) :=
    D.gamma_sharp S F
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hsh.exists_triple (D.nat_card_pts_ge S F)
    (ptOf_ne S hu hv huv.1 huv.2) (ptOf_ne S hu hw huw.1 huw.2)
    (ptOf_ne S hv hw hvw.1 hvw.2)
    (a' := ptOf (x₁ : G) A (x₁ : G) hx₁.1 hx₁.2) (b' := ptOf (x₁ : G) A (x₂ : G) hx₂.1 hx₂.2)
    (c' := ptOf (x₁ : G) A (x₃ : G) hx₃.1 hx₃.2)
    (ptOf_ne S hx₁ hx₂ h20 h21) (ptOf_ne S hx₁ hx₃ h30 h31)
    (ptOf_ne S hx₂ hx₃ h32 h33)
  obtain ⟨k, rfl⟩ := exists_eq_toGamma γ
  exact ⟨k, conj_eq_or_inv_of_actPerm S hu hx₁ hγ1, conj_eq_or_inv_of_actPerm S hv hx₂ hγ2,
    conj_eq_or_inv_of_actPerm S hw hx₃ hγ3⟩

theorem ncard_SG :
    {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w}.ncard = 22 := by
  classical
  let ptEl : Option (Fin 10) → G := fun i =>
    match i with
    | none => (x₁ : G)
    | some j => (D.zlift S F j : G)
  have hpt : ∀ i, D.pt S F i = zpowers (ptEl i) := by
    rintro (_ | j) <;> rfl
  have hel : ∀ i, ptEl i ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (ptEl i) := by
    rintro (_ | j)
    · exact ⟨x_mem_preimQ A, IsConj.refl _⟩
    · exact ⟨D.zlift_mem S F j, D.zlift_isConj S F j⟩
  let f : Option (Fin 10) × Bool → G := fun p => if p.2 then ptEl p.1 else (ptEl p.1)⁻¹
  have hfz : ∀ p, zpowers (f p) = D.pt S F p.1 := by
    rintro ⟨i, b⟩
    cases b
    · simp only [f, Bool.false_eq_true, ite_false, hpt, zpowers_inv]
    · simp only [f, ite_true, hpt]
  have hrange : {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} = Set.range f := by
    ext w
    rw [Set.mem_ofPred_eq, D.mem_SG_iff S F]
    constructor
    · rintro (rfl | rfl | ⟨i, rfl | rfl⟩)
      · exact ⟨(none, true), rfl⟩
      · exact ⟨(none, false), rfl⟩
      · exact ⟨(some i, true), rfl⟩
      · exact ⟨(some i, false), rfl⟩
    · rintro ⟨⟨i | j, b⟩, rfl⟩ <;> cases b
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨j, Or.inr rfl⟩)
      · exact Or.inr (Or.inr ⟨j, Or.inl rfl⟩)
  have hinj : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hz : D.pt S F i = D.pt S F j := by
      rw [← hfz (i, b), ← hfz (j, c)]
      exact congrArg zpowers h
    have hij : i = j := D.pt_injective S F hz
    subst hij
    have h3 : ptEl i ^ 3 = 1 := pow_three_of_isConj_x₁ S (hel i).2
    have hne1 : ptEl i ≠ 1 := ne_one_of_mem_SG S (hel i)
    cases b <;> cases c
    · rfl
    · exfalso
      apply hne1
      exact eq_one_of_eq_inv_of_pow_three h3 (by simpa [f] using h.symm)
    · exfalso
      apply hne1
      exact eq_one_of_eq_inv_of_pow_three h3 (by simpa [f] using h)
    · rfl
  rw [hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

theorem exists_fourth :
    ∃ w₄ : G, (w₄ ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w₄) ∧
      (w₄ ≠ x₁ ∧ w₄ ≠ (x₁ : G)⁻¹) ∧ (w₄ ≠ x₂ ∧ w₄ ≠ (x₂ : G)⁻¹) ∧
      (w₄ ≠ x₃ ∧ w₄ ≠ (x₃ : G)⁻¹) := by
  classical
  have hx₁ : (x₁ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₁ : G) :=
    ⟨x_mem_preimQ A, IsConj.refl _⟩
  have hx₂ : (x₂ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₂ : G) :=
    ⟨D.x₂_mem_AG S F, D.isConj_x₁_x₂ S⟩
  have hx₃ : (x₃ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₃ : G) :=
    ⟨D.x₃_mem_AG S F, (D.isConj_x₁_x₂ S).trans (isConj_x₂_x₃ D S)⟩
  have hlt : ({ptOf (x₁ : G) A (x₁ : G) hx₁.1 hx₁.2, ptOf (x₁ : G) A (x₂ : G) hx₂.1 hx₂.2,
      ptOf (x₁ : G) A (x₃ : G) hx₃.1 hx₃.2} : Finset ↥(ptsAG (x₁ : G) A)).card <
      Nat.card ↥(ptsAG (x₁ : G) A) := by
    rw [D.nat_card_pts S F]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  obtain ⟨ω, hω⟩ := exists_notMem _ hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨B, hB⟩ := ω
  obtain ⟨w₄, hc, hw, rfl⟩ := mem_deltaIn_iff.1 hB
  have hw4 : w₄ ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w₄ := ⟨hw, hc⟩
  refine ⟨w₄, hw4, ?_, ?_, ?_⟩
  · by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h
    · exact hω.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₁ hw4).2 (Or.inl (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
    · exact hω.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₁ hw4).2 (Or.inr (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
  · by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h
    · exact hω.2.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₂ hw4).2 (Or.inl (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
    · exact hω.2.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₂ hw4).2 (Or.inr (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
  · by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h
    · exact hω.2.2 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₃ hw4).2 (Or.inl (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
    · exact hω.2.2 (Subtype.ext (by
        have := (ptOf_eq_iff S hx₃ hw4).2 (Or.inr (not_not.1 h))
        exact (congrArg Subtype.val this).symm))

omit [Finite G] F in
theorem isConj_x₁_mul_x₂_of_signs {u v : G} (hu : u = (x₁ : G) ∨ u = (x₁ : G)⁻¹)
    (hv : v = (x₂ : G) ∨ v = (x₂ : G)⁻¹) : IsConj ((x₁ : G) * (x₂ : G)) (u * v) := by
  obtain ⟨a, b, -, -, -, ha1, ha2, -, hb1, hb2, -⟩ := D.exists_quaternion_lifts S
  have hA1 : (a : G) * (x₁ : G) * (a : G)⁻¹ = (x₁ : G)⁻¹ := by
    simpa using congrArg Subtype.val ha1
  have hA2 : (a : G) * (x₂ : G) * (a : G)⁻¹ = (x₂ : G) := by
    simpa using congrArg Subtype.val ha2
  have hB1 : (b : G) * (x₁ : G) * (b : G)⁻¹ = (x₁ : G) := by
    simpa using congrArg Subtype.val hb1
  have hB2 : (b : G) * (x₂ : G) * (b : G)⁻¹ = (x₂ : G)⁻¹ := by
    simpa using congrArg Subtype.val hb2
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact IsConj.refl _
  · refine isConj_iff.2 ⟨(b : G), ?_⟩
    have e : (b : G) * ((x₁ : G) * (x₂ : G)) * (b : G)⁻¹ =
        ((b : G) * (x₁ : G) * (b : G)⁻¹) * ((b : G) * (x₂ : G) * (b : G)⁻¹) := by group
    rw [e, hB1, hB2]
  · refine isConj_iff.2 ⟨(a : G), ?_⟩
    have e : (a : G) * ((x₁ : G) * (x₂ : G)) * (a : G)⁻¹ =
        ((a : G) * (x₁ : G) * (a : G)⁻¹) * ((a : G) * (x₂ : G) * (a : G)⁻¹) := by group
    rw [e, hA1, hA2]
  · refine isConj_iff.2 ⟨(a : G) * (b : G), ?_⟩
    have e : (a : G) * (b : G) * ((x₁ : G) * (x₂ : G)) * ((a : G) * (b : G))⁻¹ =
        (a : G) * (((b : G) * (x₁ : G) * (b : G)⁻¹) * ((b : G) * (x₂ : G) * (b : G)⁻¹)) *
          (a : G)⁻¹ := by group
    rw [e, hB1, hB2]
    have e2 : (a : G) * ((x₁ : G) * (x₂ : G)⁻¹) * (a : G)⁻¹ =
        ((a : G) * (x₁ : G) * (a : G)⁻¹) * ((a : G) * (x₂ : G) * (a : G)⁻¹)⁻¹ := by group
    rw [e2, hA1, hA2]

theorem exists_third {u v : G} (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v) :
    ∃ w : G, (w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w) ∧ (w ≠ u ∧ w ≠ u⁻¹) ∧
      (w ≠ v ∧ w ≠ v⁻¹) := by
  classical
  have hlt : ({ptOf (x₁ : G) A u hu.1 hu.2, ptOf (x₁ : G) A v hv.1 hv.2} :
      Finset ↥(ptsAG (x₁ : G) A)).card < Nat.card ↥(ptsAG (x₁ : G) A) := by
    rw [D.nat_card_pts S F]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨ω, hω⟩ := exists_notMem _ hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨B, hB⟩ := ω
  obtain ⟨w, hc, hw, rfl⟩ := mem_deltaIn_iff.1 hB
  have hw' : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w := ⟨hw, hc⟩
  refine ⟨w, hw', ?_, ?_⟩
  · by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h
    · exact hω.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hu hw').2 (Or.inl (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
    · exact hω.1 (Subtype.ext (by
        have := (ptOf_eq_iff S hu hw').2 (Or.inr (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
  · by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h
    · exact hω.2 (Subtype.ext (by
        have := (ptOf_eq_iff S hv hw').2 (Or.inl (not_not.1 h))
        exact (congrArg Subtype.val this).symm))
    · exact hω.2 (Subtype.ext (by
        have := (ptOf_eq_iff S hv hw').2 (Or.inr (not_not.1 h))
        exact (congrArg Subtype.val this).symm))

theorem isConj_x₁_mul_x₂_of_mul {u v : G} (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v) (h1 : v ≠ u) (h2 : v ≠ u⁻¹) :
    IsConj (u * v) ((x₁ : G) * (x₂ : G)) := by
  obtain ⟨w, hw, hwu, hwv⟩ := D.exists_third S F hu hv
  obtain ⟨k, hk1, hk2, -⟩ := D.exists_conj_triple S F hu hv hw ⟨h1, h2⟩ hwu hwv
  have hconj : IsConj (u * v) ((k : G) * u * (k : G)⁻¹ * ((k : G) * v * (k : G)⁻¹)) := by
    refine isConj_iff.2 ⟨(k : G), ?_⟩
    group
  have := D.isConj_x₁_mul_x₂_of_signs S hk1 hk2
  exact hconj.trans this.symm

theorem exists_conj_quad {u v w x w₄ : G}
    (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v)
    (hw : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w)
    (hx : x ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) x)
    (hw₄ : w₄ ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w₄)
    (huv : v ≠ u ∧ v ≠ u⁻¹) (huw : w ≠ u ∧ w ≠ u⁻¹) (hvw : w ≠ v ∧ w ≠ v⁻¹)
    (hux : x ≠ u ∧ x ≠ u⁻¹) (hvx : x ≠ v ∧ x ≠ v⁻¹) (hwx : x ≠ w ∧ x ≠ w⁻¹)
    (h41 : w₄ ≠ x₁ ∧ w₄ ≠ (x₁ : G)⁻¹) (h42 : w₄ ≠ x₂ ∧ w₄ ≠ (x₂ : G)⁻¹)
    (h43 : w₄ ≠ x₃ ∧ w₄ ≠ (x₃ : G)⁻¹) :
    ∃ k : ↥(normAG (x₁ : G) A),
      ((k : G) * u * (k : G)⁻¹ = x₁ ∨ (k : G) * u * (k : G)⁻¹ = (x₁ : G)⁻¹) ∧
      ((k : G) * v * (k : G)⁻¹ = x₂ ∨ (k : G) * v * (k : G)⁻¹ = (x₂ : G)⁻¹) ∧
      ((k : G) * w * (k : G)⁻¹ = x₃ ∨ (k : G) * w * (k : G)⁻¹ = (x₃ : G)⁻¹) ∧
      ((k : G) * x * (k : G)⁻¹ = w₄ ∨ (k : G) * x * (k : G)⁻¹ = w₄⁻¹) := by
  obtain ⟨h20, h21, h30, h31, h32, h33⟩ := D.six_ne S
  have hx₂ : (x₂ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₂ : G) :=
    ⟨D.x₂_mem_AG S F, D.isConj_x₁_x₂ S⟩
  have hx₃ : (x₃ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₃ : G) :=
    ⟨D.x₃_mem_AG S F, (D.isConj_x₁_x₂ S).trans (isConj_x₂_x₃ D S)⟩
  have hx₁ : (x₁ : G) ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) (x₁ : G) :=
    ⟨x_mem_preimQ A, IsConj.refl _⟩
  have hsh : SharplyFourTransitive ↥(gammaG (x₁ : G) A) ↥(ptsAG (x₁ : G) A) :=
    D.gamma_sharp S F
  obtain ⟨γ, ⟨hγ1, hγ2, hγ3, hγ4⟩, -⟩ := hsh.existsUnique_vec4
    (ptOf_ne S hu hv huv.1 huv.2) (ptOf_ne S hu hw huw.1 huw.2)
    (ptOf_ne S hu hx hux.1 hux.2) (ptOf_ne S hv hw hvw.1 hvw.2)
    (ptOf_ne S hv hx hvx.1 hvx.2) (ptOf_ne S hw hx hwx.1 hwx.2)
    (a' := ptOf (x₁ : G) A (x₁ : G) hx₁.1 hx₁.2) (b' := ptOf (x₁ : G) A (x₂ : G) hx₂.1 hx₂.2)
    (c' := ptOf (x₁ : G) A (x₃ : G) hx₃.1 hx₃.2) (d' := ptOf (x₁ : G) A w₄ hw₄.1 hw₄.2)
    (ptOf_ne S hx₁ hx₂ h20 h21) (ptOf_ne S hx₁ hx₃ h30 h31)
    (ptOf_ne S hx₁ hw₄ h41.1 h41.2) (ptOf_ne S hx₂ hx₃ h32 h33)
    (ptOf_ne S hx₂ hw₄ h42.1 h42.2) (ptOf_ne S hx₃ hw₄ h43.1 h43.2)
  obtain ⟨k, rfl⟩ := exists_eq_toGamma γ
  exact ⟨k, conj_eq_or_inv_of_actPerm S hu hx₁ hγ1, conj_eq_or_inv_of_actPerm S hv hx₂ hγ2,
    conj_eq_or_inv_of_actPerm S hw hx₃ hγ3, conj_eq_or_inv_of_actPerm S hx hw₄ hγ4⟩

end LyData

end Classes

end CFSG.Sporadic.Recognition.LyonsSims

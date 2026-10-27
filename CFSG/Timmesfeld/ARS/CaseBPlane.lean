module

public import CFSG.Timmesfeld.ARS.Sec5Sigma
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.ARS.Sec5Maximal
public import CFSG.Timmesfeld.ARS.Sec8Planes
public import CFSG.Timmesfeld.ARS.Sec8Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

structure HypB (G : Type*) [Group G] (R : Set (Subgroup G)) (A : Subgroup G) : Prop where
  hyp : Hyp G R
  mem : A ∈ R
  max : IsCoatom (Subgroup.normalizer (A : Set G))
  ne : sigmaSet R A ≠ lambdaSet R A
  notMax : ¬ IsSigmaMaximal R (centralGroup R A)

namespace HypB

variable {A : Subgroup G} (hB : HypB G R A)
include hB

theorem sec8 : Sec8 R A := ⟨hB.max, hB.ne⟩

theorem exists_isWeakTI : ∃ Δ, IsWeakTI R Δ ∧ A ∈ Δ := by
  have := hB.hyp.finite
  obtain ⟨K, -, hlt, -, hΔ⟩ := (not_isSigmaMaximal_iff hB.hyp.root hB.hyp.noIsolated
    hB.hyp.nondeg hB.mem).1 hB.notMax
  have hAK : A ≤ K :=
    (le_centralGroup ⟨hB.mem, hB.hyp.root.commuting_self hB.mem⟩).trans hlt.le
  exact ⟨_, hΔ, 1, K.one_mem, conjSub_one A⟩

end HypB

namespace CaseB

theorem eq_of_omegaSet (h : Hyp G R) : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
  fun _ hA _ hB hBA => eq_of_omegaSet_eq h hA hB hBA

section Plane

variable (h : Hyp G R)
include h

theorem card_sup_of_mem_lambdaSet {Y B : Subgroup G} (hY : Y ∈ R) (hB : B ∈ lambdaSet R Y) :
    Nat.card ↥(Y ⊔ B) = Nat.card Y ^ 2 := by
  have := h.finite
  have hR := h.root
  have hinf : Y ⊓ B = ⊥ := inf_eq_bot hR h.noIsolated hY hB.1.1 hB.1.2.1.symm
  rw [le_antisymm (card_sup_le_of_commuting hB.1.2.2) (card_mul_card_le_card_sup hinf),
    hR.card_eq hB.1.1 hY, sq]

theorem card_gen_eq_pow_three {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) {Y : Subgroup G}
    (hY : Y ∈ Δ) (h8 : Sec8 R Y) : Nat.card ↥(gen Δ) = Nat.card Y ^ 3 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hYR := hΔ.1 hY
  obtain ⟨-, -, m, hm, hcount, hm3⟩ := isWeakTI_structure h hΔ hY
  have hTI : ¬ IsTI R Δ := fun hTI => ((exists_isTI_iff h hYR).2 ⟨Δ, hTI, hY⟩) h8.1
  replace hm3 : m ≤ 3 := hm3.resolve_right hTI
  have hq : 2 ≤ Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).2 (hR.ne_bot Y hYR)
  have hΔ2 : 2 ≤ Nat.card Δ := by
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := hΔ.2.1
    rw [Nat.card_coe_set_eq]
    exact (Set.one_lt_ncard_iff (Set.toFinite Δ)).2 ⟨B₁, B₂, hB₁, hB₂, hne⟩
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    have hle : Nat.card Y ^ m ≤ Nat.card Y := by
      interval_cases m
      · simp only [pow_zero]; omega
      · simp
    have h1 : 1 ≤ Nat.card Y - 1 := by omega
    have : Nat.card Δ * (Nat.card Y - 1) ≤ 1 * (Nat.card Y - 1) := by
      rw [hcount, one_mul]; omega
    have := Nat.le_of_mul_le_mul_right this (by omega)
    omega
  have hm2' : m ≠ 2 := by
    rintro rfl
    obtain ⟨B, hB, hBY⟩ : ∃ B ∈ Δ, B ≠ Y := by
      obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := hΔ.2.1
      by_cases h1 : B₁ = Y
      · exact ⟨B₂, hB₂, fun e => hne (h1.trans e.symm)⟩
      · exact ⟨B₁, hB₁, h1⟩
    have hl : B ∈ lambdaSet R Y := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hY hB hBY.symm
    have hsup : Y ⊔ B = gen Δ := Subgroup.eq_of_le_of_card_ge (sup_le (le_gen hY) (le_gen hB))
      (by rw [hm, card_sup_of_mem_lambdaSet h hYR hl])
    obtain ⟨E, hE, hEle, hEl⟩ := exists_plane_of_sigmaSet_ne h hYR hl h8.2
    have hEV : Commuting E (gen Δ) := commuting_iff_le_centralizer.2 (gen_le fun Q hQ =>
      commuting_iff_le_centralizer.1 (hEl Q (hΔ.1 hQ) (hsup ▸ le_gen hQ)).1.2.2)
    exact hEle (hsup ▸ le_gen (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hΔ hE hEV))
  rw [hm]
  congr 1
  omega

theorem card_eq_of_sec8 {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) {Y : Subgroup G}
    (hY : Y ∈ Δ) (h8 : Sec8 R Y) : Nat.card Δ = Nat.card Y ^ 2 + Nat.card Y + 1 := by
  have := h.finite
  have hcount := Sec5.card_mul_card_sub_one h.root h.noIsolated h.nondeg (eq_of_omegaSet h) hΔ hY
  rw [card_gen_eq_pow_three h hΔ hY h8] at hcount
  have hq : 2 ≤ Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).2 (h.root.ne_bot Y (hΔ.1 hY))
  have key : Nat.card Y ^ 3 - 1 = (Nat.card Y ^ 2 + Nat.card Y + 1) * (Nat.card Y - 1) := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card Y = r + 1 := ⟨Nat.card Y - 1, by omega⟩
    rw [hr]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [key] at hcount
  exact Nat.eq_of_mul_eq_mul_right (by omega) hcount

end Plane

section Conjugates

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem exists_conjSet_ne (hΔ : IsWeakTI R Δ) (hTI : ¬ IsTI R Δ) {X : Subgroup G} (hX : X ∈ Δ) :
    ∃ g : G, conjSub X g = X ∧ conjSet Δ g ≠ Δ := by
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : G, Δ ∩ conjSet Δ g₁ ≠ ∅ ∧ Δ ∩ conjSet Δ g₁ ≠ Δ := by
    by_contra! hcon
    exact hTI ⟨hΔ.1, hΔ.2.1, hΔ.2.2.1, fun g => by
      by_cases h1 : Δ ∩ conjSet Δ g = ∅
      · exact Or.inl h1
      · exact Or.inr (hcon g (Set.nonempty_iff_ne_empty.2 h1))⟩
  obtain ⟨Y, hY, hYg⟩ := Set.nonempty_iff_ne_empty.2 hg₁.1
  have hne : conjSet Δ g₁ ≠ Δ := fun e => hg₁.2 (by rw [e, Set.inter_self])
  have hYg' : conjSub Y g₁⁻¹ ∈ Δ := (mem_conjSet).1 hYg
  obtain ⟨s, hs, hsX⟩ := Sec5.exists_mem_stabSet_conjSub_eq hR hiso hnd hΩ hΔ hX hY
  obtain ⟨t, ht, htX⟩ := Sec5.exists_mem_stabSet_conjSub_eq hR hiso hnd hΩ hΔ hX hYg'
  refine ⟨s⁻¹ * g₁ * t, ?_, fun e => hne ?_⟩
  · calc conjSub X (s⁻¹ * g₁ * t) = conjSub (conjSub (conjSub X t) g₁) s⁻¹ := by
          rw [mul_assoc, conjSub_mul, conjSub_mul]
      _ = X := by
          rw [htX, ← conjSub_mul Y g₁ g₁⁻¹, mul_inv_cancel, conjSub_one, ← hsX,
            ← conjSub_mul X s⁻¹ s, inv_mul_cancel, conjSub_one]
  · rw [conjSet_mul, conjSet_mul, mem_stabSet.1 ht] at e
    have := congrArg (fun Θ => conjSet Θ s) e
    rwa [← conjSet_mul, mul_inv_cancel, conjSet_one, mem_stabSet.1 hs] at this

theorem eq_of_mem_conjSet (hΔ : IsWeakTI R Δ) {g : G} (hne : conjSet Δ g ≠ Δ) {X Y : Subgroup G}
    (hX : X ∈ Δ) (hXg : X ∈ conjSet Δ g) (hY : Y ∈ Δ) (hYg : Y ∈ conjSet Δ g) : X = Y := by
  by_contra hXY
  exact hne (Sec5.eq_of_mem_of_mem hR hiso hnd hΩ hΔ (Sec5.isWeakTI_conjSet hR hΔ g)
    (Sec5.card_conjSet Δ g) hX hXg hY hYg hXY)

omit [Finite G] hiso hnd hΩ in
theorem exists_mem_sup_conjSub_eq_of_opposite {D B : Subgroup G} (hD : D ∈ R)
    (hDB : Opposite D B) : ∃ y ∈ D ⊔ B, conjSub D y = B := by
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD
  obtain ⟨b, hb, -, hbd⟩ := hDB.2.1 d hd hd1
  refine ⟨d * b, Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hb), ?_⟩
  rw [conjSub_mul, hbd, ← conjSub_mul, hR.mul_self D hD d hd, conjSub_one]

end Conjugates

section Axes

variable (h : Hyp G R) {Θ : Set (Subgroup G)} (hΘ : IsWeakTI R Θ) {A : Subgroup G}
  (hAΘ : A ∈ Θ) (hΘ3 : Nat.card ↥(gen Θ) = Nat.card A ^ 3)
include h hΘ hAΘ hΘ3

theorem card_axis_eq {E : Subgroup G} (hE : E ∈ lambdaSet R A) (hEΘ : E ∉ Θ) :
    Nat.card ↥(Sec5.axis Θ E) = Nat.card A ^ 2 := by
  have := h.finite
  have hq : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (h.root.ne_bot A (hΘ.1 hAΘ))
  have := Sec5.card_gen_eq h.root h.noIsolated h.nondeg (eq_of_omegaSet h) hΘ hAΘ hE hEΘ
  rw [hΘ3, pow_succ'] at this
  exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm

theorem exists_mem_le_axis_ne {E : Subgroup G} (hE : E ∈ lambdaSet R A) (hEΘ : E ∉ Θ) :
    ∃ P ∈ Θ, P ≤ Sec5.axis Θ E ∧ P ≠ A := by
  have := h.finite
  have hq : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (h.root.ne_bot A (hΘ.1 hAΘ))
  have hcard := card_axis_eq h hΘ hAΘ hΘ3 hE hEΘ
  obtain ⟨x, hx, hxA⟩ : ∃ x ∈ Sec5.axis Θ E, x ∉ A := by
    by_contra! hall
    have hle : Sec5.axis Θ E ≤ A := hall
    have := Subgroup.card_le_of_le hle
    rw [hcard] at this
    nlinarith
  have hx1 : x ≠ 1 := fun e => hxA (e ▸ A.one_mem)
  obtain ⟨P, hP, hPle, hxP⟩ := Sec5.exists_mem_le_axis h.root h.noIsolated h.nondeg
    (eq_of_omegaSet h) hΘ hAΘ hE hEΘ hx hx1
  exact ⟨P, hP, hPle, fun e => hxA (e ▸ hxP)⟩

theorem axis_eq_sup {E : Subgroup G} (hE : E ∈ lambdaSet R A) (hEΘ : E ∉ Θ) {P : Subgroup G}
    (hP : P ∈ Θ) (hPax : P ≤ Sec5.axis Θ E) (hPA : P ≠ A) : Sec5.axis Θ E = A ⊔ P := by
  have := h.finite
  have hPl : P ∈ lambdaSet R A := Sec5.mem_lambdaSet h.root h.noIsolated h.nondeg
    (eq_of_omegaSet h) hΘ hAΘ hP hPA.symm
  refine (Subgroup.eq_of_le_of_card_ge (sup_le ((Sec5.le_axis_iff hAΘ).2 hE.1.2.2) hPax) ?_).symm
  rw [card_axis_eq h hΘ hAΘ hΘ3 hE hEΘ, card_sup_of_mem_lambdaSet h (hΘ.1 hAΘ) hPl]

end Axes

section Eight

variable (h : Hyp G R) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hTI : ¬ IsTI R Δ)
  {A : Subgroup G} (hA : A ∈ Δ) (h3 : Nat.card ↥(gen Δ) = Nat.card A ^ 3)
include h hΔ hTI hA h3

theorem exists_mem_conjSet_of_mem_lambdaSet {C : Subgroup G} (hC : C ∈ lambdaSet R A) :
    ∃ g : G, conjSub A g = A ∧ C ∈ conjSet Δ g := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hAR := hΔ.1 hA
  by_cases hCΔ : C ∈ Δ
  · exact ⟨1, conjSub_one A, by rwa [conjSet_one]⟩
  have hCR : C ∈ R := hC.1.1
  obtain ⟨g₀, hg₀, hne₀⟩ := exists_conjSet_ne hR hiso hnd hΩ hΔ hTI hA
  set Δ₂ := conjSet Δ g₀ with hΔ₂def
  have hΔ₂ : IsWeakTI R Δ₂ := Sec5.isWeakTI_conjSet hR hΔ g₀
  have hAΔ₂ : A ∈ Δ₂ := hg₀ ▸ conjSub_mem_conjSet hA g₀
  have hΔ₂3 : Nat.card ↥(gen Δ₂) = Nat.card A ^ 3 := by rw [Sec5.card_gen_conjSet, h3]
  have hint : ∀ X ∈ Δ, X ∈ Δ₂ → X = A := fun X hX hX₂ =>
    eq_of_mem_conjSet hR hiso hnd hΩ hΔ hne₀ hX hX₂ hA hAΔ₂
  obtain ⟨P, hP, hPH, hPA⟩ := exists_mem_le_axis_ne h hΔ hA h3 hC hCΔ
  have hPl : P ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hA hP hPA.symm
  have hPΔ₂ : P ∉ Δ₂ := fun hP₂ => hPA (hint P hP hP₂)
  obtain ⟨D, hD, hDax, hDA⟩ := exists_mem_le_axis_ne h hΔ₂ hAΔ₂ hΔ₂3 hPl hPΔ₂
  have hDl : D ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ₂ hAΔ₂ hD hDA.symm
  have hDΔ : D ∉ Δ := fun hD' => hDA (hint D hD' hD)
  have hDP : Commuting D P := (Sec5.le_axis_iff hD).1 hDax
  have hAP : Nat.card ↥(A ⊔ P) = Nat.card A ^ 2 := card_sup_of_mem_lambdaSet h hAR hPl
  have hAH : A ≤ Sec5.axis Δ C := (Sec5.le_axis_iff hA).2 hC.1.2.2
  have hH : Sec5.axis Δ C = A ⊔ P := (Subgroup.eq_of_le_of_card_ge (sup_le hAH hPH)
    (by rw [card_axis_eq h hΔ hA h3 hC hCΔ, hAP])).symm
  have hHD : Sec5.axis Δ D = A ⊔ P := (Subgroup.eq_of_le_of_card_ge
    (sup_le ((Sec5.le_axis_iff hA).2 hDl.1.2.2) ((Sec5.le_axis_iff hP).2 hDP.symm))
    (by rw [card_axis_eq h hΔ hA h3 hDl hDΔ, hAP])).symm
  obtain ⟨Q, hQ, hQC⟩ : ∃ Q ∈ Δ, ¬ Commuting Q C := by
    by_contra! hall
    exact hCΔ (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hΔ hCR (commuting_iff_le_centralizer.2
      (gen_le fun Q hQ => commuting_iff_le_centralizer.1 (hall Q hQ).symm)))
  have hQA : Q ≠ A := fun e => hQC (e ▸ hC.1.2.2)
  have hQD : ¬ Commuting Q D := by
    intro hQD
    apply hQC
    have : Q ≤ Sec5.axis Δ C := by rw [hH, ← hHD]; exact (Sec5.le_axis_iff hQ).2 hQD
    exact (Sec5.le_axis_iff hQ).1 this
  obtain ⟨g₁, hg₁, hne₁⟩ := exists_conjSet_ne hR hiso hnd hΩ hΔ hTI hQ
  have hΔQ : IsWeakTI R (conjSet Δ g₁) := Sec5.isWeakTI_conjSet hR hΔ g₁
  have hQΔQ : Q ∈ conjSet Δ g₁ := hg₁ ▸ conjSub_mem_conjSet hQ g₁
  have hAQ : A ∉ conjSet Δ g₁ := fun hA' =>
    hQA (eq_of_mem_conjSet hR hiso hnd hΩ hΔ hne₁ hQ hQΔQ hA hA')
  have hAlQ : A ∈ lambdaSet R Q := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hQ hA hQA
  obtain ⟨B, hB, hBA, -⟩ := Sec5.exists_special hR hiso hnd hΩ hΔQ hQΔQ hAlQ hAQ
  have hBR : B ∈ R := hΔQ.1 hB
  have hBQ : B ≠ Q := fun e => hBA.not_commuting hR (e ▸ hAlQ.1.2.2)
  have hBl : B ∈ lambdaSet R Q := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔQ hQΔQ hB hBQ.symm
  have hBΔ : B ∉ Δ := fun hB' => hBQ (eq_of_mem_conjSet hR hiso hnd hΩ hΔ hne₁ hB' hB hQ hQΔQ)
  have hAB : ¬ Commuting A B := fun e => hBA.not_commuting hR e.symm
  have hCB : Opposite C B := Sec5.opposite_of_centre hR hiso hnd hΩ hΔ hA hQ hQA.symm hC hCΔ hBl
    hBΔ hAB hQC
  have hDB : Opposite D B := Sec5.opposite_of_centre hR hiso hnd hΩ hΔ hA hQ hQA.symm hDl hDΔ hBl
    hBΔ hAB hQD
  obtain ⟨y, hy, hDy⟩ := exists_mem_sup_conjSub_eq_of_opposite hR hDl.1.1 hDB
  obtain ⟨z, hz, hBz⟩ := exists_mem_sup_conjSub_eq_of_opposite hR hBR hCB.symm
  have hst : ∀ X ∈ R, Commuting X A → X ≤ stabSet Δ := fun X hX hXA =>
    Sec5.le_stabSet_of_commuting hR hΔ hX hA hXA
  have hBst : B ≤ stabSet Δ := Sec5.le_stabSet_of_commuting hR hΔ hBR hQ hBl.1.2.2.symm
  have hyst : y ∈ stabSet Δ := sup_le (hst D hDl.1.1 hDl.1.2.2.symm) hBst hy
  have hzst : z ∈ stabSet Δ := sup_le hBst (hst C hCR hC.1.2.2.symm) hz
  have hx : conjSub D (z * y) = C := by rw [conjSub_mul, hDy, hBz]
  have hxst : z * y ∈ stabSet Δ := (stabSet Δ).mul_mem hzst hyst
  have hVx : conjSub (gen Δ) (z * y) = gen Δ := by
    rw [conjSub_gen, mem_stabSet.1 hxst]
  have hAx : conjSub A (z * y) = A := by
    conv_lhs => rw [← Sec5.commutator_gen_eq hR hiso hnd hΩ hΔ hA hDl hDΔ]
    rw [conjSub, Subgroup.map_commutator, ← conjSub, ← conjSub, hVx, hx,
      Sec5.commutator_gen_eq hR hiso hnd hΩ hΔ hA hC hCΔ]
  refine ⟨z * y * g₀, ?_, ?_⟩
  · rw [conjSub_mul, hg₀, hAx]
  · rw [conjSet_mul, ← hx]
    exact conjSub_mem_conjSet hD (z * y)

end Eight

end CaseB

end CFSG.Timmesfeld.ARS

module

public import CFSG.Timmesfeld.ARS.CaseHBasic
public import CFSG.Timmesfeld.ARS.Sec5Maximal
public import CFSG.Timmesfeld.ARS.Sec5Ten

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def pointsOn (R : Set (Subgroup G)) (V : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ B ≤ V}

@[expose] def linesThrough (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {V | IsLine R V ∧ A ≤ V}

namespace CaseH

theorem ncard_mul_eq_ncard_mul {α β : Type*} {s : Set α} {t : Set β} (hs : s.Finite)
    (ht : t.Finite) (r : α → β → Prop) {m n : ℕ}
    (hm : ∀ a ∈ s, {b | b ∈ t ∧ r a b}.ncard = m) (hn : ∀ b ∈ t, {a | a ∈ s ∧ r a b}.ncard = n) :
    s.ncard * m = t.ncard * n := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs, Set.ncard_eq_toFinset_card t ht]
  refine Finset.card_mul_eq_card_mul r (fun a ha => ?_) (fun b hb => ?_)
  · have e : ((ht.toFinset.bipartiteAbove r a : Finset β) : Set β) = {b | b ∈ t ∧ r a b} := by
      ext b
      simp [Finset.bipartiteAbove]
    rw [← Set.ncard_coe_finset, e]
    exact hm a ((Set.Finite.mem_toFinset hs).1 ha)
  · have e : ((hs.toFinset.bipartiteBelow r b : Finset α) : Set α) = {a | a ∈ s ∧ r a b} := by
      ext a
      simp [Finset.bipartiteBelow]
    rw [← Set.ncard_coe_finset, e]
    exact hn b ((Set.Finite.mem_toFinset ht).1 hb)

theorem IsLine.conjSub (hR : IsRootClass R) {V : Subgroup G} (hV : IsLine R V) (g : G) :
    IsLine R (conjSub V g) := by
  obtain ⟨A, hA, D, hD, rfl⟩ := hV
  exact ⟨_, hR.conjSub_mem hA g, _, conjSub_mem_lambdaSet hR hD g, Subgroup.map_sup _ _ _⟩

theorem conjSet_pointsOn (hR : IsRootClass R) (V : Subgroup G) (g : G) :
    conjSet (pointsOn R V) g = pointsOn R (conjSub V g) := by
  ext E
  rw [mem_conjSet]
  constructor
  · rintro ⟨hE, hEV⟩
    refine ⟨?_, ?_⟩
    · have := hR.conjSub_mem hE g
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
    · have : conjSub (conjSub E g⁻¹) g ≤ conjSub V g := Subgroup.map_mono hEV
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  · rintro ⟨hE, hEV⟩
    refine ⟨hR.conjSub_mem hE g⁻¹, ?_⟩
    have : conjSub E g⁻¹ ≤ conjSub (conjSub V g) g⁻¹ := Subgroup.map_mono hEV
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this

theorem conjSub_injective (g : G) : Function.Injective fun B : Subgroup G => conjSub B g :=
  Subgroup.map_injective (MulAut.conj g).injective

theorem ncard_lambdaSet_conjSub (hR : IsRootClass R) (A : Subgroup G) (g : G) :
    (lambdaSet R (conjSub A g)).ncard = (lambdaSet R A).ncard := by
  rw [← Set.ncard_image_of_injective (lambdaSet R A) (conjSub_injective g)]
  congr 1
  ext C
  constructor
  · intro hC
    refine ⟨conjSub C g⁻¹, ?_, ?_⟩
    · have := conjSub_mem_lambdaSet hR hC g⁻¹
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    · change conjSub (conjSub C g⁻¹) g = C
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  · rintro ⟨B, hB, rfl⟩
    exact conjSub_mem_lambdaSet hR hB g

theorem ncard_lambdaSet_eq (hR : IsRootClass R) {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) :
    (lambdaSet R B).ncard = (lambdaSet R A).ncard := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
  exact ncard_lambdaSet_conjSub hR A g

section Count

variable (h : Hyp G R)
include h

theorem mem_linesThrough_iff {A V : Subgroup G} (hA : A ∈ R) :
    V ∈ linesThrough R A ↔ ∃ D ∈ lambdaSet R A, V = A ⊔ D := by
  have := h.finite
  constructor
  · rintro ⟨⟨A', hA', D', hD', rfl⟩, hAV⟩
    by_cases hAA' : A = A'
    · subst hAA'
      exact ⟨D', hD', rfl⟩
    · obtain ⟨hl, hsup⟩ := mem_lambdaSet_of_le_sup h.root h.noIsolated hA' hD' hA hAV hA'
        le_sup_left hAA'
      exact ⟨A', hl, hsup.symm⟩
  · rintro ⟨D, hD, rfl⟩
    exact ⟨⟨A, hA, D, hD, rfl⟩, le_sup_left⟩

theorem ncard_pointsOn {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A) :
    (pointsOn R (A ⊔ D)).ncard = Nat.card A + 1 := by
  have := h.finite
  exact ncard_setOf_mem_le_sup h.root h.noIsolated hA hD

theorem lambdaSet_inter_pointsOn {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A) :
    lambdaSet R D ∩ pointsOn R (A ⊔ D) = pointsOn R (A ⊔ D) \ {D} := by
  have := h.finite
  ext X
  constructor
  · rintro ⟨hX, hXV⟩
    exact ⟨hXV, hX.1.2.1⟩
  · rintro ⟨⟨hXR, hXV⟩, hXD⟩
    exact ⟨(mem_lambdaSet_of_le_sup h.root h.noIsolated hA hD hD.1.1 le_sup_right hXR hXV
      (Ne.symm hXD)).1, hXR, hXV⟩

theorem ncard_lambdaSet_diff_pointsOn {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) :
    (lambdaSet R D \ pointsOn R (A ⊔ D)).ncard = (lambdaSet R A).ncard - Nat.card A := by
  have := h.finite
  have hDR : D ∈ R := hD.1.1
  have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (lambdaSet R D) (pointsOn R (A ⊔ D))
  have hD' : D ∈ pointsOn R (A ⊔ D) := ⟨hDR, le_sup_right⟩
  rw [lambdaSet_inter_pointsOn h hA hD, Set.ncard_sdiff_singleton_of_mem hD',
    ncard_pointsOn h hA hD, ncard_lambdaSet_eq h.root hA hDR] at h1
  omega

theorem ncard_lambdaSet_diff_pointsOn' {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) :
    (lambdaSet R A \ pointsOn R (A ⊔ D)).ncard = (lambdaSet R A).ncard - Nat.card A := by
  have h1 := ncard_lambdaSet_diff_pointsOn h hD.1.1 (mem_lambdaSet_comm hA hD)
  rwa [sup_comm, ncard_lambdaSet_eq h.root hA hD.1.1, h.root.card_eq hD.1.1 hA] at h1

theorem ncard_lambdaSet {A : Subgroup G} (hA : A ∈ R) :
    (lambdaSet R A).ncard = (linesThrough R A).ncard * Nat.card A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have h1 := ncard_mul_eq_ncard_mul (s := lambdaSet R A) (t := linesThrough R A)
    (Set.toFinite _) (Set.toFinite _) (fun D V => D ≤ V) (m := 1) (n := Nat.card A) ?_ ?_
  · simpa using h1
  · intro D hD
    rw [Set.ncard_eq_one]
    refine ⟨A ⊔ D, ?_⟩
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hV, hDV⟩
      obtain ⟨D', hD', rfl⟩ := (mem_linesThrough_iff h hA).1 hV
      exact (eq_of_le_of_le h hA hD hA hD' hA hD.1.1 hD.1.2.1.symm le_sup_left le_sup_right
        le_sup_left hDV).symm
    · rintro rfl
      exact ⟨(mem_linesThrough_iff h hA).2 ⟨D, hD, rfl⟩, le_sup_right⟩
  · intro V hV
    obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hA).1 hV
    have e : {D' | D' ∈ lambdaSet R A ∧ D' ≤ A ⊔ D} = pointsOn R (A ⊔ D) \ {A} := by
      ext D'
      constructor
      · rintro ⟨hD', hle⟩
        exact ⟨⟨hD'.1.1, hle⟩, hD'.1.2.1⟩
      · rintro ⟨⟨hD'R, hle⟩, hne⟩
        exact ⟨(mem_lambdaSet_of_le_sup hR hiso hA hD hA le_sup_left hD'R hle (Ne.symm hne)).1,
          hle⟩
    have hA' : A ∈ pointsOn R (A ⊔ D) := ⟨hA, le_sup_left⟩
    rw [e, Set.ncard_sdiff_singleton_of_mem hA', ncard_pointsOn h hA hD, Nat.add_sub_cancel]

theorem ncard_linesThrough_eq {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) :
    (linesThrough R B).ncard = (linesThrough R A).ncard := by
  have := h.finite
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 := ncard_lambdaSet_eq h.root hA hB
  rw [ncard_lambdaSet h hA, ncard_lambdaSet h hB, h.root.card_eq hB hA] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem ncard_psiSet (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R) :
    (psiSet R A).ncard = (lambdaSet R A).ncard * ((lambdaSet R A).ncard - Nat.card A) := by
  have := h.finite
  have hR := h.root
  have h1 := ncard_mul_eq_ncard_mul (s := psiSet R A) (t := lambdaSet R A)
    (Set.toFinite _) (Set.toFinite _) (fun C D => C ∈ lambdaSet R D) (m := 1)
    (n := (lambdaSet R A).ncard - Nat.card A) ?_ ?_
  · simpa using h1
  · intro C hC
    rw [Set.ncard_eq_one]
    refine ⟨⁅A, C⁆, ?_⟩
    ext D
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    obtain ⟨hl1, hl2⟩ := commutator_mem_lambdaSet h hA hC.1 hC.2
    constructor
    · rintro ⟨hDA, hCD⟩
      exact eq_commutator h hA hC.1 hC.2 hDA (mem_lambdaSet_comm hDA.1.1 hCD)
    · rintro rfl
      exact ⟨hl1, mem_lambdaSet_comm hC.1 hl2⟩
  · intro D hD
    rw [← ncard_lambdaSet_diff_pointsOn h hA hD]
    congr 1
    ext C
    constructor
    · rintro ⟨hC, hCD⟩
      refine ⟨hCD, fun hCV => Special.not_commuting hR hC.2 ?_⟩
      exact (commuting_sup_self hR hA hD).mono le_sup_left hCV.2
    · rintro ⟨hCD, hCV⟩
      have hCR : C ∈ R := hCD.1.1
      have hCA : C ∉ lambdaSet R A := fun hCA => hCV ⟨hCR, le_line h hH hA hD hA le_sup_left
        hD.1.1 le_sup_right hD.1.2.1.symm hCR hCA.1.2.2.symm hCD.1.2.2.symm⟩
      have hne : C ≠ A := fun e => hCV ⟨hCR, e ▸ le_sup_left⟩
      exact ⟨⟨hCR, (special_of_mem_lambdaSet h hH hA hD hCD hCA hne).1⟩, hCD⟩

theorem setOf_omegaSet_lambdaSet (hH : SigmaEqLambda R) {A C : Subgroup G} (hA : A ∈ R)
    (hC : C ∈ psiSet R A) :
    {B | B ∈ omegaSet R A ∧ C ∈ lambdaSet R B} =
      lambdaSet R C \ pointsOn R (C ⊔ ⁅A, C⁆) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hCR : C ∈ R := hC.1
  obtain ⟨hZA, hZC⟩ := commutator_mem_lambdaSet h hA hCR hC.2
  have hZR : ⁅A, C⁆ ∈ R := hZA.1.1
  ext B
  constructor
  · rintro ⟨hB, hCB⟩
    have hBC : B ∈ lambdaSet R C := mem_lambdaSet_comm hB.1 hCB
    refine ⟨hBC, fun hBV => ?_⟩
    have hBZ : B ≠ ⁅A, C⁆ := fun e => hB.2.not_commuting (hR.ne_bot A hA) (e ▸ hZA.1.2.2)
    have hBl := (mem_lambdaSet_of_le_sup hR hiso hCR hZC hZR le_sup_right hB.1 hBV.2
      (Ne.symm hBZ)).1
    exact notMem_lambdaSet_of_opposite h hA hB.2 hZA (mem_lambdaSet_comm hZR hBl)
  · rintro ⟨hBC, hBV⟩
    have hBR : B ∈ R := hBC.1.1
    have hCB : C ∈ lambdaSet R B := mem_lambdaSet_comm hCR hBC
    refine ⟨⟨hBR, ?_⟩, hCB⟩
    have hBA : B ≠ A := fun e => Special.not_commuting hR hC.2 (e ▸ hBC.1.2.2.symm)
    have hBZ : ⁅A, C⁆ ≠ B := fun e => hBV ⟨hBR, e ▸ le_sup_right⟩
    have hBnl : B ∉ lambdaSet R A := fun hBA' =>
      false_of_quadrangle h hH hA hBA' hCB hZC (mem_lambdaSet_comm hA hZA)
        (fun hCA => Special.not_commuting hR hC.2 hCA.1.2.2) (fun e => Special.not_commuting hR
          hC.2 (by rw [e]; exact hR.commuting_self hA)) hBZ
    rcases hR.rel A hA B hBR hBA.symm with hc | hop | hs
    · exact absurd (mem_lambdaSet_of_commuting hH hA hBR hBA hc) hBnl
    · exact hop
    · exfalso
      have heq := commutator_eq_of_mem_psiSet h hH hA hC ⟨hBR, hs⟩ hBC
      obtain ⟨-, hZB⟩ := commutator_mem_lambdaSet h hA hBR hs
      rw [← heq] at hZB
      exact hBV ⟨hBR, le_line h hH hCR hZC hCR le_sup_left hZR le_sup_right hZC.1.2.1.symm
        hBR hCB.1.2.2 hZB.1.2.2⟩

theorem ncard_omegaSet_mul (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R) :
    (omegaSet R A).ncard * (linesThrough R A).ncard =
      (psiSet R A).ncard * ((lambdaSet R A).ncard - Nat.card A) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  refine ncard_mul_eq_ncard_mul (Set.toFinite _) (Set.toFinite _)
    (fun B C => C ∈ lambdaSet R B) (fun B hB => ?_) (fun C hC => ?_)
  ·
    have hBR : B ∈ R := hB.1
    have hop : Opposite B A := hB.2.symm
    rw [← ncard_linesThrough_eq h hA hBR]
    have h1 := ncard_mul_eq_ncard_mul (s := {C | C ∈ psiSet R A ∧ C ∈ lambdaSet R B})
      (t := linesThrough R B) (Set.toFinite _) (Set.toFinite _) (fun C V => C ≤ V) (m := 1)
      (n := 1) ?_ ?_
    · simpa using h1
    · rintro C ⟨-, hCB⟩
      rw [Set.ncard_eq_one]
      refine ⟨B ⊔ C, ?_⟩
      ext V
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hV, hCV⟩
        obtain ⟨D', hD', rfl⟩ := (mem_linesThrough_iff h hBR).1 hV
        exact (eq_of_le_of_le h hBR hCB hBR hD' hBR hCB.1.1 hCB.1.2.1.symm le_sup_left
          le_sup_right le_sup_left hCV).symm
      · rintro rfl
        exact ⟨(mem_linesThrough_iff h hBR).2 ⟨C, hCB, rfl⟩, le_sup_right⟩
    · intro V hV
      obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hBR).1 hV
      obtain ⟨P, ⟨hPR, hPV, hPψ⟩, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hBR hA hop hD
      rw [Set.ncard_eq_one]
      refine ⟨P, ?_⟩
      ext C
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hCψ, -⟩, hCV⟩
        exact huniq C ⟨hCψ.1, hCV, hCψ⟩
      · rintro rfl
        have hPB : C ≠ B := fun e => Special.not_opposite hR hA hPψ.2 (e ▸ hop.symm)
        exact ⟨⟨hPψ, (mem_lambdaSet_of_le_sup hR hiso hBR hD hBR le_sup_left hPR hPV
          (Ne.symm hPB)).1⟩, hPV⟩
  ·
    have hZC := (commutator_mem_lambdaSet h hA hC.1 hC.2).2
    rw [setOf_omegaSet_lambdaSet h hH hA hC, ncard_lambdaSet_diff_pointsOn' h hC.1 hZC,
      ncard_lambdaSet_eq hR hA hC.1, hR.card_eq hC.1 hA]

theorem ncard_eq_add (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R) :
    R.ncard = 1 + (lambdaSet R A).ncard + (psiSet R A).ncard + (omegaSet R A).ncard := by
  have := h.finite
  have hR := h.root
  have hsplit : R = insert A (lambdaSet R A ∪ (psiSet R A ∪ omegaSet R A)) := by
    ext B
    constructor
    · intro hB
      by_cases hBA : B = A
      · exact Or.inl hBA
      right
      rcases hR.rel A hA B hB (Ne.symm hBA) with hc | hop | hs
      · exact Or.inl (mem_lambdaSet_of_commuting hH hA hB hBA hc)
      · exact Or.inr (Or.inr ⟨hB, hop⟩)
      · exact Or.inr (Or.inl ⟨hB, hs⟩)
    · rintro (rfl | hB | hB | hB)
      · exact hA
      · exact hB.1.1
      · exact hB.1
      · exact hB.1
  have hA1 : A ∉ lambdaSet R A ∪ (psiSet R A ∪ omegaSet R A) := by
    rintro (hl | hs | hop)
    · exact hl.1.2.1 rfl
    · exact Special.not_commuting hR hs.2 (hR.commuting_self hA)
    · exact hop.2.1 rfl
  have hd1 : Disjoint (lambdaSet R A) (psiSet R A ∪ omegaSet R A) := by
    rw [Set.disjoint_left]
    rintro B hl (hs | hop)
    · exact Special.not_commuting hR hs.2 hl.1.2.2
    · exact hop.2.not_commuting (hR.ne_bot A hA) hl.1.2.2
  have hd2 : Disjoint (psiSet R A) (omegaSet R A) := by
    rw [Set.disjoint_left]
    rintro B hs hop
    exact Special.not_opposite hR hA hs.2 hop.2
  conv_lhs => rw [hsplit]
  rw [Set.ncard_insert_of_notMem hA1 (Set.toFinite _),
    Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _)]
  ring

theorem ncard_eq (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R) {q L : ℕ}
    (hq : Nat.card A = q) (hL : (linesThrough R A).ncard = L) :
    R.ncard = 1 + L * q + L * (L - 1) * q ^ 2 + (L - 1) ^ 2 * q ^ 3 := by
  have := h.finite
  have hΛ := ncard_lambdaSet h hA
  have hΨ := ncard_psiSet h hH hA
  have hΩ := ncard_omegaSet_mul h hH hA
  rw [hL, hq] at hΛ
  rw [hΛ, hq] at hΨ
  rw [hL, hΨ, hΛ, hq] at hΩ
  have hL1 : 1 ≤ L := by
    rw [← hL, Nat.one_le_iff_ne_zero]
    intro h0
    have := ncard_lambdaSet h hA
    rw [h0, zero_mul, Set.ncard_eq_zero (Set.toFinite _)] at this
    exact (lambdaSet_nonempty h.root h.noIsolated h.nondeg hA).ne_empty this
  have hsub : L * q - q = (L - 1) * q := (Nat.sub_one_mul L q).symm
  rw [hsub] at hΩ hΨ
  have hΩ' : (omegaSet R A).ncard = (L - 1) ^ 2 * q ^ 3 := by
    have hLpos : 0 < L := hL1
    refine Nat.eq_of_mul_eq_mul_right hLpos ?_
    rw [hΩ]
    ring
  rw [ncard_eq_add h hH hA, hΛ, hΨ, hΩ']
  ring

theorem three_le_ncard_linesThrough (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R)
    (hmax : IsCoatom (Subgroup.normalizer (A : Set G))) : 3 ≤ (linesThrough R A).ncard := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun A hA B hB e => eq_of_omegaSet_eq h hA hB e
  obtain ⟨D, hD⟩ := lambdaSet_nonempty hR hiso h.nondeg hA
  have hΔ : IsWeakTI R (pointsOn R (A ⊔ D)) := isWeakTI_line h hH hA hD
  have hnot : ¬ IsTI R (pointsOn R (A ⊔ D)) := fun hTI =>
    (exists_isTI_iff h hA).2 ⟨_, hTI, ⟨hA, le_sup_left⟩⟩ hmax
  have hthree : ¬ ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet (pointsOn R (A ⊔ D)) g₁ →
      X ∈ conjSet (pointsOn R (A ⊔ D)) g₂ → X ∈ conjSet (pointsOn R (A ⊔ D)) g₃ →
      conjSet (pointsOn R (A ⊔ D)) g₁ = conjSet (pointsOn R (A ⊔ D)) g₂ ∨
        conjSet (pointsOn R (A ⊔ D)) g₁ = conjSet (pointsOn R (A ⊔ D)) g₃ ∨
          conjSet (pointsOn R (A ⊔ D)) g₂ = conjSet (pointsOn R (A ⊔ D)) g₃ :=
    fun h2 => hnot (Sec5.isTI_of_atMostTwo hR hiso h.nondeg hΩ hΔ h2)
  push Not at hthree
  obtain ⟨X, g₁, g₂, g₃, h1, h2, h3, h12, h13, h23⟩ := hthree
  simp only [conjSet_pointsOn hR] at h1 h2 h3 h12 h13 h23
  have hX : X ∈ R := h1.1
  have hline : IsLine R (A ⊔ D) := ⟨A, hA, D, hD, rfl⟩
  have hsub : {conjSub (A ⊔ D) g₁, conjSub (A ⊔ D) g₂, conjSub (A ⊔ D) g₃} ⊆
      linesThrough R X := by
    rintro V (rfl | rfl | rfl)
    · exact ⟨IsLine.conjSub hR hline g₁, h1.2⟩
    · exact ⟨IsLine.conjSub hR hline g₂, h2.2⟩
    · exact ⟨IsLine.conjSub hR hline g₃, h3.2⟩
  have hcard : ({conjSub (A ⊔ D) g₁, conjSub (A ⊔ D) g₂, conjSub (A ⊔ D) g₃} :
      Set (Subgroup G)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, fun e => h12 (by rw [e]), fun e => h13 (by rw [e]),
      fun e => h23 (by rw [e]), rfl⟩
  rw [← ncard_linesThrough_eq h hA hX, ← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Count

end CaseH

end CFSG.Timmesfeld.ARS

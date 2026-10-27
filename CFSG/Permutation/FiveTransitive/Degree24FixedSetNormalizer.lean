module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

theorem five_point_stabilizer_fixed_points_card_eq_five_six_or_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHneOne :
      Nat.card (fixingSubgroup P s) ≠ 1) :
    let f :=
      Nat.card
        (MulAction.fixedPoints
          (fixingSubgroup P s) X)
    f = 5 ∨ f = 6 ∨ f = 7 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let F : Set X := MulAction.fixedPoints H X
  let f := Nat.card F
  change f = 5 ∨ f = 6 ∨ f = 7
  have hfCases :
      f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8 ∨ f = 11 := by
    simpa only [H, F, f] using
      five_point_stabilizer_fixed_points_card_cases
        X P hcard h5 s hs hHneOne
  by_cases hfGood : f = 5 ∨ f = 6 ∨ f = 7
  · exact hfGood
  · exfalso
    have hfBad : f = 8 ∨ f = 11 := by
      rcases hfCases with hfFive | hfSix | hfSeven |
          hfEight | hfEleven
      · exact (hfGood (Or.inl hfFive)).elim
      · exact (hfGood (Or.inr (Or.inl hfSix))).elim
      · exact (hfGood (Or.inr (Or.inr hfSeven))).elim
      · exact Or.inl hfEight
      · exact Or.inr hfEleven
    let N : Subgroup P := Subgroup.normalizer H
    let fixedSmul : SMul N F := {
      smul := fun n x =>
        ⟨(n : P) • x.1, by
          rw [MulAction.mem_fixedPoints]
          intro h
          have hconj :
              (n : P)⁻¹ * (h : P) * (n : P) ∈ H := by
            exact
              (Subgroup.mem_normalizer_iff''.mp n.prop
                (h : P)).mp h.prop
          let h' : H :=
            ⟨(n : P)⁻¹ * (h : P) * (n : P), hconj⟩
          have hcommute :
              (h : P) * (n : P) =
                (n : P) * (h' : P) := by
            change
              (h : P) * (n : P) =
                (n : P) *
                  ((n : P)⁻¹ * (h : P) * (n : P))
            simp [mul_assoc]
          calc
            (h : P) • ((n : P) • x.1) =
                ((h : P) * (n : P)) • x.1 :=
              (mul_smul (h : P) (n : P) x.1).symm
            _ = ((n : P) * (h' : P)) • x.1 :=
              congrArg (fun q : P => q • x.1) hcommute
            _ = (n : P) • ((h' : P) • x.1) :=
              mul_smul (n : P) (h' : P) x.1
            _ = (n : P) • x.1 :=
              congrArg (fun y : X => (n : P) • y)
                (MulAction.mem_fixedPoints.mp x.2 h')⟩ }
    letI : SMul N F := fixedSmul
    letI : MulAction N F :=
      Subtype.coe_injective.mulAction
        Subtype.val (fun _ _ => rfl)
    let φ : N →* Equiv.Perm F :=
      MulAction.toPermHom N F
    let R : Subgroup (Equiv.Perm F) := φ.range
    have hR5 :
        ∀ a b : Fin 5 → F,
          Function.Injective a →
          Function.Injective b →
          ∃ q : R, ∀ i, q • a i = b i := by
      intro a b ha hb
      let ea : Fin 5 ↪ X := {
        toFun := fun i => (a i).1
        inj' := fun i j hij =>
          ha (Subtype.ext hij) }
      let eb : Fin 5 ↪ X := {
        toFun := fun i => (b i).1
        inj' := fun i j hij =>
          hb (Subtype.ext hij) }
      have hea : Set.range ea ⊆ F := by
        rintro _ ⟨i, rfl⟩
        exact (a i).2
      have heb : Set.range eb ⊆ F := by
        rintro _ ⟨i, rfl⟩
        exact (b i).2
      obtain ⟨q, hq⟩ :=
        h5 ea eb ea.injective eb.injective
      have hfixA :
          fixingSubgroup P (Set.range ea) = H := by
        simpa only [H, F] using
          fixingSubgroup_eq_of_range_subset_fixedPoints
            X P h5 s hs ea hea
      have hfixB :
          fixingSubgroup P (Set.range eb) = H := by
        simpa only [H, F] using
          fixingSubgroup_eq_of_range_subset_fixedPoints
            X P h5 s hs eb heb
      have hqEmbedding : q • ea = eb := by
        ext i
        exact hq i
      have hqRange :
          q • Set.range ea = Set.range eb := by
        rw [Degree24.smul_range_fiveEmbedding,
          hqEmbedding]
      have hqNormalizer :
          q ∈ Subgroup.normalizer H := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hconj :=
          SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
            (Set.range ea) q
        rw [hqRange, hfixA, hfixB] at hconj
        exact hconj.symm
      let qN : N := ⟨q, hqNormalizer⟩
      let qR : R :=
        ⟨φ qN, ⟨qN, rfl⟩⟩
      refine ⟨qR, ?_⟩
      intro i
      apply Subtype.ext
      change q • (a i).1 = (b i).1
      exact hq i
    have hR5' :
        MulAction.IsMultiplyPretransitive R F 5 := by
      rw [MulAction.isMultiplyPretransitive_iff]
      intro a b
      obtain ⟨q, hq⟩ :=
        hR5 a b a.injective b.injective
      refine ⟨q, ?_⟩
      ext i
      simpa [Function.Embedding.smul_apply] using
        congrArg Subtype.val (hq i)
    have hfFiveLe : 5 ≤ f := by
      rcases hfBad with hfEight | hfEleven <;> omega
    have heNonempty : Nonempty (Fin 5 ↪ F) := by
      apply Fintype.card_pos_iff.mp
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin,
        ← Nat.card_eq_fintype_card]
      rw [Nat.descFactorial_pos]
      exact hfFiveLe
    let e : Fin 5 ↪ F := Classical.choice heNonempty
    let t : Set F := Set.range e
    have ht : t.ncard = 5 := by
      rw [Set.ncard_range_of_injective e.injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    let K : Subgroup R := fixingSubgroup R t
    have hKbot : K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro k hk
      obtain ⟨n, hn⟩ := k.prop
      have hnFix (i : Fin 5) :
          n • e i = e i := by
        have hkFix :=
          (mem_fixingSubgroup_iff R).mp hk
            (e i) ⟨i, rfl⟩
        change (k : Equiv.Perm F) (e i) = e i at hkFix
        rw [← hn] at hkFix
        exact hkFix
      let eX : Fin 5 ↪ X := {
        toFun := fun i => (e i).1
        inj' := fun i j hij =>
          e.injective (Subtype.ext hij) }
      have heX : Set.range eX ⊆ F := by
        rintro _ ⟨i, rfl⟩
        exact (e i).2
      have hfixE :
          fixingSubgroup P (Set.range eX) = H := by
        simpa only [H, F] using
          fixingSubgroup_eq_of_range_subset_fixedPoints
            X P h5 s hs eX heX
      have hnFixX (i : Fin 5) :
          (n : P) • eX i = eX i := by
        exact congrArg Subtype.val (hnFix i)
      have hnFixing :
          (n : P) ∈
            fixingSubgroup P (Set.range eX) := by
        rw [mem_fixingSubgroup_iff]
        rintro _ ⟨i, rfl⟩
        exact hnFixX i
      have hnH : (n : P) ∈ H := by
        rw [← hfixE]
        exact hnFixing
      have hφn : φ n = 1 := by
        ext x
        change (n : P) • x.1 = x.1
        exact
          MulAction.mem_fixedPoints.mp x.2
            ⟨(n : P), hnH⟩
      apply Subtype.ext
      change (k : Equiv.Perm F) = 1
      rw [← hn, hφn]
    have hindex :=
      hR5'.index_of_fixingSubgroup_mul ht
    change
      K.index * (Nat.card F - 5).factorial =
        (Nat.card F).factorial at hindex
    rw [hKbot] at hindex
    rcases hfBad with hfEight' | hfEleven'
    · have hRcardEight : Nat.card R = 6720 := by
        rw [show Nat.card F = 8 by
          simpa only [f] using hfEight'] at hindex
        norm_num at hindex
        rw [Nat.card_eq_fintype_card]
        omega
      have hFtype : Fintype.card F = 8 := by
        rw [← Nat.card_eq_fintype_card]
        simpa only [f] using hfEight'
      have hRtype : Fintype.card R = 6720 := by
        rw [← Nat.card_eq_fintype_card]
        exact hRcardEight
      have hclass :=
        Helpers.classification_of_five_transitive_of_card_le_eleven
          R F (by omega) (by omega) hR5
      rcases hclass with hSym | hAlt
      · rw [hFtype] at hSym
        norm_num at hSym
        omega
      · rw [hFtype] at hAlt
        norm_num at hAlt
        omega
    · have hRcardEleven : Nat.card R = 55440 := by
        rw [show Nat.card F = 11 by
          simpa only [f] using hfEleven'] at hindex
        norm_num at hindex
        rw [Nat.card_eq_fintype_card]
        omega
      have hFtype : Fintype.card F = 11 := by
        rw [← Nat.card_eq_fintype_card]
        simpa only [f] using hfEleven'
      have hRtype : Fintype.card R = 55440 := by
        rw [← Nat.card_eq_fintype_card]
        exact hRcardEleven
      have hclass :=
        Helpers.classification_of_five_transitive_of_card_le_eleven
          R F (by omega) (by omega) hR5
      rcases hclass with hSym | hAlt
      · rw [hFtype] at hSym
        norm_num at hSym
        omega
      · rw [hFtype] at hAlt
        norm_num at hAlt
        omega
end FiveTransitive.Degree24

end CFSG

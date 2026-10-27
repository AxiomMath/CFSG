module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoDoubleCount

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private abbrev FiveStabilizerConjugates
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (H : Subgroup P) :=
  MulAction.orbit (ConjAct P) H

private abbrev FiveStabilizerConjugateFixesEmbedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (H : Subgroup P)
    (e : Fin 5 ↪ X) :=
  {U : FiveStabilizerConjugates X P H //
    (U.1 : Subgroup P) ≤
      fixingSubgroup P (Set.range e)}

private noncomputable def fixedPointsConjugateEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (H : Subgroup P) (g : ConjAct P) :
    MulAction.fixedPoints H X ≃
      MulAction.fixedPoints (g • H : Subgroup P) X where
  toFun x := ⟨ConjAct.ofConjAct g • x.1, by
    rw [MulAction.mem_fixedPoints]
    intro u
    obtain ⟨h, hh, hu⟩ := u.prop
    change
      (u : P) • (ConjAct.ofConjAct g • x.1) =
        ConjAct.ofConjAct g • x.1
    rw [← hu]
    have hhfix := x.2 ⟨h, hh⟩
    change h • x.1 = x.1 at hhfix
    change
      (ConjAct.ofConjAct g *
          h * (ConjAct.ofConjAct g)⁻¹) •
          (ConjAct.ofConjAct g • x.1) =
        ConjAct.ofConjAct g • x.1
    rw [mul_smul, mul_smul, inv_smul_smul,
      hhfix]⟩
  invFun x := ⟨(ConjAct.ofConjAct g)⁻¹ • x.1, by
    rw [MulAction.mem_fixedPoints]
    intro h
    have hx :=
      x.2
        ⟨ConjAct.ofConjAct g * h *
            (ConjAct.ofConjAct g)⁻¹,
          ⟨h, h.prop, rfl⟩⟩
    change
      (ConjAct.ofConjAct g * h *
          (ConjAct.ofConjAct g)⁻¹) • x.1 =
        x.1 at hx
    have hx' :=
      congrArg
        (fun y : X =>
          (ConjAct.ofConjAct g)⁻¹ • y) hx
    change
      (h : P) • (ConjAct.ofConjAct g)⁻¹ • x.1 =
        (ConjAct.ofConjAct g)⁻¹ • x.1
    simpa [mul_smul] using hx'⟩
  left_inv x := by
    apply Subtype.ext
    exact inv_smul_smul (ConjAct.ofConjAct g) x.1
  right_inv x := by
    apply Subtype.ext
    exact smul_inv_smul (ConjAct.ofConjAct g) x.1

private noncomputable def fiveStabilizerEmbeddingIncidenceEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (H : Subgroup P) :
    (Σ e : Fin 5 ↪ X,
        FiveStabilizerConjugateFixesEmbedding X P H e) ≃
      (Σ U : FiveStabilizerConjugates X P H,
        MulAction.fixedPoints U.1 (Fin 5 ↪ X)) where
  toFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        rw [MulAction.mem_fixedPoints]
        intro u
        apply Function.Embedding.ext
        intro i
        have hu := z.2.2 u.prop
        rw [mem_fixingSubgroup_iff] at hu
        exact hu (z.1 i) ⟨i, rfl⟩⟩⟩
  invFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        intro u hu
        rw [mem_fixingSubgroup_iff]
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        have hfixed := z.2.2 ⟨u, hu⟩
        exact congrArg
          (fun e : Fin 5 ↪ X => e i) hfixed⟩⟩
  left_inv z := by
    rcases z with ⟨e, U, hU⟩
    rfl
  right_inv z := by
    rcases z with ⟨U, e, he⟩
    rfl

theorem fixingSubgroup_eq_of_range_subset_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (e : Fin 5 ↪ X)
    (he :
      Set.range e ⊆
        MulAction.fixedPoints
          (fixingSubgroup P s) X) :
    fixingSubgroup P (Set.range e) =
      fixingSubgroup P s := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e₀ : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have he₀Range : Set.range e₀ = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q, hq⟩ := hP5.exists_smul_eq e₀ e
  have hrange :
      q • Set.range e₀ = Set.range e := by
    rw [Degree24.smul_range_fiveEmbedding]
    exact congrArg
      (fun z : Fin 5 ↪ X => Set.range z) hq
  let ψ :
      fixingSubgroup P (Set.range e₀) ≃*
        fixingSubgroup P (Set.range e) :=
    fixingSubgroupEquivFixingSubgroup hrange
  have hcardEq :
      Nat.card (fixingSubgroup P (Set.range e)) =
        Nat.card H := by
    calc
      Nat.card (fixingSubgroup P (Set.range e)) =
          Nat.card (fixingSubgroup P (Set.range e₀)) :=
        Nat.card_congr ψ.symm.toEquiv
      _ = Nat.card H := by rw [he₀Range]
  have hle : H ≤ fixingSubgroup P (Set.range e) := by
    intro u hu
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxFixed := he hx
    rw [MulAction.mem_fixedPoints] at hxFixed
    exact hxFixed ⟨u, hu⟩
  exact
    (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcardEq])).symm

theorem five_point_stabilizer_fixed_points_descFactorial_dvd
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card
        (MulAction.fixedPoints
          (fixingSubgroup P s) X)).descFactorial 5 ∣
      5100480 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let E := Fin 5 ↪ X
  let C := FiveStabilizerConjugates X P H
  let A :=
    Σ e : E,
      FiveStabilizerConjugateFixesEmbedding X P H e
  let B :=
    Σ U : C,
      MulAction.fixedPoints U.1 E
  let f :=
    Nat.card (MulAction.fixedPoints H X)
  change f.descFactorial 5 ∣ 5100480
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e₀ : E := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have he₀Range : Set.range e₀ = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hFixingCard (e : E) :
      Nat.card (fixingSubgroup P (Set.range e)) =
        Nat.card H := by
    obtain ⟨q, hq⟩ := hP5.exists_smul_eq e₀ e
    have hrange :
        q • Set.range e₀ = Set.range e := by
      rw [Degree24.smul_range_fiveEmbedding]
      exact congrArg
        (fun z : E => Set.range z) hq
    let ψ :
        fixingSubgroup P (Set.range e₀) ≃*
          fixingSubgroup P (Set.range e) :=
      fixingSubgroupEquivFixingSubgroup hrange
    calc
      Nat.card (fixingSubgroup P (Set.range e)) =
          Nat.card (fixingSubgroup P (Set.range e₀)) :=
        Nat.card_congr ψ.symm.toEquiv
      _ = Nat.card H := by rw [he₀Range]
  have hConjugateCard (U : C) :
      Nat.card U.1 = Nat.card H := by
    obtain ⟨g, hg⟩ :=
      MulAction.mem_orbit_iff.mp U.prop
    rw [← hg]
    exact
      Nat.card_congr
        (Subgroup.equivSMul g H).symm.toEquiv
  have hFiberA (e : E) :
      Nat.card
          (FiveStabilizerConjugateFixesEmbedding
            X P H e) = 1 := by
    obtain ⟨q, hq⟩ := hP5.exists_smul_eq e₀ e
    have hrange :
        q • Set.range e₀ = Set.range e := by
      rw [Degree24.smul_range_fiveEmbedding]
      exact congrArg
        (fun z : E => Set.range z) hq
    have hconj :
        ConjAct.toConjAct q • H =
          fixingSubgroup P (Set.range e) := by
      change
        (fixingSubgroup P s).map
            (MulAut.conj q).toMonoidHom =
          fixingSubgroup P (Set.range e)
      rw [← he₀Range]
      exact
        SubMulAction.fixingSubgroup_map_conj_eq hrange
    let U₀ : FiveStabilizerConjugates X P H :=
      ⟨fixingSubgroup P (Set.range e),
        MulAction.mem_orbit_iff.mpr
          ⟨ConjAct.toConjAct q, hconj⟩⟩
    let z₀ :
        FiveStabilizerConjugateFixesEmbedding
          X P H e :=
      ⟨U₀, le_rfl⟩
    have hsubsingleton :
        Subsingleton
          (FiveStabilizerConjugateFixesEmbedding
            X P H e) := by
      constructor
      intro U V
      apply Subtype.ext
      apply Subtype.ext
      have hU :
          (U.1.1 : Subgroup P) =
            fixingSubgroup P (Set.range e) := by
        apply Subgroup.eq_of_le_of_card_ge U.2
        rw [hFixingCard e, hConjugateCard U.1]
      have hV :
          (V.1.1 : Subgroup P) =
            fixingSubgroup P (Set.range e) := by
        apply Subgroup.eq_of_le_of_card_ge V.2
        rw [hFixingCard e, hConjugateCard V.1]
      exact hU.trans hV.symm
    letI :
        Unique
          (FiveStabilizerConjugateFixesEmbedding
            X P H e) :=
      ⟨⟨z₀⟩, fun z => hsubsingleton.elim z z₀⟩
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨inferInstance, inferInstance⟩
  have hFiberB (U : C) :
      Nat.card
          (MulAction.fixedPoints U.1 E) =
        f.descFactorial 5 := by
    obtain ⟨g, hg⟩ :=
      MulAction.mem_orbit_iff.mp U.prop
    have hfixedCard :
        Nat.card (MulAction.fixedPoints U.1 X) = f := by
      rw [← hg]
      exact
        Nat.card_congr
          (fixedPointsConjugateEquiv X P H g).symm
    calc
      Nat.card (MulAction.fixedPoints U.1 E) =
          Nat.card
            (Fin 5 ↪
              MulAction.fixedPoints U.1 X) :=
        Nat.card_congr
          (fixedEmbeddingEquivEmbeddingFixedPoints
            5 U.1)
      _ = f.descFactorial 5 := by
        rw [Nat.card_eq_fintype_card,
          Fintype.card_embedding_eq,
          Fintype.card_fin,
          ← Nat.card_eq_fintype_card,
          hfixedCard]
  have hAcard : Nat.card A = Nat.card E := by
    rw [Nat.card_sigma]
    simp_rw [hFiberA]
    simp [Nat.card_eq_fintype_card]
  have hBcard :
      Nat.card B = Nat.card C * f.descFactorial 5 := by
    rw [Nat.card_sigma]
    simp_rw [hFiberB]
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  have hincidence : Nat.card A = Nat.card B :=
    Nat.card_congr
      (fiveStabilizerEmbeddingIncidenceEquiv X P H)
  have hcount :
      Nat.card E =
        Nat.card C * f.descFactorial 5 := by
    rw [← hAcard, ← hBcard]
    exact hincidence
  have hEcard : Nat.card E = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin, hcard]
    norm_num [Nat.descFactorial]
  rw [hEcard] at hcount
  exact
    ⟨Nat.card C, by
      simpa [Nat.mul_comm] using hcount⟩

private theorem fixed_point_card_divisor_cases :
    ∀ f : Fin 24,
      5 ≤ f.val →
      f.val.descFactorial 5 ∣ 5100480 →
      f.val = 5 ∨ f.val = 6 ∨ f.val = 7 ∨
        f.val = 8 ∨ f.val = 11 := by
  decide

theorem five_point_stabilizer_fixed_points_card_cases
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
    f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8 ∨ f = 11 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let F : Set X := MulAction.fixedPoints H X
  let f := Nat.card F
  change
    f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8 ∨ f = 11
  have hsFixed : s ⊆ F := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro h
    exact
      (mem_fixingSubgroup_iff P).mp h.prop x hx
  have hfFive : 5 ≤ f := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ F.ncard :=
        Set.ncard_le_ncard hsFixed
      _ = f := (Nat.card_coe_set_eq F).symm
  have hfLe : f ≤ 24 := by
    calc
      f = F.ncard := Nat.card_coe_set_eq F
      _ ≤ (Set.univ : Set X).ncard :=
        Set.ncard_le_ncard (Set.subset_univ F)
      _ = 24 := by
        rw [Set.ncard_univ,
          Nat.card_eq_fintype_card, hcard]
  have hfLt : f < 24 := by
    by_contra hlt
    have hfEq : f = 24 := by omega
    have hFuniv : F = Set.univ := by
      rw [Set.eq_univ_iff_ncard]
      calc
        F.ncard = f :=
          (Nat.card_coe_set_eq F).symm
        _ = 24 := hfEq
        _ = Nat.card X := by
          rw [Nat.card_eq_fintype_card, hcard]
    have hHsubsingleton : Subsingleton H := by
      constructor
      intro a b
      apply Subtype.ext
      apply P.subtype_injective
      ext x
      have hx : x ∈ F := by
        rw [hFuniv]
        simp
      have ha := hx a
      have hb := hx b
      simpa [Subgroup.smul_def,
        Equiv.Perm.smul_def] using ha.trans hb.symm
    letI : Subsingleton H := hHsubsingleton
    have hHone : Nat.card H = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨inferInstance, inferInstance⟩
    exact hHneOne hHone
  have hfDvd :
      f.descFactorial 5 ∣ 5100480 := by
    simpa only [H, F, f] using
      five_point_stabilizer_fixed_points_descFactorial_dvd
        X P hcard h5 s hs
  let f' : Fin 24 := ⟨f, hfLt⟩
  exact
    fixed_point_card_divisor_cases f' hfFive hfDvd

theorem five_point_stabilizers_have_equal_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s t : Set X) (hs : s.ncard = 5)
    (ht : t.ncard = 5) :
    Nat.card (fixingSubgroup P s) =
      Nat.card (fixingSubgroup P t) := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  letI : Fintype t := Fintype.ofFinite t
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  have htCard : Fintype.card t = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, ht]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let et : t ≃ Fin 5 :=
    Fintype.equivFinOfCardEq htCard
  let a : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  let b : Fin 5 ↪ X := {
    toFun := fun i => (et.symm i).1
    inj' := by
      intro i j hij
      apply et.symm.injective
      exact Subtype.ext hij }
  have haRange : Set.range a = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hbRange : Set.range b = t := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (et.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        et.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q, hq⟩ :=
    h5 a b a.injective b.injective
  have hqEmbedding : q • a = b := by
    ext i
    exact hq i
  have hqRange : q • s = t := by
    rw [← haRange, ← hbRange,
      Degree24.smul_range_fiveEmbedding,
      hqEmbedding]
  exact
    Nat.card_congr
      (fixingSubgroupEquivFixingSubgroup hqRange).toEquiv

end FiveTransitive.Degree24

end CFSG

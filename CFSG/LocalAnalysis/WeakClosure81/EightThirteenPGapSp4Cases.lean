module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Tis
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4CasesAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {F : Type} [Field F]

private noncomputable def wcgapscA' (A : Subgroup (StatedSp 2 F)) : AddSubgroup (F × F) where
  carrier := {x | sp4Z x.1 x.2 ∈ A}
  zero_mem' := by
    show sp4Z 0 0 ∈ A
    rw [wcgapsc_sp4Z_zero]
    exact A.one_mem
  add_mem' := by
    intro x y hx hy
    show sp4Z (x.1 + y.1) (x.2 + y.2) ∈ A
    rw [← wcgapsc_sp4Z_add]
    exact A.mul_mem hx hy
  neg_mem' := by
    intro x hx
    show sp4Z (-x.1) (-x.2) ∈ A
    rw [wcgapsc_sp4Z_neg]
    exact A.inv_mem hx

private noncomputable def wcgapscA'Equiv [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (A : Subgroup (StatedSp 2 F))
    (hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F))) :
    wcgapscA' A ≃ A :=
  Equiv.ofBijective (fun x : wcgapscA' A => (⟨sp4Z x.1.1 x.1.2, x.2⟩ : A)) (by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      obtain ⟨h1, h2⟩ := wcgapsc_sp4Z_injective (congrArg Subtype.val hxy)
      exact Prod.ext h1 h2
    · rintro ⟨g, hg⟩
      obtain ⟨b, c, hbc⟩ := (wcgapsc_sp4Z_mem_center_iff hF (g := g)).mp (hAZ hg)
      exact ⟨⟨(b, c), by show sp4Z b c ∈ A; rw [← hbc]; exact hg⟩, Subtype.ext hbc.symm⟩)

private lemma wcgapsc_mem_A_iff [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {A : Subgroup (StatedSp 2 F)}
    (hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (g : StatedSp 2 F) :
    g ∈ A ↔ ∃ x : F × F, x ∈ wcgapscA' A ∧ g = sp4Z x.1 x.2 := by
  constructor
  · intro hg
    obtain ⟨b, c, hbc⟩ := (wcgapsc_sp4Z_mem_center_iff hF (g := g)).mp (hAZ hg)
    exact ⟨(b, c), by show sp4Z b c ∈ A; rw [← hbc]; exact hg, hbc⟩
  · rintro ⟨x, hx, hg⟩
    rw [hg]
    exact hx

private theorem wcgapsc_classify [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (A' : AddSubgroup (F × F)) (hcard : Nat.card A' = 4)
    (hax1 : ∀ b : F, (b, 0) ∈ A' → b = 0)
    (hax2 : ∀ c : F, (0, c) ∈ A' → c = 0) :
    (∃ b c : F, (b ≠ 0 ∨ c ≠ 0) ∧
      ∀ x : F × F, x ∈ A' ↔ ∃ t : F, x = (t * b, t * c)) ∨
    (∃ b : F, b ≠ 0 ∧ ∀ x : F × F, x ∈ A' ↔ ∃ s : F, x = (s, b * s ^ 2)) := by
  let p1 : A' →+ F :=
    { toFun := fun x => (x.1).1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let p2 : A' →+ F :=
    { toFun := fun x => (x.1).2, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hp1_inj : Function.Injective p1 := by
    intro x y hxy
    change (x.1).1 = (y.1).1 at hxy
    have hsub : (x : F × F) - (y : F × F) ∈ A' := A'.sub_mem x.2 y.2
    have h0 : ((x : F × F) - (y : F × F)).1 = 0 := by
      show (x : F × F).1 - (y : F × F).1 = 0
      rw [hxy, sub_self]
    have hmem : (0, ((x : F × F) - (y : F × F)).2) ∈ A' := by
      have hxy' : (x : F × F) - (y : F × F) = (0, ((x : F × F) - (y : F × F)).2) :=
        Prod.ext h0 rfl
      rwa [hxy'] at hsub
    have h2 : ((x : F × F) - (y : F × F)).2 = 0 := hax2 _ hmem
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h0 h2)
  have hp2_inj : Function.Injective p2 := by
    intro x y hxy
    change (x.1).2 = (y.1).2 at hxy
    have hsub : (x : F × F) - (y : F × F) ∈ A' := A'.sub_mem x.2 y.2
    have h0 : ((x : F × F) - (y : F × F)).2 = 0 := by
      show (x : F × F).2 - (y : F × F).2 = 0
      rw [hxy, sub_self]
    have hmem : (((x : F × F) - (y : F × F)).1, 0) ∈ A' := by
      have hxy' : (x : F × F) - (y : F × F) = (((x : F × F) - (y : F × F)).1, 0) :=
        Prod.ext rfl h0
      rwa [hxy'] at hsub
    have h1 : ((x : F × F) - (y : F × F)).1 = 0 := hax1 _ hmem
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h1 h0)
  have hp1_bij : Function.Bijective p1 := by
    rw [Nat.bijective_iff_injective_and_card p1]
    exact ⟨hp1_inj, by rw [hcard, hF]⟩
  have hp2_bij : Function.Bijective p2 := by
    rw [Nat.bijective_iff_injective_and_card p2]
    exact ⟨hp2_inj, by rw [hcard, hF]⟩
  let e1 : A' ≃+ F := AddEquiv.ofBijective p1 hp1_bij
  let L : F →+ F := p2.comp e1.symm.toAddMonoidHom
  have he1_apply : ∀ y : A', e1 y = (y.1).1 := fun _ => rfl
  have he1symm : ∀ s : F, (e1.symm s : A').1 = (s, L s) := by
    intro s
    have h1 : (e1.symm s : A').1.1 = s := by
      rw [← he1_apply (e1.symm s), e1.apply_symm_apply s]
    have h2 : (e1.symm s : A').1.2 = L s := rfl
    exact Prod.ext h1 h2
  have hgraph : ∀ x : F × F, x ∈ A' ↔ ∃ s : F, x = (s, L s) := by
    intro x
    constructor
    · intro hx
      have hxe : (⟨x, hx⟩ : A') = e1.symm x.1 := by
        apply e1.injective
        rw [e1.apply_symm_apply]
        rfl
      have hxx : x = (x.1, L x.1) := by
        calc x = (⟨x, hx⟩ : A').1 := rfl
          _ = (e1.symm x.1 : A').1 := by rw [hxe]
          _ = (x.1, L x.1) := he1symm x.1
      exact ⟨x.1, hxx⟩
    · rintro ⟨s, rfl⟩
      have h := (e1.symm s).2
      rwa [he1symm s] at h
  have hL_inj : Function.Injective L := by
    intro x y hxy
    change p2 (e1.symm x) = p2 (e1.symm y) at hxy
    exact e1.symm.injective (hp2_inj hxy)
  rcases wcgapsc_graph_cases hF L hL_inj with ⟨a, ha, hax⟩ | ⟨b, hb, hbx⟩
  · left
    refine ⟨1, a, Or.inl one_ne_zero, fun x => ?_⟩
    rw [hgraph]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      ext <;> simp [hax, mul_comm]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [ht]
      ext <;> simp [hax, mul_comm]
  · right
    refine ⟨b, hb, fun x => ?_⟩
    rw [hgraph]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [hbx]⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, by rw [hs, hbx]⟩

theorem sp4_cases_of_axes {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {A : Subgroup (StatedSp 2 F)}
    (hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (hA4 : Nat.card ↥A = 4)
    (hX : ((∃ g ∈ A, g ≠ 1 ∧ ∃ b : F, g = sp4Z b 0) →
            ∀ g, g ∈ A ↔ ∃ b : F, g = sp4Z b 0) ∧
          ((∃ g ∈ A, g ≠ 1 ∧ ∃ c : F, g = sp4Z 0 c) →
            ∀ g, g ∈ A ↔ ∃ c : F, g = sp4Z 0 c)) :
    (∃ b c : F, (b ≠ 0 ∨ c ≠ 0) ∧ ∀ g, g ∈ A ↔ ∃ t : F, g = sp4Z (t * b) (t * c)) ∨
    (∃ b : F, b ≠ 0 ∧ ∀ g, g ∈ A ↔ ∃ s : F, g = sp4Z s (b * s ^ 2)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  set A' : AddSubgroup (F × F) := wcgapscA' A with hA'def
  have hcard : Nat.card A' = 4 := by
    rw [hA'def]
    exact (Nat.card_congr (wcgapscA'Equiv hF A hAZ)).trans hA4
  have hmem : ∀ g, g ∈ A ↔ ∃ x : F × F, x ∈ A' ∧ g = sp4Z x.1 x.2 := by
    intro g
    rw [hA'def]
    exact wcgapsc_mem_A_iff hF hAZ g
  by_cases hlong : ∃ g ∈ A, g ≠ 1 ∧ ∃ b : F, g = sp4Z b 0
  · have hAeq := hX.1 hlong
    left
    refine ⟨1, 0, Or.inl one_ne_zero, fun g => ?_⟩
    rw [hAeq g]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, by rw [hb, mul_one, mul_zero]⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht, mul_one, mul_zero]⟩
  · by_cases hshort : ∃ g ∈ A, g ≠ 1 ∧ ∃ c : F, g = sp4Z 0 c
    · have hAeq := hX.2 hshort
      left
      refine ⟨0, 1, Or.inr one_ne_zero, fun g => ?_⟩
      rw [hAeq g]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨c, by rw [hc, mul_zero, mul_one]⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, by rw [ht, mul_zero, mul_one]⟩
    · have hax1 : ∀ b : F, (b, 0) ∈ A' → b = 0 := by
        intro b hb
        by_contra hb0
        apply hlong
        refine ⟨sp4Z b 0, ?_, ?_, b, rfl⟩
        · exact (hmem (sp4Z b 0)).mpr ⟨(b, 0), hb, rfl⟩
        · intro h
          rw [wcgapsc_sp4Z_eq_one_iff] at h
          exact hb0 h.1
      have hax2 : ∀ c : F, (0, c) ∈ A' → c = 0 := by
        intro c hc
        by_contra hc0
        apply hshort
        refine ⟨sp4Z 0 c, ?_, ?_, c, rfl⟩
        · exact (hmem (sp4Z 0 c)).mpr ⟨(0, c), hc, rfl⟩
        · intro h
          rw [wcgapsc_sp4Z_eq_one_iff] at h
          exact hc0 h.2
      rcases wcgapsc_classify hF A' hcard hax1 hax2 with ⟨b, c, hbc0, hbc⟩ | ⟨b, hb, hbx⟩
      · left
        refine ⟨b, c, hbc0, fun g => ?_⟩
        rw [hmem g]
        constructor
        · rintro ⟨x, hx, hg⟩
          rw [hbc] at hx
          obtain ⟨t, rfl⟩ := hx
          exact ⟨t, hg⟩
        · rintro ⟨t, ht⟩
          exact ⟨(t * b, t * c), (hbc (t * b, t * c)).mpr ⟨t, rfl⟩, ht⟩
      · right
        refine ⟨b, hb, fun g => ?_⟩
        rw [hmem g]
        constructor
        · rintro ⟨x, hx, hg⟩
          rw [hbx] at hx
          obtain ⟨s, rfl⟩ := hx
          exact ⟨s, hg⟩
        · rintro ⟨s, hs⟩
          exact ⟨(s, b * s ^ 2), (hbx (s, b * s ^ 2)).mpr ⟨s, rfl⟩, hs⟩

end CFSG.LocalAnalysis.WeakClosure81

end

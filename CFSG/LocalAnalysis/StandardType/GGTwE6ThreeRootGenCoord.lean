module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenRefl
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ExcSplitRootGen.excRefl_neg
    {τ : Tag} {p : ℕ} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ExcSplitRootGen.excRefl (p := p) (-γ) = ExcSplitRootGen.excRefl (p := p) γ := by
  simp only [ExcSplitRootGen.excRefl, rootReflection_neg hγ]

namespace TwE6ThreeRootGen

theorem coordSet_eq_univ_or_hypE6
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hκrange : κ.range = ⊤ ∨
      ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) :
    ({x : Fin Tag.E6.rank → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} = Set.univ ∨
      {x : Fin Tag.E6.rank → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} =
        (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) := by
  rcases hκrange with h | h
  · left
    ext x
    change Multiplicative.ofAdd x ∈ κ.range ↔ True
    rw [h]
    exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
  · right
    ext x
    exact h x

theorem card_fix_excRefl_toAdd_mul_three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hκ : Function.Injective κ)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nat.card {a : A // ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
      Multiplicative.toAdd (κ a)} * 3 = Nat.card A := by
  let e : A ≃ ↥V :=
    Equiv.ofBijective
      (fun a : A => (⟨Multiplicative.toAdd (κ a),
        (hVmem (Multiplicative.toAdd (κ a))).1
          (MonoidHom.mem_range.mpr ⟨a, by rw [ofAdd_toAdd]⟩)⟩ : ↥V))
      ⟨fun a a' h => hκ (by
          simpa only [ofAdd_toAdd] using
            congrArg Multiplicative.ofAdd (Subtype.ext_iff.mp h)),
        fun b => by
          obtain ⟨a, ha⟩ := (hVmem b.1).2 b.2
          exact ⟨a, Subtype.ext (by
            simpa only [toAdd_ofAdd] using congrArg Multiplicative.toAdd ha)⟩⟩
  have hcardA : Nat.card A = Nat.card V := Nat.card_congr e
  have hcardFix1 : Nat.card {a : A // ExcSplitRootGen.excRefl (p := 3) γ
        (Multiplicative.toAdd (κ a)) = Multiplicative.toAdd (κ a)} =
      Nat.card {x : ↥V // ExcSplitRootGen.excRefl (p := 3) γ
        (x : Fin Tag.E6.rank → ZMod 3) = (x : Fin Tag.E6.rank → ZMod 3)} :=
    Nat.card_congr (Equiv.subtypeEquiv e (fun a => Iff.rfl))
  have hcardFix2 : Nat.card {x : ↥V // ExcSplitRootGen.excRefl (p := 3) γ
        (x : Fin Tag.E6.rank → ZMod 3) = (x : Fin Tag.E6.rank → ZMod 3)} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ExcSplitRootGen.excRefl (p := 3) γ x = x} :=
    Nat.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ V)
        (fun x => ExcSplitRootGen.excRefl (p := 3) γ x = x))
  rw [hcardFix1, hcardFix2, hcardA]
  exact card_fix_excRefl_mul_three (V := V) hV hγ

theorem image_fix_excRefl_toAdd
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    {X : Type*} {t : (Fin Tag.E6.rank → ZMod 3) → X} {γ : Fin Tag.E6.rank → ℤ} :
    (fun a : A => t (Multiplicative.toAdd (κ a))) ''
      {a : A | ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
        Multiplicative.toAdd (κ a)} =
    t '' {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧
      ExcSplitRootGen.excRefl (p := 3) γ x = x} := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Multiplicative.toAdd (κ a), ⟨(hVmem _).1
      (MonoidHom.mem_range.mpr ⟨a, by rw [ofAdd_toAdd]⟩), ha⟩, rfl⟩
  · rintro ⟨x, ⟨hxV, hxfix⟩, rfl⟩
    obtain ⟨a, ha⟩ := (hVmem x).2 hxV
    have hx : Multiplicative.toAdd (κ a) = x :=
      (congrArg Multiplicative.toAdd ha).trans (toAdd_ofAdd x)
    refine ⟨a, ?_, ?_⟩
    · change ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
        Multiplicative.toAdd (κ a)
      exact (congrArg (ExcSplitRootGen.excRefl (p := 3) γ) hx).trans
        (hxfix.trans hx.symm)
    · change t (Multiplicative.toAdd (κ a)) = t x
      exact congrArg t hx

theorem exists_excRefl_toAdd_ne_iff
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ) :
    (∃ a : A, ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) ≠
      ExcSplitRootGen.excRefl (p := 3) δ (Multiplicative.toAdd (κ a))) ↔
    ExcSplitRootGen.excRefl (p := 3) γ ≠ ExcSplitRootGen.excRefl (p := 3) δ := by
  constructor
  · rintro ⟨a, ha⟩ h
    exact ha (congrFun h (Multiplicative.toAdd (κ a)))
  · intro hne
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    have hVeq : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x =
        ExcSplitRootGen.excRefl (p := 3) δ x := by
      intro x hxV
      obtain ⟨a, ha⟩ := (hVmem x).2 hxV
      have hx : Multiplicative.toAdd (κ a) = x := by
        simpa using congrArg Multiplicative.toAdd ha
      rw [← hx]
      exact h a
    rcases eq_or_eq_neg_of_eqOn_excRefl hV hγ hδ hVeq with hδγ | hδγ
    · rw [hδγ]
    · rw [hδγ, ExcSplitRootGen.excRefl_neg hγ]

theorem excRefl_sub_mem_hypE6 (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) :
    ExcSplitRootGen.excRefl (p := 3) γ x - x ∈ NoOffRest.hypE6 := by
  simpa only [ExcSplitRootGen.excRefl] using
    TableBExc.E6Three.adAct_sub_mem_hypE6 (rootReflection γ) x

end TwE6ThreeRootGen

end CFSG.StandardType

end

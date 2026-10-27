module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Generate
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Transfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

@[expose] def FieldRigid {T : Type} [Group T] (φ : MulAut T) : Prop :=
  ∀ α : MulAut T, (∀ x ∈ fixedBy (Subgroup.zpowers φ), α x = x) → α ∈ Subgroup.zpowers φ

@[expose] def FieldPair {T : Type} [Group T] (φ : MulAut T) : Prop :=
  ∀ n : T, (fixedBy (Subgroup.zpowers φ)).map (MulAut.conj n).toMonoidHom ≠
      fixedBy (Subgroup.zpowers φ) →
    fixedBy (Subgroup.zpowers φ) ⊔ (fixedBy (Subgroup.zpowers φ)).map (MulAut.conj n).toMonoidHom
      = ⊤

@[expose] def FieldCount {T : Type} [Group T] [Finite T] (φ : MulAut T) : Prop :=
  ∀ Z : Subgroup T, IsSylowOf 3 Z ⊤ → Nat.card Z = 9 → (∀ z ∈ Z, φ z = z) →
    Nat.card (fixedBy (Subgroup.zpowers φ)) < Nat.card (normalizer (Z : Set T))

@[expose] def FieldGood {T : Type} [Group T] [Finite T] (φ : MulAut T) : Prop :=
  FieldRigid φ ∧ FieldPair φ ∧ FieldCount φ

@[expose] def HasField (T : Type) [Group T] [Finite T] : Prop :=
  ∀ W : Subgroup (MulAut T), Nat.card W = 7 → ¬ 7 ∣ Nat.card T →
    ∃ g φ : MulAut T, orderOf φ = 7 ∧
      W = (Subgroup.zpowers φ).map (MulAut.conj g).toMonoidHom ∧ FieldGood φ

theorem sevenStep_of_hasField {T : Type} [Group T] [Finite T] (hZ : Subgroup.center T = ⊥)
    (h : HasField T) : SevenStep T := by
  intro h7 W X hWcard hXsyl hXea hX9 hXfix
  obtain ⟨g, φ, hφord, hWeq, hgood⟩ := h W hWcard h7
  unfold FieldGood FieldRigid FieldPair FieldCount at hgood
  obtain ⟨hrig, hpair, hcount⟩ := hgood
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X' : Subgroup T := X.map g.symm.toMonoidHom
  have hX'card : Nat.card X' = 9 := by
    dsimp only [X']
    rw [Subgroup.card_map_of_injective g.symm.injective, hX9]
  have hX'syl : IsSylowOf 3 X' ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hX'card, ← hX9]
    exact hXsyl.card_eq
  have hX'fix : ∀ y ∈ X', φ y = y := by
    intro y hy
    dsimp only [X'] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : (MulAut.conj g) φ ∈ W := by
      rw [hWeq]
      exact Subgroup.mem_map.mpr ⟨φ, Subgroup.mem_zpowers φ, rfl⟩
    have hfixg := hXfix ((MulAut.conj g) φ) hmem x hx
    have h1 : ((MulAut.conj g) φ) x = g (φ (g.symm.toMonoidHom x)) := by
      simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [h1] at hfixg
    have := congrArg (fun z => g.symm z) hfixg
    simpa [MulAut.inv_apply] using this
  have hWp : IsPGroup 7 (Subgroup.zpowers φ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hφord, pow_one])
  have hcount' := hcount X' hX'syl hX'card hX'fix
  have htop := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven.normalizer_sup_fixedBy_eq_top
    hZ h7 (Subgroup.zpowers φ) hWp hrig X' hcount' hpair
  have hconj : MulAut.congr g = MulAut.conj g := by
    ext h x
    simp [MulAut.congr_apply, MulAut.conj_apply, MulAut.mul_apply]
  have hfixmap : (fixedBy (Subgroup.zpowers φ)).map g.toMonoidHom = fixedBy W := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven.fixedBy_map_congr g
      (Subgroup.zpowers φ)]
    rw [hWeq, hconj]
  have hX'map : X'.map g.toMonoidHom = X := by
    dsimp only [X']
    rw [Subgroup.map_map]
    have hcomp : g.toMonoidHom.comp g.symm.toMonoidHom = MonoidHom.id T := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  have hmap := congrArg (Subgroup.map g.toMonoidHom) htop
  rw [Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq, hfixmap,
    Subgroup.map_top_of_surjective g.toMonoidHom g.surjective] at hmap
  rwa [hX'map] at hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

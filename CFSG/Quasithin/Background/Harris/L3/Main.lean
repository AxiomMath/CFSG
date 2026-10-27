module

public import CFSG.Quasithin.Background.Harris.L3.Cases
public import CFSG.Quasithin.Background.Harris.L3.ClassifyWide

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Open
open scoped MatrixGroups

@[expose] def RankSharpInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m f : ℕ), OneCompSetting Γ A L m → 1 ≤ f →
    ∀ π : SL(3, GaloisField 2 f) →* ↥L, Function.Surjective π →
    (∀ g, π g = 1 → g ∈ Subgroup.center SL(3, GaloisField 2 f)) → ¬ SelfDual L ⊤ → m ≤ 2 * f

@[expose] def RankCrudeInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m f : ℕ), OneCompSetting Γ A L m → 2 ≤ f →
    ∀ π : SL(3, GaloisField 2 f) →* ↥L, Function.Surjective π →
    (∀ g, π g = 1 → g ∈ Subgroup.center SL(3, GaloisField 2 f)) → m ≤ 2 * f + 2

@[expose] def RankTwoInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m : ℕ), OneCompSetting Γ A L m →
    ∀ π : SL(3, GaloisField 2 1) →* ↥L, Function.Surjective π →
    (∀ g, π g = 1 → g ∈ Subgroup.center SL(3, GaloisField 2 1)) → m ≤ 2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_ne_one_of_isComponentOf {L Γ : Subgroup (GLV V)} (h : IsComponentOf L Γ) :
    ∃ l ∈ L, l ≠ 1 := by
  obtain ⟨-, -, -, hsimp⟩ := h
  by_contra hcon
  push Not at hcon
  have hbot : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr hcon
  have : Subsingleton ↥L := by
    rw [hbot]
    infer_instance
  have hnt := hsimp.toNontrivial
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  congr 1
  exact Subsingleton.elim _ _

theorem g93Concl_of_cover (h8 : Case8Input) (h17 : Case17Input) (hnsd : NotSelfDualInput)
    (hsharp : RankSharpInput) (hcrude : RankCrudeInput) (htwo : RankTwoInput) [Finite V]
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m) {f : ℕ} (hf : 1 ≤ f)
    (π : SL(3, GaloisField 2 f) →* ↥L) (hπ : Function.Surjective π)
    (hker : ∀ g, π g = 1 → g ∈ Subgroup.center SL(3, GaloisField 2 f)) :
    G93Concl Γ L m := by
  classical
  let _inst : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  have hirr := repOfHom_isIrreducible π hπ hs.L_irr
  have hnt := repOfHom_nontrivial π hπ (exists_ne_one_of_isComponentOf hs.L_comp)
  have hbound := hs.bound
  have hcase8 : NatShape L π → m ≤ 2 * f → G93Concl Γ L m := fun hN hm =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (h8 V Γ A L m f hs hf π hπ hm hN)))))))))
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  ·
    obtain rfl : f = 1 := by omega
    have hm := htwo V Γ A L m hs π hπ hker
    obtain ⟨hN, -⟩ := sl3_f_one_classification hFcard (repOfHom L π) hirr hnt (by omega)
    exact hcase8 hN (by omega)
  ·
    have hmc := hcrude V Γ A L m f hs hf2 π hπ hker
    rcases sl3_classification_wide hf2 hFcard (repOfHom L π) hirr hnt (by omega) with
      ⟨hN, -⟩ | ⟨k, hfk, hdim9, hH⟩
    · have hsd := hnsd V L f hf π hπ hs.L_irr (Or.inl hN)
      exact hcase8 hN (hsharp V Γ A L m f hs hf π hπ hker hsd)
    · have hsd := hnsd V L f hf π hπ hs.L_irr (Or.inr ⟨k, hH⟩)
      have hm := hsharp V Γ A L m f hs hf π hπ hker hsd
      subst hfk
      have hk : k = 1 ∨ k = 2 := by omega
      have h := h17 V Γ A L m k hs hk π hπ (by omega) hH
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))

theorem oneCompFor_famL3_of (h8 : Case8Input) (h17 : Case17Input) (hnsd : NotSelfDualInput)
    (hsharp : RankSharpInput) (hcrude : RankCrudeInput) (htwo : RankTwoInput) :
    OneCompFor FamL3 := by
  intro V _ _ _ Γ A L m hs hL
  obtain ⟨f, hf, π, hπ, hker⟩ := exists_cover_famL3 hL
  exact g93Concl_of_cover h8 h17 hnsd hsharp hcrude htwo hs hf π hπ hker

theorem oneCompFor_famCoverSL3Two_of (h8 : Case8Input) (h17 : Case17Input)
    (hnsd : NotSelfDualInput) (hsharp : RankSharpInput) (hcrude : RankCrudeInput)
    (htwo : RankTwoInput) : OneCompFor FamCoverSL3Two := by
  intro V _ _ _ Γ A L m hs hL
  obtain ⟨e, he, -, ⟨φ⟩⟩ := exists_cover_famCoverSL3Two hL
  refine g93Concl_of_cover h8 h17 hnsd hsharp hcrude htwo hs he φ.toMonoidHom φ.surjective
    fun g hg => ?_
  have : g = 1 := φ.injective (by simpa using hg)
  rw [this]
  exact Subgroup.one_mem _

end CFSG.Quasithin.G11.Harris.L3

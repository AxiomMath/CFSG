module

public import CFSG.Quasithin.Background.FFC4Three

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Vocabulary

variable {W : Type} [CommGroup W]

@[expose] def stabAt (Γ : Subgroup (MulAut W)) (w : W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ Γ ∧ g w = w}
  one_mem' := ⟨Γ.one_mem, rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨Γ.mul_mem ha.1 hb.1, by
    show a (b w) = w
    rw [hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨Γ.inv_mem ha.1, by
    show a⁻¹ w = w
    have h := ha.2
    calc a⁻¹ w = a⁻¹ (a w) := by rw [h]
      _ = w := MulAut.inv_apply_self W a w⟩

theorem mem_stabAt {Γ : Subgroup (MulAut W)} {w : W} {g : MulAut W} :
    g ∈ stabAt Γ w ↔ g ∈ Γ ∧ g w = w := Iff.rfl

theorem stabAt_le (Γ : Subgroup (MulAut W)) (w : W) : stabAt Γ w ≤ Γ := fun _ h => h.1

@[expose] def orbitSpan (Γ : Subgroup (MulAut W)) (w : W) : Subgroup W :=
  Subgroup.closure ((fun g : MulAut W => g w) '' (Γ : Set (MulAut W)))

end Vocabulary

section Statement

variable {W : Type} [CommGroup W]

structure Insp67Data (Γ : Subgroup (MulAut W)) (w : W) (𝒪 : Set (Subgroup (MulAut W))) : Prop where
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  o2 : pCoreOf 2 Γ = ⊥
  rank3 : ¬ FFC.ThreeRank2 ↥Γ
  w_ne : w ≠ 1
  gen : orbitSpan Γ w = ⊤
  three_prime : ¬ 3 ∣ Nat.card ↥(stabAt Γ w)
  offender : ∀ B ∈ 𝒪, B ≤ Γ ∧ IsElemAbelian2 B ∧ Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B)
  nontrivial : ∃ B ∈ 𝒪, B ≠ ⊥
  frattini : ∀ N : Subgroup (MulAut W), N ≤ Γ → (N.subgroupOf Γ).Normal → (∀ B ∈ 𝒪, B ≤ N) →
    Γ = N ⊔ stabAt Γ w ∧ ∃ S : Subgroup (MulAut W), IsSylowTwoOf S N ∧
      Subgroup.normalizer (S : Set (MulAut W)) ⊓ N ≤ stabAt Γ w

end Statement

@[expose] def Input15367Module : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ v : W, v ^ 2 = 1) →
    ∀ (Γ : Subgroup (MulAut W)) (w : W) (𝒪 : Set (Subgroup (MulAut W))),
      Insp67Data Γ w 𝒪 → (stabAt Γ w).relIndex Γ = 3

end CFSG.Quasithin.S153N

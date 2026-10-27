module

public import CFSG.RankThree.PartOne.K133H.WeylKey
public import CFSG.RankThree.PartOne.K133H.TorusOdd
public import CFSG.RankThree.PartOne.K133H.F4Torus
public import CFSG.RankThree.PartOne.K133H.F4Weyl
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K

set_option linter.unusedSectionVars false

theorem dvd_card_pow_sub_one {X : Type} [Field X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpX : ¬ p ∣ Nat.card X) : p ∣ Nat.card X ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime (Nat.card X) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpX).symm
  have h := (Nat.ModEq.pow_totient hcop).symm
  rw [Nat.totient_prime hp] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 h

theorem oddOrderOneOrThree_torusImage_F4 {X : Type} [Field X] [Finite X] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP X ℓ] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpX : ¬ p ∣ Nat.card X) {Q : Type}
    [Group Q] (ι₀ : Q →* ModGL .F4 X) (hι₀ : Function.Injective ι₀)
    (hC : ∀ x, ι₀ x ∈ adjointGroup .F4 X) {Ē : Subgroup Q} (hpow : ∀ x ∈ Ē, x ^ p = 1) :
    OddOrderOneOrThree ↥(torusImage Ē ⊤) := by
  classical
  have : NeZero (p - 1) := ⟨by omega⟩
  have hcard : Nat.card (FiniteField.Extension X ℓ (p - 1)) = Nat.card X ^ (p - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := X), FiniteField.finrank_extension]
  have hdvd : p ∣ Nat.card (FiniteField.Extension X ℓ (p - 1)) - 1 := by
    rw [hcard]
    exact dvd_card_pow_sub_one hp hpX
  let f : X →+* FiniteField.Extension X ℓ (p - 1) := algebraMap X _
  let ι₁ : Q →* ModGL .F4 (FiniteField.Extension X ℓ (p - 1)) := (baseChangeGL f).comp ι₀
  have hι₁ : Function.Injective ι₁ := (baseChangeGL_injective (τ := .F4) f).comp hι₀
  have hι₁C : ∀ x, ι₁ x ∈ adjointGroup .F4 (FiniteField.Extension X ℓ (p - 1)) :=
    fun x => baseChangeGL_mem_adjointGroup f (hC x)
  obtain ⟨g, hgC, hg⟩ := exists_conj_into_torus_F4 hp hp5 hdvd (A := Ē.map ι₁)
    (by rintro _ ⟨x, -, rfl⟩; exact hι₁C x)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hpow x hx, map_one])
  let ι₂ : Q →* ModGL .F4 (FiniteField.Extension X ℓ (p - 1)) := (MulAut.conj g).toMonoidHom.comp ι₁
  have hι₂ : Function.Injective ι₂ := (MulAut.conj g).injective.comp hι₁
  have hι₂C : ∀ x, ι₂ x ∈ adjointGroup .F4 (FiniteField.Extension X ℓ (p - 1)) := fun x =>
    mul_mem (mul_mem hgC (hι₁C x)) (inv_mem hgC)
  have hV : Ē.map ι₂ ≤ torusGroup .F4 (FiniteField.Extension X ℓ (p - 1)) := by
    rw [show ι₂ = (MulAut.conj g).toMonoidHom.comp ι₁ from rfl, ← Subgroup.map_map]
    exact hg
  exact oddOrderOneOrThree_torusImage_of_injective ι₂ hι₂ rfl hι₂C fun β hβ hodd =>
    eq_one_or_three_of_mem_torusImage oddOrder_weylGroup_F4 hV hβ hodd

end CFSG.RankThree.PartOne.K133H

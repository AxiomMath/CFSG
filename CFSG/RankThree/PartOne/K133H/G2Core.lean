module

public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.K133B.Defs

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327T
  CFSG.RankThree.PartOne.K133B

set_option linter.unusedSectionVars false

theorem card_torusImage_dvd_twelve_of_quadratic {K K₂ : Type} [Field K] [Finite K] [Field K₂]
    [Finite K₂] (f : K →+* K₂) (hK₂ : Nat.card K₂ = Nat.card K ^ 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hd : p ∣ Nat.card K ^ 2 - 1) {Q : Type} [Group Q]
    (ι₀ : Q →* adjointGroup .G2 K) (hι₀ : Function.Injective ι₀) {Ē : Subgroup Q}
    (hpow : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 2) :
    Nat.card ↥(torusImage Ē ⊤) ∣ 12 := by
  classical
  let ι₁ : Q →* ModGL .G2 K₂ := (baseChangeGL f).comp ((adjointGroup .G2 K).subtype.comp ι₀)
  have hι₁ : Function.Injective ι₁ :=
    (baseChangeGL_injective (τ := .G2) f).comp (Subtype.val_injective.comp hι₀)
  have hι₁C : ∀ x, ι₁ x ∈ adjointGroup .G2 K₂ := fun x => baseChangeGL_mem_adjointGroup f (ι₀ x).2
  have hpK₂ : ¬ p ∣ Nat.card K₂ := by
    rw [hK₂]
    exact fun h => hpK (hp.dvd_of_dvd_pow h)
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    rw [hK₂]
    exact hd
  obtain ⟨g, hgC, hg⟩ := exists_conj_eq_torusTorsion (K := K₂) hp hp5 hpK₂ hpq₂ (A := Ē.map ι₁)
    (by rintro _ ⟨x, -, rfl⟩; exact hι₁C x)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hpow x hx, map_one])
    (by rw [Subgroup.card_map_of_injective hι₁, hcard])
  let ι₂ : Q →* ModGL .G2 K₂ := (MulAut.conj g).toMonoidHom.comp ι₁
  have hι₂ : Function.Injective ι₂ := (MulAut.conj g).injective.comp hι₁
  have hV : Ē.map ι₂ = torusTorsion K₂ p := by
    rw [← hg, Subgroup.map_map]
  have hι₂C : ∀ x, ι₂ x ∈ adjointGroup .G2 K₂ := fun x =>
    mul_mem (mul_mem hgC (hι₁C x)) (inv_mem hgC)
  exact (card_torusImage_dvd_of_injective ι₂ hι₂ hV hι₂C).trans
    (card_torusImage_torusTorsion_dvd hp (by omega) hpq₂)

theorem card_torusImage_dvd_twelve {K : Type} [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hd : p ∣ Nat.card K ^ 2 - 1) {Q : Type} [Group Q] (ι₀ : Q →* adjointGroup .G2 K)
    (hι₀ : Function.Injective ι₀) {Ē : Subgroup Q} (hpow : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 2) : Nat.card ↥(torusImage Ē ⊤) ∣ 12 :=
  card_torusImage_dvd_twelve_of_quadratic (K₂ := FiniteField.Extension K ℓ 2)
    (algebraMap K (FiniteField.Extension K ℓ 2))
    (by rw [Module.natCard_eq_pow_finrank (K := K), FiniteField.finrank_extension]) hp hp5 hpK hd
    ι₀ hι₀ hpow hcard

theorem row8OddConcl_of_G2 {K : Type} [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {Q : Type} [Group Q] [Finite Q] {p g : ℕ} {Ē : Subgroup Q} (h : Row8Conf p g Q Ē)
    (eQ : Q ≃* adjointGroup .G2 K) (hpK : ¬ p ∣ Nat.card K) (hd : p ∣ Nat.card K ^ 2 - 1) :
    Row8OddConcl p Q Ē := by
  intro _
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.elem
  have hdvd : Nat.card ↥(torusImage Ē ⊤) ∣ 12 :=
    card_torusImage_dvd_twelve h.prime h.five_le hpK hd (eQ.toMonoidHom) eQ.injective
      (fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := Ē) x hx) h.card
  have : Finite (MulAut ↥Ē) :=
    Finite.of_injective (fun φ : MulAut ↥Ē => (φ : ↥Ē → ↥Ē)) DFunLike.coe_injective
  exact OddOrderOneOrThree.of_card_dvd (a := 2) (by simpa using hdvd)

end CFSG.RankThree.PartOne.K133H

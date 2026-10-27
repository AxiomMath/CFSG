module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_complement {p : ℕ} (hp : p.Prime) {X A Y : Subgroup G}
    (hX : IsPGroup p X) (hAX : A ≤ normalizer (X : Set G)) (hA : ¬ p ∣ Nat.card A)
    (hΦY : nineFrattini X ≤ Y) (hYX : Y ≤ X) (hAY : A ≤ normalizer (Y : Set G)) :
    ∃ Y' : Subgroup G, nineFrattini X ≤ Y' ∧ Y' ≤ X ∧ A ≤ normalizer (Y' : Set G) ∧
      Y ⊔ Y' = X ∧ Y ⊓ Y' = nineFrattini X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcommQ, hpowQ, -, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient (p := p) hX
  have hΦX : nineFrattini X ≤ X := Subgroup.map_subtype_le (frattini ↥X)
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ nineFrattini X := by
    intro x hx y hy
    have hmem :
        (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ ∈ frattini ↥X := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcommQ.is_comm.comm
        ((⟨x, hx⟩ : ↥X) : ↥X ⧸ frattini ↥X) ((⟨y, hy⟩ : ↥X) : ↥X ⧸ frattini ↥X)]
      group
    exact Subgroup.mem_map.mpr
      ⟨(⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹, hmem, rfl⟩
  have hpow : ∀ x ∈ X, x ^ p ∈ nineFrattini X := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥X) ^ p, ?_, rfl⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpowQ _
  have hcop : Nat.Coprime p (Nat.card A) := (Nat.Prime.coprime_iff_not_dvd hp).2 hA
  have hDQ : ∀ d ∈ A, ∀ x ∈ X, d * x * d⁻¹ ∈ X := fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAX hd) x).1 hx
  have hDΦ : ∀ d ∈ A, ∀ x ∈ nineFrattini X, d * x * d⁻¹ ∈ nineFrattini X := by
    intro d hd x hx
    obtain ⟨w, hw, hxw⟩ := Subgroup.mem_map.mp hx
    rw [← hxw]
    refine Subgroup.mem_map.mpr ⟨(X.normalizerMonoidHom ⟨d, hAX hd⟩) w, ?_, rfl⟩
    have hfix := (inferInstance : (frattini ↥X).Characteristic).fixed
      (X.normalizerMonoidHom ⟨d, hAX hd⟩)
    have : w ∈ (frattini ↥X).comap (X.normalizerMonoidHom ⟨d, hAX hd⟩).toMonoidHom := by
      rw [hfix]
      exact hw
    exact Subgroup.mem_comap.mp this
  have hDT : ∀ d ∈ A, ∀ x ∈ Y, d * x * d⁻¹ ∈ Y := fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAY hd) x).1 hx
  obtain ⟨Y', hΦY', hY'X, hinv, hsupXY, hinfXY⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := p)
      (X := G) (Q := X) (Φ := nineFrattini X) (D := A) (T := Y)
      hΦX hcomm hpow hcop hDQ hDΦ hΦY hYX hDT
  refine ⟨Y', hΦY', hY'X, ?_, hsupXY, hinfXY⟩
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hinv a ha n hn
  · intro hn
    have h2 := hinv a⁻¹ (A.inv_mem ha) (a * n * a⁻¹) hn
    simpa [mul_assoc] using h2

theorem irredOnFrattiniQuot_of_sup_ne {p : ℕ} (hp : p.Prime) {S X : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥)
    (hS : ¬ p ∣ Nat.card ↥(S ⊓ normalizer (X : Set G)))
    (hsup : ∀ Y₁ Y₂ : Subgroup G, nineFrattini X ≤ Y₁ → Y₁ ≤ X → Y₁ ≠ X →
      (∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y₁, s * y * s⁻¹ ∈ Y₁) →
      nineFrattini X ≤ Y₂ → Y₂ ≤ X → Y₂ ≠ X →
      (∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y₂, s * y * s⁻¹ ∈ Y₂) →
      Y₁ ⊔ Y₂ ≠ X) :
    IrredOnFrattiniQuot S X := by
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hΦlt : nineFrattini X < X := by
    have hΦne : frattini ↥X ≠ ⊤ := by
      obtain h | ⟨M, hM, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥X)
      · exact absurd h bot_ne_top
      · intro htop
        exact hM.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hM))
    have hΦtop : frattini ↥X < ⊤ := lt_top_iff_ne_top.mpr hΦne
    have htop : (⊤ : Subgroup ↥X).map X.subtype = X := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    show (frattini ↥X).map X.subtype < X
    simpa only [htop] using
      (Subgroup.map_subtype_lt_map_subtype (G' := X) (H := frattini ↥X) (K := ⊤)).mpr hΦtop
  refine ⟨hΦlt, ?_⟩
  intro Y hΦY hYX hY
  by_cases hYx : Y = X
  · exact Or.inr hYx
  · left
    have hAY : S ⊓ normalizer (X : Set G) ≤ normalizer (Y : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hY a ha n hn
      · intro hn
        have h2 := hY a⁻¹ ((S ⊓ normalizer (X : Set G)).inv_mem ha) (a * n * a⁻¹) hn
        simpa [mul_assoc] using h2
    obtain ⟨Y', hΦY', hY'X, hAY', hsupXY, hinfXY⟩ :=
      exists_invariant_complement hp hX inf_le_right hS hΦY hYX hAY
    have hY'inv : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y', s * y * s⁻¹ ∈ Y' :=
      fun s hs y hy => (Subgroup.mem_normalizer_iff.mp (hAY' hs) y).1 hy
    by_cases hY'x : Y' = X
    · rw [← hinfXY, hY'x, inf_eq_left.mpr hYX]
    · exact absurd hsupXY (hsup Y Y' hΦY hYX hYx hY hΦY' hY'X hY'x hY'inv)

end CFSG.LocalAnalysis.WeakClosure81

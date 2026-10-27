module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

section Descent


theorem bigElemAbelianToralBar_of_finite {τ : Tag} {p M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 1 ≤ M)
    (hfin : ∀ (K₁ : Type) [Field K₁] [Finite K₁] [CharP K₁ 2], p ^ M ∣ Nat.card K₁ - 1 →
      ∀ A : Subgroup (ModGL τ K₁), A ≤ adjointGroup τ K₁ →
        (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ p = 1) →
        p ^ (τ.rank - 1) ≤ Nat.card A →
          ∃ g ∈ adjointGroup τ K₁, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ K₁) :
    BigElemAbelianToralBar τ p := by
  intro K _ _ _ _ A hA hcomm hpow hcard
  have := Fact.mk hp
  have hAfin : (A : Set (ModGL τ (AlgebraicClosure K))).Finite := by
    have : Finite A := Nat.finite_of_card_ne_zero (lt_of_lt_of_le (pow_pos hp.pos _) hcard).ne'
    exact Set.toFinite _
  obtain ⟨K₁, hK₁, -, hq, hdesc⟩ := exists_descent_subgroup (ℓ := 2) (r := p) hp2.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hA hAfin ∅ hM
  haveI : Finite K₁ := hK₁
  set ι := K₁.subtype
  have hA₁C : A.comap (baseChangeGL ι) ≤ adjointGroup τ K₁ := comap_le_adjointGroup ι hdesc
  have hcomm₁ : ∀ x ∈ A.comap (baseChangeGL ι), ∀ y ∈ A.comap (baseChangeGL ι),
      x * y = y * x := fun x hx y hy => baseChangeGL_injective ι (by
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy))
  have hpow₁ : ∀ x ∈ A.comap (baseChangeGL ι), x ^ p = 1 := fun x hx =>
    baseChangeGL_injective ι (by rw [map_pow, map_one]; exact hpow _ (Subgroup.mem_comap.mp hx))
  have hcard₁ : Nat.card (A.comap (baseChangeGL ι)) = Nat.card A := by
    have hrange : A ≤ (baseChangeGL (τ := τ) ι).range := fun x hx => by
      obtain ⟨y, -, hy⟩ := hdesc x hx
      exact ⟨y, hy⟩
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    exact (Subgroup.card_map_of_injective (baseChangeGL_injective ι)).symm
  have hqM : p ^ M ∣ Nat.card K₁ - 1 := (Nat.modEq_iff_dvd' Nat.card_pos).mp hq.symm
  obtain ⟨g, hgC, hg⟩ := hfin K₁ hqM _ hA₁C hcomm₁ hpow₁ (hcard₁ ▸ hcard)
  have hH : torusGroup τ K₁ ≤ (torusGroup τ (AlgebraicClosure K)).comap (baseChangeGL ι) := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  refine ⟨baseChangeGL ι g, baseChangeGL_mem_adjointGroup ι hgC, fun x hx => ?_⟩
  obtain ⟨x₁, -, rfl⟩ := hdesc x hx
  rw [← map_inv, ← map_mul, ← map_mul]
  exact hH (hg x₁ hx)

end Descent

section Sylow

variable {τ : Tag} {K : Type} [Field K]

theorem exists_conj_torusGroup_of_weylX [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) {S : Subgroup (WeylGroup τ)}
    (hidx : ¬ p ∣ (TableBExc.weylX τ K S).index) {B : ℕ}
    (hS : ∀ s ∈ S, s ≠ 1 → ∃ (k : ℕ) (ω : List (Fin τ.rank)),
      (coxeterSystem τ).wordProd ω = s ^ k ∧
        Nat.card S * Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusWord τ p ω x = x} < B)
    {A : Subgroup (ModGL τ K)} (hA : A ≤ adjointGroup τ K)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hpow : ∀ x ∈ A, x ^ p = 1)
    (hcard : B ≤ Nat.card A) :
    ∃ g ∈ adjointGroup τ K, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ K := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  set E := A.subgroupOf (adjointGroup τ K) with hEdef
  have hE : CFSG.Open.IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩,
      fun x hx => Subtype.ext ((Subgroup.coe_pow _ x p).trans (hpow _ hx))⟩
  have hEcard : Nat.card E = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  obtain ⟨k, hk⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  have hcard' : Nat.card (E.map (MulAut.conj k).toMonoidHom) = Nat.card A := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hEcard]
  rcases TableBExc.le_torusPow_or_card_lt_of_le_weylX hp hpq hdet hV hS
    (TableB.isElemAbelian_map hE _) hk with h | h
  · refine ⟨(k : ModGL τ K)⁻¹, inv_mem k.2, fun x hx => ?_⟩
    have hmem : (MulAut.conj k).toMonoidHom ⟨x, hA hx⟩ ∈ E.map (MulAut.conj k).toMonoidHom :=
      ⟨⟨x, hA hx⟩, hx, rfl⟩
    obtain ⟨h1, -⟩ := h hmem
    rw [inv_inv]
    simpa using h1
  · omega

end Sylow

end CFSG.StandardType.ExcFramesHalf

module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.SemiregularSylowFixedSet

open MulAction

theorem fixedBy_eq_fixedPoints
    (Q X : Type*) [Group Q] [MulAction Q X]
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (q : Q) (hq : q ≠ 1) : fixedBy X q = fixedPoints Q X := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    exact hq (hfree q x hnot hx)
  · intro hx
    exact mem_fixedPoints.mp hx q

def fixedByConjugateEquiv
    (G X : Type*) [Group G] [MulAction G X] (g c : G) :
    fixedBy X g ≃ fixedBy X (c * g * c⁻¹) where
  toFun x := ⟨c • x.val, by
    change (c * g * c⁻¹) • (c • x.val) = c • x.val
    rw [mul_smul, mul_smul, inv_smul_smul, x.property]⟩
  invFun x := ⟨c⁻¹ • x.val, by
    change g • (c⁻¹ • x.val) = c⁻¹ • x.val
    have hx := congrArg (fun y : X => c⁻¹ • y) x.property
    simpa only [mul_smul, inv_smul_smul] using hx⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem exists_conjugate_mem_sylow
    (H : Type*) [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (u : H) (hu : orderOf u = p) :
    ∃ c : H, c * u * c⁻¹ ∈ S := by
  have hcyc : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, hu, pow_one])
  obtain ⟨T, hT⟩ := hcyc.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_smul_eq H T S
  have hcSub : (T : Subgroup H).map (MulAut.conj c).toMonoidHom =
      (S : Subgroup H) := congrArg Sylow.toSubgroup hc
  refine ⟨c, ?_⟩
  change c * u * c⁻¹ ∈ (S : Subgroup H)
  rw [← hcSub]
  exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom
    (hT (Subgroup.mem_zpowers u))

private theorem exists_conjugate_into_base_sylow
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G (Set.range e)))
    (g : G) (hg : orderOf g = p) (hfix : k ≤ (fixedBy X g).ncard) :
    ∃ (c : G) (q : S), c * g * c⁻¹ = ((q : fixingSubgroup G (Set.range e)) : G) := by
  classical
  let _ : Fintype (fixedBy X g) := Fintype.ofFinite _
  obtain ⟨a⟩ : Nonempty (Fin k ↪ fixedBy X g) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, Nat.card_fin] using hfix)
  let aX : Fin k ↪ X := a.trans (Function.Embedding.subtype _)
  obtain ⟨b, hb⟩ := isMultiplyPretransitive_iff.mp hk aX e
  have hb' (i : Fin k) : b • aX i = e i := congrArg (fun f : Fin k ↪ X => f i) hb
  let H := fixingSubgroup G (Set.range e)
  have hu_mem : b * g * b⁻¹ ∈ H := by
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    rw [← hb' i, mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun x : X => b • x) (a i).property
  let u : H := ⟨b * g * b⁻¹, hu_mem⟩
  have hu : orderOf u = p := by
    rw [← Subgroup.orderOf_coe u]
    exact (orderOf_injective (MulAut.conj b).toMonoidHom
      (MulAut.conj b).injective g).trans hg
  obtain ⟨d, hd⟩ := exists_conjugate_mem_sylow H S u hu
  refine ⟨(d : G) * b, ⟨d * u * d⁻¹, hd⟩, ?_⟩
  change ((d : G) * b) * g * ((d : G) * b)⁻¹ =
    (d : G) * (b * g * b⁻¹) * (d : G)⁻¹
  group

theorem fixedBy_ncard_eq_of_base_le
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G (Set.range e)))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (g : G) (hg : orderOf g = p) (hfix : k ≤ (fixedBy X g).ncard) :
    (fixedBy X g).ncard = (fixedPoints S X).ncard := by
  obtain ⟨c, q, hc⟩ := exists_conjugate_into_base_sylow G X k hk e S g hg hfix
  have hq : q ≠ 1 := by
    intro hq
    have hconj : c * g * c⁻¹ = 1 := by simpa [hq] using hc
    have hg1 : g = 1 := (MulAut.conj c).injective (by simpa using hconj)
    have hp : p = 1 := hg.symm.trans (by simp [hg1])
    exact (Fact.out : p.Prime).ne_one hp
  calc
    (fixedBy X g).ncard = (fixedBy X (c * g * c⁻¹)).ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (fixedByConjugateEquiv G X g c)
    _ = (fixedBy X q).ncard := by rw [hc]; rfl
    _ = (fixedPoints S X).ncard := congrArg Set.ncard (fixedBy_eq_fixedPoints S X hfree q hq)

end FiveTransitive.SemiregularSylowFixedSet

end CFSG

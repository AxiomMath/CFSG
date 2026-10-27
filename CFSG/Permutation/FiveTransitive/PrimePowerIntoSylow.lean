module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.PrimePowerIntoSylow

open MulAction

private theorem exists_conjugate_mem_sylow
    (H : Type*) [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (u : H) (n : ℕ) (hu : orderOf u = p ^ n) :
    ∃ c : H, c * u * c⁻¹ ∈ S := by
  have hcyc : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := n) (by simp only [Nat.card_zpowers, hu])
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
    (g : G) (n : ℕ) (hg : orderOf g = p ^ n) (hfix : k ≤ (fixedBy X g).ncard) :
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
  have hu : orderOf u = p ^ n := by
    rw [← Subgroup.orderOf_coe u]
    exact (orderOf_injective (MulAut.conj b).toMonoidHom
      (MulAut.conj b).injective g).trans hg
  obtain ⟨d, hd⟩ := exists_conjugate_mem_sylow H S u n hu
  refine ⟨(d : G) * b, ⟨d * u * d⁻¹, hd⟩, ?_⟩
  change ((d : G) * b) * g * ((d : G) * b)⁻¹ =
    (d : G) * (b * g * b⁻¹) * (d : G)⁻¹
  group

theorem exists_conjugate_into_set_sylow
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (s : Set X) (hs : s.ncard = k)
    {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup G s))
    (g : G) (n : ℕ) (hg : orderOf g = p ^ n) (hfix : k ≤ (fixedBy X g).ncard) :
    ∃ (c : G) (q : S), c * g * c⁻¹ = ((q : fixingSubgroup G s) : G) := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin k ↪ X, Set.range e = s := by
    let _ : Fintype s := Fintype.ofFinite _
    let e₀ : s ≃ Fin k := Fintype.equivFinOfCardEq
      (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hs)
    let e : Fin k ↪ X := e₀.symm.toEmbedding.trans (Function.Embedding.subtype _)
    refine ⟨e, ?_⟩
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e₀.symm i).property
    · intro hx
      refine ⟨e₀ ⟨x, hx⟩, ?_⟩
      change (e₀.symm (e₀ ⟨x, hx⟩)).val = x
      simp
  subst s
  exact exists_conjugate_into_base_sylow G X k hk e S g n hg hfix

theorem fixed_lt_four_of_order_four
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hsq : ∀ q : S, q * q = 1)
    (a : G) (ha : orderOf a = 4) : (fixedBy X a).ncard < 4 := by
  by_contra hn
  obtain ⟨c, q, hc⟩ := exists_conjugate_into_set_sylow G X 4 h4 s hs S a 2 ha (by omega)
  have hq : (((q : fixingSubgroup G s) : G)) ^ 2 = 1 := by
    exact congrArg (fun q : S => ((q : fixingSubgroup G s) : G)) (show q ^ 2 = 1 by simpa only [pow_two] using hsq q)
  have ha2 : a ^ 2 = 1 := by
    apply (MulAut.conj c).injective
    change (c * a ^ 2 * c⁻¹) = c * 1 * c⁻¹
    rw [← conj_pow, hc, hq]
    simp
  have hd := orderOf_dvd_of_pow_eq_one ha2
  rw [ha] at hd
  norm_num at hd

end FiveTransitive.PrimePowerIntoSylow

end CFSG

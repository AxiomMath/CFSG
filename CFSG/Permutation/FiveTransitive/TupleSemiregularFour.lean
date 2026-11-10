module

public import CFSG.Permutation.FiveTransitive.SemiregularSylowFixedSet

public section

namespace CFSG

namespace FiveTransitive.TupleSemiregularFour

open MulAction

abbrev image {G X : Type*} [Group G] [MulAction G X] {k p : ℕ}
    (e : Fin k ↪ X) (S : Sylow p (stabilizer G e)) : Subgroup G :=
  (S : Subgroup (stabilizer G e)).map (stabilizer G e).subtype

theorem exists_conjugate_into_sylow
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    {p : ℕ} [Fact p.Prime] (S : Sylow p (stabilizer G e))
    (g : G) (hg : orderOf g = p) (hfix : k ≤ (fixedBy X g).ncard) :
    ∃ c : G, c * g * c⁻¹ ∈ image e S := by
  classical
  let _ : Fintype (fixedBy X g) := Fintype.ofFinite _
  obtain ⟨a⟩ : Nonempty (Fin k ↪ fixedBy X g) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, Nat.card_fin] using hfix)
  let aX : Fin k ↪ X := a.trans (Function.Embedding.subtype _)
  obtain ⟨b, hb⟩ := isMultiplyPretransitive_iff.mp hk aX e
  have hb' (i : Fin k) : b • aX i = e i := DFunLike.congr_fun hb i
  let H := stabilizer G e
  have humem : b * g * b⁻¹ ∈ H := by
    apply Function.Embedding.ext
    intro i
    change (b * g * b⁻¹) • e i = e i
    rw [← hb' i, mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun x : X => b • x) (a i).property
  let u : H := ⟨b * g * b⁻¹, humem⟩
  have hu : orderOf u = p := by
    rw [← Subgroup.orderOf_coe u]
    exact (orderOf_injective (MulAut.conj b).toMonoidHom
      (MulAut.conj b).injective g).trans hg
  obtain ⟨d, hd⟩ := SemiregularSylowFixedSet.exists_conjugate_mem_sylow H S u hu
  refine ⟨(d : G) * b, ?_⟩
  have he : ((d : G) * b) * g * ((d : G) * b)⁻¹ =
      ((d * u * d⁻¹ : H) : G) := by
    change ((d : G) * b) * g * ((d : G) * b)⁻¹ =
      (d : G) * (b * g * b⁻¹) * (d : G)⁻¹
    group
  rw [he]
  exact Subgroup.mem_map_of_mem H.subtype hd

end FiveTransitive.TupleSemiregularFour

end CFSG

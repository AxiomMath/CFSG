module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutL2

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem card_inf_pglAction_le_nine {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (B : Subgroup (MulAut (PSL2 K))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card (B ⊓ (pglAction K).range : Subgroup (MulAut (PSL2 K))) ≤ 9 := by
  set E := (B ⊓ (pglAction K).range).comap (pglAction K)
  have hcardE : Nat.card E = Nat.card (B ⊓ (pglAction K).range : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) (KFacts.pglAction_injective (K := K))
    rw [Subgroup.map_comap_eq_self inf_le_right] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← hcardE]
  refine card_le_nine_of_pgl2 h3 E (fun x hx y hy => KFacts.pglAction_injective ?_)
    (fun x hx => KFacts.pglAction_injective ?_)
  · rw [map_mul, map_mul]
    exact hBc _ (Subgroup.mem_comap.mp hx).1 _ (Subgroup.mem_comap.mp hy).1
  · rw [map_pow, map_one]
    exact hB.2 _ (Subgroup.mem_comap.mp hx).1

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary

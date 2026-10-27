module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module Equiv

theorem leafCentralizer_holds : LeafCentralizer := by
  intro Γ _ _ Y K T T₀ B R hC
  obtain ⟨-, hYK, hKs, hT, hYeq, hO2, hBK, -, -, -, hBB, hBiso, -, -, -, -⟩ := hC
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hB : B = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [← hBB]
      refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hcomm ⟨x, hBK.le hx⟩ ⟨y, hBK.le hy⟩)
    obtain ⟨φ, hφs, -⟩ := hBiso
    have h6 : (⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.2 (by decide)⟩ :
        ↥(alternatingGroup (Fin 6))) ≠ 1 := by
      intro h
      have h' : swap 0 1 * swap 0 2 = (1 : Perm (Fin 6)) := congrArg Subtype.val h
      exact absurd h' (by decide)
    obtain ⟨x, hx⟩ := hφs ⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.2 (by decide)⟩
    have hx1 : x = 1 := Subtype.ext (by
      have hxB : (x : Γ) ∈ (⊥ : Subgroup Γ) := by rw [← hB]; exact x.2
      simpa using hxB)
    exact h6 (by rw [← hx, hx1, map_one])
  exact CFSG.Quasithin.H13.KG12618.inf_centralizer_eq_bot hYK hKs hnc hT hYeq hO2

end CFSG.Quasithin.H13.KG12617L52

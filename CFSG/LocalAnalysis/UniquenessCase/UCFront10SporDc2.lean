module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.Certificates.Kernel.SporLatDc2Sound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.KC.SLD2 CFSG.KC.E64F CFSG.QuasithinUnique.K1.SporadicPerm

theorem k105SporAt_of_dc2 {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
    [MulAction Γ (Fin n)] (C : Dc2Ctx) (hn : C.n = n) (D : Dc2Data) (els : List Γ)
    (hel : els.length = C.nl)
    (hL : ∀ l < C.nl, Good n (tab n (els.getD l 1)).toArray (C.L l))
    (hk : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k)
    (hN : Nat.card Γ = C.N1 * C.N2 * 2 ^ C.k) (hodd : ¬ 2 ∣ C.N1 * C.N2)
    (hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1) (h : dc2Check C D = true)
    (e : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) : K105SporAt s := by
  have hsound := dc2Check_sound C hn D els hel hL hk hN hsep h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf (Subgroup.closure {x | x ∈ els.take C.ns}) ⊤ := by
    refine ⟨le_top, IsPGroup.of_card hk, ?_⟩
    rw [show ((Subgroup.closure {x | x ∈ els.take C.ns}).subgroupOf ⊤).index =
      (Subgroup.closure {x | x ∈ els.take C.ns}).index from Subgroup.relIndex_top_right _]
    have hi := Subgroup.card_mul_index (Subgroup.closure {x | x ∈ els.take C.ns})
    rw [hk, hN, mul_comm (C.N1 * C.N2)] at hi
    rwa [Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hi]
  refine k105SporAt_of_index hS₀ (fun Z hZ _ m hm => ?_) e
  rcases hsound Z hZ with rfl | h3
  · left
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hm.symm.trans (one_mul _).symm)
  · right
    rw [hm, hk] at h3
    exact (Nat.Coprime.pow_right C.k (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Three
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isSylowTwoOf_inf_of_normal {S N K : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (hN : N.Normal)
    (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set Γ)) : IsSylowTwoOf (S ⊓ K) K := by
  have h1 : IsSylowTwoOf (S ⊓ N) N :=
    B6.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.2 hN).ge
  have h2 := B6.isSylowTwoOf_inf_normal h1 hKN hNK
  rwa [inf_assoc, inf_eq_right.2 hKN] at h2

theorem mem_of_commutes_sylow {K D : Subgroup Γ} (hK : L27 ↥K) (hD : IsSylowTwoOf D K) {z : Γ}
    (hzK : z ∈ K) (hzD : ∀ d ∈ D, d * z = z * d) : z ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' : IsSylowTwoOf (D.subgroupOf K) (⊤ : Subgroup ↥K) := isSylowTwoOf_subgroupOf_top' hD
  have h8 := hK.card2 _ hD'
  have hne : D.subgroupOf K ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h8
    omega
  obtain ⟨w, hwD, hw2, hwc⟩ := E217R3.exists_involution_mem_center_of_normal (T := D.subgroupOf K)
    (Y := D.subgroupOf K) hD'.2.1 le_rfl (fun t ht y hy => (D.subgroupOf K).mul_mem
      ((D.subgroupOf K).mul_mem ht hy) ((D.subgroupOf K).inv_mem ht)) hne
  have hw2' : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw2
    omega
  have key := centralizer_le_of_L27 hK hw2' hw1 hD' (fun d hd => hwc d hd) ⟨z, hzK⟩
    (Subtype.ext (hzD _ (Subgroup.mem_subgroupOf.1 hwD)).symm)
  exact Subgroup.mem_subgroupOf.1 key

end E217R4

end CFSG.Quasithin

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off12
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off13
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3CaseCentral
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Stmt

public section

namespace CFSG.Quasithin.Fan86

open Sigma3

theorem exists_orderOf_three {H : Type*} [Group H] [Finite H] {S : Subgroup H}
    (hcard : Nat.card H = 3 * Nat.card S) : ∃ x : H, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (hcard ▸ dvd_mul_right 3 _)

theorem sigma3PushingUp : Sigma3PushingUp := by
  intro H _ _ S hquot hS2 hcard hno
  have hsig : Sig3 H S := ⟨hS2, hcard, hquot⟩
  obtain ⟨x, hx⟩ := exists_orderOf_three hcard
  by_cases hQx : ∀ q ∈ oQ H, x * q = q * x
  · exact Or.inl (hsig.case_central hx hQx hno)
  · have h : Hyp3 H S x := ⟨hsig, hx, hQx, hno⟩
    obtain ⟨t, htS, htQ, ht2, htc, -⟩ := h.exists_t
    obtain ⟨T, hT, hTc, hTi, hTs⟩ := h.exists_perm4 htS htQ ht2 htc
    exact Or.inr ⟨T, q0Sub H x, hT, oQ_two.to_le q0Sub_le_Q, hTc, hTi, hTs⟩

theorem sigma3Aut : Sigma3Aut := by
  intro H _ _ S x f q hquot hS2 hcard hx hq hq2 hfq hno
  have hsig : Sig3 H S := ⟨hS2, hcard, hquot⟩
  by_cases hQx : ∀ y ∈ oQ H, x * y = y * x
  · exact hsig.zpowers_normal hx hQx
  · exfalso
    have hno' : ∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal →
        K = ⊥ := by
      intro K hKS hKc hKn
      refine hno K hKS (fun s hs => ?_) hKn
      have hmap := (Subgroup.characteristic_iff_map_le.1 hKc) f
      have hs' : s ∈ K.subgroupOf S := Subgroup.mem_subgroupOf.2 hs
      exact Subgroup.mem_subgroupOf.1 (hmap (Subgroup.mem_map_of_mem f.toMonoidHom hs'))
    have h : Hyp3 H S x := ⟨hsig, hx, hQx, hno'⟩
    exact no_aut_of_s4data h.s4Data hx f q hq hq2 hfq hno

end CFSG.Quasithin.Fan86

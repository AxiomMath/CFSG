module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartOne.FIS

open Equiv Equiv.Perm

theorem eq_top_of_normal_alternating {H : Type} [Group H] [Finite H] (N K : Subgroup H)
    [N.Normal] (hC : Subgroup.centralizer (N : Set H) = ⊥) (k : ℕ) (hk : 5 ≤ k) (hk6 : k ≠ 6)
    (e : N ≃* alternatingGroup (Fin k)) (hK : Nat.card (Perm (Fin k)) ≤ Nat.card K) :
    K = ⊤ := by
  have hinj : Function.Injective (MulAut.conjNormal (H := N) : H →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxC : x ∈ Subgroup.centralizer (N : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : H)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc n * x = x * n * x⁻¹ * x := by rw [h]
        _ = x * n := by group
    rw [hC] at hxC
    exact hxC
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k hk hk6
  have hle : Nat.card H ≤ Nat.card (Perm (Fin k)) :=
    calc Nat.card H ≤ Nat.card (MulAut N) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card (MulAut (alternatingGroup (Fin k))) := Nat.card_congr (MulAut.congr e).toEquiv
      _ = Nat.card (Perm (Fin k)) := (Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv).symm
  exact Subgroup.eq_top_of_le_card K (hle.trans hK)

end CFSG.RankThree.PartOne.FIS

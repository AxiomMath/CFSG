module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB21
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem false_of_confR (hA : F53Amalgam H M S) (h : ConfR δ μ U) : False := by
  obtain ⟨n, hn, hnδ, -⟩ := h.exists_not_Zv_le hA
  obtain ⟨fr⟩ := h.exists_frame hA
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have hcard := h.aZ_eq_card_img hA fr hn hnδ
  have h24 : aZ δ n = 2 ∨ aZ δ n = 4 := by
    rcases h.classify hA fr hn hnδ with e | e | e
    · left
      rw [hcard, e, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) (fun h => by
        have := Equiv.swap_eq_one_iff.1 h; exact absurd this (by decide))
    · left
      rw [hcard, e, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) (fun h => by
        have := Equiv.swap_eq_one_iff.1 h; exact absurd this (by decide))
    · right
      rw [hcard, e, O2.card_S5That]
  rcases h24 with h2 | h4
  · exact h.false_of_a2 hA ⟨n, hn, hnδ, h2⟩
  · exact h.false_of_a4 hA fun m hm hmδ =>
      (h.aZ_unif hA hδ hm hδ hn (Ne.symm hmδ) (Ne.symm hnδ)).trans h4

end ConfR

end CFSG.Quasithin.F53

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom

variable {G : Type} [Group G] [Finite G]

theorem hss26ResidualAt_holds {H M S : Subgroup G} (hA : F53Amalgam H M S) :
    Hss26ResidualAt H M := fun hb _ _ _ hSig hQ hR hQδ =>
  (F53.ConfR.false_of_confR hA ⟨hb, hSig, hQ, hR, hQδ⟩).elim

theorem hss26AAt_holds {H M S : Subgroup G} (hA : F53Amalgam H M S) : Hss26AAt H M :=
  hss26AAt_of_residual hA (hss26ResidualAt_holds hA)

end CFSG.Quasithin.F53.Stellmacher

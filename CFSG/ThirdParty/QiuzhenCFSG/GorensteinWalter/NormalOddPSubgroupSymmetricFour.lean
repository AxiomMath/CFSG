module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal odd-prime subgroups of `S₄`

Every normal odd-prime subgroup of a finite group isomorphic to `S₄` lies
in its alternating index-two subgroup and is therefore trivial by the
corresponding `A₄` result.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd-prime subgroup of a finite group isomorphic to `S₄` is
trivial. -/
public theorem normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
    {G : Type u} [Group G] [Finite G]
    (he : Nonempty (G ≃* Equiv.Perm (Fin 4)))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hPnormal : P.Normal) (hPp : IsPGroup p P) :
    P = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let e : G ≃* Equiv.Perm (Fin 4) := he.some
  let Q : Subgroup (Equiv.Perm (Fin 4)) := P.map e.toMonoidHom
  have hQnormal : Q.Normal := hPnormal.map e.toMonoidHom e.surjective
  have hQp : IsPGroup p Q := IsPGroup.map hPp e.toMonoidHom
  let A : Subgroup (Equiv.Perm (Fin 4)) := alternatingGroup (Fin 4)
  have hAnormal : A.Normal := by
    dsimp [A]
    infer_instance
  let q : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4) ⧸ A :=
    QuotientGroup.mk' A
  let Qbar : Subgroup (Equiv.Perm (Fin 4) ⧸ A) := Q.map q
  have hQcard_odd : Odd (Nat.card Q) := by
    rcases hQp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  have hQbar_dvd_Q : Nat.card Qbar ∣ Nat.card Q :=
    Subgroup.card_map_dvd (f := q) (H := Q)
  have hQbar_dvd_two : Nat.card Qbar ∣ 2 := by
    have hquot_card : Nat.card (Equiv.Perm (Fin 4) ⧸ A) = 2 := by
      rw [← A.index_eq_card]
      exact alternatingGroup.index_eq_two
    have hdvd := Subgroup.card_subgroup_dvd_card Qbar
    rwa [hquot_card] at hdvd
  have hQbar_card : Nat.card Qbar = 1 := by
    have hcoprime : Nat.Coprime 2 (Nat.card Q) :=
      hQcard_odd.coprime_two_right.symm
    exact Nat.eq_one_of_dvd_coprimes hcoprime hQbar_dvd_two hQbar_dvd_Q
  have hQbar_bot : Qbar = ⊥ :=
    Subgroup.eq_bot_of_card_eq (H := Qbar) hQbar_card
  have hQleA : Q ≤ A := by
    have hQleKer : Q ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := Q) (f := q)).mp hQbar_bot
    simpa [q, A, QuotientGroup.ker_mk'] using hQleKer
  let QA : Subgroup A := Q.subgroupOf A
  have hQAnormal : QA.Normal := hQnormal.subgroupOf A
  have hQAp : IsPGroup p QA :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQleA).symm
  have hQAbot : QA = ⊥ :=
    normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
      ⟨MulEquiv.refl (alternatingGroup (Fin 4))⟩ p hp hpodd
      QA hQAnormal hQAp
  have hQbot : Q = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxQA : (⟨x, hQleA hx⟩ : A) ∈ QA :=
      Subgroup.mem_subgroupOf.mpr hx
    have hx_one : (⟨x, hQleA hx⟩ : A) = 1 := by
      rw [hQAbot] at hxQA
      exact Subgroup.mem_bot.mp hxQA
    exact congrArg Subtype.val hx_one
  have hPleKer : P ≤ e.toMonoidHom.ker := by
    have hmap : P.map e.toMonoidHom = ⊥ := by simpa [Q] using hQbot
    exact (Subgroup.map_eq_bot_iff (H := P) (f := e.toMonoidHom)).mp hmap
  apply le_bot_iff.mp
  intro x hx
  have hxker : e x = 1 := hPleKer hx
  have hxone : x = 1 := e.injective (by simpa using hxker)
  simp [hxone]

end CFSG.GorensteinWalter

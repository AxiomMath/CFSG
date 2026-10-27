module

public import CFSG.RankThree.PartOne.FOC.AltBlocks
public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.FOC.Cases
import CFSG.RankThree.PartOne.FOC.Equiv
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut)

theorem mem_innerAut_of_not_dvd_outer {T : Type} [Group T] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ Nat.card (Outer T)) {β : MulAut T} (hβ : β ^ p = 1) : β ∈ innerAut T := by
  have h1 : (QuotientGroup.mk β : Outer T) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk β : Outer T) ∣ p := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hp).mp h2 with h | h
  · have h3 : β ∈ inner T := (QuotientGroup.eq_one_iff β).mp (orderOf_eq_one_iff.mp h)
    exact h3
  · exact absurd (h ▸ orderOf_dvd_natCard _) hnd

theorem fieldInnerT_alt {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 5 ≤ n)
    (hnab : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a) :
    FieldInnerT p (alternatingGroup (Fin n)) := by
  intro hLR x β E hxp hβp hβx hβinn hE hxN hxnot hLie
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hcen : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := center_eq_bot_of_nonab hs hnab
  have hβ : β ∈ innerAut (alternatingGroup (Fin n)) :=
    mem_innerAut_of_not_dvd_outer hp (not_dvd_outer_alternating hp (by omega) hn) hβp
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨hbp, hfix, hbx⟩ := inner_case hcen hb hβp hβx
  rw [hfix] at hE
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact hxnot (Alt.mem_sup_centralizer_of_component_alt hodd hbp hxp hbx hE)

theorem fieldInnerAlt : FieldInnerAlt := by
  intro T _ _ n p hn hp hp5 _ hnab ⟨e⟩
  have hnab' : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact FieldInnerT.of_mulEquiv e hp (fieldInnerT_alt hp hp5 hn hnab')

end CFSG.RankThree.PartOne.FOC

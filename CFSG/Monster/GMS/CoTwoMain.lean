module

public import CFSG.Monster.GMS.CoTwoCentral
public import CFSG.Monster.GMS.LeechCohTwo
import CFSG.Monster.GMS.Griess13.ChecksUniqueness
import CFSG.Monster.GMS.Leech.Pairs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem coTwoPerfect_of_facts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co2McLFacts) : CoTwoPerfect a z₀ := by
  intro t t' ht ht' hcomm hmul
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (h.gms t' ht')
  have htQ : t ∈ leechQ t' := h.mem_leechQ_of_isConj_mul ht ht' hcomm hmul
  exact L.commutator_centralizer_inf_one hF
    (L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem ht' htQ ht))

theorem coTwoIrreducible_of_facts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co2McLFacts) : CoTwoIrreducible a z₀ := by
  intro t t' ht ht' hcomm hmul N htN ht'N hNle hinv
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (h.gms t' ht')
  have htQ : t ∈ leechQ t' := h.mem_leechQ_of_isConj_mul ht ht' hcomm hmul
  exact L.irreducible_centralizer_inf_one hF
    (L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem ht' htQ ht)) N htN ht'N hNle hinv

theorem fourAPerfect_of_facts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co2McLFacts) : FourAPerfect a z₀ := by
  intro b x hb hx
  have hx' : x ∈ fourANbr a z₀ b := hx
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨hbQ, hxQ⟩ := h.fourANbr_data hb hx'
  have hwB : IsConj z₀ ((b * x) ^ 2) := hx'.2.2
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (h.gms _ hwB)
  have hbL : b ∈ L.typeSet 0 := L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem hwB hbQ hb)
  have hxL : x ∈ L.typeSet 0 := L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem hwB hxQ hx'.1)
  have hsq : q₀ (L.vec (b * x)) = 1 :=
    (L.mul_self_eq_z_iff (mul_mem hbQ hxQ)).1 (pow_two (b * x)).symm
  rw [L.vec_mul b hbQ x hxQ] at hsq
  exact L.commutator_centralizer_inf_two hF hbL hxL (Leech.mem_co1Orbit_one_of_q₀_eq_one hsq)
    (centralizer_inf_le_centralizer_pow b x 2)

end CFSG.Monster.GMS

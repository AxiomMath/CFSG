module

public import CFSG.Monster.GMS.LeechOddSetup
public import CFSG.Monster.GMS.Facts.Section4Coh

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module.Odd (threeC_no_two threeC_no_twoA)

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem threeC_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x t : G}
    (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .threeC)
    (ht : t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (ht2 : orderOf t = 2) : IsConj z₀ t := by
  obtain ⟨⟨hxa, hxb, hodd, w, hwH, hwB⟩, hk⟩ := hx
  have hY : IsOddPair a w b x := IsOddPair.of_mem_inf hb hxa hxb.symm hodd hwH
  have hty : LeechOddType w b x 1 := hk w hwH hwB
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hwB
  have hyp := LeechOdd.oddPairHyp I hG hwB hY L
  have hot := LeechOdd.oddType I hG hwB hY L hty
  obtain ⟨h, hh, hth⟩ :=
    LeechOdd.exists_conj_mem_centralizer I hG hwB hY (k := 1) (by decide) hty ht ht2
  have hconj : IsConj t (h * t * h⁻¹) := isConj_iff.2 ⟨h, rfl⟩
  have ht₁H : h * t * h⁻¹ ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) := mul_mem (mul_mem hh ht) (inv_mem hh)
  have ht₁2 : orderOf (h * t * h⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ht2
  refine IsConj.trans ?_ hconj.symm
  by_cases hQ : h * t * h⁻¹ ∈ leechQ w
  · rcases orderOf_eq_two_mem_leechQ I.sls I.tableV I.leech hG hwB hQ ht₁2 with h1 | h1 | h1
    · rw [h1]
      exact hwB
    · exfalso
      have hq0 : h * t * h⁻¹ ∈ L.typeSet 0 := S365.mem_typeSet_zero_of_isConj I hG hwB L hQ h1
      have hvec := (LeechOdd.mem_inf_iff_vec I hG hwB hY L hQ).1 ht₁H
      exact threeC_no_two hyp hot _ hvec hq0.2
    · exact h1
  · rcases s31_five I.sls I.tableV I.leech hG I.leechInv ht₁2 with h1 | h1
    · exfalso
      have hlift := S365.isLeechCentralLift_of_isConj I hG hwB hth h1 hQ
      exact threeC_no_twoA hyp hot _ (LeechOdd.phi_mem_inf hY L hth ht₁H)
        (L.isCo1TwoA_phi co1InvolutionFacts hlift)
    · exact h1

theorem threeCInvolutions_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ThreeCInvolutions a z₀ := by
  intro b x t hb hx ht ht2
  have h2B := threeC_isConj I hG hb hx ht ht2
  obtain ⟨⟨hxa, hxb, hodd, w, hwH, hwB⟩, -⟩ := hx
  have hYt : IsOddPair a t b x := IsOddPair.of_mem_inf hb hxa hxb.symm hodd ht
  obtain ⟨hbQ, hxQ, -⟩ := not_mem_leechQ_of_odd hG.1.1 hYt
  have hbt : b * t = t * b :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).1).symm
  have hxt : x * t = t * x :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2).symm
  refine ⟨h2B, ?_, ?_⟩
  · rw [hbt]
    exact (S365.isConj_mul_iff I hG h2B hb hbt).2 hbQ
  · rw [hxt]
    exact (S365.isConj_mul_iff I hG h2B hxa hxt).2 hxQ

theorem threeCSingleClass_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ThreeCSingleClass a z₀ := by
  intro b x t s hb hx ht hs ht2 hs2
  have ht2B := threeC_isConj I hG hb hx ht ht2
  have hs2B := threeC_isConj I hG hb hx hs hs2
  obtain ⟨hmem, -⟩ := hx
  exact s348_transitive I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hb hmem ht hs ht2B
    hs2B

end CFSG.Monster.GMS

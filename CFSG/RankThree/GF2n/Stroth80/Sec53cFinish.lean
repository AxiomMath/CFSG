module

public import CFSG.RankThree.GF2n.Stroth80.Sec53cShared

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem inf_QB_inf_QB_le_vone (Q B C V : Subgroup G) :
    QB B ⊓ QB C ⊓ Q ≤ Vone Q B C V := by
  intro x hx
  obtain ⟨⟨hxB, hxC⟩, hxQ⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxQ, hxB⟩),
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩)⟩

theorem stroth53b_of_51_decomp
    (h51 : Stroth51Statement)
    (hprod : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
          ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b)
    (hboxB : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ⁅QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, LB M Q B ⊓ hc.CN t⁆ ≤
          Sec8V1 M Q Z B t r)
    (hboxC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ⁅QB B ⊓ Sec8W1 M Q Z B t r, LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤
          Sec8V1 M Q Z B t r) :
    Stroth53bStatement := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane C N V W₁ V₁ hC hN hV hV₁ hW₁
  subst hC hN hV hV₁ hW₁
  have hprod' : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b :=
    hprod G M Q Z B hc n t hs hsp r hr hplane
  refine ⟨hprod', ?_⟩
  have hcomm := sec53b_comm_of_51 h51 hc hs hsp hr hplane hprod'
    (hboxB G M Q Z B hc n t hs hsp r hr hplane)
    (hboxC G M Q Z B hc n t hs hsp r hr hplane)
  intro s hsN x hxW
  rw [← commutatorElement_inv]
  exact (Sec8V1 M Q Z B t r).inv_mem
    ((Subgroup.commutator_le.mp hcomm) x hxW s hsN)

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Sporadic.ONOddCore.OuterEmbeds
public import CFSG.Sporadic.ONOddCore.LocalAutOrders

public section

namespace CFSG.Sporadic.SteinbergBI

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_Pv_dvd_four : Nat.card (Outer Pv) ∣ 4 := by
  have h := CFSG.LocalAnalysis.ComponentInitial.card_outer_dvd_card_outer Mv
    Mv_conjugacyInvariant fun φ hφ => MonoidHom.mem_range.1
      (r3e_on_involution_centralizer_pointwise_automorphisms_inner.2.2 φ
        fun m hm => hφ m (mem_Mv.2 hm))
  rwa [Nat.card_congr (equivalence (Subgroup.subgroupOfEquivOfLe onM_le)).toEquiv,
    card_outer_M] at h

theorem card_outer_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) := by
  obtain ⟨⟨f, -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e
  exact Nat.card_congr f.toEquiv

theorem cti_on_outer_order_divides_four
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* Blueprint.NativeSporadic.ON)) : Nat.card (Outer T) ∣ 4 := by
  obtain ⟨e⟩ := hT
  rw [card_outer_eq_of_mulEquiv (e.trans onEquivPv)]
  exact card_outer_Pv_dvd_four

end CFSG.Sporadic.SteinbergBI

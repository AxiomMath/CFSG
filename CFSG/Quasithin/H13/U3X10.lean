module

public import CFSG.Quasithin.H13.U3X10L
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.H13.U3X10U

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem card_quasithinG2_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(quasithinG2 K) = 12096 := by
  have : CharP K 2 := Vol2.KGNat.charP_two_of_card (n := 1) (by norm_num) (by rw [hK]; norm_num)
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    Vol2.KGNat.card_cayleyGroup, hK]
  norm_num

theorem not_isG2Block_of_A6 {T L V : Subgroup G} (hTL : T ≤ normalizer (L : Set G))
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hA6 : Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6)))) : ¬ H13.IsG2Block L := by
  rintro ⟨-, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun v hv => ((mem_reducedAggregate' (hV.1 hv)).2.1 k hk).symm
  have h1 := card_autOn_dvd hLV hO
  obtain ⟨e6⟩ := hA6
  rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin, Nat.card_congr e.toEquiv] at h1
  have h2 : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ ∣ Nat.card ↥(quasithinG2 K) :=
    Subgroup.card_dvd_of_le (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
  rw [card_quasithinG2_two hK] at h2
  have h3 := h1.trans h2
  norm_num [Nat.factorial] at h3

theorem stmt13_3_10_of
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1334 : A6.Stmt13_3_4)
    (hC137 : C137Statement) (h13227 : Stmt13_2_2_7) (hG2 : Stmt13_3_10G2) : Stmt13_3_10 := by
  intro G _ _ T L V Lp hH hV hZV hLp1 hLp2
  obtain ⟨-, ⟨hTL, -, -, -⟩, -, -⟩ := h1332 G T L hH L hH.faithful
  refine ⟨fun hcase => ?_, fun hlin => ?_⟩
  · rcases hcase with hA6 | hU3
    · exact ⟨(h13227 G T L V Lp hH hV hZV hLp1 hLp2 hA6).elim Or.inl
        (fun h => Or.inr (Or.inl h)), fun hB => (not_isG2Block_of_A6 hTL hV hA6 hB).elim⟩
    · have hLp := hLp2 (not_isHatA6_of_psu hU3)
      subst hLp
      exact ⟨(stmt13_3_10_U33 h1332 hC137 hH hV hU3).elim Or.inl
        (fun h => Or.inr (Or.inr h)), hG2 G T L V _ hH hV hZV rfl hU3⟩
  · have hnh : ¬ A6.IsHatA6 L := by
      rintro ⟨-, h3, ⟨e⟩⟩
      obtain ⟨e'⟩ := nonempty_equiv_SL32_of_lieModel hlin
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      rw [Nat.card_congr e'.toEquiv, HSType.card_SL_three_two, h3, Nat.card_congr e.toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
      norm_num [Nat.factorial] at h2
    rw [hLp2 hnh]
    exact stmt13_3_10_L32 h1332 h1222 h1334 hC137 hH hV hZV hlin

end CFSG.Quasithin.H13.U3

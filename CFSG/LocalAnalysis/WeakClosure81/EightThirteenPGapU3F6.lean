module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapPull
import CFSG.GH74.Uniqueness.Bender.Sylow2Special
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.StronglyEmbedded.BenderU3Commutator

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)
open scoped commutatorElement

theorem orderFiveData_of_isU3 {G : Type} [Group G] [Finite G]
    (h : IsU3 G 2) (S : Sylow 2 G) : OrderFiveData (S : Subgroup G) := by
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 h
  let e : G ≃* CFSG.Theory.Comparator.PSU3Model 2 := e₁
  have hB : BenderType G 2 3 5 := by
    have h_eq : (2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1) = 5 := by norm_num
    simpa [h_eq] using BenderType.unitary 2 le_rfl e
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hcard_cartan : Nat.card (cartan (S : Subgroup G) t) = 15 := by
    rw [hc.card_cartan]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨d, hd_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cartan (S : Subgroup G) t)) 5 (by
    rw [hcard_cartan]
    norm_num)
  have hd_mem : (d : G) ∈ cartan (S : Subgroup G) t := d.2
  have hd_N : (d : G) ∈ normalizer ((S : Subgroup G) : Set G) :=
    cartan_le_borel (S : Subgroup G) t hd_mem
  have hd_pow : (d : G) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (d : G)
    rwa [orderOf_coe d, hd_order] at this
  have hd_ne_one : (d : G) ≠ 1 := by
    intro hd1
    have : d = 1 := Subtype.ext hd1
    rw [this, orderOf_one] at hd_order
    norm_num at hd_order
  refine ⟨(d : G), hd_N, hd_pow, ?_, ?_, ?_⟩
  · intro x hx hdx
    exact hB.fixedPointFree_unitary S hc.sq_eq_one hc.not_mem hd_mem hd_ne_one hx hdx
  · intro x hx y hy
    have hcommutator : ⁅(S : Subgroup G), (S : Subgroup G)⁆ = rootCenter (S : Subgroup G) :=
      (hB.lemma_3_5_a_unitary S).1
    have hxy : ⁅x, y⁆ ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [hcommutator, commutatorElement_def] at hxy
    exact hxy.2
  · intro z hz
    have hS_card : Nat.card (S : Subgroup G) = 64 := by
      rw [hc.card_eq]
      norm_num
    have hZ_card : Nat.card (rootCenter (S : Subgroup G)) = 4 := by
      rw [hc.card_center]
      norm_num
    have hS_ne_Z : (S : Subgroup G) ≠ rootCenter (S : Subgroup G) := by
      intro h_eq
      rw [h_eq, hZ_card] at hS_card
      norm_num at hS_card
    have h_exists_r : ∃ r ∈ (S : Subgroup G), r ∉ rootCenter (S : Subgroup G) := by
      by_contra h
      have hle : (S : Subgroup G) ≤ rootCenter (S : Subgroup G) := by
        intro r hr
        by_contra hrZ
        exact h ⟨r, hr, hrZ⟩
      have heq : (S : Subgroup G) = rootCenter (S : Subgroup G) :=
        le_antisymm hle inf_le_left
      exact hS_ne_Z heq
    obtain ⟨r, hr_mem, hr_not_mem⟩ := h_exists_r
    have honto := CFSG.StronglyEmbedded.BenderCentre.u3CommutatorOntoStatement_holds
      G 2 (by norm_num) ⟨e₁⟩ S r hr_mem hr_not_mem z hz
    obtain ⟨s, hs_mem, hs_comm⟩ := honto
    exact ⟨s, hs_mem, r, hr_mem, by rw [← hs_comm, commutatorElement_def]⟩

theorem borelGL32SylowOn_shapeU3 : BorelGL32SylowOn ShapeU3 :=
  borelGL32SylowOn_of_kills ShapeU3 fun Y _ _ L hL S hSy => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact borelKills_sylow_of_orderFive (orderFiveData_of_isU3 hL.2 hSy.toSylow)

end CFSG.LocalAnalysis.WeakClosure81

end

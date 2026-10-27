module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BCard
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace B

theorem false_of_simple_index_five {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 360) {W : Subgroup Q} (hW : W.index = 5) : False := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W.normalCore with h | h
  · have := W.index_normalCore_le_factorial_index
    rw [h, Subgroup.index_bot, hQ, hW] at this
    norm_num [Nat.factorial] at this
  · have hW' : W = ⊤ := top_le_iff.mp (h ▸ W.normalCore_le)
    rw [hW', Subgroup.index_top] at hW
    omega

theorem center_le_of_index_fifteen {Xb : Type*} [Group Xb] [Finite Xb]
    (hq : CFSG.IsQuasisimple Xb) (hc : Nat.card (Subgroup.center Xb) = 3)
    (hQ : Nat.card (Xb ⧸ Subgroup.center Xb) = 360) {U : Subgroup Xb} (hU : U.index = 15) :
    Subgroup.center Xb ≤ U := by
  by_contra hnle
  have hinf : U ⊓ Subgroup.center Xb = ⊥ := by
    have hdvd : Nat.card ↥(U ⊓ Subgroup.center Xb) ∣ Nat.card (Subgroup.center Xb) := by
      have := Subgroup.card_dvd_of_le (inf_le_right : U ⊓ Subgroup.center Xb ≤ Subgroup.center Xb)
      exact this
    rw [hc] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : U ⊓ Subgroup.center Xb = Subgroup.center Xb :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hc])
      exact hnle (heq ▸ inf_le_left)
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal U
    (Subgroup.center Xb)
  rw [hinf, hc] at hcard
  have h1 : Nat.card (↥(⊥ : Subgroup Xb)) = 1 := by simp
  rw [h1, mul_one] at hcard
  have h2 := Subgroup.index_mul_card (H := U)
  have h3 := Subgroup.index_mul_card (H := U ⊔ Subgroup.center Xb)
  rw [hU] at h2
  rw [hcard] at h3
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hidx : (U ⊔ Subgroup.center Xb).index = 5 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos (by norm_num : 0 < 3)) ?_
    nlinarith
  have hW : ((U ⊔ Subgroup.center Xb).map (QuotientGroup.mk' (Subgroup.center Xb))).index = 5 := by
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right)]
    exact hidx
  have : IsSimpleGroup (Xb ⧸ Subgroup.center Xb) := hq.2.1
  exact false_of_simple_index_five hQ hW

theorem card_quot_of_isHat {Xb : Type} [Group Xb] [Finite Xb]
    (hHat : IsHat Xb (alternatingGroup (Fin 6))) :
    Nat.card Xb = 1080 ∧ Nat.card (Xb ⧸ Subgroup.center Xb) = 360 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := hHat
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hQ : Nat.card (Xb ⧸ Subgroup.center Xb) = 360 := by
    rw [Nat.card_congr e.toEquiv, hA6]
  refine ⟨?_, hQ⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Xb), hQ, hc]

variable {G : Type} [Group G] [Finite G]

theorem oTwoZIn_le_of_relIndex_fifteen {X U : Subgroup G}
    (hHat : IsHat (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6)))
    (hQU : pCoreOf 2 X ≤ U) (hidx : U.relIndex X = 15) : oTwoZIn X ≤ U := by
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  obtain ⟨-, hQ⟩ := card_quot_of_isHat hHat
  have hker : CFSG.pCore 2 ↥X ≤ U.subgroupOf X := fun x hx => hQU (mem_pCoreOf_of_mem_pCore hx)
  have hidx' : ((U.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).index = 15 := by
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])]
    exact hidx
  have hcen := center_le_of_index_fifteen hHat.1 hHat.2.1 hQ hidx'
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨u, hu, hπ⟩ := hcen hy
  have hmem : u⁻¹ * y ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥X), MonoidHom.mem_ker, map_mul, map_inv, hπ,
      inv_mul_cancel]
  have h := (U.subgroupOf X).mul_mem hu (hker hmem)
  rw [mul_inv_cancel_left] at h
  exact h

theorem exists_orderOf_three_mem_oTwoZIn {X : Subgroup G}
    (hHat : IsHat (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6))) :
    ∃ z : G, z ∈ oTwoZIn X ∧ orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨zc, hzc⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X))) 3
      (by rw [hHat.2.1])
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (zc : ↥X ⧸ CFSG.pCore 2 ↥X)
  have hyZ : (y : G) ∈ oTwoZIn X := ⟨y, by simp [hy], rfl⟩
  have h3 : 3 ∣ orderOf y := by
    have h1 : orderOf (zc : ↥X ⧸ CFSG.pCore 2 ↥X) = 3 := by rw [Subgroup.orderOf_coe, hzc]
    rw [← h1, ← hy]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) y
  have hz : orderOf ((y : G) ^ (orderOf (y : G) / 3)) = 3 := by
    have h3' : 3 ∣ orderOf (y : G) := by rwa [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos _).ne' h3'
  refine ⟨(y : G) ^ (orderOf (y : G) / 3), ?_, hz⟩
  exact Subgroup.pow_mem _ hyZ _

end B

end S15223P4

end CFSG.Quasithin

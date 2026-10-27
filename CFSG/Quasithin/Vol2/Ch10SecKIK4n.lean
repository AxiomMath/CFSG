module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4m

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem card_perm_seven : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem comap_eq_alternatingGroup {F : Type*} [Group F] {π : Equiv.Perm (Fin 7) →* F}
    (hπ : Function.Bijective π) {S : Subgroup F} (hS : Nat.card ↥S = 2520) :
    S.comap π = alternatingGroup (Fin 7) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h := Subgroup.card_mul_index (S.comap π)
  rw [card_comap_of_bijective hπ, hS, card_perm_seven] at h
  omega

theorem map_autOnHom_eq {J X W : Subgroup G} (hJN : J ≤ Subgroup.normalizer (W : Set G))
    (hXJ : X ≤ J) :
    (X.subgroupOf J).map (InternalSec.autOnHom hJN) = (autOn X W).subgroupOf (autOn J W) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Setup.mem_autOn_iff.2 ⟨⟨x, hJN x.2⟩, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · intro hy
    obtain ⟨g, hgX, hg⟩ := Setup.mem_autOn_iff.1 hy
    refine ⟨⟨g, hXJ hgX⟩, Subgroup.mem_subgroupOf.2 hgX, Subtype.ext ?_⟩
    rw [← hg]
    rfl

variable [Finite G]

theorem card_autOn_sylow {J S W : Subgroup G} [IsMulCommutative ↥W]
    (hJN : J ≤ Subgroup.normalizer (W : Set G)) (hS : IsSylowTwoOf S J)
    (hX : Nat.card ↥(autOn J W) = 2520) : Nat.card ↥(autOn S W) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSJ : S ≤ J := hS.1
  set Q := (autOn S W).subgroupOf (autOn J W) with hQ
  have hQc : Nat.card ↥Q = Nat.card ↥(autOn S W) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A4.autOn_mono hSJ)).toEquiv
  have hodd : ¬ 2 ∣ Q.index := by
    intro h
    apply hS.2.2
    rw [hQ, ← map_autOnHom_eq hJN hSJ] at h
    exact h.trans (Subgroup.index_map_dvd _ (InternalSec.autOnHom_surjective hJN))
  have hp : IsPGroup 2 ↥(autOn S W) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hgS, rfl⟩ := Setup.mem_autOn_iff.1 hx
    obtain ⟨k, hk⟩ := hS.2.1 ⟨g, hgS⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hg1 : (g : Subgroup.normalizer (W : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hg1, map_one]
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h := Subgroup.card_mul_index Q
  rw [hQc, ha, hX] at h
  have hodd' : Odd Q.index := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
  obtain ⟨h3, -⟩ := SecA.two_pow_mul_odd_inj (n := a) (a := 3) hodd' (by decide : Odd 315)
    (by rw [h]; norm_num)
  rw [ha, h3]
  norm_num

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5e
public import CFSG.Quasithin.Vol2.Ch11SecA04Star
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Vol2.Ch10SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem isQuasisimple_alt7 : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 7)) := by
  have := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  have ha : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hb : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 3 ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  set a : ↥(alternatingGroup (Fin 7)) := ⟨_, ha⟩
  set b : ↥(alternatingGroup (Fin 7)) := ⟨_, hb⟩
  have hab : a * b ≠ b * a := by
    intro h
    have h1 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2 * (Equiv.swap 0 1 * Equiv.swap 0 3) =
        Equiv.swap 0 1 * Equiv.swap 0 3 * (Equiv.swap 0 1 * Equiv.swap 0 2) :=
      congrArg Subtype.val h
    revert h1
    decide
  have hperf : Group.IsPerfect ↥(alternatingGroup (Fin 7)) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(alternatingGroup (Fin 7)))
      with h | h
    · exfalso
      have : ⁅a, b⁆ ∈ commutator ↥(alternatingGroup (Fin 7)) :=
        Subgroup.commutator_mem_commutator trivial trivial
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact hab this
    · exact ⟨h⟩
  let e : ↥(alternatingGroup (Fin 7)) ⧸ Subgroup.center ↥(alternatingGroup (Fin 7)) ≃*
      ↥(alternatingGroup (Fin 7)) :=
    (QuotientGroup.quotientMulEquivOfEq center_alt7).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

theorem three_dvd_card_alt7 : 3 ∣ Nat.card ↥(alternatingGroup (Fin 7)) := by
  have ha : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h3 : orderOf (⟨_, ha⟩ : ↥(alternatingGroup (Fin 7))) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (0 : Fin 7)) (by decide) (by decide)
      (by decide)).orderOf
  rw [← h3]
  exact orderOf_dvd_natCard _

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem mem_J_of_orderOf_three (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h318 : A318Facts) (h36' : A36ForSQTK) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo)
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥(alternatingGroup (Fin 7))) {y : G}
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hy3 : orderOf y = 3) : y ∈ J := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hS : SQTKGroup ↥(Subgroup.centralizer ({w} : Set G)) :=
    InternalSec.sqtkGroup_of_localSQTK hK (pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq)
  have hSQ := SQTKHyp.of_sqtkGroup _ hS
  have hJc := subgroupOf_mem_cComp c.mem
  obtain ⟨e₀⟩ := Ch11.SecA.quotPCore_subgroupOf_equiv (L := J) c.J_le
  set e := e₀.trans eJ with he
  have hQ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_alt7
  have hrank : 1 < CFSG.Open.pRank 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))) := by
    rw [Ch11.SecA.pRank_subgroupOf_eq c.J_le Nat.prime_three (by norm_num),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eJ]
    have := C1GN.two_le_pRank_alt7
    omega
  have hconc := a318 h318 hS (h36' _ hSQ) (a38ForSQTK_of_cat h38 _ hSQ) hJc hQ Nat.prime_three
    (by norm_num) hrank
  set y' : ↥(Subgroup.centralizer ({w} : Set G)) := ⟨y, hy⟩
  have hy'3 : orderOf y' = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  suffices hy' : y' ∈ J.subgroupOf (Subgroup.centralizer ({w} : Set G)) from
    Subgroup.mem_subgroupOf.mp hy'
  have hZ' : Subgroup.center (↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G))) ⧸
      CFSG.pCore 2 ↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G)))) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [center_alt7] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have h3 : 3 ∣ Nat.card (↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G))) ⧸
      CFSG.pCore 2 ↥(J.subgroupOf (Subgroup.centralizer ({w} : Set G)))) := by
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alt7
  obtain ⟨ψ, hψ, hψk⟩ := Ch11.SecA.exists_starHom hQ hZ' h3
  set ψ' := e.toMonoidHom.comp ψ with hψ'
  have hψ's : Function.Surjective ψ' := e.surjective.comp hψ
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3', -⟩
  · rw [h1]
    exact Subgroup.subset_closure ⟨trivial, 1, by rw [pow_one]; exact hy'3⟩
  · exfalso
    obtain ⟨s, q, -, ⟨r, k, -, -, -, hPSL⟩, -⟩ := h2
    exact hK7 _ s r k hPSL ψ' hψ's
  · exfalso
    have hc := hE _ h3'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center
      ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G)))))) 3 (by rw [hc])
    have hzc : ψ' (z : ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))))) ∈
        Subgroup.center ↥(alternatingGroup (Fin 7)) :=
      Subgroup.map_center_le_center hψ's ⟨_, z.2, rfl⟩
    rw [center_alt7, Subgroup.mem_bot] at hzc
    have h1 : ψ z = 1 := by
      have := congrArg e.symm hzc
      rwa [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        map_one] at this
    obtain ⟨k, hk⟩ := hψk _ h1
    have h2 : orderOf (z : ↥(starImage 3 (J.subgroupOf (Subgroup.centralizer ({w} : Set G))))) ∣
        2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_coe, hz] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC

module

import CFSG.GroupTheory.PermFinThree
public import CFSG.Quasithin.Background.E1Defs
import CFSG.Quasithin.Background.E1Invariance
import CFSG.Quasithin.Background.E1Sec3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem oTwoPTwo_perm_fin_three :
    CFSG.Quasithin.E1.oTwoPTwo (Equiv.Perm (Fin 3)) 3 = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.Quasithin.E1.oTwoPTwo_eq_top_of_series
    (N₂ := ⊥) (N₂p := CFSG.pCore 3 (Equiv.Perm (Fin 3))) ?_ ?_ ?_
  · exact IsPGroup.of_card (n := 0) (by simp)
  · intro x hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 3))) ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro q
    refine ⟨1, ?_⟩
    have hindex : (alternatingGroup (Fin 3)).index = 2 := alternatingGroup.index_eq_two
    have hq2 : q ^ 2 ∈ alternatingGroup (Fin 3) :=
      Subgroup.pow_mem_of_index_ne_zero_of_dvd
        (H := alternatingGroup (Fin 3))
        (by rw [hindex]; norm_num) q
        (n := 2) (by
          intro m hm0 hm2
          have hm2' : m ≤ 2 := by simpa [hindex] using hm2
          interval_cases m <;> norm_num)
    simp [CFSG.GroupTheory.pCore_three_perm_fin_three]

private noncomputable def bar2PermFinThree :
    ((Equiv.Perm (Fin 3)) ⧸ CFSG.pCore 2 (Equiv.Perm (Fin 3))) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq CFSG.GroupTheory.pCore_two_perm_fin_three).trans
    QuotientGroup.quotientBot

private theorem bar2PermFinThree_mk (x : Equiv.Perm (Fin 3)) :
    bar2PermFinThree (QuotientGroup.mk' (CFSG.pCore 2 (Equiv.Perm (Fin 3))) x) = x :=
  rfl

private theorem pCore_three_bar2_perm_fin_three :
    CFSG.pCore 3 ((Equiv.Perm (Fin 3)) ⧸ CFSG.pCore 2 (Equiv.Perm (Fin 3))) =
      (alternatingGroup (Fin 3)).map bar2PermFinThree.symm.toMonoidHom := by
  have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 3 bar2PermFinThree
  rw [CFSG.GroupTheory.pCore_three_perm_fin_three] at h
  apply (CFSG.Quasithin.E1.map_inj_mulEquiv bar2PermFinThree).mp
  rw [Subgroup.map_map, h]
  simp

private theorem bar2PermFinThree_barO2 (B : Subgroup (Equiv.Perm (Fin 3))) :
    (CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B).map
        bar2PermFinThree.toMonoidHom = B := by
  rw [show CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B =
      B.map (QuotientGroup.mk' (CFSG.pCore 2 (Equiv.Perm (Fin 3)))) from rfl,
    Subgroup.map_map]
  have hcomp : bar2PermFinThree.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pCore 2 (Equiv.Perm (Fin 3)))) = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact bar2PermFinThree_mk x
  rw [hcomp, Subgroup.map_id]

theorem eOne_perm_fin_three_of_card_eq_two {B : Subgroup (Equiv.Perm (Fin 3))}
    (hB : Nat.card B = 2) : CFSG.Quasithin.E1.EOne (Equiv.Perm (Fin 3)) B := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3ne : alternatingGroup (Fin 3) ≠ ⊥ := by
    intro hbot
    have hc : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ∈
        alternatingGroup (Fin 3) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    rw [hbot] at hc
    have hc1 : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    exact hc1 (Subgroup.mem_bot.mp hc)
  refine ⟨3, Nat.prime_three, by norm_num, oTwoPTwo_perm_fin_three, ?_, ?_, ?_⟩
  · intro hbot
    have hmap : (CFSG.pCore 3 ((Equiv.Perm (Fin 3)) ⧸
        CFSG.pCore 2 (Equiv.Perm (Fin 3)))).map bar2PermFinThree.toMonoidHom = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv 3 bar2PermFinThree,
      CFSG.GroupTheory.pCore_three_perm_fin_three] at hmap
    exact hA3ne hmap
  · have hA3 : ((alternatingGroup (Fin 3)).map
        bar2PermFinThree.symm.toMonoidHom).map bar2PermFinThree.toMonoidHom =
        alternatingGroup (Fin 3) := by
      rw [Subgroup.map_map]
      simp
    apply (CFSG.Quasithin.E1.map_inj_mulEquiv bar2PermFinThree).mp
    rw [Subgroup.map_commutator, pCore_three_bar2_perm_fin_three, hA3,
      bar2PermFinThree_barO2]
    exact (CFSG.GroupTheory.commutator_alternatingGroup_fin_three_of_card_eq_two hB).symm
  · have h := Subgroup.card_map_of_injective
      (K := CFSG.Quasithin.E1.barO2 (Equiv.Perm (Fin 3)) B)
      (f := bar2PermFinThree.toMonoidHom) bar2PermFinThree.injective
    rw [bar2PermFinThree_barO2] at h
    exact h.symm.trans hB

end CFSG.LocalAnalysis.WeakClosure81

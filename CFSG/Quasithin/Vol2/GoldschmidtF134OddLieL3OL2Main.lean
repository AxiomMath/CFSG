module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OL2Dickson
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
open scoped MatrixGroups

namespace L2Odd

theorem isCyclic_of_isPGroup {K : Type} [Field K] [Finite K] {r f p : ℕ} [Fact r.Prime]
    [Fact p.Prime] (hr2 : r ≠ 2) (hp2 : p ≠ 2) (hpr : p ≠ r) (hK : Nat.card K = r ^ f)
    {Q : Subgroup (StatedProj (StatedSL 2 K))} (hQ : IsPGroup p Q) : IsCyclic Q := by
  obtain ⟨R, hR⟩ := hQ.exists_le_sylow
  have hRc : IsCyclic (R : Subgroup (StatedProj (StatedSL 2 K))) :=
    (odd_psl_two_sylow_data hr2 hK).2.2.2.2.2.2 p Fact.out hp2 hpr R
  have : IsCyclic (Q.subgroupOf (R : Subgroup (StatedProj (StatedSL 2 K)))) := inferInstance
  exact ((Subgroup.subgroupOfEquivOfLe hR).isCyclic).1 this

end L2Odd

theorem psl2Odd_simple :
    ∀ r f : ℕ, r.Prime → r ≠ 2 → (f = 1 ∨ f = 2) →
      NoOddCfg fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 r f := by
  intro r f hr hr2 hf A _ _ p _ L P T hp5 hL hcfg
  have hrf : Fact r.Prime := ⟨hr⟩
  have hp2 : p ≠ 2 := by omega
  have hLm := hL
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  by_cases hpr : p = r
  · subst hpr
    have hdata := odd_psl_two_sylow_data hr2 hK
    have hLcard : Nat.card ↥L = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
      rw [Nat.card_congr e.toEquiv]
      exact hdata.2.2.1
    obtain ⟨-, hnd⟩ := psl_two_cofactor hr hr2 hf1
    obtain ⟨a, ha, S, H, Q, hS2, hSidx, hSH, hQH, hHcard, hQcard, -⟩ := hcfg.exists_data hp5
    have hQdvd : p ^ a ∣ Nat.card ↥L := hQcard ▸ Subgroup.card_subgroup_dvd_card Q
    rw [hLcard] at hQdvd
    rcases hf with rfl | rfl
    · exfalso
      generalize ((p ^ 1) ^ 2 - 1) / 2 = d at hnd hQdvd
      have h2 : p ^ 2 ∣ p ^ a := pow_dvd_pow p (by omega)
      have h3 := h2.trans hQdvd
      rw [pow_succ p 1] at h3
      exact hnd ((Nat.mul_dvd_mul_iff_left (pow_pos hr.pos 1)).1 h3)
    · have ha2 : a = 2 := by
        rcases ha with h | h
        · exact h
        · exfalso
          subst h
          have : p ^ 3 ∣ p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2) := hQdvd
          rw [pow_succ] at this
          exact hnd ((Nat.mul_dvd_mul_iff_left (pow_pos hr.pos 2)).1 this)
      subst ha2
      obtain ⟨c, hc⟩ := L2Odd.exists_sq_eq (hr.odd_of_ne_two hr2)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
      have hidx : 2 ^ k * S.index = p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2) := by
        rw [← hk, ← hLcard]
        exact S.card_mul_index
      obtain ⟨e'⟩ := nonempty_mulEquiv_psl2_odd hLm
      refine L2Odd.false_of_dickson (k := k) (m := S.index) hp5 hSidx hidx (H.map e'.toMonoidHom) ?_
      rw [Subgroup.card_map_of_injective e'.injective, hHcard, hk]
  · have hpG : IsPGroup p ↥P := hcfg.isPGroup
    let eP : ↥P ≃* ↥(P.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hcfg.le).symm
    let eP2 : ↥(P.subgroupOf L) ≃* ↥((P.subgroupOf L).map e.toMonoidHom) :=
      (P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective
    have hP2 : IsPGroup p ↥((P.subgroupOf L).map e.toMonoidHom) := hpG.of_equiv (eP.trans eP2)
    have hc := L2Odd.isCyclic_of_isPGroup hr2 hp2 hpr hK hP2
    exact hcfg.not_isCyclic (((eP.trans eP2).isCyclic).2 hc)

end CFSG.Quasithin.H13.NQCore

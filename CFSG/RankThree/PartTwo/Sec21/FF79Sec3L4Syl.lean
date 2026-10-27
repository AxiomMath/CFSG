module


import CFSG.RankThree.PartTwo.Sec21.FF79ThmAOdd
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4V

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem sec34S_inf_zpowers (hb : orderOf b = 3) {H : Subgroup G} (hbH : b ∉ H) :
    H ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxH, hxz⟩ := hx
  have hxo : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := by
      rw [← hb]; exact orderOf_dvd_of_mem_zpowers hxz
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).mpr hxz
  have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hb]
  have : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
  exact hbH ((Subgroup.zpowers_le).mpr hxH this)

theorem sec34S_b_not_mem {a : G} (hU : FF79Sec34UFacts b a J A) : b ∉ CenS (U34 b a J A) := by
  intro hb
  haveI := hU.elemU.1
  have hle : U34 b a J A ≤ Cen b := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.mp hb u hu).symm
  have h1 : U34 b a J A = Subgroup.zpowers a := by
    rw [← hU.cenU_b]; exact (inf_eq_left.mpr hle).symm
  have h2 : orderOf a ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (A := U34 b a J A) a hU.a_mem)
  have h3 : Nat.card (U34 b a J A) = 9 := by simpa using hU.elemU.2
  rw [h1, Nat.card_zpowers] at h3
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem sec34_As_syl (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D) {a : G}
    (hU : FF79Sec34UFacts b a J A) {As : Subgroup G} (hAs : FF79AStar b D A As) :
    IsSylowOf 3 As (CenS (U34 b a J A)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := CenS (U34 b a J A) with hC
  set Z : Subgroup G := Subgroup.zpowers b with hZ
  obtain ⟨hAAs, hAsyl, hcomm, hbAs, -, -, hTsyl, -⟩ := hAs
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hAsC : As ≤ C := hAsyl.1.trans (Subgroup.centralizer_le (by exact_mod_cast hU.U_le_A))
  have hbC : b ∉ C := sec34S_b_not_mem hU
  have hbAs' : b ∉ As := fun hb => hbC (hAsC hb)
  have hZC : Z ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.zpowers_le).mpr (nor_cenS_of_nor hU.b_nor)
  have hZAs : Z ≤ Subgroup.normalizer (As : Set G) := (Subgroup.zpowers_le).mpr hbAs
  have hcZ : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hb3]
  have hN : Nat.card ↥(C ⊔ Z) = Nat.card C * 3 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZC
      (sec34S_inf_zpowers hb3 hbC), hcZ]
  have hS : Nat.card ↥(As ⊔ Z) = Nat.card As * 3 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZAs
      (sec34S_inf_zpowers hb3 hbAs'), hcZ]
  have hSG : Nat.card ↥(As ⊔ Z) = 3 ^ (Nat.card G).factorization 3 := by
    have := L41.isSylowOf_card_p hTsyl
    simpa using this
  obtain ⟨k, hk⟩ := hAsyl.2.1.exists_card_eq
  have hAsC' : Nat.card As ∣ Nat.card C := Subgroup.card_dvd_of_le hAsC
  have hkC : k ≤ (Nat.card C).factorization 3 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp ?_
    rwa [hk] at hAsC'
  have hNG : (Nat.card ↥(C ⊔ Z)).factorization 3 ≤ (Nat.card G).factorization 3 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) 3
  have hNf : (Nat.card ↥(C ⊔ Z)).factorization 3 = (Nat.card C).factorization 3 + 1 := by
    rw [hN, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply]
    simp [Nat.Prime.factorization Nat.prime_three]
  have hGk : (Nat.card G).factorization 3 = k + 1 := by
    have h1 : 3 ^ (Nat.card G).factorization 3 = 3 ^ (k + 1) := by
      rw [← hSG, hS, hk, pow_succ]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  refine L41.isSylowOf_of_card_p hAsC ?_
  rw [hk]
  congr 1
  omega

theorem sec34_no27 (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D) {a : G}
    (hU : FF79Sec34UFacts b a J A) :
    ∀ T : Subgroup G, T ≤ Cen b ⊓ CenS (U34 b a J A) → ¬ IsElemAb 3 3 T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T hT hE
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hbC := sec34S_b_not_mem hU
  have hbT : b ∉ T := fun hb => hbC (hT hb).2
  set Z : Subgroup G := Subgroup.zpowers b with hZ
  have hZT : Z ≤ Subgroup.normalizer (T : Set G) := by
    rw [hZ, Subgroup.zpowers_le]
    refine L41.mem_nor_of_forall (fun y hy => ?_)
    have := Subgroup.mem_centralizer_iff.mp (hT hy).1 b (Set.mem_singleton b)
    rw [this]; simpa using hy
  have hcZ : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hb3]
  have hcT : Nat.card T = 27 := by simpa using hE.2
  have h81 : Nat.card ↥(T ⊔ Z) = 3 ^ 4 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZT
      (sec34S_inf_zpowers hb3 hbT), hcZ, hcT]
    norm_num
  have hP : IsPGroup 3 ↥(T ⊔ Z) := IsPGroup.of_card h81
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hSyl : IsSylowOf 3 (Q : Subgroup G) ⊤ := by
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr Q.not_dvd_index
  have hbQ : b ∈ (Q : Subgroup G) := hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hTQ : T ≤ (Q : Subgroup G) := le_sup_left.trans hQ
  have := (sec34_cenb_syl h _ hSyl hbQ T hTQ (fun x hx => (hT hx).1)).2 hcT
  exact hbT this

theorem sec34_odd_opp (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D) {a : G}
    (hU : FF79Sec34UFacts b a J A) :
    Odd (Nat.card (Opp 3 (CenS (U34 b a J A)))) :=
  ff79_opp3_cenS_odd h.elemA hU.U_le_A hs.rank3

end CFSG.RankThree.PartTwo.Sec21.FF79

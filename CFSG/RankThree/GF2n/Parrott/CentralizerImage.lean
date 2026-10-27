module

public import CFSG.RankThree.GF2n.Parrott.CentralizerOrders

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem map_centralizer_sigma1Nine_eq (h : Tim79a.ParrottHyp z) :
    (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (qH D) =
      Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) := by
  classical
  set K : Subgroup ↥(H z) := Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))
  set f : ↥K →* QA45.originalSubgroup := (qH D).comp K.subtype with hf
  have hKcard : Nat.card ↥K = 10368 := card_centralizer_sigma1Nine (z := z) D h
  have hker : f.ker = (K ⊓ (J z).subgroupOf (H z)).subgroupOf K := by
    ext x
    constructor
    · intro hx
      have hx1 : (qH D) (x : ↥(H z)) = 1 := MonoidHom.mem_ker.mp hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, (J_mem_iff D (x : ↥(H z))).mpr hx1⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact MonoidHom.mem_ker.mpr ((J_mem_iff D (x : ↥(H z))).mp hx.2)
  have hkercard : Nat.card ↥f.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      K ⊓ (J z).subgroupOf (H z) ≤ K)).toEquiv]
    exact (card_centralizer_inf_J_subgroupOf (z := z)
      (x := sigma1Nine (z := z) D)).trans (card_centralizerJ_sigma1Nine h D)
  have hrangecard : Nat.card ↥f.range = 648 := by
    have hmul := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hKcard] at hmul
    omega
  have hrange : f.range = K.map (qH D) := by
    rw [hf, MonoidHom.range_comp]
    congr 1
    exact K.range_subtype
  have hle : f.range ≤ Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} : Set QA45.originalSubgroup) := by
    intro x hx
    rw [hrange] at hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : (k : ↥(H z)) * sigma1Nine (z := z) D =
        sigma1Nine (z := z) D * (k : ↥(H z)) :=
      Subgroup.mem_centralizer_singleton_iff.mp hk
    have hq := congrArg (qH D) hk'
    simpa [map_mul, qH_sigma1Nine] using hq
  have hcard : Nat.card ↥(Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} : Set QA45.originalSubgroup)) ≤
      Nat.card ↥f.range := by
    rw [card_centralizer_sigma1_QA45, hrangecard]
  have hfinal : f.range = Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} : Set QA45.originalSubgroup) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← hrange]
  exact hfinal

end CFSG.RankThree.GF2n.Parrott

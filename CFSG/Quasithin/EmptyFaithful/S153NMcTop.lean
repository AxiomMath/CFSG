module

public import CFSG.Quasithin.EmptyFaithful.S153NBase
public import CFSG.Quasithin.EmptyFaithful.S153NMcAct
public import CFSG.Quasithin.EmptyFaithful.S153NMcSimple
public import CFSG.Quasithin.H13.NQRigidWMGroups

public section

namespace CFSG.Quasithin.S153N

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section L32TypeC

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_l32_typeC (hW : ∀ v : W, v ^ 2 = 1) {Γ J : Subgroup (MulAut W)} {w : W}
    (hJΓ : J ≤ Γ) (hJn : (J.subgroupOf Γ).Normal)
    (hiso : Nonempty (↥J ≃* ↥(StatedSL 3 (ZMod 2))))
    (hcard : Nat.card W = 2 ^ 4 * Nat.card ↥(fixV J))
    (hw : w ∉ fixV J) (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w))
    (hS : ∃ S : Subgroup (MulAut W), IsSylowTwoOf S Γ ∧ S ≤ stabAt Γ w) : False := by
  obtain ⟨S, hSyl, hSw⟩ := hS
  obtain ⟨e⟩ := hiso
  have hsimp : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have : IsSimpleGroup ↥J := e.isSimpleGroup
  have hJcard : Nat.card ↥J = 168 := by
    have h := CFSG.SectionRank.OddCover.card_statedSL_three (K := ZMod 2)
    rw [Nat.card_zmod] at h
    have h2 := Nat.card_congr e.toEquiv
    norm_num at h
    omega
  have hnorm : Γ ≤ Subgroup.normalizer (J : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJn
  have hS0 : IsSylowTwoOf (S ⊓ J) J :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hSyl hJΓ hnorm
  have hP8 : Nat.card ↥((S ⊓ J).subgroupOf J) = 8 := by
    have hcP : Nat.card ↥((S ⊓ J).subgroupOf J) = Nat.card ↥(S ⊓ J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    obtain ⟨k, hk⟩ := hS0.2.1.exists_card_eq
    have hmul := Subgroup.index_mul_card ((S ⊓ J).subgroupOf J)
    have hodd : ¬ 2 ∣ ((S ⊓ J).subgroupOf J).index := hS0.2.2
    rw [hcP, hk, hJcard] at hmul
    rw [hcP, hk]
    have hle : 2 ^ k ≤ 168 := Nat.le_of_dvd (by norm_num) ⟨_, by rw [← hmul]; ring⟩
    have hk8 : k < 8 := by
      by_contra hk8
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hk8)
      omega
    interval_cases k <;> omega
  have hPle : (S ⊓ J).subgroupOf J ≤ stabQ J w := by
    intro g hg
    have hgS : (g : MulAut W) ∈ S := (Subgroup.mem_subgroupOf.1 hg).1
    rw [mem_stabQ, (hSw hgS).2, mul_inv_cancel]
    exact one_mem _
  have hdvd8 : 8 ∣ Nat.card ↥(stabQ J w) := by
    have := Subgroup.card_dvd_of_le hPle
    rwa [hP8] at this
  have hidx := index_stabQ_add_one_le J hw
  rw [card_quot_fixV hcard] at hidx
  have hmul := Subgroup.index_mul_card (stabQ J w)
  rw [hJcard] at hmul
  have hcases : 3 ∣ Nat.card ↥(stabQ J w) ∨ (stabQ J w).index = 3 := by
    generalize (stabQ J w).index = i at hidx hmul ⊢
    generalize Nat.card ↥(stabQ J w) = n at hdvd8 hmul ⊢
    have hi : i ≤ 15 := by omega
    interval_cases i <;> omega
  rcases hcases with h3n | hi3
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3n
    have hgo : orderOf ((x : ↥J) : MulAut W) = 3 := by
      rw [Subgroup.orderOf_coe (x : ↥J), Subgroup.orderOf_coe x, hx]
    have hg3 : ((x : ↥J) : MulAut W) ^ 3 = 1 := by
      rw [← hgo]
      exact pow_orderOf_eq_one _
    have hg1 : ((x : ↥J) : MulAut W) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hgo
      omega
    exact false_of_lift hW hJΓ h3 (x : ↥J).2 hg1 hg3 (mem_stabQ.1 x.2)
  · exact index_ne_three_of_isSimpleGroup (by omega) (stabQ J w) hi3

end L32TypeC

end CFSG.Quasithin.S153N

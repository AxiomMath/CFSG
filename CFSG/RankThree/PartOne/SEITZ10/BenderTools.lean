module

public import CFSG.Timmesfeld.Bridge.StrongEmbedding

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Open

section Odd

variable {X : Type*} [Group X]

theorem mem_of_pow_two_pow_eq_one_of_odd_index (N : Subgroup X) [N.Normal] (hN : Odd N.index)
    {x : X} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) : x ∈ N := by
  obtain ⟨n, hn⟩ := hx
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) N.index := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 : orderOf (QuotientGroup.mk x : X ⧸ N) = 1 :=
    (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem le_of_isSimpleGroup_of_odd_index (N : Subgroup X) [N.Normal] (hN : Odd N.index)
    (R : Subgroup X) [IsSimpleGroup R] (hR : Even (Nat.card R)) : R ≤ N := by
  by_contra hRN
  have hnorm : (N.subgroupOf R).Normal := inferInstance
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.subgroupOf R) with hbot | htop
  · let f : R →* X ⧸ N := (QuotientGroup.mk' N).comp R.subtype
    have hker : f.ker = ⊥ := by
      have : f.ker = N.subgroupOf R := by
        ext r
        simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
      rw [this, hbot]
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
    have hdvd : Nat.card R ∣ Nat.card (X ⧸ N) := Subgroup.card_dvd_of_injective f hinj
    have hodd : Odd (Nat.card (X ⧸ N)) := hN
    exact (Nat.not_even_iff_odd.2 (hodd.of_dvd_nat hdvd)) hR
  · exact hRN (Subgroup.subgroupOf_eq_top.1 htop)

end Odd

section Borel

variable {X : Type*} [Group X] [Finite X]

theorem exists_mem_normalizer_conj_of_central_involutions (Q : Sylow 2 X)
    (hQ : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup X) : Set X))) {z z' : X}
    (hz' : z' ∈ (Q : Subgroup X)) (hz2 : orderOf z = 2) (hz'2 : orderOf z' = 2)
    (hzc : ∀ y ∈ (Q : Subgroup X), y * z = z * y) :
    ∃ n ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X), n * z * n⁻¹ = z' := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Timmesfeld.Bridge.isConj_of_orderOf_eq_two hQ hz2 hz'2)
  have hle : (Q : Subgroup X).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.normalizer ((Q : Subgroup X) : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    refine CFSG.Timmesfeld.Connectivity.mem_of_commute_of_stronglyEmbedded hQ
      (Subgroup.le_normalizer hz') hz'2 ?_
    change Commute ((MulAut.conj c) y) z'
    rw [← hc]
    have h := hzc y hy
    unfold Commute SemiconjBy
    simp only [MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * z * c⁻¹) = c * (y * z) * c⁻¹ := by group
      _ = c * (z * y) * c⁻¹ := by rw [h]
      _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group
  have hP : IsPGroup 2 ((Q : Subgroup X).map (MulAut.conj c).toMonoidHom) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : y ^ 2 ^ n = 1 := congrArg Subtype.val hn
    change ((MulAut.conj c) y) ^ 2 ^ n = 1
    rw [← map_pow, hn', map_one]
  have hQP : (Q : Subgroup X).map (MulAut.conj c).toMonoidHom ≤ (Q : Subgroup X) := by
    have h1 := hP.inf_normalizer_sylow Q
    have hle' : (Q : Subgroup X).map (MulAut.conj c).toMonoidHom ≤
        Subgroup.normalizer (Q : Set X) := hle
    rw [inf_eq_left.2 hle'] at h1
    exact h1.le.trans inf_le_right
  have hcard : Nat.card (Q : Subgroup X) ≤
      Nat.card ((Q : Subgroup X).map (MulAut.conj c).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hQeq : (Q : Subgroup X).map (MulAut.conj c).toMonoidHom = (Q : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hQP hcard
  refine ⟨c, ?_, hc⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : c * h * c⁻¹ ∈ (Q : Subgroup X).map (MulAut.conj c).toMonoidHom :=
      ⟨h, hh, by simp [MulAut.conj_apply]⟩
    rw [hQeq] at this
    exact this
  · intro hh
    rw [← hQeq] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyh
      simpa using hyh
    rw [← this]
    exact hy

end Borel

end CFSG.RankThree.PartOne.SEITZ10

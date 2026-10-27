module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

open CFSG CFSG.RankThree.LocalRank CFSG.GH74.GLS

private theorem oPrimeResidual_three_normal (H : Type) [Group H] :
    (oPrimeResidual 3 H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    calc (g * x * g⁻¹) ^ (3 ^ k) = g * x ^ (3 ^ k) * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hk]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

private theorem oPrimeResidual_three_eq_top {H : Type} [Group H] [Finite H]
    (hK : Group.IsPerfect H)
    (hs : IsSimpleGroup (H ⧸ aschbacherSolvableCore 3 H))
    (h3 : 3 ∣ Nat.card (H ⧸ aschbacherSolvableCore 3 H)) :
    oPrimeResidual 3 H = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hN : (oPrimeResidual 3 H).Normal := oPrimeResidual_three_normal H
  haveI hθ : Group.IsSolvable (aschbacherSolvableCore 3 H) :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ aschbacherSolvableCore 3 H) 3 h3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 H) z
  obtain ⟨a, c, hc3, hxc⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have hyN : x ^ c ∈ oPrimeResidual 3 H := by
    unfold oPrimeResidual
    apply Subgroup.subset_closure
    refine ⟨a, ?_⟩
    have hc : c * 3 ^ a = orderOf x := by rw [hxc]; ring
    rw [← pow_mul, hc, pow_orderOf_eq_one]
  have hyne : QuotientGroup.mk' (aschbacherSolvableCore 3 H) (x ^ c) ≠ 1 := by
    intro h1
    have hdvd : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 H) x) ∣ c := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      exact h1
    rw [hz] at hdvd
    exact hc3 hdvd
  have hM : ((oPrimeResidual 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have htop : (oPrimeResidual 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
        ((oPrimeResidual 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) with hb | ht
    · exfalso
      apply hyne
      have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) hyN
      rw [hb, Subgroup.mem_bot] at hmem
      exact hmem
    · exact ht
  have hsurj : ∀ h : H, ∃ n ∈ oPrimeResidual 3 H,
      QuotientGroup.mk' (aschbacherSolvableCore 3 H) n =
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) h := by
    intro h
    have hh : QuotientGroup.mk' (aschbacherSolvableCore 3 H) h ∈
        (oPrimeResidual 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.mp hh
  have hψ : Function.Surjective
      ((QuotientGroup.mk' (oPrimeResidual 3 H)).comp (aschbacherSolvableCore 3 H).subtype) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oPrimeResidual 3 H) q
    obtain ⟨n, hnN, hnh⟩ := hsurj h
    have ht : n⁻¹ * h ∈ aschbacherSolvableCore 3 H := by
      refine (QuotientGroup.eq_one_iff (n⁻¹ * h)).mp ?_
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 H) (n⁻¹ * h) = 1 := by
        rw [map_mul, map_inv, hnh, inv_mul_cancel]
      exact h1
    refine ⟨⟨n⁻¹ * h, ht⟩, ?_⟩
    have hn1 : QuotientGroup.mk' (oPrimeResidual 3 H) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hnN
    show QuotientGroup.mk' (oPrimeResidual 3 H) (n⁻¹ * h) =
      QuotientGroup.mk' (oPrimeResidual 3 H) h
    rw [map_mul, map_inv, hn1, inv_one, one_mul]
  haveI hQ : Group.IsSolvable (H ⧸ oPrimeResidual 3 H) := Group.isSolvable_of_surjective hψ
  haveI hsub : Subsingleton (H ⧸ oPrimeResidual 3 H) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (H ⧸ oPrimeResidual 3 H) hQ
  exact QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub

theorem oPrimeResidualOf_eq_self_of_simple_theta {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : Group.IsPerfect ↥K)
    (hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K)) :
    oPrimeResidualOf 3 K = K := by
  unfold oPrimeResidualOf
  rw [oPrimeResidual_three_eq_top hK hs h3, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.RankThree.PartTwo.Sec14.Ronan148M

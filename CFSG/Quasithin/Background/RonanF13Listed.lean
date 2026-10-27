module

public import CFSG.Quasithin.Background.RonanF13SU
public import CFSG.Quasithin.Background.RonanF13Small

public section

namespace CFSG.Quasithin.RonanF13

open CFSG.Open CFSG.Quasithin CFSG.GH74.Uniqueness.Bender

theorem _root_.CFSG.Quasithin.IsRankOneListed.finite {K : Type*} [Group K]
    (h : IsRankOneListed K) : Finite K := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : NeZero n := ⟨by omega⟩
    exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv

theorem rankOneTwist_of_central_cover_selfNorm {K K' : Type*} [Group K] [Group K']
    (π : K →* K') (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center K)
    (hker3 : ∀ z ∈ π.ker, z ^ 3 = 1) (hkercyc : IsCyclic ↥π.ker) (hK' : SelfNormSylow K') :
    RankOneTwist K := by
  intro T D α hT hTodd hTD hDodd hαT hαD hαodd _ x hx
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  have hDker : D ≤ π.ker := by
    intro d hd
    have hT' : IsPGroup 2 (T.map π) := hT.map π
    have hTodd' : ¬ 2 ∣ (T.map π).index := fun hdv =>
      hTodd (hdv.trans (Subgroup.index_map_dvd T hπ))
    have hdn : π d ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') :=
      Subgroup.le_normalizer_map π ⟨d, hDN hd, rfl⟩
    have hself := hK' (T.map π) hT' hTodd'
    rw [hself] at hdn
    obtain ⟨t, ht, htd⟩ := Subgroup.mem_map.mp hdn
    have hz : t⁻¹ * d ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htd, inv_mul_cancel]
    have hdodd : Odd (orderOf d) := by
      have h1 : orderOf d ∣ Nat.card D := by
        have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hDodd h1
    have hzodd : Odd (orderOf (t⁻¹ * d)) := by
      have h3 : orderOf (t⁻¹ * d) ∣ 3 := orderOf_dvd_of_pow_eq_one (hker3 _ hz)
      exact Odd.of_dvd_nat (by decide : Odd 3) h3
    have hc0 : Commute d (t⁻¹ * d) := Subgroup.mem_center_iff.mp (hZ hz) d
    have hcomm : Commute d (t⁻¹ * d)⁻¹ := hc0.inv_right
    have htd' : t = d * (t⁻¹ * d)⁻¹ := by group
    have htodd : Odd (orderOf t) := by
      have h4 := hcomm.orderOf_mul_dvd_lcm
      rw [← htd', orderOf_inv] at h4
      exact Odd.of_dvd_nat (hdodd.mul hzodd) (h4.trans (Nat.lcm_dvd_mul _ _))
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have ht1 : t = 1 := eq_one_of_odd_orderOf_of_pow' htodd (congrArg Subtype.val hk)
    have : t⁻¹ * d = d := by rw [ht1]; simp
    rw [← this]
    exact hz
  have hDcyc : IsCyclic ↥D :=
    isCyclic_of_injective (Subgroup.inclusion hDker : ↥D →* ↥π.ker)
      (Subgroup.inclusion_injective hDker)
  exact aut_trivial_of_cyclic_exp3 D hDcyc (fun z hz => hker3 z (hDker hz)) α hαD hαodd x hx

theorem isCyclic_statedScalars_subgroupOf {F : Type} [Field F] [Finite F]
    (H : Subgroup (GL (Fin 3) F)) :
    IsCyclic ↥((StatedScalars (Fin 3) F).subgroupOf H) := by
  let s : Fˣ →* GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3)
  have hs : Function.Injective s := by
    intro a b hab
    have h1 := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 0)) hab
    apply Units.ext
    simpa [s] using h1
  let e : Fˣ ≃* ↥s.range := MonoidHom.ofInjective hs
  let g : ↥((StatedScalars (Fin 3) F).subgroupOf H) →* ↥s.range :=
    MonoidHom.codRestrict
      (H.subtype.comp ((StatedScalars (Fin 3) F).subgroupOf H).subtype) s.range
      (fun z => Subgroup.mem_subgroupOf.mp z.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h2 := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    exact h2
  exact isCyclic_of_injective (e.symm.toMonoidHom.comp g) (e.symm.injective.comp hg)

theorem rankOneTwist_statedSU_one {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) : RankOneTwist (StatedSU 3 (2 ^ 1) F) := by
  refine rankOneTwist_of_central_cover_selfNorm
    (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ 1) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ ?_ (selfNormSylow_statedProj_one hF)
  · rw [QuotientGroup.ker_mk']
    exact statedSU_scalars_le_center
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    exact statedSU_three_kernel z hz
  · rw [QuotientGroup.ker_mk']
    exact isCyclic_statedScalars_subgroupOf _

theorem rankOneTwist_of_listed
    {K : Type*} [Group K] (h : IsRankOneListed K) : RankOneTwist K := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact rankOneTwist_of_selfNormSylow (selfNormSylow_of_psl_two_one e)
    · have : NeZero n := ⟨by omega⟩
      have : Finite K := Finite.of_equiv _ e.symm.toEquiv
      exact bender_twist (.linear n h2 e)
  · rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      exact rankOneTwist_of_selfNormSylow (selfNormSylow_of_sz_zero e)
    · have : Finite K := Finite.of_equiv _ e.symm.toEquiv
      exact bender_twist (.suzuki a h1 e)
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact RankOneTwist.of_mulEquiv e.symm (rankOneTwist_statedSU_one hF)
    · exact RankOneTwist.of_mulEquiv e.symm (rankOneTwist_statedSU h2 hF)
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact rankOneTwist_of_selfNormSylow
        (SelfNormSylow.of_mulEquiv e.symm (selfNormSylow_statedProj_one hF))
    · obtain ⟨e', hB⟩ := benderType_statedProj h2 hF
      exact RankOneTwist.of_mulEquiv e.symm (bender_twist hB)
  · exact rankOneTwist_of_selfNormSylow (selfNormSylow_of_dihedral_five e)

end CFSG.Quasithin.RonanF13

module

public import CFSG.Quasithin.Recognition.F112Crit.BenderCartan
public import CFSG.Quasithin.Recognition.F112Crit.BenderTrichotomy
public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki
public import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.GH74.Uniqueness.Bender

structure IsTrichQuot (K : Type*) [Group K] : Prop where
  trich : ∀ P : Sylow 2 K, ∀ N : Subgroup K, N ≤ P →
    (∀ x ∈ (P : Subgroup K), ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
    (∀ d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), Odd (orderOf d) →
      ∀ y ∈ N, d * y * d⁻¹ ∈ N) →
    N = ⊥ ∨ N = P ∨
      ((∀ n ∈ N, ∀ u ∈ (P : Subgroup K), n * u * n⁻¹ * u⁻¹ = 1) ∧
        (∀ a ∈ (P : Subgroup K), ∀ b ∈ (P : Subgroup K), a * b * a⁻¹ * b⁻¹ ∈ N) ∧
        (∀ n ∈ N, n * n = 1) ∧
        ∃ a ∈ (P : Subgroup K), ∃ b ∈ (P : Subgroup K), ∃ y : K,
          y⁻¹ * (a * b * a⁻¹ * b⁻¹) * y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K))

theorem BenderType.isTrichQuot {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : IsTrichQuot K := by
  refine ⟨fun P N hNP hN hD => ?_⟩
  obtain ⟨t, hc⟩ := h.exists_benderCore P
  have hD' : ∀ d ∈ cartan (P : Subgroup K) t, ∀ y ∈ N, d * y * d⁻¹ ∈ N := by
    intro d hd y hy
    exact hD d (cartan_le_borel _ _ hd)
      (Odd.of_dvd_nat hc.odd_card_cartan (Subgroup.orderOf_dvd_natCard _ hd)) y hy
  rcases h.normal_trichotomy P hc hNP hN hD' with h1 | h2 | h3
  · exact Or.inl h1
  · obtain rfl : N = rootCenter (P : Subgroup K) := h2
    by_cases hZ : rootCenter (P : Subgroup K) = (P : Subgroup K)
    · exact Or.inr (Or.inl hZ)
    · right; right
      have hti : t⁻¹ = t := inv_eq_of_mul_self hc.sq_eq_one
      refine ⟨?_, ?_, hc.center_sq, ?_⟩
      · intro n hn u hu
        have h1 : n * u = u * n := ((mem_rootCenter_iff.mp hn).2 u hu).symm
        rw [h1]
        group
      · intro a ha b hb
        rcases h.cases' with ⟨hi, -, -⟩ | ⟨hi, he, -⟩ | ⟨hi, -, -⟩
        · subst hi
          have hZQ : rootCenter (P : Subgroup K) = (P : Subgroup K) := by
            apply Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
            rw [hc.card_center, hc.card_eq, pow_one]
          exact absurd hZQ hZ
        · subst hi
          subst he
          exact commutator_mem_of_sq_mem
            (fun z hz p hp => ((mem_rootCenter_iff.mp hz).2 p hp).symm)
            (fun x hx => h.sq_mem_rootCenter_suzuki P hx) ha hb
        · subst hi
          exact commutator_mem_of_sq_mem
            (fun z hz p hp => ((mem_rootCenter_iff.mp hz).2 p hp).symm)
            (fun x hx => h.sq_mem_rootCenter_unitary P hx) ha hb
      · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ (P : Subgroup K), ∃ b ∈ (P : Subgroup K),
            a * b ≠ b * a := by
          by_contra hall
          push Not at hall
          exact hZ (le_antisymm (rootCenter_le _)
            fun x hx => mem_rootCenter_iff.mpr ⟨hx, fun p hp => hall p hp x hx⟩)
        refine ⟨a, ha, b, hb, t, ?_⟩
        intro hconj
        apply hab
        have hconj' : a * b * a⁻¹ * b⁻¹ ∈ conjugate (borel (P : Subgroup K)) t := by
          rw [mem_conjugate_iff_mul_inv, hti]
          rw [hti] at hconj
          exact hconj
        have hPc : a * b * a⁻¹ * b⁻¹ ∈ (P : Subgroup K) :=
          mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
        have hbot : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup K) := by
          rw [← hc.inf_eq]
          exact Subgroup.mem_inf.mpr ⟨hPc, Subgroup.mem_inf.mpr ⟨le_borel _ hPc, hconj'⟩⟩
        rw [Subgroup.mem_bot] at hbot
        exact commutatorElement_eq_one_iff_mul_comm.mp (by
          rw [commutatorElement_def]; exact hbot)
  · exact Or.inr (Or.inl h3)

theorem IsTrichQuot.of_surjective {K K' : Type*} [Group K] [Group K'] [Finite K] (f : K →* K')
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) (h : IsTrichQuot K') : IsTrichQuot K := by
  have hNm : ∀ (P : Sylow 2 K) (a : K),
      a ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ↔
        f a ∈ Subgroup.normalizer (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') :=
    fun P a => by
      rw [Sylow.coe_mapSurjective]
      exact ⟨fun ha => Subgroup.le_normalizer_map f ⟨a, ha, rfl⟩,
        fun ha => RonanF13.mem_normalizer_of_central_cover f hker hodd P.isPGroup' ha⟩
  have hkerP : ∀ (P : Sylow 2 K) {x : K}, x ∈ (P : Subgroup K) → f x = 1 → x = 1 := by
    intro P x hx hx1
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact RonanF13.eq_one_of_odd_orderOf_of_pow'
      (hodd x (MonoidHom.mem_ker.mpr hx1)) (by simpa using congrArg Subtype.val hk)
  have hinj : ∀ (P : Sylow 2 K) {x y : K}, x ∈ (P : Subgroup K) → y ∈ (P : Subgroup K) →
      f x = f y → x = y := by
    intro P x y hx hy hxy
    have h1 : x⁻¹ * y ∈ (P : Subgroup K) := mul_mem (inv_mem hx) hy
    exact inv_mul_eq_one.mp (hkerP P h1 (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
  refine ⟨fun P N hNP hN hD => ?_⟩
  have hPN : N.map f ≤ (P.mapSurjective hf : Subgroup K') := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hNP
  have hNinv : ∀ x ∈ (P.mapSurjective hf : Subgroup K'), ∀ y ∈ N.map f, x * y * x⁻¹ ∈ N.map f := by
    intro x hx y hy
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr
      ⟨x₀ * y₀ * x₀⁻¹, hN x₀ hx₀ y₀ hy₀, by simp [map_mul, map_inv]⟩
  have hDinv : ∀ d' ∈ Subgroup.normalizer
      (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K'),
      Odd (orderOf d') → ∀ y' ∈ N.map f, d' * y' * d'⁻¹ ∈ N.map f := by
    intro d' hd' hodd' y' hy'
    obtain ⟨d, rfl⟩ := hf d'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
    have hd : d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := (hNm P d).mpr hd'
    have hodd : Odd (orderOf d) := by
      have hk : d ^ orderOf (f d) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        simpa using pow_orderOf_eq_one (f d)
      refine Odd.of_dvd_nat (hodd'.mul (hodd _ hk)) ?_
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact Subgroup.mem_map.mpr
      ⟨d * y * d⁻¹, hD d hd hodd y hy, by simp [map_mul, map_inv]⟩
  rcases h.trich (P.mapSurjective hf) (N.map f) hPN hNinv hDinv with h1 | h2 | h3
  · left
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hy' : f y ∈ N.map f := Subgroup.mem_map_of_mem f hy
    rw [h1, Subgroup.mem_bot] at hy'
    exact hkerP P (hNP hy) hy'
  · right; left
    refine le_antisymm hNP fun x hx => ?_
    have hx' : f x ∈ (P.mapSurjective hf : Subgroup K') := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem f hx
    rw [← h2] at hx'
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hx'
    rw [hinj P hx (hNP hy) hfy.symm]
    exact hy
  · right; right
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn u hu
      have h1 := h3.1 (f n) (Subgroup.mem_map_of_mem f hn) (f u)
        (Subgroup.mem_map_of_mem f hu)
      refine hkerP P ?_ (by simpa [map_mul, map_inv] using h1)
      exact mul_mem (mul_mem (mul_mem (hNP hn) hu) (inv_mem (hNP hn))) (inv_mem hu)
    · intro a ha b hb
      have h1 := h3.2.1 (f a) (Subgroup.mem_map_of_mem f ha) (f b)
        (Subgroup.mem_map_of_mem f hb)
      obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp h1
      have hPc : a * b * a⁻¹ * b⁻¹ ∈ (P : Subgroup K) :=
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      have hfy' : f y = f (a * b * a⁻¹ * b⁻¹) := by
        rw [hfy]
        simp [map_mul, map_inv]
      rw [← hinj P (hNP hy) hPc hfy']
      exact hy
    · intro n hn
      have h1 := h3.2.2.1 (f n) (Subgroup.mem_map_of_mem f hn)
      exact hkerP P (mul_mem (hNP hn) (hNP hn)) (by simpa [map_mul] using h1)
    · obtain ⟨a', ha', b', hb', y', hy'⟩ := h3.2.2.2
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
      obtain ⟨y, hy, rfl⟩ := hf y'
      refine ⟨a, ha, b, hb, y, fun hconj => hy' ?_⟩
      simpa [map_mul, map_inv] using (hNm P _).mp hconj

theorem IsTrichQuot.of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K] (e : K ≃* K')
    (h : IsTrichQuot K') : IsTrichQuot K := by
  have hker : ∀ z ∈ e.toMonoidHom.ker, z = 1 := fun z hz => e.injective (by simpa using hz)
  exact IsTrichQuot.of_surjective e.toMonoidHom e.surjective
    (fun z hz => by rw [hker z hz]; exact Subgroup.one_mem _)
    (fun z hz => by rw [hker z hz, orderOf_one]; exact odd_one) h

theorem isTrichQuot_of_listed {K : Type} [Group K] [Finite K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) : IsTrichQuot K := by
  rcases cases_of_listed_of_not_isSolvable hK hs with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩
  · exact BenderType.isTrichQuot (BenderType.linear n hn e)
  · exact BenderType.isTrichQuot
      (BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    let π : StatedSU 3 (2 ^ n) F →* StatedProj (StatedSU 3 (2 ^ n) F) :=
      QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    haveI : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
    refine IsTrichQuot.of_mulEquiv e (IsTrichQuot.of_surjective π hπ ?_ ?_
      (BenderType.isTrichQuot hB))
    · show π.ker ≤ _
      rw [QuotientGroup.ker_mk']
      exact statedSU_scalars_le_center
    · intro z hz
      rw [QuotientGroup.ker_mk'] at hz
      exact statedSU_three_scalars_odd z hz
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact BenderType.isTrichQuot (hB.of_mulEquiv e.symm)

end CFSG.Quasithin.F112Crit

end

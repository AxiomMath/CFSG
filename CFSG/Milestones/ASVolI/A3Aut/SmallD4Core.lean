module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.Quasithin.EmptyFaithful.S152RD4

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.QuasithinUnique.Setup.X6
open scoped Pointwise

theorem burnsideAut_relIndex_eq_of_mul {G : Type*} [Group G] {H Y P : Subgroup G} (hYP : Y ≤ P)
    (h : ∀ x ∈ P, ∃ y ∈ Y, ∃ b ∈ H, x = y * b) : H.relIndex Y = H.relIndex P := by
  unfold Subgroup.relIndex Subgroup.index
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hYP)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hYP).injective, ?_⟩
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, hy, b, hb, rfl⟩ := h x hx
  refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hb

section D4


theorem burnsideAut_d42_cell {K : Type} [Field K] (σ : K ≃+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
    (hxB : x ∉ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      ∃ b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
        x = u * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a))⁻¹ * b := by
  have hx' : x⁻¹ ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := inv_mem hx
  have hxB' : x⁻¹ ∉ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := fun h =>
    hxB (by simpa using inv_mem h)
  have hcells := (fixed_standard_parabolic_cells TwistTag.D4 K σ).1 {a}
  have hmem : x⁻¹ ∈ ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :
      Subgroup (ModGL TwistTag.D4.tag K)) : Set (ModGL TwistTag.D4.tag K)) := hx'
  rw [hcells, Set.mem_iUnion] at hmem
  obtain ⟨⟨w, hw⟩, hxw⟩ := hmem
  rcases mem_foldedParabolicWeylGroup_singleton hw with rfl | rfl
  · exfalso
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_graphFixedRootBruhatCell.1 hxw
    apply hxB'
    rw [← hbb, canonicalRep_one, mul_one]
    exact mul_mem hb hb'
  · obtain ⟨p, ⟨hp1, hp2⟩, hp⟩ :=
      (bijOn_graphFixedRootBruhatCell σ.surjective (TwistTag.D4.orbitReflection_mem a)).2.2 hxw
    refine ⟨p.2⁻¹, inv_mem (graphFixedInversionUnipotent_le_graphFixedPosUnipotent _ hp2),
      p.1⁻¹, inv_mem hp1, ?_⟩
    have hp' : p.1 * canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection a) * p.2 = x⁻¹ := hp
    calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
      _ = _ := by rw [← hp']; group

theorem burnsideAut_d42_mul {K : Type} [Field K] (σ : K ≃+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) {Y : Subgroup (ModGL TwistTag.D4.tag K)}
    (hUY : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ Y)
    (hYP : Y ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
    (hYB : ¬ Y ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∀ x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a},
      ∃ y ∈ Y, ∃ b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom, x = y * b := by
  obtain ⟨y₀, hy₀, hy₀B⟩ := Set.not_subset.1 hYB
  obtain ⟨u₀, hu₀, b₀, hb₀, he₀⟩ := burnsideAut_d42_cell σ a (hYP hy₀) hy₀B
  intro x hx
  by_cases hxB : x ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom
  · exact ⟨1, one_mem _, x, hxB, (one_mul x).symm⟩
  · obtain ⟨u, hu, b, hb, he⟩ := burnsideAut_d42_cell σ a hx hxB
    refine ⟨u * u₀⁻¹ * y₀, mul_mem (mul_mem (hUY hu) (inv_mem (hUY hu₀))) hy₀,
      b₀⁻¹ * b, mul_mem (inv_mem hb₀) hb, ?_⟩
    rw [he, he₀]
    group

theorem burnsideAut_d42_not_solvable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hLa : Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) = 8) :
    ¬ Group.IsSolvable ↥(graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
  intro hsolv
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨R, -, -, -, -, -, hRrange, -, hker, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a
  haveI hchar : CharP ↥(orbitField TwistTag.D4 K σ.toRingHom a) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 3)
      Nat.prime_two (by norm_num) hLa
  have hRinj : Function.Injective R := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl2, hgl⟩ := hker g (MonoidHom.mem_ker.2 hg)
    have hl1 : (l : ↥(orbitField TwistTag.D4 K σ.toRingHom a)) = 1 := by
      have h2 : (2 : ↥(orbitField TwistTag.D4 K σ.toRingHom a)) = 0 := CharTwo.two_eq_zero
      have h3 : ((l : ↥(orbitField TwistTag.D4 K σ.toRingHom a)) - 1) ^ 2 = 0 := by
        linear_combination hl2 + (1 - (l : ↥(orbitField TwistTag.D4 K σ.toRingHom a))) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
    apply Subtype.ext
    rw [hgl, hl1, one_smul]
    rfl
  have hRA : R.range ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
    rw [hRrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
        (graphFixedPosUnipotent_le_graphFixedRootBorel
          (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom a c))
    · exact orbitY_mem_graphFixedParabolic a c
  have hq := CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le
    (K := ↥(orbitField TwistTag.D4 K σ.toRingHom a)) (by rw [hLa]; norm_num)
  haveI := hsolv
  have hfinj : Function.Injective
      ((Subgroup.inclusion hRA).comp R.rangeRestrict) := by
    intro g g' h
    apply hRinj
    exact congrArg (fun y : ↥(graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =>
      (y : ModGL TwistTag.D4.tag K)) h
  haveI : Group.IsSolvable
      (Matrix.SpecialLinearGroup (Fin 2) ↥(orbitField TwistTag.D4 K σ.toRingHom a)) :=
    solvable_of_solvable_injective hfinj
  haveI : Nontrivial
      (Matrix.SpecialLinearGroup (Fin 2) ↥(orbitField TwistTag.D4 K σ.toRingHom a)) := by
    haveI := hq.2.1
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2)
      ↥(orbitField TwistTag.D4 K σ.toRingHom a) ⧸ Subgroup.center _)
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x', y', fun h => hxy (h ▸ rfl)⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Matrix.SpecialLinearGroup (Fin 2)
    ↥(orbitField TwistTag.D4 K σ.toRingHom a))).ne hq.1.commutator_eq_top

theorem burnsideAut_d42_card_torus_dvd {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∣ 7 := by
  have hLa : ∀ b, Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) =
      (2 ^ 1) ^ (TwistTag.D4.orbit b).card := fun b =>
    card_orbitField_D4_orientation Nat.prime_two le_rfl hK (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ c) b
  rw [graphFixedRootTorus_eq_compatTorus σ.surjective]
  have h1 := card_compatTorus_mul (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
  rw [card_compatSubgroup, Finset.prod_congr rfl fun b _ => by rw [hLa b]] at h1
  have h2 : ∏ b : Fin TwistTag.D4.foldedTag.rank, ((2 ^ 1) ^ (TwistTag.D4.orbit b).card - 1) =
      7 := by decide
  rw [h2] at h1
  exact Dvd.intro _ h1

theorem burnsideAut_d42_core {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (Bm : Subgroup (ModGL TwistTag.D4.tag K))
    (hBC : Bm ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hodd : Odd (Nat.card ↥Bm)) (hnot3 : ¬ IsPGroup 3 ↥Bm)
    (hcases : IsMulCommutative ↥Bm ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥Bm)
    (hperm : (Bm : Set (ModGL TwistTag.D4.tag K)) *
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
        (Bm : Set (ModGL TwistTag.D4.tag K)))
    (hU2 : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (hsolv : Group.IsSolvable ↥(Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (hne : Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≠
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom) =
        7 * Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ∧
      ∃ Dm : Subgroup (ModGL TwistTag.D4.tag K), Dm ≤ Bm ∧
        Dm ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom ∧ Nat.card ↥Dm = 7 ∧
        (Bm = Dm ∨ ∃ Am : Subgroup (ModGL TwistTag.D4.tag K), Am ≤ Bm ∧ Nat.card ↥Am = 3 ∧
          Dm ⊓ Am = ⊥ ∧ (∀ d ∈ Dm, ∀ a ∈ Am, d * a = a * d) ∧ Bm = Dm ⊔ Am) := by
  classical
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have p7 : Nat.Prime 7 := by norm_num
  have hUB : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootBorel
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hB₁card := card_graphFixedRootBorel (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    σ.surjective
  have hH7 := burnsideAut_d42_card_torus_dvd hK σ hσ
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hLa : ∀ b, Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) =
      (2 ^ 1) ^ (TwistTag.D4.orbit b).card := fun b =>
    card_orbitField_D4_orientation Nat.prime_two le_rfl hK (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ c) b
  have hs : ∀ b : Fin TwistTag.D4.foldedTag.rank,
      (TwistTag.D4.orbit b).card = 3 ∨ (TwistTag.D4.orbit b).card = 1 := by
    intro b
    rcases foldedRank_D4_cases b with h | h <;> rw [h] <;> decide
  have hcopB : Nat.Coprime (Nat.card ↥Bm) (2 ^ k) :=
    (Nat.coprime_two_right.2 hodd).pow_right k
  have hBU : Bm ⊓ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom = ⊥ := by
    have h1 : Nat.card ↥(Bm ⊓ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ∣ 1 :=
      hcopB.gcd_eq_one ▸ Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left)
        (hk ▸ Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
  have hXcard : Nat.card ↥(Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) =
      Nat.card ↥Bm * 2 ^ k := by
    rw [burnsideA315x_card_sup hperm hBU, hk]
  have h3pow : ∀ j : ℕ, Nat.card ↥Bm = 3 ^ j → False := fun j hj =>
    hnot3 (IsPGroup.of_card hj)
  have hpar := CFSG.QuasithinUnique.B113Lie.D4.overgroup_le_parabolic σ
    (Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) le_sup_right (sup_le hBC hUC) hne
  suffices key : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} →
      Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom) =
          7 * Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ∧
        ∃ Dm : Subgroup (ModGL TwistTag.D4.tag K), Dm ≤ Bm ∧
          Dm ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom ∧ Nat.card ↥Dm = 7 ∧
          (Bm = Dm ∨ ∃ Am : Subgroup (ModGL TwistTag.D4.tag K), Am ≤ Bm ∧ Nat.card ↥Am = 3 ∧
            Dm ⊓ Am = ⊥ ∧ (∀ d ∈ Dm, ∀ a ∈ Am, d * a = a * d) ∧ Bm = Dm ⊔ Am) by
    rcases hpar with h | h
    · exact key _ h
    · exact key _ h
  intro a hXP
  by_cases hXB : Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom
  ·
    have hBB : Bm ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := le_sup_left.trans hXB
    have h1 : Nat.card ↥Bm ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) * 2 ^ k := by
      rw [← hk, ← hB₁card]
      exact Subgroup.card_dvd_of_le hBB
    have h2 : Nat.card ↥Bm ∣ 7 := (hcopB.dvd_of_dvd_mul_right h1).trans hH7
    rcases (Nat.dvd_prime p7).1 h2 with h7 | h7
    · exact (h3pow 0 (by rw [h7]; rfl)).elim
    · have hT7 : Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) = 7 :=
        Nat.dvd_antisymm hH7 (h7 ▸ hcopB.dvd_of_dvd_mul_right h1)
      refine ⟨by rw [hB₁card, hT7], Bm, le_rfl, hBB, h7, Or.inl rfl⟩
  ·
    have hmul := burnsideAut_d42_mul σ a le_sup_right hXP hXB
    have hrel := burnsideAut_relIndex_eq_of_mul hXP hmul
    rw [relIndex_graphFixedParabolic_singleton σ a, hLa a] at hrel
    have h1 := Subgroup.relIndex_mul_card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
      (Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    rw [hrel, hXcard] at h1
    have hUI : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
        graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓
          (Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := le_inf hUB le_sup_right
    have h2 := Subgroup.relIndex_mul_card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓
        (Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    rw [inf_eq_left.2 hUI, hk] at h2
    set m := (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).relIndex
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓
        (Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) with hm
    have hmT : m ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) := by
      have h3 : m * 2 ^ k ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) * 2 ^ k := by
        rw [h2, ← hk, ← hB₁card]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h3
    have hcm : (1 + (2 ^ 1) ^ (TwistTag.D4.orbit a).card) * m = Nat.card ↥Bm := by
      rw [← h2] at h1
      have h4 : ((1 + (2 ^ 1) ^ (TwistTag.D4.orbit a).card) * m) * 2 ^ k =
          Nat.card ↥Bm * 2 ^ k := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h4
    rcases (Nat.dvd_prime p7).1 (hmT.trans hH7) with hm1 | hm7
    ·
      rw [hm1, mul_one] at hcm
      rcases hs a with h | h <;> rw [h] at hcm
      · exact (h3pow 2 (by rw [← hcm]; norm_num)).elim
      · exact (h3pow 1 (by rw [← hcm]; norm_num)).elim
    · have hT7 : Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) = 7 :=
        Nat.dvd_antisymm hH7 (hm7 ▸ hmT)
      have hB7 : Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom) =
          7 * Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
        rw [hB₁card, hT7]
      rw [hm7] at hcm
      rcases hs a with ha | ha
      ·
        exfalso
        rw [ha] at hcm
        have hPcard := CFSG.Quasithin.card_graphFixedParabolic_singleton_d4 σ a
        rw [hLa a, ha, hB7, hk] at hPcard
        have hXeq : Bm ⊔ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom =
            graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
          refine Subgroup.eq_of_le_of_card_ge hXP ?_
          rw [hPcard, hXcard, ← hcm]
          exact le_of_eq (by ring)
        rw [hXeq] at hsolv
        exact burnsideAut_d42_not_solvable σ a (by rw [hLa a, ha]; norm_num) hsolv
      ·
        rw [ha] at hcm
        have hB21 : Nat.card ↥Bm = 21 := by rw [← hcm]; norm_num
        have hBP : Bm ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := le_sup_left.trans hXP
        have hidx : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex Bm ≤ 3 := by
          have h5 := relIndex_graphFixedParabolic_singleton σ a
          rw [hLa a, ha] at h5
          rw [← show 1 + (2 ^ 1) ^ 1 = 3 by norm_num, ← h5]
          exact Subgroup.relIndex_le_of_le_right hBP (by rw [h5]; norm_num)
        have h6 := Subgroup.relIndex_mul_card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) Bm
        rw [hB21] at h6
        have hD7 : Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ Bm) = 7 := by
          have h7 : Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ Bm) ∣
              7 * 2 ^ k := by
            rw [← hk, ← hB7]
            exact Subgroup.card_dvd_of_le inf_le_left
          have h8 : Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ Bm) ∣ 21 :=
            hB21 ▸ Subgroup.card_dvd_of_le inf_le_right
          have hcop : Nat.Coprime (Nat.card ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ Bm))
              (2 ^ k) := by
            refine Nat.Coprime.pow_right k (Nat.coprime_two_right.2 ?_)
            exact Odd.of_dvd_nat (by decide) h8
          rcases (Nat.dvd_prime p7).1 (hcop.dvd_of_dvd_mul_right h7) with h9 | h9
          · rw [h9] at h6
            omega
          · exact h9
        have hab : IsMulCommutative ↥Bm := by
          rcases hcases with hab | ⟨r, hr, hBr⟩
          · exact hab
          · exfalso
            haveI : Fact r.Prime := ⟨hr⟩
            obtain ⟨j, hj⟩ := hBr.exists_card_eq
            rw [hB21] at hj
            have h3r : 3 ∣ r ^ j := hj ▸ (by norm_num : 3 ∣ 21)
            have h7r : 7 ∣ r ^ j := hj ▸ (by norm_num : 7 ∣ 21)
            have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
              (Nat.prime_three.dvd_of_dvd_pow h3r)
            have e7 := (Nat.prime_dvd_prime_iff_eq p7 hr).1 (p7.dvd_of_dvd_pow h7r)
            omega
        obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Bm) 3 (n := 1)
          (by rw [hB21]; norm_num)
        set Am : Subgroup (ModGL TwistTag.D4.tag K) := A₀.map Bm.subtype with hAm
        have hAmB : Am ≤ Bm := Subgroup.map_subtype_le _
        have hA3 : Nat.card ↥Am = 3 := by
          rw [hAm, Subgroup.card_map_of_injective Bm.subtype_injective, hA₀, pow_one]
        set Dm := graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ Bm with hDm
        have hDA : Dm ⊓ Am = ⊥ := by
          have h1 : Nat.card ↥(Dm ⊓ Am) ∣ 1 := by
            have ha7 : Nat.card ↥(Dm ⊓ Am) ∣ 7 := hD7 ▸ Subgroup.card_dvd_of_le inf_le_left
            have ha3 : Nat.card ↥(Dm ⊓ Am) ∣ 3 := hA3 ▸ Subgroup.card_dvd_of_le inf_le_right
            have := Nat.dvd_gcd ha7 ha3
            simpa using this
          exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
        refine ⟨hB7, Dm, inf_le_right, inf_le_left, hD7, Or.inr ⟨Am, hAmB, hA3, hDA, ?_, ?_⟩⟩
        · intro d hd x hx
          have := hab.is_comm.comm (⟨d, (inf_le_right : Dm ≤ Bm) hd⟩ : ↥Bm) ⟨x, hAmB hx⟩
          exact congrArg Subtype.val this
        · have hle : Dm ⊔ Am ≤ Bm := sup_le inf_le_right hAmB
          refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
          have h7 : 7 ∣ Nat.card ↥(Dm ⊔ Am) := hD7 ▸ Subgroup.card_dvd_of_le le_sup_left
          have h3 : 3 ∣ Nat.card ↥(Dm ⊔ Am) := hA3 ▸ Subgroup.card_dvd_of_le le_sup_right
          have h21 : 21 ∣ Nat.card ↥(Dm ⊔ Am) :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 3) h7 h3
          rw [hB21]
          exact Nat.le_of_dvd Nat.card_pos h21

end D4

end CFSG.ASVolI

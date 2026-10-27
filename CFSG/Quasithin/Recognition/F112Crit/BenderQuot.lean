module

public import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.GH74.Uniqueness.Bender

structure IsBenderQuot (K : Type*) [Group K] (q i : ℕ) : Prop where
  oddGen : Subgroup.closure {x : K | Odd (orderOf x)} = ⊤
  trans : ∀ P : Sylow 2 K, ∀ x y : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    y ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    ∃ u ∈ (P : Subgroup K), y⁻¹ * u * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)
  reg : ∀ P : Sylow 2 K, ∀ u ∈ (P : Subgroup K), ∀ x : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * u * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) → u = 1
  index_eq : ∀ P : Sylow 2 K,
    (Subgroup.normalizer ((P : Subgroup K) : Set K)).index = q ^ i + 1

section Lift

variable {K K' : Type*} [Group K] [Group K']

private theorem pow_two_pow_add_eq_one {a : K} {k : ℕ} (h : a ^ 2 ^ k = 1) (m : ℕ) :
    a ^ 2 ^ (k + m) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

private theorem conj_mem_of_map_mem_normalizer {f : K →* K'} (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) {P : Subgroup K} (hP : IsPGroup 2 P) {x t : K}
    (hx : f x ∈ Subgroup.normalizer ((P.map f : Subgroup K') : Set K')) (ht : t ∈ P) :
    x * t * x⁻¹ ∈ P := by
  have hu : f (x * t * x⁻¹) ∈ P.map f := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx (f t)).mp (Subgroup.mem_map_of_mem f ht)
  obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.mp hu
  have hz : t0⁻¹ * (x * t * x⁻¹) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ht0eq, inv_mul_cancel]
  have hu_eq : x * t * x⁻¹ = t0 * (t0⁻¹ * (x * t * x⁻¹)) := by group
  have hcomm : Commute t0 (t0⁻¹ * (x * t * x⁻¹)) := Subgroup.mem_center_iff.mp (hker hz) t0
  obtain ⟨k1, hk1⟩ := hP ⟨t, ht⟩
  obtain ⟨k2, hk2⟩ := hP ⟨t0, ht0⟩
  have hk1' : t ^ 2 ^ k1 = 1 := congrArg Subtype.val hk1
  have hk2' : t0 ^ 2 ^ k2 = 1 := congrArg Subtype.val hk2
  have hpt : (x * t * x⁻¹) ^ 2 ^ (k1 + k2) = 1 := by
    rw [conj_pow, pow_two_pow_add_eq_one hk1' k2]
    simp
  have hpt0 : t0 ^ 2 ^ (k1 + k2) = 1 := by
    rw [add_comm]
    exact pow_two_pow_add_eq_one hk2' k1
  have hzp : (t0⁻¹ * (x * t * x⁻¹)) ^ 2 ^ (k1 + k2) = 1 := by
    rw [hu_eq, hcomm.mul_pow, hpt0, one_mul] at hpt
    exact hpt
  have hz1 : t0⁻¹ * (x * t * x⁻¹) = 1 := eq_one_of_odd_orderOf_of_pow (hodd _ hz) hzp
  rw [hu_eq, hz1, mul_one]
  exact ht0

private theorem normalizer_eq_comap_map {f : K →* K'} (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) {P : Subgroup K} (hP : IsPGroup 2 P) :
    Subgroup.normalizer (P : Set K) =
      (Subgroup.normalizer ((P.map f : Subgroup K') : Set K')).comap f := by
  ext x
  rw [Subgroup.mem_comap]
  refine ⟨fun hx => Subgroup.le_normalizer_map f ⟨x, hx, rfl⟩, fun hx => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_of_map_mem_normalizer hker hodd hP hx hg, fun hg => ?_⟩
  have hx' : f x⁻¹ ∈ Subgroup.normalizer ((P.map f : Subgroup K') : Set K') := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have := conj_mem_of_map_mem_normalizer hker hodd hP hx' hg
  simpa [mul_assoc] using this

private theorem exists_odd_lift {f : K →* K'} (hf : Function.Surjective f)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) {y : K'} (hy : Odd (orderOf y)) :
    ∃ x : K, f x = y ∧ Odd (orderOf x) := by
  obtain ⟨x, rfl⟩ := hf y
  have hz : x ^ orderOf (f x) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hdvd : orderOf x ∣ orderOf (f x) * orderOf (x ^ orderOf (f x)) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact ⟨x, rfl, Odd.of_dvd_nat (hy.mul (hodd _ hz)) hdvd⟩

private theorem normal_closure_odd (L : Type*) [Group L] :
    (Subgroup.closure {x : L | Odd (orderOf x)}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : Subgroup.closure {x : L | Odd (orderOf x)} ≤
      (Subgroup.closure {x : L | Odd (orderOf x)}).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    apply Subgroup.subset_closure
    show Odd (orderOf (MulAut.conj g y))
    rwa [MulEquiv.orderOf_eq]
  simpa [MulAut.conj_apply] using h1 hn

private theorem IsBenderQuot.of_map {q i : ℕ} (f : K →* K') (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center K) (hodd : ∀ z ∈ f.ker, Odd (orderOf z))
    (hsyl : ∀ P : Sylow 2 K, ∃ P' : Sylow 2 K', (P' : Subgroup K') = (P : Subgroup K).map f)
    (h : IsBenderQuot K' q i) : IsBenderQuot K q i where
  oddGen := by
    set C := Subgroup.closure {x : K | Odd (orderOf x)}
    have hmap : C.map f = ⊤ := by
      rw [eq_top_iff, ← h.oddGen, Subgroup.closure_le]
      intro y hy
      obtain ⟨x, rfl, hx⟩ := exists_odd_lift hf hodd hy
      exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure hx)
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp (hmap ▸ Subgroup.mem_top (f g))
    have hz : c⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
    have := C.mul_mem hc (Subgroup.subset_closure (hodd _ hz))
    simpa using this
  trans := by
    intro P x y hx hy
    obtain ⟨P', hP'⟩ := hsyl P
    have hN := normalizer_eq_comap_map hker hodd (P := (P : Subgroup K)) P.isPGroup'
    rw [← hP'] at hN
    rw [hN, Subgroup.mem_comap] at hx hy
    obtain ⟨u', hu', hmem⟩ := h.trans P' (f x) (f y) hx hy
    rw [hP'] at hu'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
    refine ⟨u, hu, ?_⟩
    rw [hN, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hmem
  reg := by
    intro P u hu x hx hxu
    obtain ⟨P', hP'⟩ := hsyl P
    have hN := normalizer_eq_comap_map hker hodd (P := (P : Subgroup K)) P.isPGroup'
    rw [← hP'] at hN
    rw [hN, Subgroup.mem_comap] at hx hxu
    rw [map_mul, map_mul, map_inv] at hxu
    have hu' : f u ∈ (P' : Subgroup K') := by
      rw [hP']
      exact Subgroup.mem_map_of_mem f hu
    have h1 : f u = 1 := h.reg P' (f u) hu' (f x) hx hxu
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
    exact eq_one_of_odd_orderOf_of_pow (hodd u h1) (congrArg Subtype.val hk)
  index_eq := by
    intro P
    obtain ⟨P', hP'⟩ := hsyl P
    have hN := normalizer_eq_comap_map hker hodd (P := (P : Subgroup K)) P.isPGroup'
    rw [← hP'] at hN
    rw [hN, Subgroup.index_comap_of_surjective _ hf]
    exact h.index_eq P'

end Lift

theorem IsBenderQuot.of_mulEquiv {K K' : Type*} [Group K] [Group K'] {q i : ℕ} (e : K ≃* K')
    (h : IsBenderQuot K q i) : IsBenderQuot K' q i := by
  have hker : ∀ z ∈ e.symm.toMonoidHom.ker, z = 1 := fun z hz =>
    e.symm.injective (by simpa using hz)
  refine IsBenderQuot.of_map e.symm.toMonoidHom e.symm.surjective
    (fun z hz => by rw [hker z hz]; exact Subgroup.one_mem _)
    (fun z hz => by rw [hker z hz, orderOf_one]; exact odd_one) (fun P => ?_) h
  refine ⟨P.comapOfInjective e.toMonoidHom e.injective (by simp), ?_⟩
  exact Subgroup.comap_equiv_eq_map_symm' e P

private theorem closure_odd_eq_top_of_simple {L : Type*} [Group L] [IsSimpleGroup L] {x : L}
    (hx1 : x ≠ 1) (hx : Odd (orderOf x)) :
    Subgroup.closure {y : L | Odd (orderOf y)} = ⊤ := by
  haveI := normal_closure_odd L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {y : L | Odd (orderOf y)})
    with h | h
  · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_closure hx)) hx1
  · exact h

private theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem exists_odd_ne_one_of_benderType {K : Type*}
    [Group K] [Finite K] {n i e : ℕ} (h : BenderType K n i e) :
    ∃ x : K, x ≠ 1 ∧ Odd (orderOf x) := by
  have hn : 2 ≤ n := by
    rcases h.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, rfl⟩ | ⟨-, -, hn⟩
    · exact hn
    · omega
    · exact hn
  have h4 := four_le_two_pow hn
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  have hD : cartan ((default : Sylow 2 K) : Subgroup K) t ≠ ⊥ := by
    intro hbot
    have h1 := Subgroup.card_eq_one.mpr hbot
    rw [hc.card_cartan] at h1
    have h2 := Nat.eq_one_of_mul_eq_one_right h1
    omega
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD
  exact ⟨x, fun h1 => hx (Subtype.ext h1), Odd.of_dvd_nat hc.odd_card_cartan
    (Subgroup.orderOf_dvd_natCard _ x.2)⟩

theorem BenderType.isBenderQuot {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : IsBenderQuot K (2 ^ n) i where
  oddGen := by
    haveI := h.isSimple
    obtain ⟨x, hx1, hx⟩ := exists_odd_ne_one_of_benderType h
    exact closure_odd_eq_top_of_simple hx1 hx
  trans := by
    intro P x y hx hy
    obtain ⟨t, hc⟩ := h.exists_benderCore P
    obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hx
    obtain ⟨p', hp', m', hm', rfl⟩ := hc.bruhat hy
    refine ⟨p' * p⁻¹, (P : Subgroup K).mul_mem hp' ((P : Subgroup K).inv_mem hp), ?_⟩
    have : (p' * t * m')⁻¹ * (p' * p⁻¹) * (p * t * m) = m'⁻¹ * m := by group
    rw [this]
    exact (borel (P : Subgroup K)).mul_mem ((borel (P : Subgroup K)).inv_mem hm') hm
  reg := by
    intro P u hu x hx hxu
    obtain ⟨t, hc⟩ := h.exists_benderCore P
    have hxinv : x⁻¹ ∉ borel (P : Subgroup K) := fun hm => hx (by
      have := (borel (P : Subgroup K)).inv_mem hm
      rw [inv_inv] at this
      exact this)
    have hodd := hc.strong.2.2 x⁻¹ hxinv
    have hmem : u ∈ borel (P : Subgroup K) ⊓ conjugate (borel (P : Subgroup K)) x⁻¹ := by
      refine Subgroup.mem_inf.mpr ⟨le_borel _ hu, ?_⟩
      rw [mem_conjugate_iff_mul_inv, inv_inv]
      exact hxu
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
    exact eq_one_of_odd_orderOf_of_pow
      (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hmem)) (congrArg Subtype.val hk)
  index_eq := fun P => (h.exists_benderCore P).choose_spec.index_eq

theorem IsBenderQuot.of_surjective {K K' : Type*} [Group K] [Group K'] [Finite K] {q i : ℕ}
    (f : K →* K') (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) (h : IsBenderQuot K' q i) : IsBenderQuot K q i :=
  IsBenderQuot.of_map f hf hker hodd (fun P => ⟨P.mapSurjective hf, rfl⟩) h

section Listed

theorem cases_of_listed_of_not_isSolvable {K : Type*} [Group K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) :
    (∃ n : ℕ, 2 ≤ n ∧
      Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) ∨
    (∃ a : ℕ, 1 ≤ a ∧ Nonempty (K ≃* Sz a)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (K ≃* StatedSU 3 (2 ^ n) F)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (K ≃* StatedProj (StatedSU 3 (2 ^ n) F))) := by
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact absurd (isSolvable_of_isL2Quot_one ⟨e⟩) hs
    · exact Or.inl ⟨n, h2, ⟨e⟩⟩
  · rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      exact absurd (isSolvable_of_equiv_sz_zero e) hs
    · exact Or.inr (Or.inl ⟨a, h1, ⟨e⟩⟩)
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      have := isSolvable_statedSU_one (F := F) hF
      exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hs
    · exact Or.inr (Or.inr (Or.inl ⟨n, h2, F, i1, i2, hF, ⟨e⟩⟩))
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      have := isSolvable_statedProj_one (F := F) hF
      exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hs
    · exact Or.inr (Or.inr (Or.inr ⟨n, h2, F, i1, i2, hF, ⟨e⟩⟩))
  · exact absurd (isSolvable_of_equiv_dihedral_five e) hs

section Unitary

variable {n : ℕ} {F : Type} [Field F] [Finite F]

private theorem exists_cover_statedSU (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ (e : ℕ) (π : StatedSU 3 (2 ^ n) F →* StatedProj (StatedSU 3 (2 ^ n) F)),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center (StatedSU 3 (2 ^ n) F) ∧
        (∀ z ∈ π.ker, Odd (orderOf z)) ∧
        BenderType (StatedProj (StatedSU 3 (2 ^ n) F)) n 3 e := by
  obtain ⟨e, hB⟩ := benderType_statedProj hn hF
  refine ⟨e, QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F)),
    QuotientGroup.mk'_surjective _, ?_, ?_, hB⟩
  · rw [QuotientGroup.ker_mk']
    exact statedSU_scalars_le_center
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    exact statedSU_three_scalars_odd z hz

private theorem isBenderQuot_statedSU (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : IsBenderQuot (StatedSU 3 (2 ^ n) F) (2 ^ n) 3 := by
  obtain ⟨e, π, hπ, hker, hodd, hB⟩ := exists_cover_statedSU hn hF
  haveI : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
  exact IsBenderQuot.of_surjective π hπ hker hodd (BenderType.isBenderQuot hB)

end Unitary

private theorem sixtyFive_le_two_pow_cube {n : ℕ} (hn : 2 ≤ n) : 65 ≤ (2 ^ n) ^ 3 + 1 := by
  have h64 : 4 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left (four_le_two_pow hn) 3
  omega

theorem exists_isBenderQuot_of_listed {K : Type} [Group K] [Finite K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) :
    ∃ n i : ℕ, 2 ≤ n ∧ IsBenderQuot K (2 ^ n) i ∧
      ((i = 1 ∧ IsL2Quot n K) ∨ 65 ≤ (2 ^ n) ^ i + 1) := by
  rcases cases_of_listed_of_not_isSolvable hK hs with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩
  · exact ⟨n, 1, hn, BenderType.isBenderQuot (BenderType.linear n hn e), Or.inl ⟨rfl, ⟨e⟩⟩⟩
  · have hB : BenderType K (2 * a + 1) 2 1 :=
      BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
    refine ⟨2 * a + 1, 2, by omega, BenderType.isBenderQuot hB, Or.inr ?_⟩
    have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 8 ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    omega
  · exact ⟨n, 3, hn, (isBenderQuot_statedSU hn hF).of_mulEquiv e.symm,
      Or.inr (sixtyFive_le_two_pow_cube hn)⟩
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact ⟨n, 3, hn, BenderType.isBenderQuot (hB.of_mulEquiv e.symm),
      Or.inr (sixtyFive_le_two_pow_cube hn)⟩

private theorem isQuasisimple_of_central_cover {G Q : Type*} [Group G] [Group Q] [IsSimpleGroup Q]
    (π : G →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hperf : Group.IsPerfect G) (hnc : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple G := by
  let e : G ⧸ π.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  haveI : IsSimpleGroup (G ⧸ π.ker) := e.isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient π.ker hker hperf
    inferInstance ?_
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

private theorem isQuasisimple_of_isSimpleGroup {L : Type*} [Group L] [IsSimpleGroup L]
    (hs : ¬ Group.IsSolvable L) : CFSG.IsQuasisimple L := by
  have hnc : ∃ a b : L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hs (IsSimpleGroup.comm_iff_isSolvable.mp hcon)
  have hperf : Group.IsPerfect L := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
    · exact absurd ⟨⟨1, by rw [derivedSeries_one]; exact h⟩⟩ hs
    · exact ⟨h⟩
  exact isQuasisimple_of_central_cover (MonoidHom.id L) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) hperf hnc

private theorem isQuasisimple_of_equiv_statedSU {n : ℕ} {F : Type} [Field F] [Finite F]
    {K : Type*} [Group K] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : K ≃* StatedSU 3 (2 ^ n) F) : CFSG.IsQuasisimple K := by
  obtain ⟨e', π, hπ, hker, -, hB⟩ := exists_cover_statedSU hn hF
  haveI : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
  haveI := hB.isSimple
  have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => by
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (StatedSU 3 (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
  haveI : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine isQuasisimple_of_central_cover (π.comp e.toMonoidHom) (hπ.comp e.surjective) ?_
    inferInstance ?_
  · intro z hz
    have hz' : e z ∈ π.ker := hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hker hz') (e g)
  · by_contra hcon
    push Not at hcon
    exact not_isSolvable_statedProj hn hF (IsSimpleGroup.comm_iff_isSolvable.mp hcon)

theorem isQuasisimple_of_listed {K : Type} [Group K] [Finite K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) : CFSG.IsQuasisimple K := by
  rcases cases_of_listed_of_not_isSolvable hK hs with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩
  · haveI := (BenderType.linear n hn e).isSimple
    exact isQuasisimple_of_isSimpleGroup hs
  · haveI := (BenderType.suzuki a ha
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))).isSimple
    exact isQuasisimple_of_isSimpleGroup hs
  · exact isQuasisimple_of_equiv_statedSU hn hF e
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    haveI := (hB.of_mulEquiv e.symm).isSimple
    exact isQuasisimple_of_isSimpleGroup hs

end Listed

end CFSG.Quasithin.F112Crit

end

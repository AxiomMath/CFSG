module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.GH74.Uniqueness.Bender

@[expose] def OddOffSolvable {X : Type*} [Group X] (d : X) : Prop :=
  Odd (orderOf d) ∧ ∀ N : Subgroup X, N.Normal → d ∈ N → ¬ Group.IsSolvable N

theorem OddOffSolvable.of_map {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (hπ : Function.Surjective π) {d : X} (hd : OddOffSolvable (π d)) (hodd : Odd (orderOf d)) :
    OddOffSolvable d := by
  refine ⟨hodd, fun N hN hdN hNs => hd.2 (N.map π) (hN.map π hπ)
    (Subgroup.mem_map_of_mem π hdN) ?_⟩
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π N)

theorem exists_oddOffSolvable_of_benderType {X : Type*} [Group X]
    [Finite X] {n i e : ℕ} (hB : BenderType X n i e) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hodd : ¬ 2 ∣ P.index) :
    ∃ d ∈ Subgroup.normalizer (P : Set X), OddOffSolvable d := by
  have hQ : ((hP.toSylow hodd : Sylow 2 X) : Subgroup X) = P := IsPGroup.toSylow_coe hP hodd
  obtain ⟨t, hc⟩ := hB.exists_benderCore (hP.toSylow hodd)
  rw [hQ] at hc
  have hn : 2 ≤ n := hB.two_le.2
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard := hc.card_commutator_cartan
  have hne : ⁅cartan P t, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨hdD, hinv⟩ := hc.mem_commutator_cartan_iff.mp a.2
  have hd1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
  have hdodd : Odd (orderOf (a : X)) :=
    Odd.of_dvd_nat hc.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hdD)
  refine ⟨a, cartan_le_borel P t hdD, hdodd, ?_⟩
  intro N hN haN hNs
  have hsimple : IsSimpleGroup X := hB.isSimple
  have := hN
  rcases hsimple.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact hd1 (by simpa [hbot] using haN)
  · subst htop
    have hXs : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm.toMonoidHom)
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm.injective
    have hcomm : (a : X) * t = t * (a : X) :=
      (IsSimpleGroup.comm_iff_isSolvable (G := X)).mpr hXs _ _
    have h1 : t * (a : X) * t = (a : X)⁻¹ := hinv
    have h2 : (a : X)⁻¹ = (a : X) := by
      rw [← h1, ← hcomm, mul_assoc, hc.sq_eq_one, mul_one]
    have h3 : (a : X) ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.mpr h2.symm
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact hd1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hdodd
      exact absurd hdodd (by decide)

theorem mem_normalizer_of_central_cover {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (hZ : π.ker ≤ Subgroup.center X) (hodd : ∀ z ∈ π.ker, Odd (orderOf z)) {P : Subgroup X}
    (hP : IsPGroup 2 P) {x : X}
    (hx : π x ∈ Subgroup.normalizer ((P.map π : Subgroup X') : Set X')) :
    x ∈ Subgroup.normalizer (P : Set X) := by
  have hexp : ∀ t ∈ P, ∃ k : ℕ, t ^ 2 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hclaim : ∀ x : X, π x ∈ Subgroup.normalizer ((P.map π : Subgroup X') : Set X') →
      ∀ t ∈ P, x * t * x⁻¹ ∈ P := by
    intro x hx t ht
    have hu : π (x * t * x⁻¹) ∈ P.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hx (π t)).mp (Subgroup.mem_map_of_mem π ht)
    obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.mp hu
    obtain ⟨z, hzdef⟩ : ∃ z, z = t0⁻¹ * (x * t * x⁻¹) := ⟨_, rfl⟩
    have hz : z ∈ π.ker := by
      rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, ht0eq, inv_mul_cancel]
    have hu_eq : x * t * x⁻¹ = t0 * z := by rw [hzdef]; group
    have hcomm : Commute t0 z := Subgroup.mem_center_iff.mp (hZ hz) t0
    obtain ⟨k1, hk1⟩ := hexp t ht
    obtain ⟨k2, hk2⟩ := hexp t0 ht0
    have hpt : (x * t * x⁻¹) ^ 2 ^ (k1 + k2) = 1 := by
      rw [conj_pow, pow_add, pow_mul, hk1, one_pow]
      simp
    have hpt0 : t0 ^ 2 ^ (k1 + k2) = 1 := by
      rw [add_comm, pow_add, pow_mul, hk2, one_pow]
    have hzp : z ^ 2 ^ (k1 + k2) = 1 := by
      rw [hu_eq, hcomm.mul_pow, hpt0, one_mul] at hpt
      exact hpt
    have hz1 : z = 1 := eq_one_of_odd_orderOf_of_pow (hodd z hz) hzp
    rw [hu_eq, hz1, mul_one]
    exact ht0
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hclaim x hx g hg, fun hg => ?_⟩
  have hx' : π x⁻¹ ∈ Subgroup.normalizer ((P.map π : Subgroup X') : Set X') := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have := hclaim x⁻¹ hx' _ hg
  simpa [mul_assoc] using this

theorem exists_oddOffSolvable_of_central_cover {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center X)
    (hodd : ∀ z ∈ π.ker, Odd (orderOf z)) {P : Subgroup X} (hP : IsPGroup 2 P)
    (h : ∃ d' ∈ Subgroup.normalizer ((P.map π : Subgroup X') : Set X'), OddOffSolvable d') :
    ∃ d ∈ Subgroup.normalizer (P : Set X), OddOffSolvable d := by
  obtain ⟨d', hd'N, hd'⟩ := h
  obtain ⟨d, rfl⟩ := hπ d'
  refine ⟨d, mem_normalizer_of_central_cover π hZ hodd hP hd'N, ?_⟩
  have hz : d ^ orderOf (π d) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have h1 : d ^ (orderOf (π d) * orderOf (d ^ orderOf (π d))) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one]
  exact OddOffSolvable.of_map π hπ hd'
    (Odd.of_dvd_nat (hd'.1.mul (hodd _ hz)) (orderOf_dvd_of_pow_eq_one h1))

theorem IsBenderQuot.exists_oddOffSolvable {n : ℕ} (hn : 2 ≤ n)
    {X : Type} [Group X] [Finite X] (hX : IsBenderQuot n X) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hodd : ¬ 2 ∣ P.index) : ∃ d ∈ Subgroup.normalizer (P : Set X), OddOffSolvable d := by
  rcases hX with hL | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · obtain ⟨e⟩ := hL
    exact exists_oddOffSolvable_of_benderType (BenderType.linear n hn e) hP hodd
  · exact exists_oddOffSolvable_of_benderType (BenderType.suzuki a (by omega)
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))) hP hodd
  ·
    set S0 : Subgroup (StatedSU 3 (2 ^ n) F) :=
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) with hS0
    let π : X →* StatedProj (StatedSU 3 (2 ^ n) F) :=
      (QuotientGroup.mk' S0).comp e.toMonoidHom
    have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective S0).comp e.surjective
    have hker : ∀ x, x ∈ π.ker ↔ e x ∈ S0 := fun x => by
      rw [MonoidHom.mem_ker]
      exact QuotientGroup.eq_one_iff (e x)
    have hZ : π.ker ≤ Subgroup.center X := by
      intro x hx
      have hc := statedSU_scalars_le_center ((hker x).mp hx)
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro y
      apply e.injective
      simpa using hc (e y)
    have hodd' : ∀ z ∈ π.ker, Odd (orderOf z) := fun z hz => by
      rw [← MulEquiv.orderOf_eq e]
      exact statedSU_three_scalars_odd _ ((hker z).mp hz)
    have : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
    obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    refine exists_oddOffSolvable_of_central_cover π hπ hZ hodd' hP ?_
    exact exists_oddOffSolvable_of_benderType hB (hP.map π)
      (fun hd => hodd (hd.trans (Subgroup.index_map_dvd P hπ)))
  ·
    obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact exists_oddOffSolvable_of_benderType (hB.of_mulEquiv e.symm) hP hodd

end CFSG.Quasithin

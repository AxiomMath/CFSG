module

public import CFSG.Quasithin.SteinbergCDEvenLinearThreeParabolicOddCyclic

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type*} [Group G] [Finite G]

theorem original_noncyclic_prime_witness_forbids_full_even_linear_three_parabolic_image
    (D K : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (X : Subgroup G) (hXD : X ≤ D)
    (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K)
    (hpg : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hnc : ¬IsCyclic (X ⧸ CFSG.pCore 2 X))
    {k : Type*} [Field k] [Finite k] (hk : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k)
    (φ : K →* projectiveSL 3 k) (hker : ¬p ∣ Nat.card φ.ker) :
    (∀ E : Submodule k (Fin 3 → k), (finrank k E = 1 ∨ finrank k E = 2) →
      ((D ⊓ K).subgroupOf K).map φ ≠ (stabilizer E).map (proj 3 k)) ∧
    Group.IsSolvable ((X.subgroupOf K).map φ) ∧
    (((X.subgroupOf K).map φ).subgroupOf (((D ⊓ K).subgroupOf K).map φ)).Normal ∧
    ∀ P : Sylow p X, ¬IsCyclic (((P : Subgroup X).map (Subgroup.inclusion hXK)).map φ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A := CFSG.pCore 2 X with hAdef
  have hXsolv : Group.IsSolvable X := by
    have hA2 : IsPGroup 2 A := CFSG.pCore_isPGroup
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsSolvable A := by
      have : Group.IsNilpotent A := hA2.isNilpotent
      infer_instance
    have : Group.IsSolvable (X ⧸ A) := by
      have : Group.IsNilpotent (X ⧸ A) := hpg.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range A.subtype (QuotientGroup.mk' A)
      (by rw [QuotientGroup.ker_mk', range_subtype])
  have hφXsolv : Group.IsSolvable ((X.subgroupOf K).map φ) := by
    have : Group.IsSolvable (X.subgroupOf K) :=
      Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hXK).symm.toMonoidHom)
        (subgroupOfEquivOfLe hXK).symm.surjective
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective (X.subgroupOf K))
  have hle : (X.subgroupOf K).map φ ≤ ((D ⊓ K).subgroupOf K).map φ := by
    refine map_mono fun x hx => ?_
    exact mem_subgroupOf.2 ⟨hXD (mem_subgroupOf.1 hx), x.2⟩
  have hnorm : (((X.subgroupOf K).map φ).subgroupOf (((D ⊓ K).subgroupOf K).map φ)).Normal := by
    refine ⟨fun y hy z => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨d, hd, hdz⟩ := z.2
    rw [coe_mul, coe_mul, coe_inv, ← hxy, ← hdz, ← map_inv, ← map_mul, ← map_mul]
    refine ⟨d * x * d⁻¹, mem_subgroupOf.2 ?_, rfl⟩
    have hdD : ((d : K) : G) ∈ D := (mem_subgroupOf.1 hd).1
    have hxX : ((x : K) : G) ∈ X := mem_subgroupOf.1 hx
    have h1 := hXn.conj_mem ⟨_, hXD hxX⟩ (mem_subgroupOf.2 hxX) ⟨_, hdD⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hequiv : ∀ P : Sylow p X, Nonempty (↥(P : Subgroup X) ≃*
      ↥(((P : Subgroup X).map (Subgroup.inclusion hXK)).map φ)) := by
    intro P
    let ψ : (P : Subgroup X) →* ((P : Subgroup X).map (Subgroup.inclusion hXK)).map φ :=
      ((φ.comp (Subgroup.inclusion hXK)).comp (P : Subgroup X).subtype).codRestrict _
        fun y => ⟨Subgroup.inclusion hXK y, ⟨y, y.2, rfl⟩, rfl⟩
    have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have h1 : φ (Subgroup.inclusion hXK (y : X)) = 1 := congrArg Subtype.val hy
      obtain ⟨n, hn⟩ := P.isPGroup' y
      have hord : orderOf (Subgroup.inclusion hXK (y : X)) ∣ p ^ n := by
        refine orderOf_dvd_of_pow_eq_one ?_
        have := congrArg (fun z : (P : Subgroup X) => Subgroup.inclusion hXK (z : X)) hn
        simpa using this
      have hker' : orderOf (Subgroup.inclusion hXK (y : X)) ∣ Nat.card φ.ker :=
        Subgroup.orderOf_dvd_natCard φ.ker (MonoidHom.mem_ker.2 h1)
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hord
      rcases m with _ | m
      · rw [pow_zero, orderOf_eq_one_iff] at hm
        exact Subtype.ext (Subgroup.inclusion_injective hXK (by rw [hm, Subgroup.coe_one, map_one]))
      · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero m)).trans (hm ▸ hker')) hker
    have hsurj : Function.Surjective ψ := by
      rintro ⟨_, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩
  have hPnc : ∀ P : Sylow p X,
      ¬IsCyclic (((P : Subgroup X).map (Subgroup.inclusion hXK)).map φ) := by
    intro P hcyc
    obtain ⟨e⟩ := hequiv P
    have hPcyc : IsCyclic (P : Subgroup X) := isCyclic_of_surjective e.symm.toMonoidHom
      e.symm.surjective
    set S := P.mapSurjective (QuotientGroup.mk'_surjective A) with hS
    have hStop : ((P : Subgroup X).map (QuotientGroup.mk' A)) = ⊤ :=
      (S.is_maximal' (hpg.to_subgroup ⊤) le_top).symm
    have hmap : IsCyclic ((P : Subgroup X).map (QuotientGroup.mk' A)) :=
      isCyclic_of_surjective ((QuotientGroup.mk' A).subgroupMap (P : Subgroup X))
        ((QuotientGroup.mk' A).subgroupMap_surjective (P : Subgroup X))
    rw [hStop] at hmap
    exact hnc (isCyclic_of_surjective (⊤ : Subgroup (X ⧸ A)).subtype fun y => ⟨⟨y, mem_top y⟩, rfl⟩)
  refine ⟨fun E hE heq => ?_, hφXsolv, hnorm, hPnc⟩
  obtain ⟨hcyc, -⟩ := SteinbergCD.even_projective_linear_three_parabolic_solvable_normal_odd_cyclic
    hk hk4 E hE heq hle hnorm hφXsolv
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p X))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 P.isPGroup'
  obtain ⟨e⟩ := hequiv P
  refine hPnc P (hcyc _ (map_mono fun y hy => ?_) p m hp hp2 ?_)
  · obtain ⟨z, -, rfl⟩ := hy
    exact mem_subgroupOf.2 z.2
  · rw [← Nat.card_congr e.toEquiv, hm]

end CFSG.Quasithin.SteinbergBT

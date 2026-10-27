module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem S57.holt_mod (hH : KF_HoltThm1) {C Z M T : Subgroup G} (hZC : Z ≤ C) (hMC : M ≤ C)
    (hZn : ∀ c ∈ C, ∀ x ∈ Z, c * x * c⁻¹ ∈ Z) (hZM : Z ⊓ M = ⊥)
    (hM : StatedClassicalModel M .PSp 3 2 1) {z : G} (hz : z ∈ M) (hz2 : orderOf z = 2)
    (hTC : T ≤ C) (hTz : T ≤ Cen z) (hzT : z ∈ T) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ P : Subgroup G, P ≤ C → IsPGroup 2 P → T ≤ P → P = T)
    (hfix : ∀ g ∈ C, g⁻¹ * z * g ∈ Z ⊔ M → g ∈ Z ⊔ M) : C ≤ Z ⊔ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z' := Z.subgroupOf C with hZ'
  haveI hZ'n : Z'.Normal := ⟨fun x hx c => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hZn c c.2 x hx⟩
  set π := QuotientGroup.mk' Z' with hπ
  set M' := M.subgroupOf C with hM'
  set Mb := M'.map π with hMb
  have hker : ∀ {c : ↥C}, π c = 1 → (c : G) ∈ Z := fun {c} h => by
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ', Subgroup.mem_subgroupOf] at h
  have hinj : Function.Injective (π.comp M'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : ((m : ↥C) : G) ∈ Z ⊓ M := Subgroup.mem_inf.mpr ⟨hker hm, m.2⟩
    rw [hZM, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hrange : (π.comp M'.subtype).range = Mb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eM : ↥M' ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMC
  have e : ↥Mb ≃* ↥M :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans eM)
  have hMb' : StatedClassicalModel ↥Mb .PSp 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM
  have hmemMb : ∀ c : ↥C, π c ∈ Mb ↔ (c : G) ∈ Z ⊔ M := fun c => by
    constructor
    · rintro ⟨m, hm, hmc⟩
      have h1 : π (m⁻¹ * c) = 1 := by rw [map_mul, map_inv, hmc, inv_mul_cancel]
      have h2 := hker h1
      have : (c : G) = (m : G) * ((m⁻¹ * c : ↥C) : G) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hm))
        (Subgroup.mem_sup_left h2)
    · intro hc
      have hc' : c ∈ (Z ⊔ M).subgroupOf C := Subgroup.mem_subgroupOf.mpr hc
      rw [Subgroup.subgroupOf_sup hZC hMC] at hc'
      have h := Subgroup.mem_map_of_mem π hc'
      rw [Subgroup.map_sup] at h
      have hZb : Z'.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      rwa [hZb, bot_sup_eq] at h
  set zc : ↥C := ⟨z, hMC hz⟩ with hzc
  have hzM : π zc ∈ Mb := (hmemMb zc).mpr (Subgroup.mem_sup_right hz)
  have hz1 : π zc ≠ 1 := fun h => by
    have h1 : z ∈ Z ⊓ M := Subgroup.mem_inf.mpr ⟨hker h, hz⟩
    rw [hZM, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz2
    omega
  have hzo : orderOf (π zc) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    rw [← map_pow]
    have : zc ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hzc, ← hz2, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [this, map_one]
  have hT'2 : IsPGroup 2 (T.subgroupOf C) := hT2.comap_of_injective C.subtype C.subtype_injective
  let P : Sylow 2 ↥C :=
    { toSubgroup := T.subgroupOf C
      isPGroup' := hT'2
      is_maximal' := fun {Q} hQ hTQ => by
        have hQC : Q.map C.subtype ≤ C := Subgroup.map_subtype_le Q
        have hQ2 : IsPGroup 2 (Q.map C.subtype) := hQ.map C.subtype
        have hTQ' : T ≤ Q.map C.subtype := fun t ht =>
          ⟨⟨t, hTC ht⟩, hTQ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
        have heq := hTmax _ hQC hQ2 hTQ'
        ext q
        rw [Subgroup.mem_subgroupOf, ← heq]
        exact ⟨fun h => ⟨q, h, rfl⟩, fun ⟨q', hq', hqq⟩ => by
          rw [Subtype.ext hqq] at hq'; exact hq'⟩ }
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z'
  have hS : ∃ S : Sylow 2 (↥C ⧸ Z'), π zc ∈ (S : Subgroup (↥C ⧸ Z')) ∧
      (S : Subgroup (↥C ⧸ Z')) ≤ Cen (π zc) := by
    refine ⟨P.mapSurjective hsurj, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨zc, Subgroup.mem_subgroupOf.mpr hzT, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
        (hTz (Subgroup.mem_subgroupOf.mp ht)))
  have hfix' : ∃! q : (↥C ⧸ Z') ⧸ Mb, π zc • q = q := by
    refine ⟨QuotientGroup.mk 1, ?_, fun q hq => ?_⟩
    · show π zc • (QuotientGroup.mk 1 : (↥C ⧸ Z') ⧸ Mb) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
      exact Subgroup.inv_mem _ hzM
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨c, rfl⟩ := hsurj x
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hq
      have h1 : π (c⁻¹ * zc * c) ∈ Mb := by
        have : (π zc * π c)⁻¹ * π c = (π (c⁻¹ * zc * c))⁻¹ := by
          simp only [map_mul, map_inv]; group
        rw [this] at hq
        simpa using Subgroup.inv_mem _ hq
      have h2 := (hmemMb _).mp h1
      have h3 := hfix c c.2 (by simpa [hzc] using h2)
      rw [QuotientGroup.eq, mul_one]
      exact Subgroup.inv_mem _ ((hmemMb c).mpr h3)
  have htop := hH _ Mb hMb' (π zc) hzo hzM hS hfix'
  intro c hc
  have : π ⟨c, hc⟩ ∈ Mb := by rw [htop]; exact Subgroup.mem_top _
  exact (hmemMb ⟨c, hc⟩).mp this

end CFSG.RankThree.PartTwo.Sec21.FF81

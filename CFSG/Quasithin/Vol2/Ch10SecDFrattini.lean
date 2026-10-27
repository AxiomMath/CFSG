module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mem_preimage_pCore {H S : Subgroup G} (hS : IsSylowTwoOf S H)
    (C' : Subgroup ↥H) [C'.Normal] {p : ↥H}
    (hp : QuotientGroup.mk' C' p ∈ CFSG.pCore 2 (↥H ⧸ C')) :
    ∃ c ∈ C', ∃ r : ↥H, (r : G) ∈ S ∧ QuotientGroup.mk' C' r ∈ CFSG.pCore 2 (↥H ⧸ C') ∧
      p = c * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.comap_of_injective _ (Subgroup.subtype_injective _)
  let SH : Sylow 2 ↥H := hS2.toSylow hS.2.2
  let SQ : Sylow 2 (↥H ⧸ C') := SH.mapSurjective (QuotientGroup.mk'_surjective C')
  have hP2 : IsPGroup 2 (CFSG.pCore 2 (↥H ⧸ C')) := CFSG.pCore_isPGroup
  have hle : CFSG.pCore 2 (↥H ⧸ C') ≤ SQ := hP2.le_sylow_of_normal SQ
  obtain ⟨r', hr', hrp⟩ := hle hp
  have hr'S : (r' : G) ∈ S := by
    have h1 : r' ∈ S.subgroupOf H := hr'
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨p * r'⁻¹, ?_, r', hr'S, hrp ▸ hp, by group⟩
  have h1 : QuotientGroup.mk' C' p = QuotientGroup.mk' C' r' := hrp.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have := (Subgroup.Normal.mem_comm inferInstance h1)
  simpa [mul_assoc] using C'.inv_mem this

theorem isSylowTwoOf_map_conj {R N : Subgroup G} (hR : IsSylowTwoOf R N) {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    IsSylowTwoOf (R.map (MulAut.conj g).toMonoidHom) N := by
  have hle : R.map (MulAut.conj g).toMonoidHom ≤ N := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg r).mp (hR.1 hr)
  refine ⟨hle, hR.2.1.map _, ?_⟩
  have hcard : Nat.card (R.map (MulAut.conj g).toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h1 := Subgroup.relIndex_mul_card R N
  have h2 := Subgroup.relIndex_mul_card (R.map (MulAut.conj g).toMonoidHom) N
  rw [inf_of_le_left hR.1] at h1
  rw [inf_of_le_left hle, hcard] at h2
  have hpos : 0 < Nat.card R := Nat.card_pos
  have heq : (R.map (MulAut.conj g).toMonoidHom).relIndex N = R.relIndex N :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
  rw [← Subgroup.relIndex, heq]
  exact hR.2.2

theorem exists_mul_mem_normalizer {R N : Subgroup G} (hR : IsSylowTwoOf R N) {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    ∃ n ∈ N, n * g ∈ Subgroup.normalizer (R : Set G) := by
  obtain ⟨h, hhN, hh⟩ := A4.exists_conj_of_isSylowTwoOf hR (isSylowTwoOf_map_conj hR hg)
  refine ⟨h⁻¹, N.inv_mem hhN, A4.mem_normalizer_of_conj_mem fun r hr => ?_⟩
  have := (hh (g * r * g⁻¹)).mp ⟨r, hr, rfl⟩
  simpa [mul_assoc] using this

theorem exists_mul_normalizer_of_cover {H N R C : Subgroup G} (hR : IsSylowTwoOf R N)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hcov : ∀ n ∈ N, ∃ c ∈ C, ∃ r ∈ R, n = c * r) {g : G} (hg : g ∈ H) :
    ∃ c ∈ C, ∃ m ∈ H ⊓ Subgroup.normalizer (R : Set G), g = c * m := by
  obtain ⟨n, hnN, hng⟩ := exists_mul_mem_normalizer hR (hHN hg)
  obtain ⟨c, hc, r, hr, hcr⟩ := hcov n⁻¹ (N.inv_mem hnN)
  refine ⟨c, hc, r * (n * g), ⟨H.mul_mem (hNH (hR.1 hr)) (H.mul_mem (hNH hnN) hg),
    (Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer hr) hng⟩, ?_⟩
  calc g = n⁻¹ * (n * g) := by group
    _ = c * r * (n * g) := by rw [hcr]
    _ = c * (r * (n * g)) := by group

end CFSG.Quasithin.Vol2.Ch10.SecD

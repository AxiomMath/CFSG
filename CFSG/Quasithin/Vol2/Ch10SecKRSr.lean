module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G27

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

omit [Finite G] in
theorem rho_mem_normalizer {S : Type*} [Group S] (ρ : ↥J →* S) (hLJ : L ≤ J) {d : G}
    (hdJ : d ∈ J) (hdN : d ∈ Subgroup.normalizer (L : Set G)) :
    ρ ⟨d, hdJ⟩ ∈ Subgroup.normalizer ((piL ρ hLJ).range : Set S) :=
  image_le_normalizer ρ hLJ (R := Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdN)
    ⟨⟨d, hdJ⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers d), rfl⟩

theorem rho_comm_mem_pCoreOf {S : Type*} [Group S] (ρ : ↥J →* S) (hLJ : L ≤ J) {d : G}
    (hdJ : d ∈ J) (hdc : ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∀ x ∈ (piL ρ hLJ).range, ρ ⟨d, hdJ⟩ * x * (ρ ⟨d, hdJ⟩)⁻¹ * x⁻¹ ∈
      pCoreOf 2 (piL ρ hLJ).range := by
  rintro _ ⟨l, rfl⟩
  have hmem := hdc l l.2
  have hL : d * l * d⁻¹ * (l : G)⁻¹ ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hmem
  have h := image_pCoreOf_le ρ hLJ hmem
  convert h using 1
  rw [piL_apply, piL_apply, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
  rfl

variable (c : Conf T L I t w J)
include c

theorem Conf.comm_mem_of_conjugate (h37 : Vol2Native.A37ForSQTKCat) {d : G}
    (hd : d ∈ CFSG.conjugate L t) : ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  intro l hl
  have h1 : ⁅d, l⁆ ∈ ⁅CFSG.conjugate L t, L⁆ := Subgroup.commutator_mem_commutator hd hl
  rw [Subgroup.commutator_comm] at h1
  have h2 := (SecA.commutator_conjugate_le h37 c.hyp c.ht c.htn h1).1
  rwa [commutatorElement_def] at h2

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

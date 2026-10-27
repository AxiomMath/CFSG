module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1d3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem centerOf_stab_eq_bot (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    centerOf (stab l) = ⊥ := by
  obtain ⟨e, he⟩ := exists_adj l
  have hv := Std.vtype_nbr_S3 hl (show e ∈ nbrs l from he)
  exact centerOf_eq_bot_of_Zv_central hS.glob.amalg (show l ∈ nbrs e from he.symm)
    (hS.glob.central e hv)

theorem exists_proj_S3 (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    ∃ π : ↥(stab l) →* Equiv.Perm (Fin 3), Function.Surjective π ∧
      ∀ g : ↥(stab l), π g = 1 ↔ (g : G) ∈ Qv l := by
  obtain ⟨φ⟩ := quot_stab_three hS.glob.amalg hl
  refine ⟨φ.toMonoidHom.comp (QuotientGroup.mk' _),
    φ.surjective.comp (QuotientGroup.mk'_surjective _), fun g => ?_⟩
  change φ (QuotientGroup.mk g) = 1 ↔ _
  rw [map_eq_one_iff φ φ.injective, QuotientGroup.eq_one_iff]
  constructor
  · intro h; exact ⟨g, h, rfl⟩
  · rintro ⟨x, hx, hxg⟩
    rwa [← Subtype.ext hxg]

theorem omegaOneCenter_Qv_le_Zv (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) {y : G}
    (hy : y ∈ Qv l) (hy2 : y ^ 2 = 1) (hyc : ∀ q ∈ Qv l, q * y = y * q) : y ∈ Zv l := by
  obtain ⟨π, hsurj, hker⟩ := exists_proj_S3 hS hl
  have hcen : ∀ x ∈ stab l, (∀ g ∈ stab l, g * x = x * g) → x = 1 := by
    intro x hx hxc
    have : x ∈ centerOf (stab l) := ⟨hx, Subgroup.mem_centralizer_iff.mpr hxc⟩
    rwa [centerOf_stab_eq_bot hS hl, Subgroup.mem_bot] at this
  obtain ⟨u₀, u₁, u₂, rfl, h₀, h₁, h₂⟩ :=
    exists_factor π (pCoreOf_le 2 (stab l)) hsurj hker hcen
      (show y ∈ Ysub (Qv l) from ⟨hy, hy2, hyc⟩)
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact mem_Zv_of_good π hker (by decide) (by decide) h₀
  · exact mem_Zv_of_good π hker (by decide) (by decide) h₁
  · exact mem_Zv_of_good π hker (by decide) (by decide) h₂

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin

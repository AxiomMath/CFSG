module

public import CFSG.Quasithin.EmptyFaithful.E111RFam

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type} [Group G] {K : Subgroup G}

theorem sSup_image_subgroupOf {𝒟 : Set (Subgroup G)} (h𝒟 : ∀ D ∈ 𝒟, D ≤ K) :
    sSup ((fun D : Subgroup G => D.subgroupOf K) '' 𝒟) = (sSup 𝒟).subgroupOf K := by
  have hle : sSup 𝒟 ≤ K := sSup_le h𝒟
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle, sSup_image, Subgroup.map_iSup, sSup_eq_iSup]
  refine iSup_congr fun D => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hD => Subgroup.map_subgroupOf_eq_of_le (h𝒟 D hD)

theorem commutator_subgroupOf {D B : Subgroup G} (hD : D ≤ K) (hB : B ≤ K) :
    ⁅D.subgroupOf K, B.subgroupOf K⁆ = (⁅D, B⁆ : Subgroup G).subgroupOf K := by
  have hle : ⁅D, B⁆ ≤ K := Subgroup.commutator_le.mpr fun d hd b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hD hd) (hB hb)) (K.inv_mem (hD hd))) (K.inv_mem (hB hb))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hD,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hle]

theorem conjSub_le_of_mem {k : G} (hk : k ∈ K) {D : Subgroup G} (hD : D ≤ K) :
    A1b.conjSub k D ≤ K := by
  intro x hx
  rw [A1b.mem_conjSub_iff] at hx
  have := K.mul_mem (K.mul_mem hk (hD hx)) (K.inv_mem hk)
  simpa [mul_assoc] using this

theorem conjSub_subgroupOf (k : ↥K) {D : Subgroup G} (hD : D ≤ K) :
    A1b.conjSub k (D.subgroupOf K) = (A1b.conjSub (k : G) D).subgroupOf K := by
  have hle : A1b.conjSub (k : G) D ≤ K := by
    intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    have := K.mul_mem (K.mul_mem k.2 (hD hx)) (K.inv_mem k.2)
    simpa [mul_assoc] using this
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle]
  unfold A1b.conjSub
  rw [Subgroup.map_map]
  have e : K.subtype.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (k : G)).toMonoidHom.comp K.subtype := by
    ext x
    simp [MulAut.conj_apply]
  rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hD]

theorem mem_normalizer_subgroupOf_iff {D : Subgroup G} {k : ↥K} :
    k ∈ Subgroup.normalizer (D.subgroupOf K : Set ↥K) ↔
      (k : G) ∈ Subgroup.normalizer ((D ⊓ K : Subgroup G) : Set G) := by
  rw [← Subgroup.inf_subgroupOf_right, ← Subgroup.subgroupOf_normalizer_eq inf_le_right,
    Subgroup.mem_subgroupOf]

theorem mem_centralizer_subgroupOf_iff {D : Subgroup G} (hD : D ≤ K) {k : ↥K} :
    k ∈ Subgroup.centralizer (D.subgroupOf K : Set ↥K) ↔
      (k : G) ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h d hd
    have := h ⟨d, hD hd⟩ (Subgroup.mem_subgroupOf.mpr hd)
    exact congrArg Subtype.val this
  · intro h d hd
    exact Subtype.ext (h d (Subgroup.mem_subgroupOf.mp hd))

namespace SemiFam

variable {𝒟 : Set (Subgroup G)}

theorem subgroupOf (h : SemiFam 𝒟) (h𝒟 : ∀ D ∈ 𝒟, D ≤ K) :
    SemiFam ((fun D : Subgroup G => D.subgroupOf K) '' 𝒟) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨D, hD, rfl⟩
    have := h.simple D hD
    exact (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe (h𝒟 D hD))).mpr this
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨a, b, hab⟩ := h.nonabelian D hD
    set e := (Subgroup.subgroupOfEquivOfLe (h𝒟 D hD)).symm
    refine ⟨e a, e b, fun he => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact he
  · rintro _ ⟨D, hD, rfl⟩ _ ⟨D', hD', rfl⟩ hne x hx y hy
    have hne' : D ≠ D' := fun e => hne (by rw [e])
    exact Subtype.ext (h.comm D hD D' hD' hne' x (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy))

end SemiFam

end CFSG.Quasithin.E2.E22N.E111R

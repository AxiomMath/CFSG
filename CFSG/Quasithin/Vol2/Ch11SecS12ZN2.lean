module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZI
public import CFSG.Quasithin.Vol2.Ch11SecS12ZL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ZN2

omit [Finite G] in
theorem commutator_eq_self {J H : Subgroup G} (hJ : CFSG.GorensteinWalter.IsComponentOf J H) :
    ⁅J, J⁆ = J := by
  rw [← Subgroup.map_subtype_commutator, hJ.2.2.2.1, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

omit [Finite G] in
theorem commutator_le_inf {L J : Subgroup G} (hLJ : L ≤ Subgroup.normalizer (J : Set G))
    (hJL : J ≤ Subgroup.normalizer (L : Set G)) : ⁅L, J⁆ ≤ L ⊓ J := by
  rw [Subgroup.commutator_le]
  intro ℓ hℓ w hw
  rw [commutatorElement_def]
  refine ⟨?_, J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLJ hℓ) w).mp hw) (J.inv_mem hw)⟩
  have h1 : w * ℓ⁻¹ * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hJL hw) ℓ⁻¹).mp (L.inv_mem hℓ)
  have e : ℓ * w * ℓ⁻¹ * w⁻¹ = ℓ * (w * ℓ⁻¹ * w⁻¹) := by group
  rw [e]
  exact L.mul_mem hℓ h1

omit [Finite G] in
theorem normal_inf {L J : Subgroup G} (hJL : J ≤ Subgroup.normalizer (L : Set G)) :
    ((L ⊓ J).subgroupOf J).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxJ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hJL hw) x).mp hxL,
      J.mul_mem (J.mul_mem hw hxJ) (J.inv_mem hw)⟩
  · rintro ⟨hxL, hxJ⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hJL hw) x).mpr hxL, ?_⟩
    have h1 : w⁻¹ * (w * x * w⁻¹) * w ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hw) hxJ) hw
    have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rwa [e] at h1

omit [Finite G] in
theorem le_centralizer {L J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hc : ∀ x ∈ ⁅L, J⁆, ∀ y ∈ J, x * y = y * x) : L ≤ Subgroup.centralizer (J : Set G) := by
  have h1 : ⁅⁅L, J⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc x hx y hy).symm
  have h2 : ⁅⁅J, L⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm J L]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := L) h2 h1
  rw [hJ, Subgroup.commutator_comm] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

omit [Finite G] in
theorem centralizer_normal {L J : Subgroup G} (hLJ : L ≤ Subgroup.normalizer (J : Set G)) :
    ((Subgroup.centralizer (J : Set G)).subgroupOf L).Normal := by
  refine ⟨fun c hc ℓ => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
  intro j hj
  have hj' : (ℓ : G)⁻¹ * j * ℓ ∈ J := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hLJ ℓ.2) _).mpr
      (show (ℓ : G) * ((ℓ : G)⁻¹ * j * ℓ) * (ℓ : G)⁻¹ ∈ J by simpa [mul_assoc] using hj)
  have h := hc _ hj'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc j * ((ℓ : G) * c * (ℓ : G)⁻¹)
      = ℓ * (((ℓ : G)⁻¹ * j * ℓ) * c) * (ℓ : G)⁻¹ := by group
    _ = ℓ * (c * ((ℓ : G)⁻¹ * j * ℓ)) * (ℓ : G)⁻¹ := by rw [h]
    _ = (ℓ : G) * c * (ℓ : G)⁻¹ * j := by group

end ZN2

open ZN2 in
theorem false_of_component_le_normalizer {X₁ L J₁ J₂ : Subgroup G}
    (hJ₁ : CFSG.GorensteinWalter.IsComponentOf J₁ (Subgroup.normalizer (X₁ : Set G)))
    (hJ₂ : CFSG.GorensteinWalter.IsComponentOf J₂ (Subgroup.normalizer (X₁ : Set G)))
    (hne : J₁ ≠ J₂) (hL : commutator ↥L = ⊤) {F : Type} [Field F] [Fintype F]
    (π : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) (hLJ₁ : L ≤ Subgroup.normalizer (J₁ : Set G))
    (hLJ₂ : L ≤ Subgroup.normalizer (J₂ : Set G)) (hJ₂L : J₂ ≤ Subgroup.normalizer (L : Set G))
    (hL₁ : ¬ L ≤ Subgroup.centralizer (J₁ : Set G))
    (hL₂ : ¬ L ≤ Subgroup.centralizer (J₂ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ₂C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_ne hJ₂ hJ₁ (Ne.symm hne))
  have hcomm := commutator_le_inf hLJ₂ hJ₂L
  have hn := normal_inf hJ₂L
  obtain ⟨hnt₂, hperf₂, hsimp₂⟩ := hJ₂.2.2
  have hq₂ : CFSG.Open.IsQuasisimple ↥J₂ := ⟨hperf₂, hsimp₂⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq₂
    ((L ⊓ J₂).subgroupOf J₂) with hc | ht
  ·
    refine hL₂ (le_centralizer (commutator_eq_self hJ₂) fun x hx y hy => ?_)
    have hx' := hcomm hx
    have hz := hc (Subgroup.mem_subgroupOf.mpr hx' : (⟨x, hx'.2⟩ : ↥J₂) ∈ (L ⊓ J₂).subgroupOf J₂)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
  ·
    have hJ₂L' : J₂ ≤ L := fun w hw => by
      have : (⟨w, hw⟩ : ↥J₂) ∈ (L ⊓ J₂).subgroupOf J₂ := by rw [ht]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    have hN := centralizer_normal hLJ₁
    have hNt : (Subgroup.centralizer (J₁ : Set G)).subgroupOf L ≠ ⊤ := fun h =>
      hL₁ fun ℓ hℓ => Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨ℓ, hℓ⟩ : ↥L))
    have hZ := map_le_center_of_ne_top hL π hπ hker _ hNt
    let ι : ↥J₂ →* ↥L := Subgroup.inclusion hJ₂L'
    have hcen : ∀ w : ↥J₂, (π.comp ι) w ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := fun w =>
      hZ ⟨ι w, Subgroup.mem_subgroupOf.mpr (hJ₂C w.2), rfl⟩
    let g := (π.comp ι).codRestrict _ hcen
    have hg : ∀ w : ↥J₂, π (ι w) = 1 := by
      intro w
      have hw : w ∈ commutator ↥J₂ := by rw [hperf₂]; exact Subgroup.mem_top w
      have h1 := Abelianization.commutator_subset_ker g hw
      rw [MonoidHom.mem_ker] at h1
      exact congrArg Subtype.val h1
    have h2 : IsPGroup 2 ↥J₂ := by
      intro w
      obtain ⟨k, hk⟩ := hker ⟨ι w, hg w⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun x : ↥π.ker => ((x : ↥L) : G)) hk
      simpa [ι] using this
    have : Nontrivial ↥J₂ := hnt₂
    have : Group.IsPerfect ↥J₂ := Group.isPerfect_def.mpr hperf₂
    exact Group.IsPerfect.not_isNilpotent ↥J₂ h2.isNilpotent

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

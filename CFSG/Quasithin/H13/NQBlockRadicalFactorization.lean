module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G]

section Transport

theorem coe_mem_normalizer_map {V : Subgroup G} {J : Subgroup ↥V} {a : ↥V}
    (ha : a ∈ normalizer (J : Set ↥V)) : (a : G) ∈ normalizer (J.map V.subtype : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨a * j * a⁻¹, (mem_normalizer_iff.mp ha j).mp hj, rfl⟩
  · rintro ⟨j', hj', hjg⟩
    have hgV : g ∈ V := by
      have e : g = (a : G)⁻¹ * j' * a := by
        change (j' : G) = a * g * (a : G)⁻¹ at hjg
        rw [hjg]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem a.2) j'.2) a.2
    refine ⟨⟨g, hgV⟩, (mem_normalizer_iff.mp ha ⟨g, hgV⟩).mpr ?_, rfl⟩
    have e : a * ⟨g, hgV⟩ * a⁻¹ = j' := Subtype.ext hjg.symm
    rw [e]
    exact hj'

theorem coe_mem_centralizer_map {V : Subgroup G} {U : Subgroup ↥V} {b : ↥V}
    (hb : b ∈ centralizer (U : Set ↥V)) : (b : G) ∈ centralizer (U.map V.subtype : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  exact congrArg Subtype.val ((mem_centralizer_iff.mp hb) u hu)

theorem map_quasithinOmegaOneCenter_subgroupOf {V R : Subgroup G} (hRV : R ≤ V) :
    (quasithinOmegaOneCenter (R.subgroupOf V)).map V.subtype = quasithinOmegaOneCenter R := by
  rw [quasithinOmegaOneCenter, quasithinOmegaOneCenter, MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hw2⟩, rfl⟩
    obtain ⟨hwR, hwc⟩ := mem_inf.mp hw
    refine ⟨mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hwR,
      mem_centralizer_iff.mpr fun r hr => ?_⟩, ?_⟩
    · exact congrArg Subtype.val ((mem_centralizer_iff.mp hwc) ⟨r, hRV hr⟩
        (Subgroup.mem_subgroupOf.mpr hr))
    · change (w : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, hw2, Subgroup.coe_one]
  · rintro ⟨hz, hz2⟩
    obtain ⟨hzR, hzc⟩ := mem_inf.mp hz
    refine ⟨⟨z, hRV hzR⟩, ⟨mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hzR,
      mem_centralizer_iff.mpr fun r hr => Subtype.ext ((mem_centralizer_iff.mp hzc) r
        (Subgroup.mem_subgroupOf.mp hr))⟩, Subtype.ext ?_⟩, rfl⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hz2

theorem map_normalClosure_subgroupOf {V Z : Subgroup G} (hZV : Z ≤ V) :
    (normalClosure ((Z.subgroupOf V : Subgroup ↥V) : Set ↥V)).map V.subtype =
      sSup {W | ∃ v ∈ V, CFSG.conjugate Z v = W} := by
  set F : Set (Subgroup G) := {W | ∃ v ∈ V, CFSG.conjugate Z v = W} with hFdef
  set T := sSup F with hTdef
  have hconj : ∀ v ∈ V, ∀ t ∈ T, v * t * v⁻¹ ∈ T := by
    intro v hv t ht
    have hle : T ≤ T.comap (MulAut.conj v).toMonoidHom := by
      refine sSup_le fun C hC => ?_
      obtain ⟨w, hw, rfl⟩ := hC
      rintro _ ⟨z, hz, rfl⟩
      change v * ((MulAut.conj w⁻¹) z) * v⁻¹ ∈ T
      have hmem : v * ((MulAut.conj w⁻¹) z) * v⁻¹ ∈ CFSG.conjugate Z (w * v⁻¹) := by
        refine ⟨z, hz, ?_⟩
        change (MulAut.conj (w * v⁻¹)⁻¹) z = v * ((MulAut.conj w⁻¹) z) * v⁻¹
        simp only [MulAut.conj_apply]
        group
      have hF : CFSG.conjugate Z (w * v⁻¹) ∈ F := ⟨w * v⁻¹, mul_mem hw (inv_mem hv), rfl⟩
      exact (le_sSup hF : CFSG.conjugate Z (w * v⁻¹) ≤ T) hmem
    exact hle ht
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have : (T.comap V.subtype).Normal :=
      ⟨fun t ht v => by
        change (v : G) * t * (v : G)⁻¹ ∈ T
        exact hconj v v.2 t ht⟩
    refine Subgroup.normalClosure_le_normal fun z hz => ?_
    change (z : G) ∈ T
    have hmem : (z : G) ∈ CFSG.conjugate Z 1 := ⟨z, Subgroup.mem_subgroupOf.mp hz, by simp⟩
    have hF : CFSG.conjugate Z 1 ∈ F := ⟨1, one_mem V, rfl⟩
    exact (le_sSup hF : CFSG.conjugate Z 1 ≤ T) hmem
  · refine sSup_le fun C hC => ?_
    obtain ⟨w, hw, rfl⟩ := hC
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨w, hw⟩⁻¹ * ⟨z, hZV hz⟩ * ⟨w, hw⟩⁻¹⁻¹,
      (normalClosure_normal (s := ((Z.subgroupOf V : Subgroup ↥V) : Set ↥V))).conj_mem _
        (subset_normalClosure (Subgroup.mem_subgroupOf.mpr hz)) _, ?_⟩
    change (w : G)⁻¹ * z * (w : G)⁻¹⁻¹ = (MulAut.conj w⁻¹) z
    rw [MulAut.conj_apply]

theorem coe_eq_mul_of_mul_eq_univ {V : Subgroup G} {P Q : Subgroup ↥V} {P' Q' : Subgroup G}
    (hPQ : (P : Set ↥V) * (Q : Set ↥V) = Set.univ) (hP : ∀ a ∈ P, (a : G) ∈ P')
    (hQ : ∀ b ∈ Q, (b : G) ∈ Q') :
    (V : Set G) = ((V ⊓ P' : Subgroup G) : Set G) * ((V ⊓ Q' : Subgroup G) : Set G) := by
  ext g
  constructor
  · intro hg
    have h1 : (⟨g, hg⟩ : ↥V) ∈ (P : Set ↥V) * (Q : Set ↥V) := by
      rw [hPQ]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    refine ⟨a, mem_inf.mpr ⟨a.2, hP a ha⟩, b, mem_inf.mpr ⟨b.2, hQ b hb⟩, ?_⟩
    exact congrArg Subtype.val hab
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1

end Transport

variable [Finite G]

end CFSG.Quasithin.H13.NQBlock

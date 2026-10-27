
module

public import CFSG.Sporadic.Co1.Module.OrbitsBase
import all CFSG.Sporadic.Co1.Module.OrbitsBase

public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co1.Module.OrbitsInputs
public import Certificates.Certificate10075
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Perm.OrbitTree
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate10075Base

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm.Native Matrix

theorem orbitCheck_v₂ : orbitCheck 2 98280 [4096, 1] = true :=
  Certificates.certificate10075.1

theorem orbitCheck_v₃ : orbitCheck 4096 8386560 [1] = true :=
  Certificates.certificate10075.2.1

theorem orbitCheck_v₄ : orbitCheck 1 8292375 [] = true :=
  Certificates.certificate10075.2.2

theorem orbit_ncard_v₂ :
    (MulAction.orbit Jmat v₂).ncard = 98280 := by
  rw [← toVecD_v₂]
  exact ncard_orbit_of_check orbitCheck_v₂

theorem orbit_ncard_v₃ :
    (MulAction.orbit Jmat v₃).ncard = 8386560 := by
  rw [← toVecD_v₃]
  exact ncard_orbit_of_check orbitCheck_v₃

theorem orbit_ncard_v₄ :
    (MulAction.orbit Jmat v₄).ncard = 8292375 := by
  rw [← toVecD_v₄]
  exact ncard_orbit_of_check orbitCheck_v₄

theorem v₃_not_mem_orbit_v₂ :
    v₃ ∉ MulAction.orbit Jmat v₂ := by
  rw [← toVecD_v₂, ← toVecD_v₃]
  exact not_mem_orbit_of_check orbitCheck_v₂ (by simp) (by norm_num)

theorem v₄_not_mem_orbit_v₂ :
    v₄ ∉ MulAction.orbit Jmat v₂ := by
  rw [← toVecD_v₂, ← toVecD_v₄]
  exact not_mem_orbit_of_check orbitCheck_v₂ (by simp) (by norm_num)

theorem v₄_not_mem_orbit_v₃ :
    v₄ ∉ MulAction.orbit Jmat v₃ := by
  rw [← toVecD_v₃, ← toVecD_v₄]
  exact not_mem_orbit_of_check orbitCheck_v₃ (by simp) (by norm_num)

theorem disjoint_orbit_v₂_v₃ :
    Disjoint (MulAction.orbit Jmat v₂) (MulAction.orbit Jmat v₃) :=
  (disjoint_orbit v₃_not_mem_orbit_v₂).symm

theorem disjoint_orbit_v₂_v₄ :
    Disjoint (MulAction.orbit Jmat v₂) (MulAction.orbit Jmat v₄) :=
  (disjoint_orbit v₄_not_mem_orbit_v₂).symm

theorem disjoint_orbit_v₃_v₄ :
    Disjoint (MulAction.orbit Jmat v₃) (MulAction.orbit Jmat v₄) :=
  (disjoint_orbit v₄_not_mem_orbit_v₃).symm

theorem orbits_union :
    MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₃ ∪
    MulAction.orbit Jmat v₄ ∪ {0} = Set.univ := by
  have d23 := disjoint_orbit_v₂_v₃
  have d24 := disjoint_orbit_v₂_v₄
  have d34 := disjoint_orbit_v₃_v₄
  have hv₂ := v₂_ne_zero
  have hv₃ := v₃_ne_zero
  have hv₄ := v₄_ne_zero
  have d0 : ∀ {v : Vec24}, v ≠ 0 → Disjoint (MulAction.orbit Jmat v) ({0} : Set Vec24) :=
    fun hv => Set.disjoint_singleton_right.2 (zero_not_mem_orbit hv)
  have e1 : (MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₃).ncard = 98280 + 8386560 := by
    rw [Set.ncard_union_eq d23, orbit_ncard_v₂, orbit_ncard_v₃]
  have e2 : (MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₃ ∪ MulAction.orbit Jmat v₄).ncard =
      98280 + 8386560 + 8292375 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d24, d34⟩), e1, orbit_ncard_v₄]
  have e3 : (MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₃ ∪ MulAction.orbit Jmat v₄ ∪
      {0}).ncard = 98280 + 8386560 + 8292375 + 1 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2
      ⟨Set.disjoint_union_left.2 ⟨d0 hv₂, d0 hv₃⟩, d0 hv₄⟩), e2, Set.ncard_singleton]
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
  rw [e3, Set.ncard_univ]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem orbit_trichotomy
    {v : Vec24} (hv : v ≠ 0) :
    (v ∈ MulAction.orbit Jmat v₂ ∧ v ∉ MulAction.orbit Jmat v₃ ∧ v ∉ MulAction.orbit Jmat v₄) ∨
    (v ∉ MulAction.orbit Jmat v₂ ∧ v ∈ MulAction.orbit Jmat v₃ ∧ v ∉ MulAction.orbit Jmat v₄) ∨
    (v ∉ MulAction.orbit Jmat v₂ ∧ v ∉ MulAction.orbit Jmat v₃ ∧ v ∈ MulAction.orbit Jmat v₄) := by
  have h : v ∈ MulAction.orbit Jmat v₂ ∪ MulAction.orbit Jmat v₃ ∪ MulAction.orbit Jmat v₄ ∪
      {0} := by
    rw [orbits_union]
    trivial
  have d23 := Set.disjoint_left.1 disjoint_orbit_v₂_v₃
  have d24 := Set.disjoint_left.1 disjoint_orbit_v₂_v₄
  have d34 := Set.disjoint_left.1 disjoint_orbit_v₃_v₄
  rcases h with ((h | h) | h) | h
  · exact Or.inl ⟨h, fun h' => d23 h h', fun h' => d24 h h'⟩
  · exact Or.inr (Or.inl ⟨fun h' => d23 h' h, h, fun h' => d34 h h'⟩)
  · exact Or.inr (Or.inr ⟨fun h' => d24 h' h, fun h' => d34 h' h, h⟩)
  · exact absurd (Set.mem_singleton_iff.1 h) hv

theorem exists_unique_orbit
    {v : Vec24} (hv : v ≠ 0) :
    ∃! i : Fin 3, v ∈ MulAction.orbit Jmat (reps i) := by
  rcases orbit_trichotomy hv with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · refine ⟨0, h2, fun j hj => ?_⟩
    fin_cases j
    · rfl
    · exact absurd hj h3
    · exact absurd hj h4
  · refine ⟨1, h3, fun j hj => ?_⟩
    fin_cases j
    · exact absurd hj h2
    · rfl
    · exact absurd hj h4
  · refine ⟨2, h4, fun j hj => ?_⟩
    fin_cases j
    · exact absurd hj h2
    · exact absurd hj h3
    · rfl

theorem co1_exists_unique_orbit
    {v : Vec24} (hv : v ≠ 0) :
    ∃! i : Fin 3, v ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (reps i)) := by
  simp only [range_co1Act]
  exact exists_unique_orbit hv

section Generic

variable {D : VecData} (hB : BaseFacts D)
include hB

end Generic

theorem co1_orbit_ncard_v₂ :
    (Set.range fun g : NativeSporadic.Co1 => co1Act g v₂).ncard = 98280 := by
  rw [range_co1Act]
  exact orbit_ncard_v₂

theorem co1_orbit_ncard_v₃ :
    (Set.range fun g : NativeSporadic.Co1 => co1Act g v₃).ncard = 8386560 := by
  rw [range_co1Act]
  exact orbit_ncard_v₃

theorem co1_orbit_ncard_v₄ :
    (Set.range fun g : NativeSporadic.Co1 => co1Act g v₄).ncard = 8292375 := by
  rw [range_co1Act]
  exact orbit_ncard_v₄

theorem co1_orbit_trichotomy
    {v : Vec24} (hv : v ≠ 0) :
    (v ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₂) ∧
      v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₃) ∧
      v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₄)) ∨
    (v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₂) ∧
      v ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₃) ∧
      v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₄)) ∨
    (v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₂) ∧
      v ∉ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₃) ∧
      v ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v₄)) := by
  simp only [range_co1Act]
  exact orbit_trichotomy hv

end CFSG.Sporadic.Co1.Module

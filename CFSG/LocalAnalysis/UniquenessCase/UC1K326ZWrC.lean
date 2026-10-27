module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {n : ℕ}

theorem zwr_centralizer_of_mem_omegaBase (hn : 1 ≤ n) {a : ZWr n}
    (ha : a ∈ omegaBase n) (ha2 : a ∉ Subgroup.upperCentralSeries (ZWr n) 2) :
    Subgroup.centralizer ({a} : Set (ZWr n)) = base n ∧
      IsMulCommutative (Subgroup.centralizer ({a} : Set (ZWr n))) ∧
      (Subgroup.centralizer ({a} : Set (ZWr n))).index = 3 ∧
      ∀ x : ZWr n, x ∉ Subgroup.centralizer ({a} : Set (ZWr n)) →
        ⁅x, a⁆ ∉ Subgroup.center (ZWr n) := by
  obtain ⟨p, q, r, ha_eq⟩ := exists_el_of_mem_base (omegaBase_le_base ha)
  have haω : 3 • p = 0 ∧ 3 • q = 0 ∧ 3 • r = 0 := by
    rw [ha_eq] at ha
    exact el_mem_omegaBase_iff.mp ha
  have hsum : p + q + r ≠ 0 := by
    intro h0
    apply ha2
    rw [ha_eq]
    exact (mem_Z2_omegaBase_iff hn haω.1 haω.2.1 haω.2.2).mpr h0
  have hCeq : Subgroup.centralizer ({a} : Set (ZWr n)) = base n := by
    refine le_antisymm ?_ ?_
    · intro y hy
      by_contra hyb
      have hya : a ∈ Subgroup.centralizer ({y} : Set (ZWr n)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
      have hdiag : a ∈ diagSub n :=
        centralizer_base_le_diag hyb ⟨hya, omegaBase_le_base ha⟩
      have hcenter : a ∈ Subgroup.center (ZWr n) := by rwa [center_eq_diag hn]
      exact ha2 (Subgroup.upperCentralSeries_mono (ZWr n) (by norm_num : (1 : ℕ) ≤ 2)
        (by rw [Subgroup.upperCentralSeries_one]; exact hcenter))
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact base_comm hy (omegaBase_le_base ha)
  refine ⟨hCeq, ?_, ?_, ?_⟩
  · rw [hCeq]
    exact ⟨⟨fun x y => Subtype.ext (base_comm x.2 y.2)⟩⟩
  · rw [hCeq]; exact base_index n
  · intro x hx
    have hxb : x ∉ base n := by rwa [hCeq] at hx
    intro hcomm
    have hcomm' : ⁅a, x⁆ ∈ Subgroup.center (ZWr n) := by
      rw [← commutatorElement_inv x a]
      exact (Subgroup.center (ZWr n)).inv_mem hcomm
    have hdiag : ⁅a, x⁆ ∈ diagSub n := by rwa [center_eq_diag hn] at hcomm'
    obtain ⟨A, B, C, s, hx_eq⟩ : ∃ A B C s, x = el n A B C s := ⟨_, _, _, _, el_eta x⟩
    have h3r : (3 : ZMod (3 ^ n)) * r = 0 := by
      have h := haω.2.2
      rwa [nsmul_eq_mul] at h
    have hs : s ≠ 0 := by
      intro h0
      apply hxb
      rw [hx_eq, h0]
      exact (el_mem_base_iff A B C 0).mpr rfl
    rcases zmod3_cases s with h0 | h1 | h2
    · exact hs h0
    · rw [ha_eq, hx_eq, h1] at hdiag
      rw [commutator_el_base_one, el_mem_diagSub_iff] at hdiag
      exact hsum (by linear_combination hdiag.1 + hdiag.2 + h3r)
    · rw [ha_eq, hx_eq, h2] at hdiag
      rw [commutator_el_base_two, el_mem_diagSub_iff] at hdiag
      exact hsum (by linear_combination hdiag.2 + h3r)

theorem zwr_centralizer_abelian_of_not_mem_base (hn : 1 ≤ n) {y : ZWr n} (hy : y ∉ base n) :
    IsMulCommutative (Subgroup.centralizer ({y} : Set (ZWr n))) := by
  let C := Subgroup.centralizer ({y} : Set (ZWr n))
  have hker : (RegularWreathProduct.rightHom.comp C.subtype).ker ≤ Subgroup.center C := by
    intro x hx
    have hxb : (x : ZWr n) ∈ base n := by simpa [base] using hx
    have hxy : (x : ZWr n) ∈ C := x.2
    have hdiag : (x : ZWr n) ∈ diagSub n := centralizer_base_le_diag hy ⟨hxy, hxb⟩
    have hcent : (x : ZWr n) ∈ Subgroup.center (ZWr n) := by rwa [center_eq_diag hn]
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcent (z : ZWr n)
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (RegularWreathProduct.rightHom.comp C.subtype) hker

theorem zwr_centralizer_of_mem_J (hn : 1 ≤ n) (e : P ≃* ZWr n) {a : P}
    (ha : a ∈ CFSG.elemThompson P 3) (ha2 : a ∉ Subgroup.upperCentralSeries P 2) :
    IsMulCommutative (Subgroup.centralizer ({a} : Set P)) ∧
      (Subgroup.centralizer ({a} : Set P)).index = 3 ∧
      ∀ x : P, x ∉ Subgroup.centralizer ({a} : Set P) → ⁅x, a⁆ ∉ Subgroup.center P := by
  have ha' : e a ∈ omegaBase n := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom ha
    rwa [CFSG.elemThompson_map_mulEquiv e 3, zwr_elemThompson_Zwr hn] at h
  have ha2' : e a ∉ Subgroup.upperCentralSeries (ZWr n) 2 := by
    intro h
    apply ha2
    have hc := Subgroup.comap_upperCentralSeries e 2
    rw [← hc]
    exact h
  obtain ⟨hZeq, -, -, hZcommut⟩ := zwr_centralizer_of_mem_omegaBase hn ha' ha2'
  have hCeq : Subgroup.centralizer ({a} : Set P) = (base n).comap e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      rw [← hZeq, Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg e hx
    · intro hx
      apply e.injective
      rw [map_mul, map_mul]
      exact base_comm hx (omegaBase_le_base ha')
  have hCcomm : IsMulCommutative (Subgroup.centralizer ({a} : Set P)) := by
    rw [hCeq]
    haveI : IsMulCommutative (base n) := ⟨⟨fun x y => Subtype.ext (base_comm x.2 y.2)⟩⟩
    exact Subgroup.comap_injective_isMulCommutative (base n) e.injective
  have hCidx : (Subgroup.centralizer ({a} : Set P)).index = 3 := by
    rw [hCeq, Subgroup.index_comap_of_surjective (H := base n) e.surjective, base_index]
  refine ⟨hCcomm, hCidx, ?_⟩
  intro x hx hcomm
  have hx' : e x ∉ Subgroup.centralizer ({e a} : Set (ZWr n)) := by
    rw [hZeq]
    intro hb
    apply hx
    rw [hCeq]
    exact hb
  have hmap : ⁅e x, e a⁆ ∈ Subgroup.center (ZWr n) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa using congrArg e (Subgroup.mem_center_iff.mp hcomm w)
  exact hZcommut (e x) hx' hmap

theorem zwr_no_commuting_nonabelian (hn : 1 ≤ n) (e : P ≃* ZWr n) {T₁ T₂ : Subgroup P}
    (h : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) :
    IsMulCommutative T₁ ∨ IsMulCommutative T₂ := by
  by_cases h2 : IsMulCommutative T₂
  · exact Or.inr h2
  · left
    have hT2notbase : ¬ T₂ ≤ (base n).comap e.toMonoidHom := by
      intro hle
      apply h2
      haveI : IsMulCommutative (base n) := ⟨⟨fun x y => Subtype.ext (base_comm x.2 y.2)⟩⟩
      haveI : IsMulCommutative ((base n).comap e.toMonoidHom) :=
        Subgroup.comap_injective_isMulCommutative (base n) e.injective
      exact isMulCommutative_anti hle
    obtain ⟨y, hyT2, hybase⟩ : ∃ y, y ∈ T₂ ∧ e y ∉ base n := by
      rw [SetLike.le_def] at hT2notbase
      push Not at hT2notbase
      obtain ⟨y, hy, hynot⟩ := hT2notbase
      exact ⟨y, hy, by simpa using hynot⟩
    have hCyZwr : IsMulCommutative (Subgroup.centralizer ({e y} : Set (ZWr n))) :=
      zwr_centralizer_abelian_of_not_mem_base hn hybase
    have hCeq : Subgroup.centralizer ({y} : Set P) =
        (Subgroup.centralizer ({e y} : Set (ZWr n))).comap e.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx; simpa using congrArg e hx
      · intro hx; exact e.injective (by simpa using hx)
    have hCcomm : IsMulCommutative (Subgroup.centralizer ({y} : Set P)) := by
      rw [hCeq]
      haveI := hCyZwr
      exact Subgroup.comap_injective_isMulCommutative
        (Subgroup.centralizer ({e y} : Set (ZWr n))) e.injective
    have hT1le : T₁ ≤ Subgroup.centralizer ({y} : Set P) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h x hx y hyT2)
    haveI := hCcomm
    exact isMulCommutative_anti hT1le

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

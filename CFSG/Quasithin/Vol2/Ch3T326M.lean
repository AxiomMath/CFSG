module

public import CFSG.Quasithin.Vol2.Ch3T326K
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (conjugate_eq_self_iff mem_conjugate_iff)

section Basic

variable {G : Type} [Group G]

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

end Basic

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem normalizes_conjugate {t : G} (ht : t ∈ T) :
    L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) ∧
      CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) :=
  ⟨c.L_le_L₀.trans (Vol2.Ch10.SecA.fsuL0_le_normalizer_conjugate c.fsu.maximal.1 (c.T_le_M ht)),
    (Vol2.Ch10.SecA.conjugate_le_fsuL0 ht).trans
      (Vol2.Ch10.SecA.fsuL0_le_normalizer c.fsu.maximal.1)⟩

theorem sup_U (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  rw [c.conjugate_U (c.T_le_M ht)]
  have hLtVM := (Vol2.Ch10.SecA.conjugate_le_fsuL0 ht).trans c.L₀_le_NVM
  have hL₀ := c.L₀_eq hA37 hA38 ht htn
  have hVM := c.comm_VM
  have hLVM := c.L_le_NVM
  obtain ⟨hLLt, hLtL⟩ := c.normalizes_conjugate ht
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set Lt := CFSG.conjugate L t with hLtdef
  refine le_antisymm (sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hLVM)
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hLtVM)) ?_
  have hN : L ⊔ Lt ≤ Subgroup.normalizer ((⁅VM, L⁆ ⊔ ⁅VM, Lt⁆ : Subgroup G) : Set G) := by
    refine sup_le (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩)
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩)
    · exact Subgroup.normalizer_commutator_ge_right _ _ hg
    · exact mem_normalizer_commutator (hLVM hg) (hLLt hg)
    · exact mem_normalizer_commutator (hLtVM hg) (hLtL hg)
    · exact Subgroup.normalizer_commutator_ge_right _ _ hg
  have hVM' : VM = ⁅L ⊔ Lt, VM⁆ := by
    rw [← hL₀, Subgroup.commutator_comm]
    exact hVM.symm
  calc VM = ⁅L ⊔ Lt, VM⁆ := hVM'
    _ ≤ ⁅VM, L⁆ ⊔ ⁅VM, Lt⁆ :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize L Lt VM _
        (by rw [Subgroup.commutator_comm]; exact le_sup_left)
        (by rw [Subgroup.commutator_comm]; exact le_sup_right)
        (le_sup_left.trans hN) (le_sup_right.trans hN)

theorem conjugate_le_centralizer (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {U : Subgroup G}
    (hU : U ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G)) :
    CFSG.conjugate U t ≤ Subgroup.centralizer (L : Set G) := by
  have ht2 : CFSG.conjugate L (t * t) = L := conjugate_eq_self_iff.mpr
    (Vol2.Ch10.SecA.mul_self_mem_normalizer_of_fsu hA37 hA38 c.fsu c.not_le_normalizer ht htn)
  intro x hx
  rw [mem_conjugate_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : t * l * t⁻¹ ∈ CFSG.conjugate L t := by
    rw [mem_conjugate_iff]
    have h1 : l ∈ CFSG.conjugate L (t * t) := by
      rw [ht2]
      exact hl
    rw [mem_conjugate_iff] at h1
    have e : t * (t * l * t⁻¹) * t⁻¹ = t * t * l * (t * t)⁻¹ := by group
    rw [e]
    exact h1
  have hc := Subgroup.mem_centralizer_iff.mp (hU hx) _ hl'
  have h2 : t * (l * x) * t⁻¹ = t * (x * l) * t⁻¹ :=
    calc t * (l * x) * t⁻¹ = (t * l * t⁻¹) * (t * x * t⁻¹) := by group
      _ = (t * x * t⁻¹) * (t * l * t⁻¹) := hc
      _ = t * (x * l) * t⁻¹ := by group
  simpa using h2

theorem concl_a (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hU : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L t : Set G)) :
    ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G)) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
      (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) ⊓
        (CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G) ∧
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
        Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
  intro t' ht' htn'
  have hsup := c.sup_U hA37 hA38 ht' htn'
  have hL₀ := c.L₀_eq hA37 hA38 ht' htn'
  have hUVM := Subgroup.le_normalizer_iff_commutator_le_left.mp c.L_le_NVM
  have hLtL₀ := Vol2.Ch10.SecA.conjugate_le_fsuL0 (L := L) ht'
  have hU' : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L t' : Set G) := by
    rw [c.conjugate_eq_of hA37 hA38 ht htn ht' htn']
    exact hU
  have hUt := c.conjugate_le_centralizer hA37 hA38 ht' htn' hU'
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set U := ⁅VM, L⁆ with hUdef
  set C := VM ⊓ Subgroup.centralizer (conjClosure L T : Set G) with hCdef
  have hCL : C ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.L_le_L₀))
  have hCLt : C ≤ Subgroup.centralizer (CFSG.conjugate L t' : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLtL₀))
  refine ⟨?_, ?_, hU'⟩
  · rw [hsup]
    exact sup_eq_left.mpr inf_le_left
  · refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxVM : x ∈ VM := sup_le hUVM inf_le_left hx1
    have hxLt : x ∈ Subgroup.centralizer (CFSG.conjugate L t' : Set G) := sup_le hU' hCLt hx1
    have hxL : x ∈ Subgroup.centralizer (L : Set G) := sup_le hUt hCL hx2
    refine Subgroup.mem_inf.mpr ⟨hxVM, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, hL₀] at hg
    have hle : L ⊔ CFSG.conjugate L t' ≤ Subgroup.centralizer {x} := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxL l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxLt l hl)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end Ctx

end CFSG.Quasithin.H13.T326

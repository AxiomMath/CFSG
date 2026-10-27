module

public import CFSG.RankThree.GF2n.Smith81.LinSmallG2

public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG.Open CFSG.Timmesfeld

theorem KG2Concl.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (φ : Y ≃* Y') {D : Set Y}
    {f : ℕ} {d : Y} (h : KG2Concl (φ '' D) f (φ d)) : KG2Concl D f d := by
  classical
  unfold KG2Concl at h
  obtain ⟨hdvd, t', ht'C, ht'3, x', hx'P, hx'root, hcomm'⟩ := h
  have hC : (Subgroup.centralizer ({d} : Set Y)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set Y') :=
    CFSG.centralizer_singleton_map φ d
  have hcard : Nat.card (Subgroup.centralizer ({d} : Set Y)) =
      Nat.card (Subgroup.centralizer ({φ d} : Set Y')) := by
    rw [← hC, Subgroup.card_map_of_injective φ.injective]
  have ht : φ.symm t' ∈ Subgroup.centralizer ({d} : Set Y) := by
    rw [← Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective, hC]
    simpa using ht'C
  have ht3 : orderOf (φ.symm t') = 3 := by
    rw [MulEquiv.orderOf_eq, ht'3]
  have hx : φ.symm x' ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set Y)) := by
    rw [← Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective,
      ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 φ
        (Subgroup.centralizer ({d} : Set Y)), hC]
    simpa using hx'P
  have hinj : Function.Injective (φ : Y →* Y') := φ.injective
  have hrootmap : rootGroup (φ '' D) (φ d) = (rootGroup D d).map φ.toMonoidHom := by
    simpa using CFSG.RankThree.GF2n.Smith81.rootGroup_image (φ : Y →* Y') hinj D d
  have hxroot : φ.symm x' ∉ rootGroup D d := by
    intro hmem
    apply hx'root
    rw [hrootmap]
    simpa using Subgroup.mem_map_of_mem φ.toMonoidHom hmem
  have hφc : φ.toMonoidHom (φ.symm t' * φ.symm x' * (φ.symm t')⁻¹ * (φ.symm x')⁻¹) =
      t' * x' * t'⁻¹ * x'⁻¹ := by
    simp [MulEquiv.toMonoidHom_eq_coe]
  have hcomm : φ.symm t' * φ.symm x' * (φ.symm t')⁻¹ * (φ.symm x')⁻¹ ∈
      rootGroup D d := by
    rw [← Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective]
    rw [hφc, ← hrootmap]
    exact hcomm'
  refine ⟨?_, φ.symm t', ht, ht3, φ.symm x', hx, hxroot, hcomm⟩
  rw [hcard]
  exact hdvd

end CFSG.RankThree.GF2n.Smith81.Insp

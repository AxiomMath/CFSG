module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed subgroups inside a nilpotent normal subgroup

The normalizer argument identifying restricted fixed subgroups only needs the
normal subgroup to be nilpotent, not a group of prime-power order.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `R` is nilpotent and normal in `U`, restricted fixed subgroups in
`R ∩ M` and `U ∩ M` are the full fixed subgroups once the smaller fixed
subgroup has ambient normalizer `M`. -/
public theorem full_fixed_subgroups_of_nilpotent_normalizer_eq
    {G : Type u} [Group G] [Finite G]
    (U R M P B : Subgroup G) (s : G)
    (hRnil : Group.IsNilpotent R)
    (hRnormalU : IsNormalIn R U)
    (hP_eq : P = centralizerIn (R ⊓ M) s)
    (hB_eq : B = centralizerIn (U ⊓ M) s)
    (hNPeq : Subgroup.normalizer (P : Set G) = M) :
    P = centralizerIn R s ∧ B = centralizerIn U s := by
  let C : Subgroup G := centralizerIn R s
  have hPleC : P ≤ C := by
    intro x hx
    rw [hP_eq] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hCleR : C ≤ R := inf_le_left
  have hCnil : Group.IsNilpotent C := by
    let : Group.IsNilpotent R := hRnil
    have hsub : Group.IsNilpotent (C.subgroupOf R) :=
      Subgroup.isNilpotent (C.subgroupOf R)
    let : Group.IsNilpotent (C.subgroupOf R) := hsub
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCleR)
  have hP_eq_C : P = C := by
    let PC : Subgroup C := P.subgroupOf C
    have hnormPC : Subgroup.normalizer (PC : Set C) = PC := by
      apply le_antisymm
      · intro x hx
        have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            let yC : C := ⟨y, hPleC hy⟩
            have hyPC : yC ∈ PC := Subgroup.mem_subgroupOf.mpr hy
            have hconj := (Subgroup.mem_normalizer_iff.mp hx) yC |>.mp hyPC
            exact Subgroup.mem_subgroupOf.mp hconj
          · intro hy
            have hyC : y ∈ C := by
              have hconjC : (x : G) * y * (x : G)⁻¹ ∈ C := hPleC hy
              have hbackC := C.mul_mem (C.mul_mem (C.inv_mem x.2) hconjC) x.2
              simpa [mul_assoc] using hbackC
            let yC : C := ⟨y, hyC⟩
            have hconjPC : x * yC * x⁻¹ ∈ PC := Subgroup.mem_subgroupOf.mpr hy
            exact Subgroup.mem_subgroupOf.mp
              ((Subgroup.mem_normalizer_iff.mp hx yC).mpr hconjPC)
        have hxM : (x : G) ∈ M := hNPeq ▸ hxN
        have hxP : (x : G) ∈ P := by
          rw [hP_eq]
          exact ⟨⟨hCleR x.2, hxM⟩, x.2.2⟩
        exact Subgroup.mem_subgroupOf.mpr hxP
      · exact Subgroup.le_normalizer
    let : Group.IsNilpotent C := hCnil
    have hnc : NormalizerCondition C :=
      Group.normalizerCondition_of_isNilpotent (G := C)
    have hPCtop : PC = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc)
        PC hnormPC
    apply le_antisymm hPleC
    intro x hx
    have hxPC : (⟨x, hx⟩ : C) ∈ PC := by rw [hPCtop]; simp
    exact Subgroup.mem_subgroupOf.mp hxPC
  constructor
  · exact hP_eq_C
  · apply le_antisymm
    · rw [hB_eq]
      exact inf_le_inf inf_le_left le_rfl
    · intro x hx
      have hxU : x ∈ U := hx.1
      have hxfix : s * x * s⁻¹ = x := by
        have hcomm : s * x = x * s :=
          (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
        rw [hcomm]
        group
      have hconj_mem : ∀ z : G, z ∈ U → s * z * s⁻¹ = z →
          ∀ y : G, y ∈ P → z * y * z⁻¹ ∈ P := by
        intro z hzU hzfix y hy
        have hyC : y ∈ C := hP_eq_C ▸ hy
        have hconjR : z * y * z⁻¹ ∈ R :=
          hRnormalU.2 z hzU y (hCleR hyC)
        have hyfix : s * y * s⁻¹ = y := by
          have hcomm : s * y = y * s :=
            (Subgroup.mem_centralizer_iff.mp hyC.2) s (by simp)
          rw [hcomm]
          group
        have hzInvFix : s * z⁻¹ * s⁻¹ = z⁻¹ := by
          calc
            s * z⁻¹ * s⁻¹ = (s * z * s⁻¹)⁻¹ := by group
            _ = z⁻¹ := by rw [hzfix]
        have hconjFix : s * (z * y * z⁻¹) * s⁻¹ = z * y * z⁻¹ := by
          calc
            s * (z * y * z⁻¹) * s⁻¹ =
                (s * z * s⁻¹) * (s * y * s⁻¹) * (s * z⁻¹ * s⁻¹) := by group
            _ = z * y * z⁻¹ := by rw [hzfix, hyfix, hzInvFix]
        have hcent : z * y * z⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hmul := congrArg (fun a : G => a * s) hconjFix
          have hscomm : s * (z * y * z⁻¹) = (z * y * z⁻¹) * s := by
            simpa [mul_assoc] using hmul
          exact hscomm.symm
        have hconjC : z * y * z⁻¹ ∈ C := ⟨hconjR, hcent⟩
        exact hP_eq_C.symm ▸ hconjC
      have hxNormP : x ∈ Subgroup.normalizer (P : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · exact hconj_mem x hxU hxfix y
        · intro hconj
          have hxinvfix : s * x⁻¹ * s⁻¹ = x⁻¹ := by
            calc
              s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
              _ = x⁻¹ := by rw [hxfix]
          have hback := hconj_mem x⁻¹ (U.inv_mem hxU) hxinvfix
            (x * y * x⁻¹) hconj
          simpa [mul_assoc] using hback
      have hxM : x ∈ M := hNPeq ▸ hxNormP
      rw [hB_eq]
      exact ⟨⟨hxU, hxM⟩, hx.2⟩

end CFSG.GorensteinWalter

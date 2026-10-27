module

public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Open
open CFSG.Yardstones.M3aba7dc4b8a8

structure ThSetting (G : Type) [Group G] [Finite G] where
  z : G
  ord_z : orderOf z = 2
  ext : IsExtraspecialPGroup 2 (coreQ z)
  card_Q : Nat.card (coreQ z) = 2 ^ 9
  θ : ↥(Subgroup.centralizer ({z} : Set G)) →* alternatingGroup (Fin 9)
  θ_surj : Function.Surjective θ
  θ_ker : θ.ker = (coreQ z).subgroupOf (Subgroup.centralizer ({z} : Set G))
  g₀ : G
  g₀_mem : g₀⁻¹ * z * g₀ ∈ coreQ z
  g₀_ne : g₀⁻¹ * z * g₀ ≠ z

namespace ThSetting

variable {G : Type} [Group G] [Finite G]

abbrev H (S : ThSetting G) : Subgroup G := Subgroup.centralizer ({S.z} : Set G)

abbrev Q (S : ThSetting G) : Subgroup G := coreQ S.z

theorem Q_le_H (S : ThSetting G) : S.Q ≤ S.H :=
  Subgroup.map_subtype_le (generalizedFitting S.H)

theorem z_mem_Q (S : ThSetting G) : S.z ∈ S.Q := by
  have hzH : S.z ∈ S.H := Subgroup.mem_centralizer_singleton_iff.mpr (by group)
  have hcenter : Subgroup.center S.H ≤ generalizedFitting S.H := by
    rw [generalizedFitting]
    exact le_sup_of_le_left (le_sSup ⟨inferInstance, inferInstance⟩)
  have hzcenter : (⟨S.z, hzH⟩ : S.H) ∈ Subgroup.center S.H := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h.2)
  exact Subgroup.mem_map_of_mem S.H.subtype (hcenter hzcenter)

theorem card_H (S : ThSetting G) : Nat.card S.H = 2 ^ 9 * 181440 := by
  have hcardA : Nat.card ↥(alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hker : Nat.card ↥S.θ.ker = Nat.card ↥S.Q := by
    rw [S.θ_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Q_le_H).toEquiv
  have hrange : Nat.card ↥S.θ.range = 181440 := by
    rw [MonoidHom.range_eq_top.mpr S.θ_surj]
    simpa using hcardA
  have h := Subgroup.card_ker_mul_card_range S.θ
  rw [hker, hrange, S.card_Q] at h
  exact h.symm

@[expose] def h₀ (S : ThSetting G) : G := S.g₀⁻¹ * S.z * S.g₀

theorem h₀_def (S : ThSetting G) : S.h₀ = S.g₀⁻¹ * S.z * S.g₀ := rfl

theorem h₀_mem_Q (S : ThSetting G) : S.h₀ ∈ S.Q := S.g₀_mem

theorem h₀_ne_z (S : ThSetting G) : S.h₀ ≠ S.z := S.g₀_ne

theorem orderOf_h₀ (S : ThSetting G) : orderOf S.h₀ = 2 := by
  have h : SemiconjBy S.g₀⁻¹ S.z S.h₀ := by
    show S.g₀⁻¹ * S.z = S.h₀ * S.g₀⁻¹
    unfold h₀
    group
  rw [← S.ord_z]
  exact (SemiconjBy.orderOf_eq S.g₀⁻¹ h).symm

end ThSetting

structure ThCore (G : Type) [Group G] [Finite G] where
  z : G
  ψ : ↥(CFSG.Sporadic.Th.Max3.M) ≃* ↥(Subgroup.centralizer ({z} : Set G))
  conj : ∀ j : G, orderOf j = 2 → ∃ g : G, g * z * g⁻¹ = j

@[expose] noncomputable def thCoreJ :
    ThCore ↥CFSG.Sporadic.Th.J where
  z := CFSG.Sporadic.Th.a
  ψ := (MulEquiv.subgroupCongr (CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M
    CFSG.Sporadic.Th.th_kernel_facts)).symm
  conj := fun j hj =>
    isConj_iff.mp (CFSG.Sporadic.Th.Max3.all_involutions_conjugate j hj)

namespace ThSetting

@[expose] noncomputable def ofLeaf {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ 9) (hwc : ¬ ZWeaklyClosedInCore z)
    {Mbar : Type} [Group Mbar]
    (hM : timmesfeldQuotientIso
      (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar)
    (e : Mbar ≃* alternatingGroup (Fin 9)) : ThSetting G := by
  classical
  have hM' : ∃ φ : ↥(Subgroup.centralizer ({z} : Set G)) →* Mbar,
      Function.Surjective φ ∧
        φ.ker = generalizedFitting (Subgroup.centralizer ({z} : Set G)) := hM
  let φ := Classical.choose hM'
  have hφsurj : Function.Surjective φ := (Classical.choose_spec hM').1
  have hφker : φ.ker = generalizedFitting
      (Subgroup.centralizer ({z} : Set G)) := (Classical.choose_spec hM').2
  have hwc' : ∃ g : G, g⁻¹ * z * g ∈ coreQ z ∧ g⁻¹ * z * g ≠ z := by
    by_contra h
    apply hwc
    intro g hg
    by_contra hne
    exact h ⟨g, hg, hne⟩
  let g₀ := Classical.choose hwc'
  have hg₀mem : g₀⁻¹ * z * g₀ ∈ coreQ z := (Classical.choose_spec hwc').1
  have hg₀ne : g₀⁻¹ * z * g₀ ≠ z := (Classical.choose_spec hwc').2
  refine
    { z := z
      ord_z := hz
      ext := hext
      card_Q := hcard
      θ := e.toMonoidHom.comp φ
      θ_surj := e.surjective.comp hφsurj
      θ_ker := ?_
      g₀ := g₀
      g₀_mem := hg₀mem
      g₀_ne := hg₀ne }
  rw [MonoidHom.ker_comp_of_injective φ e.toMonoidHom e.injective, hφker]
  simp only [coreQ, inSubgroup]
  exact (Subgroup.comap_map_eq_self_of_injective
    (Subgroup.centralizer ({z} : Set G)).subtype_injective _).symm

end ThSetting

end CFSG.Sporadic.Th.Recog

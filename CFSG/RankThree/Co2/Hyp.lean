module

public import CFSG.RankThree.Co2.Transport
public import Certificates.Certificate3054
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import Certificates.Certificate16000

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Blueprint CFSG.Monster.B.TwoA.Co2Inv

local notation "Co₂" => NativeSporadic.Co2

structure Co2CentHyp (G : Type) [Group G] : Type where
  finite : Finite G
  simple : IsSimpleGroup G
  z : G
  hz : orderOf z = 2
  φ : Subgroup.centralizer ({z} : Set G) ≃* Cr

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

abbrev H : Subgroup G := Subgroup.centralizer ({h.z} : Set G)

@[expose] def zG : h.H := ⟨h.z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem zG_mem_center : h.zG ∈ Subgroup.center h.H := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)

theorem zG_ne_one : h.zG ≠ 1 := by
  intro e
  have h1 : h.z = 1 := congrArg Subtype.val e
  have := h.hz
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem φ_zG : h.φ h.zG = rCr := by
  have hc : h.φ h.zG ∈ Subgroup.center Cr := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := h.φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 h.zG_mem_center x)
  rcases eq_one_or_eq_rCr_of_mem_center hc with h1 | h1
  · exact absurd ((MulEquiv.map_eq_one_iff h.φ).1 h1) h.zG_ne_one
  · exact h1

theorem φ_symm_rCr : h.φ.symm rCr = h.zG := by
  rw [MulEquiv.symm_apply_eq, h.φ_zG]

@[expose] def ofTwoCentral {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (z : G)
    (hz : orderOf z = 2) (z₀ : Co₂) (hz₀ : z₀ ≠ 1)
    (hcen : ∃ S : Sylow 2 Co₂, z₀ ∈ (S : Subgroup Co₂) ∧
      ∀ s ∈ (S : Subgroup Co₂), z₀ * s = s * z₀)
    (e : Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer ({z₀} : Set Co₂)) :
    Co2CentHyp G where
  finite := inferInstance
  simple := inferInstance
  z := z
  hz := hz
  φ := e.trans (Classical.choice (nonempty_centralizer_mulEquiv_Cr z₀ hz₀ hcen))

end Co2CentHyp

end CFSG.RankThree.Co2

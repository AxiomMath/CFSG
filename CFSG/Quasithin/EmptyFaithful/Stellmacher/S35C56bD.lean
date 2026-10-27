module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56bC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim6b (hS : Sit H M S) (hI : CaseI H M) : Claim6b H M := by
  intro β l δ E hβ hl hlδ hδ hE hVE hEW hEL
  refine le_antisymm ?_ (le_inf inf_le_left (inf_le_right.trans hVE))
  rintro b hb
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hirr : ∀ U : Subgroup G, Zv β ≤ U → U ≤ Vn β → Lr β ≤ Subgroup.normalizer (U : Set G) →
      U = Zv β ∨ U = Vn β := fun U h1 h2 h3 =>
    (orthZ hS hI hβ).eq_or_eq_of_oTwoRes h1 h2 h3
  obtain ⟨t, htQ, htl⟩ := Set.not_subset.mp (claim6a hS hI β l hβ hl)
  have hZ := comm_mem_Zv hS hI hirr hβ hl hlδ hδ hE hEW hEL htQ htl hb
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mpr hl
  have hδl : δ ∈ nbrs l := Std.mem_nbrs_symm.mpr hlδ
  obtain ⟨δ', hδ', h2, h3, -⟩ := Std.nbrs_S3_third hS hlt hβl hδl hδ.symm
  have htβ : t ∈ Qv β := Q_le_Qv β htQ
  have hsw : (⟨t, stab_le β (Qv_le_stab_self β htβ)⟩ : ↥(H ⊔ M)) • δ = δ' :=
    C1.smul_eq_third hS hlt hβl hδl hδ' hδ.symm h2.symm h3.symm htβ htl
  have h1 : t * b * t⁻¹ ∈ Vn δ' := by
    rw [← hsw, Vn_smul, mem_conjSub]
    simpa [mul_assoc] using hb.1
  have hzt : ⁅t, b⁆ ∈ Zv β := by
    rw [← commutatorElement_inv]
    exact (Zv β).inv_mem (hZ t htQ)
  have hzV : Zv β ≤ Vn δ := (Std.Zv_le_Zv_of_nbr hS hβ hl).trans (Std.Zv_le_Vn hlδ)
  have e : t * b * t⁻¹ = ⁅t, b⁆ * b := by
    simp only [commutatorElement_def]
    group
  have h4 : t * b * t⁻¹ ∈ Vn δ ⊓ Vn δ' := by
    refine ⟨?_, h1⟩
    rw [e]
    exact (Vn δ).mul_mem (hzV hzt) hb.1
  rw [← C1.inter_eq' hS hβ hl hlδ hδ (Std.mem_nbrs_symm.mpr hδ') h3.symm] at h4
  have hb' : b ∈ Vn β := by
    have : b = ⁅t, b⁆⁻¹ * (t * b * t⁻¹) := by
      rw [e]
      group
    rw [this]
    exact (Vn β).mul_mem ((Vn β).inv_mem (Std.Zv_le_Vn_S5 hS hβ hzt)) h4.1
  exact ⟨hb.1, hb'⟩

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin

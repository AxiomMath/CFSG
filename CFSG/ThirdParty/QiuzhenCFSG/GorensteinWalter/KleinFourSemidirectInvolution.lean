module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! An involution outside the Klein-four factor of a semidirect product has
a nontrivial commuting involution in the complementary factor. -/

public theorem exists_complement_involution_commuting_of_kleinFour_sup
    {G : Type u} [Group G] [Finite G]
    (A V E : Subgroup G)
    (hVnorm : IsNormalIn V A)
    (hEleA : E ≤ A)
    (hVK : IsKleinFour V)
    (hdisj : Disjoint V E)
    (hsup : V ⊔ E = A)
    {y : G} (hyA : y ∈ A) (hyI : IsInvolution y) (hyV : y ∉ V) :
    ∃ e : G, e ∈ E ∧ IsInvolution e ∧ Commute e y := by
  classical
  have hEnormV : E ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he v hv
    exact hVnorm.2 e (hEleA he) v hv
  have hySup : y ∈ V ⊔ E := by
    rw [hsup]
    exact hyA
  have hyProd : y ∈ (V : Set G) * (E : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V E hEnormV]
    exact hySup
  rcases hyProd with ⟨v, hv, e, he, hve⟩
  have hve' : v * e = y := hve
  have heA : e ∈ A := hEleA he
  have hevV : e * v * e⁻¹ ∈ V := hVnorm.2 e heA v hv
  have hwV : v * (e * v * e⁻¹) ∈ V := V.mul_mem hv hevV
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hwe2 : (v * (e * v * e⁻¹)) * e ^ 2 = 1 := by
    rw [pow_two]
    calc
      (v * (e * v * e⁻¹)) * (e * e) = (v * e) * (v * e) := by group
      _ = y * y := congrArg₂ (· * ·) hve' hve'
      _ = 1 := hy2
  have he2V : e ^ 2 ∈ V := by
    have heq : e ^ 2 = (v * (e * v * e⁻¹))⁻¹ := by
      calc
        e ^ 2 = (v * (e * v * e⁻¹))⁻¹ *
            ((v * (e * v * e⁻¹)) * e ^ 2) := by group
        _ = (v * (e * v * e⁻¹))⁻¹ := by rw [hwe2]; simp
    rw [heq]
    exact V.inv_mem hwV
  have he2E : e ^ 2 ∈ E := E.pow_mem he 2
  have he2 : e ^ 2 = 1 := by
    have hbot : e ^ 2 ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp hdisj) ⟨he2V, he2E⟩
    exact Subgroup.mem_bot.mp hbot
  have hee : e * e = 1 := by simpa [pow_two] using he2
  have hene : e ≠ 1 := by
    intro he1
    apply hyV
    have : v = y := by simpa [he1] using hve'
    rw [← this]
    exact hv
  have heI : IsInvolution e := ⟨hene, he2⟩
  have hv2 : v * v = 1 := by
    simpa using congrArg Subtype.val (hVK.mul_self ⟨v, hv⟩)
  have hev : e * v = v * e := by
    have hsq : (v * e) * (v * e) = 1 := by rw [hve', hy2]
    have hcalc : v * ((v * e) * (v * e)) * e = e * v := by
      calc
        v * ((v * e) * (v * e)) * e = (v * v) * e * v * (e * e) := by group
        _ = e * v := by rw [hv2, hee]; simp
    calc
      e * v = v * ((v * e) * (v * e)) * e := hcalc.symm
      _ = v * e := by rw [hsq]; simp
  refine ⟨e, he, heI, ?_⟩
  rw [commute_iff_eq]
  calc
    e * y = e * (v * e) := congrArg (fun z => e * z) hve'.symm
    _ = (e * v) * e := by group
    _ = (v * e) * e := by rw [hev]
    _ = y * e := congrArg (fun z => z * e) hve'

end CFSG.GorensteinWalter

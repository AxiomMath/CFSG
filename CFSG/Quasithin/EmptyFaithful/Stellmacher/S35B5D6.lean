module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem trivAct_of_condD (hC : Ch.Ctx H M S) (hD : CondD H M) {γ l β : Geo H M}
    (hγ : vtype γ = false) (hl : l ∈ nbrs γ) (hlβ : l ∈ nbrs β) (hβγ : β ≠ γ) :
    ∀ q ∈ Qv γ, ∀ y ∈ Vn β, q * y * q⁻¹ * y⁻¹ ∈ Vn γ := by
  have hS := hC.sit
  have hl3 : vtype l = true := vtype_nbr_S5 hγ hl
  obtain ⟨β'', h3, h31, h32, -⟩ :=
    nbrs_S3_third hS hl3 (mem_nbrs_symm.mp hl) (mem_nbrs_symm.mp hlβ) hβγ.symm
  have hD' := hD γ l β β'' hγ hl hlβ (mem_nbrs_symm.mpr h3) hβγ h31 h32
  exact dswap hC hγ hl hlβ (mem_nbrs_symm.mpr h3) hβγ h31 h32 hD'

theorem condD_false (hC : Ch.Ctx H M S) (hclaimR : ClaimR H M) (hb : bMin H M = 5)
    (hD : CondD H M) {β α' m γ : Geo H M} (hp : S34.PD β α') (hback : Back H M β α' m γ) :
    False := by
  have hS := hC.sit
  obtain ⟨hm, hγm, d1, d2⟩ := hback
  have hback : Back H M β α' m γ := ⟨hm, hγm, d1, d2⟩
  have d0 := hp.dist_eq
  have hvm : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  have hvγ : vtype γ = false := vtype_nbr_S3 hvm hγm
  have hdβγ : dist γ β = 2 := by
    rw [CosetGeom.dist_comm]; omega
  have hαγ : α' ≠ γ := by
    intro h; subst h; omega
  obtain ⟨l0, hl0, hγl0, hγβ⟩ := dist_eq_two_iff.mp hdβγ
  have hmγ : m ∈ nbrs γ := mem_nbrs_symm.mpr hγm
  have hdαγ : dist α' γ = 2 :=
    dist_eq_two_iff.mpr ⟨m, hmγ, mem_nbrs_symm.mpr hm, hαγ⟩
  have hl0γ : l0 ∈ nbrs γ := mem_nbrs_symm.mpr hγl0
  have hQβ := trivAct_of_condD hC hD hvγ hl0γ hl0 hγβ.symm
  have hQα := trivAct_of_condD hC hD hvγ hmγ hm hαγ
  have hβW : Vn β ≤ Wb γ := Vn_le_Wb (by rw [CosetGeom.dist_comm]; exact hdβγ)
  have hαW : Vn α' ≤ Wb γ := Vn_le_Wb hdαγ
  have hcent := comm_le_centralizer hS hβW hαW hQβ hQα
  obtain ⟨-, hRle, hnot⟩ := hclaimR β α' m γ hp hback
  have hZ : ⁅Vn β, Vn α'⁆ ≤ Zv γ :=
    (le_inf (hRle.trans inf_le_right) hcent).trans (cent_Vn_le_Zv hC hvγ)
  exact hnot (hZ.trans (Zv_le_Zv_of_nbr hS hvγ hmγ))

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K6bB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Inter
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K6bA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.K6b

open S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_mem_Zv (hS : Sit H M S) (hII : CaseII H M) {β l δ : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β) {E : Subgroup G}
    (hE : stab β ≤ Subgroup.normalizer (E : Set G)) (hEW : E ≤ Wb β) (hEL : ⁅E, Lr β⁆ ≤ Vn β)
    {t : G} (ht : t ∈ ⁅Qv β, Lr β⁆) (htl : t ∉ Qv l) {b : G} (hb : b ∈ Vn δ ⊓ E) :
    ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b, q⁆ ∈ Zv β := by
  have hC' : ∀ b' ∈ Vn δ ⊓ E, ∀ q ∈ ⁅Qv β, Lr β⁆, ⁅b', q⁆ ∈ S34.Cb β :=
    fun b' hb' => comm_mem_Cb hS hII hβ hl hlδ hδ hE hEW hEL ht htl hb'
  have hBE : Vn δ ⊓ E ≤ E := inf_le_right
  have hBs : Vn δ ⊓ E ≤ stab β :=
    hBE.trans (hEW.trans ((Std.Wb_le_Qv hS β).trans (Qv_le_stab_self β)))
  have hZn : stab β ≤ Subgroup.normalizer (Zv β : Set G) := stab_le_normalizer_Zv hS.glob.amalg β
  have hQs : ⁅Qv β, Lr β⁆ ≤ stab β := (Q_le_Qv β).trans (Qv_le_stab_self β)
  have h1 : ⁅⁅Lr β, Vn δ ⊓ E⁆, ⁅Qv β, Lr β⁆⁆ ≤ Zv β := by
    have hLB : ⁅Lr β, Vn δ ⊓ E⁆ ≤ Vn β := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hBE le_rfl).trans hEL
    rw [Subgroup.commutator_le]
    intro x hx q hq
    exact S34.comm_Vn_Qv_le hS.glob hβ
      (Subgroup.commutator_mem_commutator (hLB hx) (Q_le_Qv β hq))
  have h2 : ⁅⁅Vn δ ⊓ E, ⁅Qv β, Lr β⁆⁆, Lr β⁆ ≤ Zv β := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hxC : x ∈ S34.Cb β := by
      have : ⁅Vn δ ⊓ E, ⁅Qv β, Lr β⁆⁆ ≤ S34.Cb β := by
        rw [Subgroup.commutator_le]
        exact fun b' hb' q hq => hC' b' hb' q hq
      exact this hx
    have hxl : x * l = l * x := (Subgroup.mem_centralizer_iff.mp hxC.2 l hl).symm
    have hcomm : ⁅x, l⁆ = 1 := by
      rw [commutatorElement_def, hxl]
      group
    rw [hcomm]
    exact (Zv β).one_mem
  have hQL : ⁅⁅Qv β, Lr β⁆, Lr β⁆ = ⁅Qv β, Lr β⁆ :=
    comm_comm_oTwoRes (X := stab β) (P := Qv β) (pCoreOf_isPGroup 2 _)
      ((Lr_le_stab β).trans (Qv_normal β))
  have h3 := three_subgroups_mod (X := Lr β) (Y := Vn δ ⊓ E) (Z := ⁅Qv β, Lr β⁆) (N := Zv β)
    ((Lr_le_stab β).trans hZn) (hBs.trans hZn) (hQs.trans hZn) h1 h2
  rw [hQL] at h3
  intro q hq
  have h4 : ⁅q, b⁆ ∈ Zv β := h3 (Subgroup.commutator_mem_commutator hq hb)
  rw [← commutatorElement_inv]
  exact (Zv β).inv_mem h4

theorem claim6b (hS : Sit H M S) (hII : CaseII H M) (h6a : Claim6a H M) : Claim6b H M := by
  intro β l δ E hβ hl hlδ hδ hE hVE hEW hEL
  refine le_antisymm ?_ (le_inf inf_le_left (inf_le_right.trans hVE))
  rintro b hb
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  obtain ⟨t, htQ, htl⟩ := Set.not_subset.mp (h6a β l hβ hl)
  have hZ := comm_mem_Zv hS hII hβ hl hlδ hδ hE hEW hEL htQ htl hb
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
  have hvδ : vtype δ = false := Std.vtype_nbr_S3 hlt hδl
  have h5 : Vn δ ⊓ Vn δ' = Zv l := hII δ l δ' hvδ hlδ (Std.mem_nbrs_symm.mpr hδ') h3
  rw [h5, ← hII β l δ hβ hl hlδ hδ] at h4
  have hb' : b ∈ Vn β := by
    have : b = ⁅t, b⁆⁻¹ * (t * b * t⁻¹) := by
      rw [e]
      group
    rw [this]
    exact (Vn β).mul_mem ((Vn β).inv_mem (Std.Zv_le_Vn_S5 hS hβ hzt)) h4.1
  exact ⟨hb.1, hb'⟩

end S35.K6b

end F53.Stellmacher

end CFSG.Quasithin

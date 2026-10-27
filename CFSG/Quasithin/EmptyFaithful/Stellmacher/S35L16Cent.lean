module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2 S35.II
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem rCent_II (hS : Sit H M S) : RCent H M := by
  intro β α' m γ' hp hb hT r hr q hq
  obtain ⟨c⟩ := exists_chart2 hS hp.vδ'
  have hl : m ∈ nbrs α' := hb.1
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hl
  have hle1 : Vn β ≤ stab α' := (Back.Vn_le hS hp hb).1
  have hRV : r ∈ Vn α' := (PD_comm_le hS hp hr).2
  have hqs : q ∈ stab α' := (That2_le_inf hS α' m hq).1
  have hbar : c.bar (Vn β) ≤ That (c.Dl m) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := c.mem_bar_iff.mp hx
    exact c.θ_mem_That_of_mem_That2 hS hp.vδ' hl (hT hu)
  have hrR : r ∈ commSec (Vn β) (Cb α') (Vn α') := by
    have h1 : r ∈ ⁅Vn α', Vn β⁆ := by rw [Subgroup.commutator_comm]; exact hr
    exact Subgroup.mem_sup_left h1
  have hπ : c.π ⟨r, hRV⟩ ∈ commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤ := by
    rw [← commW_That_eq hD]
    refine commW_mono_left' hbar ⊤ ?_
    rw [← c.img_commSec hle1]
    exact (c.mem_img_iff').mpr ⟨⟨r, hRV⟩, hrR, rfl⟩
  have hθq : c.θ ⟨q, hqs⟩ ∈ That (c.Dl m) :=
    c.θ_mem_That_of_mem_That2 hS hp.vδ' hl hq
  rw [← cenW_commW_z hD (isCentInv_zc hD)] at hθq
  have hfix := mem_cenW.mp hθq _ hπ
  have hCb : q * r * q⁻¹ * r⁻¹ ∈ Cb α' := (c.comm_mem_iff ⟨q, hqs⟩ ⟨r, hRV⟩).mpr hfix
  have hcomm : q * r * q⁻¹ * r⁻¹ ∈ ⁅Vn α', stab α'⁆ := by
    have h1 : ⁅r, q⁆ ∈ ⁅Vn α', stab α'⁆ := Subgroup.commutator_mem_commutator hRV hqs
    have e : q * r * q⁻¹ * r⁻¹ = ⁅r, q⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  rw [commutatorElement_def]
  exact UC.of_sit hS hp.vδ' ⟨hcomm, hCb⟩

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Zl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.C3

open S35.Std S35.Fin S35.Ch2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

theorem claim3a_of (hS : Sit H M S) : S35.II.Claim3a H M := by
  intro β α' m γ' hp hb
  refine ⟨fun h => S34.pd_not_comm_le hS.glob hp (h ▸ bot_le), ?_⟩
  intro hRZ
  obtain ⟨c⟩ := exists_chart2 hS hp.vδ'
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hp.not_le
  have hvα : v ∈ stab α' := (PD_Vn_le_stab hS hp).1 hv
  have hmα : m ∈ nbrs α' := hb.1
  have hθ : c.θ ⟨v, hvα⟩ ≠ 1 := fun h => hvQ ((c.ker_iff hS hp.vδ' _).mp h)
  have hxs : Subgroup.zpowers v ≤ stab α' := Subgroup.zpowers_le.mpr hvα
  have hZm : Zv m ≤ c.pre (c.img (Zv m)) := fun z hz => by
    have hzV : z ∈ Vn α' := Zv_le_Vn hmα hz
    exact (c.mem_pre_iff ⟨z, hzV⟩).mpr ((c.mem_img_iff').mpr ⟨⟨z, hzV⟩, hz, rfl⟩)
  have hcs : commSec (Subgroup.zpowers v) (S34.Cb α') (Vn α') ≤ c.pre (c.img (Zv m)) := by
    refine sup_le ?_ (c.Cb_le_pre _)
    refine le_trans ?_ hZm
    rw [Subgroup.commutator_le]
    intro u hu a ha
    have ha' : a ∈ Vn β := Subgroup.zpowers_le.mpr hv ha
    rw [← commutatorElement_inv]
    exact (Zv m).inv_mem (hRZ (Subgroup.commutator_mem_commutator ha' hu))
  have himg := c.img_mono hcs
  rw [c.img_commSec hxs, c.bar_zpowers hvα, c.img_pre, c.img_Zv_nbr hS hp.vδ' hmα] at himg
  exact S35.At.not_commW_le_vp hθ _ himg

end S35.C3

end F53.Stellmacher

end CFSG.Quasithin

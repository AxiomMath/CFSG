module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtR
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

theorem isPGroup_Wb (hS : Sit H M S) (β : Geo H M) : IsPGroup 2 (Wb β) :=
  IsPGroup.to_le (pCoreOf_isPGroup 2 (stab β)) (Wb_le_Qv hS β)

theorem claim9_of_dict (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) : Claim9 H M := by
  intro β α' m γ' hp hb
  obtain ⟨hvm, hvγ, hne, -, -⟩ := Back.facts hp hb
  obtain ⟨-, hRle, hRm⟩ := claimR_of_dict hS hZ hA β α' m γ' hp hb
  obtain ⟨c⟩ := exists_chart hS hZ hvγ
  have hml : m ∈ nbrs γ' := mem_nbrs_symm.mp hb.2.1
  have hαm : α' ∈ nbrs m := mem_nbrs_symm.mp hb.1
  have hne' : α' ≠ γ' := fun h => hne h.symm
  obtain ⟨hplane, hline⟩ := hA γ' m α' c hvγ hml hαm hne'
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hml
  obtain ⟨r, hrR, hrZ⟩ := IsConcreteLE.not_le_iff_exists.mp hRm
  have hrγ : r ∈ Vn γ' := (hRle hrR).2
  have hrα : r ∈ Vn α' := (hRle hrR).1
  have hrβ : r ∈ Vn β := (S35.Std.PD_comm_le hS hp hrR).1
  have hπ : c.π ⟨r, hrγ⟩ ∈ commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤ := by
    rw [← hplane]
    exact (c.mem_img_iff').mpr ⟨⟨r, hrγ⟩, ⟨hrγ, hrα⟩, rfl⟩
  have hπ' : c.π ⟨r, hrγ⟩ ∉ Subgroup.zpowers (vp (fixPt (c.Dl m))) := by
    rw [← hline]
    intro h
    exact hrZ ((c.mem_img_iff (S34.Zv_le_Zv_nbr hS.glob hvγ hml) ⟨r, hrγ⟩).mp h)
  obtain ⟨x, y, hxy, hxe, hsw⟩ := exists_ep_of_mem_commW hD hπ hπ'
  have hW : Wb β ≤ stab γ' := Back.Wb_le_stab hS hp hb
  have hfix : ∀ g ∈ c.bar (Wb β), orth.act g (ep x y) = ep x y := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := (c.mem_bar_iff).mp hg
    rw [← hxe]
    refine (c.comm_mem_iff w ⟨r, hrγ⟩).mp ?_
    have hc : ⁅r, (w : G)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hrβ hw
      rw [comm_Vn_Wb hS β] at this
      exact Subgroup.mem_bot.mp this
    have e : (w : G) * r * (w : G)⁻¹ * r⁻¹ = ⁅r, (w : G)⁆⁻¹ := by
      rw [commutatorElement_def]; group
    show (w : G) * r * (w : G)⁻¹ * r⁻¹ ∈ Zv γ'
    rw [e, hc]
    simp
  have h2 := relIndex_inf_le_two (isPGroup_bar c hW (isPGroup_Wb hS β)) hxy hfix hsw
  have e1 : Wb β ⊓ stab m = Wb β ⊓ c.preθ (c.Dl m) := by
    rw [c.preθ_Dl hS hvγ hml]
    ext g
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, hW h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e1, Subgroup.inf_relIndex_left, relIndex_preθ c hW]
  rw [inf_comm, Subgroup.inf_relIndex_right] at h2
  exact h2

end S35.At

end F53.Stellmacher

end CFSG.Quasithin

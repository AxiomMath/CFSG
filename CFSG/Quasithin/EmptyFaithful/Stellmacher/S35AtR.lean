module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtArc
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtBase

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

theorem exists_chart (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ)) {δ : Geo H M}
    (hδ : vtype δ = false) : Nonempty (Ch.Chart δ) :=
  Ch.nonempty_chart (Zv_le_Vn_S5 hS hδ) (hZ δ hδ)

theorem Back.comm_le (hS : Sit H M S) (hA : ArcDict H M) (c : Ch.Chart α') (hp : S34.PD β α')
    (hb : Back H M β α' m γ') {v : G} (hv : v ∈ Vn β) :
    c.θ ⟨v, (Back.Vn_le hS hp hb).1 hv⟩ ∈ That (c.Dl m) ∧
      ∀ u ∈ Vn α', ⁅u, v⁆ ∈ Vn α' ⊓ Vn γ' := by
  obtain ⟨h1, h2, -⟩ := Back.Vn_le hS hp hb
  have hcen : ∀ r ∈ Vn α' ⊓ Vn γ', v * r * v⁻¹ = r := fun r hr => by
    rw [Back.comm hS hp hb v hv r hr.2]; simp
  exact Arc.thm hS hA c hp.vδ' hb.1 hb.2.1 (Back.facts hp hb).2.2.1 ⟨h1 hv, h2 hv⟩ hcen

theorem claimR_of_dict (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) : ClaimR H M := by
  intro β α' m γ' hp hb
  obtain ⟨c⟩ := exists_chart hS hZ hp.vδ'
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact S34.pd_not_comm_le hS.glob hp (h ▸ bot_le)
  · rw [Subgroup.commutator_le]
    intro v hv u hu
    rw [← commutatorElement_inv]
    exact (Vn α' ⊓ Vn γ').inv_mem ((Back.comm_le hS hA c hp hb hv).2 u hu)
  · intro hRZ
    obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hp.not_le
    obtain ⟨hvα, hvm, -⟩ := Back.Vn_le hS hp hb
    have hθ : c.θ ⟨v, hvα hv⟩ ≠ 1 := fun h => hvQ ((c.ker_iff hS hp.vδ' _).mp h)
    obtain ⟨-, hline⟩ := hA α' m γ' c hp.vδ' hb.1 hb.2.1 (Back.facts hp hb).2.2.1
    have hxs : Subgroup.zpowers v ≤ stab α' := Subgroup.zpowers_le.mpr (hvα hv)
    have hcs : commSec (Subgroup.zpowers v) (Zv α') (Vn α') ≤ Zv m := by
      refine sup_le ?_ (S34.Zv_le_Zv_nbr hS.glob hp.vδ' hb.1)
      rw [Subgroup.commutator_le]
      intro u hu a ha
      have ha' : a ∈ Vn β := Subgroup.zpowers_le.mpr hv ha
      rw [← commutatorElement_inv]
      exact (Zv m).inv_mem (hRZ (Subgroup.commutator_mem_commutator ha' hu))
    have himg := c.img_mono hcs
    rw [c.img_commSec hxs, hline, c.bar_zpowers (hvα hv)] at himg
    exact not_commW_le_vp hθ _ himg

end S35.At

end F53.Stellmacher

end CFSG.Quasithin

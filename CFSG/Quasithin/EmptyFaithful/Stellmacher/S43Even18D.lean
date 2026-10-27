module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even18A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even18C
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModSec

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace C18

variable {α : Geo H M}

theorem Zv_le_Wcomm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) :
    Zv α ≤ Wcomm α := by
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hβ' : β ∈ nbrs α := hβ
  obtain ⟨D⟩ := hs.exists_dict hA hβ'
  have hZn := stab_le_normalizer_Zv hA α
  have hV : ⁅Zv α, stab α⁆ ≤ Zv α := D.commutator_le le_rfl
  have hVn : stab α ≤ Subgroup.normalizer ((⁅Zv α, stab α⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hZn Subgroup.le_normalizer
  rcases D.eq_bot_or_eq_of_invariant_oTwoRes hV (fun l hl v hv =>
      (Subgroup.mem_normalizer_iff.mp (hVn (oTwoRes_le _ hl)) v).mp hv) with h | h
  · exfalso
    have hβv := Sit43.vtype_true_of_adj hs.vα hβ'
    have h8 := hs.card_comm_Qv hA h26 hβv (nbrs_symm hβ')
    have hle : ⁅Zv α, Qv β⁆ ≤ ⁅Zv α, stab α⁆ :=
      Subgroup.commutator_mono le_rfl (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ'))
    rw [h, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at h8
    omega
  · calc Zv α = ⁅Zv α, stab α⁆ := h.symm
      _ ≤ Wcomm α := Subgroup.commutator_mono (hs.Zv_le_Wn hA h26) le_rfl

theorem isSec_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) : IsSec (stab α) (Zv α) (Wn α) := by
  have hW := hs.w17Hyp hA h26 hb
  exact ⟨hs.Zv_le_Wn hA h26, stab_le_normalizer_Wn α, stab_le_normalizer_Zv hA α,
    fun _ hx _ hy => hW.comm_le (Subgroup.commutator_mem_commutator hx hy), hW.sq_mem⟩

theorem split18 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) (hWQ : ⁅Wn α, Qv α⁆ ≤ Zv α) {x : G} (hx : x ∈ stab α)
    (hxt : IsTransvec 1 x (Zv α) (Wn α)) :
    IsOrthSec (stab α) (Zv α) (Wcomm α) ∧ Estar α ⊔ Wcomm α = Wn α ∧
      Estar α ⊓ Wcomm α = Zv α := by
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hβ' : β ∈ nbrs α := hβ
  obtain ⟨D⟩ := hs.exists_dict hA hβ'
  have hsec := isSec_Wn hA h26 hs hb
  have hQ : ⁅Wn α, pCoreOf 2 (stab α)⁆ ≤ Zv α := hWQ
  have hc : cSecIn (stab α) (Zv α) (Wn α) ≤ pCoreOf 2 (stab α) := by
    refine (secMod_faithful_iff D hsec hQ).mp (secMod_faithful_of_not_le D hsec hQ fun hL =>
      not_forall_Lres_comm hA h26 hs (by omega) hβ' ?_)
    intro l hl w hw
    exact ((mem_cSecIn_iff hsec.normL).mp (hL hl)).2 w hw
  obtain ⟨-, -, -, hinf, hsup, -, -, -, horth⟩ := S18_sec D hsec hQ hc hx hxt
  have hWc : ⁅Wn α, stab α⁆ ⊔ Zv α = Wcomm α := sup_eq_left.mpr (Zv_le_Wcomm hA h26 hs)
  rw [hWc] at hinf hsup horth
  exact ⟨horth, hsup, hinf⟩

end C18

end CFSG.Quasithin.F53.Stellmacher.S43.Even

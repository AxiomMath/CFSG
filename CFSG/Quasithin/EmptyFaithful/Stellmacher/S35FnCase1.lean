module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCfg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem case1 (hS : Sit H M S) (h14 : Claim14 H M) (h15a : Claim15a H M) (h15c : Claim15c H M)
    {β α' m γ' : Geo H M} (hL : Lam β α') (hB : Back H M β α' m γ') {l δ : Geo H M}
    (hl : l ∈ nbrs β) (hn : ¬ Vn α' ≤ Subgroup.normalizer (Zv l : Set G))
    (hδ : δ ∈ nbrs l) (hδβ : δ ≠ β) (hnQ : ¬ Vn δ ≤ Qv γ') : False := by
  have hvβ : vtype β = false := hL.1.vδ
  have hlt : vtype l = true := Std.vtype_nbr_S5 hvβ hl
  have hvδ : vtype δ = false := Std.vtype_nbr_S3 hlt hδ
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδ
  have hdβ := hL.1.dist_eq
  have hdγ := dist_γ' hL hB
  have hd2 : dist δ β = 2 := Std.dist_eq_two_iff.mpr ⟨l, hl, hδ, hδβ⟩
  have hdle : dist δ γ' ≤ dist δ β + dist β γ' := dist_triangle rfl δ β γ'
  have hdeq : dist δ γ' + 1 = bMin H M := by
    by_contra hne
    exact hnQ (Std.Vn_le_Qv_dist hS (by omega))
  have hPD : S34.PD δ γ' := ⟨hvδ, vtype_γ' hL hB, hdeq, hnQ⟩
  have hnZ : ¬ Zv δ ≤ Vn γ' := by
    intro hle
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Zv δ)).mp
      (F53.Zv_ne_bot hS.glob.amalg δ)
    have hgδ : (g : G) ∈ Zv δ := g.2
    have hgl : (g : G) ∈ Zv l := Std.Zv_le_Zv_of_nbr hS hvδ hlδ hgδ
    have hgβ : (g : G) ∈ Zv β := mem_Zv_of_cent hS hL hl hn hgl fun x hx =>
      Vα'_comm_Vγ' hS hL hB x hx g (hle hgδ)
    have hbot := (Std.Zv_ne hS hlt hβl hδ (Ne.symm hδβ)).2.2
    have : (g : G) ∈ Zv β ⊓ Zv δ := ⟨hgβ, hgδ⟩
    rw [hbot] at this
    exact hg1 (Subtype.ext (Subgroup.mem_bot.mp this))
  have hZW : ¬ Zv γ' ≤ Wb δ := h14 δ γ' ⟨hPD, hnZ⟩
  apply hZW
  have hVW : Vn β ≤ Wb δ :=
    Std.Vn_le_Wb (by rw [CosetGeom.dist_comm]; exact hd2)
  refine le_trans ?_ hVW
  have hne15 := h15a β α' m γ' hL hB
  obtain ⟨w, hw, hwα⟩ := IsConcreteLE.not_le_iff_exists.mp hne15
  have hZ0 : Zv α' ≠ ⊥ := by
    intro h
    have := hS.cardZ5 α' hL.1.vδ'
    rw [h] at this
    simp at this
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Zv α')).mp hZ0
  have hzA : (z : G) ∈ Zv α' := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hαγ : α' ≠ γ' := by
    intro h
    subst h
    omega
  obtain ⟨hc, hc1⟩ := comm_swap hS (vtype_m hL hB) (Std.mem_nbrs_symm.mp hB.1)
    hB.2.1 hαγ hw.2 (Wb_le_stab_γ' hS hL hB hw.1) hwα hzA hz1'
  have hzK : (z : G) ∈ Kb β := Zm_le_Kb hS hL hB (Zα'_le_Zm hS hL hB hzA)
  have hwz : ⁅w, (z : G)⁆ ∈ Vn β :=
    h15c β hvβ (Subgroup.commutator_mem_commutator hw.1 hzK)
  have hmem : ⁅(z : G), w⁆ ∈ Vn β := by
    rw [← commutatorElement_inv]
    exact inv_mem hwz
  exact le_of_mem_of_card_two (hS.cardZ5 γ' (vtype_γ' hL hB)) hc hc1 hmem

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin

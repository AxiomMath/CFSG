module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnD2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnChart

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem case2b (hS : Sit H M S) (hF : ChartFacts H M) (h15c : Claim15c H M)
    (hI2 : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → Vn β ⊓ Vn δ = Vn β ⊓ Vn δ')
    {β α' m γ' : Geo H M} (hL : Lam β α') (hB : Back H M β α' m γ') {l : Geo H M}
    (hl : l ∈ Delta0 β α')
    (hQ : ∀ l ∈ Delta0 β α', Wl l ≤ Qv γ') (hW : ∀ l ∈ Delta0 β α', ¬ Wl l ≤ stab α') :
    False := by
  have hβ := hL.1.vδ
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl.1
  have hl3 : vtype l = true := Std.vtype_nbr_S5 hβ hl.1
  obtain ⟨y, hy, hyN, hyl⟩ := hF.ex_out β l hβ hl.1
  set g : ↥(H ⊔ M) := ⟨y, stab_le β hy⟩ with hg
  have hμ : g • l ∈ nbrs β := Std.smul_mem_nbrs_of_stab (g := g) hy hl.1
  have hμl : g • l ≠ l := fun h => hyl (mem_stab_of_smul_eq h)
  have hZμ : Zv (g • l) = Zv l := by
    rw [Zv_smul, F7.conjSub_eq_of_mem_normalizer hyN]
  have hμ0 : g • l ∈ Delta0 β α' := ⟨hμ, by rw [hZμ]; exact hl.2⟩
  obtain ⟨δ, -, hδ, -, hδβ, -, -⟩ := Std.exists_two_others hS hl3 hβl
  obtain ⟨δ', -, hδ', -, hδ'β, -, -⟩ :=
    Std.exists_two_others hS (Std.vtype_nbr_S5 hβ hμ) (Std.mem_nbrs_symm.mp hμ)
  have h1 := Zγ'_le_inter hS h15c hI2 hL hB hl.1 (hQ l hl) (hW l hl) hδ hδβ
  have h2 := Zγ'_le_inter hS h15c hI2 hL hB hμ (hQ _ hμ0) (hW _ hμ0) hδ' hδ'β
  have h3 : Zv γ' ≤ Zv l :=
    (le_inf h1 h2).trans (hF.inter β l (g • l) δ δ' hβ hl.1 hμ hμl hZμ
      (Std.mem_nbrs_symm.mpr hδ) hδβ (Std.mem_nbrs_symm.mpr hδ') hδ'β)
  have h4 : Zv γ' ≤ Zv β := by
    intro x hx
    refine mem_Zv_of_cent hS hL hl.1 hl.2 (h3 hx) fun a ha => ?_
    exact Vα'_comm_Vγ' hS hL hB a ha x (Std.Zv_le_Vn_S5 hS (vtype_γ' hL hB) hx)
  have h5 : Zv γ' = Zv β := by
    refine Subgroup.eq_of_le_of_card_ge h4 ?_
    rw [hS.cardZ5 β hβ, hS.cardZ5 γ' (vtype_γ' hL hB)]
  apply hL.2
  rw [← h5]
  exact (Zγ'_le_Zm hS hL hB).trans (Zm_le_Vα' hB)

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB9

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_eq_of_decomp {Z O N : Subgroup G} (hOZ : O ≤ Z)
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hdec : ∀ z ∈ Z, ∃ o ∈ O, o⁻¹ * z ∈ N) :
    (Z ⊓ N).relIndex Z = (O ⊓ N).relIndex O := by
  set A : Subgroup ↥Z := (Z ⊓ N).subgroupOf Z with hAdef
  set B : Subgroup ↥Z := O.subgroupOf Z with hBdef
  have : A.Normal := ⟨fun x hx g => by
    have : (g : ↥Z) * x * g⁻¹ = x := by
      apply Subtype.ext
      have := hcomm (g : G) g.2 (x : G) x.2
      show (g : G) * (x : G) * (g : G)⁻¹ = x
      rw [this]; group
    rw [this]; exact hx⟩
  have hsup : B ⊔ A = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨o, ho, hc⟩ := hdec z z.2
    have hoZ : o ∈ Z := hOZ ho
    have hcZ : o⁻¹ * (z : G) ∈ Z := Z.mul_mem (Z.inv_mem hoZ) z.2
    have e : z = (⟨o, hoZ⟩ : ↥Z) * ⟨o⁻¹ * (z : G), hcZ⟩ := by
      apply Subtype.ext; simp
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact ho
    · exact ⟨hcZ, hc⟩
  have h1 := Subgroup.relIndex_sup_right (H := B) (K := A)
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : A.relIndex B = (Z ⊓ N).relIndex O := by
    rw [hAdef, hBdef, Subgroup.relIndex_subgroupOf hOZ]
  have e : (Z ⊓ N) ⊓ O = O ⊓ N := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hOZ h.1, h.2⟩, h.1⟩⟩
  calc (Z ⊓ N).relIndex Z = A.index := rfl
    _ = (Z ⊓ N).relIndex O := h1.trans h2
    _ = ((Z ⊓ N) ⊓ O).relIndex O := (Subgroup.inf_relIndex_right _ _).symm
    _ = (O ⊓ N).relIndex O := by rw [e]

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem centerOf_le_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) {j : Geo H M}
    (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) : centerOf (stab δ) ≤ Qv j := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have hZc : centerOf (stab δ) ≤ Qv μ :=
    (centerOf_stab_le_Qv hA δ).trans h.hQδ
  rw [← h.centralizer_Zv hA hj hδ hjδ]
  refine le_inf (hZc.trans (Qv_le_stab_of_mem_nbrs hA hj)) fun x hx => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hy' : y ∈ stab δ := (h.Zv_le_Qv_mu hj).trans (Qv_le_stab_of_mem_nbrs hA hδ) hy
  exact Subgroup.mem_centralizer_iff.mp hx.2 y hy'

theorem relIndex_Zv_eq_Oo (hA : F53Amalgam H M S) (h : ConfR δ μ U) {j : Geo H M}
    (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) :
    (Zv δ ⊓ Qv j).relIndex (Zv δ) = (OoOf δ ⊓ Qv j).relIndex (OoOf δ) := by
  refine relIndex_eq_of_decomp (h.Oo_le_Zv hA) (fun x hx y hy =>
    isElemAbelian_comm (isElemAbelian_Zv hA δ) hx hy) fun z hz => ?_
  have hOS : OoOf δ ≤ stab δ := by
    obtain ⟨c, V₀, -, -, -, -, -, -, -, -, h9, -⟩ := h.A3 hA
    exact h9.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  obtain ⟨o, ho, c, hc, rfl⟩ := mem_sup_of_commute
    (fun o ho c (hc : c ∈ centerOf (stab δ)) =>
      Subgroup.mem_centralizer_iff.mp hc.2 o (hOS ho))
    (h.Zv_le_Oo_sup hA hz)
  refine ⟨o, ho, ?_⟩
  have : o⁻¹ * (o * c) = c := by group
  rw [this]
  exact h.centerOf_le_Qv hA hj hjδ hc

end ConfR

end CFSG.Quasithin.F53

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB11
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB10

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def OrthFrame.img {δ μ : Geo H M} (fr : OrthFrame δ μ) (X : Subgroup G) :
    Subgroup (Perm (Fin 5)) := (X.subgroupOf (stab δ)).map fr.Ψ

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem img_le_That (fr : OrthFrame δ μ) {X : Subgroup G} (hX : X ≤ Qv μ) :
    fr.img X ≤ S5That := by
  rw [← fr.mapP]
  exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hX (Subgroup.mem_subgroupOf.mp hx)))

theorem card_img (fr : OrthFrame δ μ) {X : Subgroup G} (hXS : X ≤ stab δ) :
    Nat.card (fr.img X) = (Qv δ ⊓ X).relIndex X := by
  have h1 := Subgroup.relIndex_ker (K := X.subgroupOf (stab δ)) fr.Ψ
  have hker : fr.Ψ.ker = (Qv δ).subgroupOf (stab δ) := by
    ext k; rw [MonoidHom.mem_ker, fr.ker, Subgroup.mem_subgroupOf]
  rw [hker, Subgroup.relIndex_subgroupOf hXS] at h1
  unfold OrthFrame.img
  rw [← h1, Subgroup.inf_relIndex_right]

theorem Oo_inf_Qv_eq_map (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {j : Geo H M} (hj : j ∈ nbrs μ) :
    OoOf δ ⊓ Qv j = (fixW orth (fr.img (OoOf j))).map fr.γ := by
  have hOj : OoOf j ≤ stab δ :=
    (h.Oo_le_Qv_mu_at hA hj).trans (Qv_le_stab_of_mem_nbrs hA (h.sig.adj.symm : δ ∈ nbrs μ))
  rw [h.Oo_inf_Qv_eq hA (h.sig.adj.symm : δ ∈ nbrs μ) hj]
  ext x
  constructor
  · rintro ⟨hxO, hxc⟩
    obtain ⟨w, rfl⟩ := fr.surj x hxO
    refine ⟨w, fun b hb => ?_, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hb
    apply fr.inj
    rw [fr.equiv]
    have h2 := Subgroup.mem_centralizer_iff.mp hxc (k : G) (Subgroup.mem_subgroupOf.mp hk)
    calc (k : G) * fr.γ w * (k : G)⁻¹ = fr.γ w * (k : G) * (k : G)⁻¹ := by rw [h2]
      _ = fr.γ w := by group
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fr.mem w, Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩
    have hb : fr.Ψ ⟨o, hOj ho⟩ ∈ fr.img (OoOf j) := ⟨⟨o, hOj ho⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩
    have := fr.equiv ⟨o, hOj ho⟩ w
    rw [hw _ hb] at this
    calc o * fr.γ w = (o * fr.γ w * o⁻¹) * o := by group
      _ = fr.γ w * o := by rw [← this]

theorem index_fixW (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {j : Geo H M} (hj : j ∈ nbrs μ) :
    (fixW orth (fr.img (OoOf j))).index = (OoOf δ ⊓ Qv j).relIndex (OoOf δ) := by
  rw [h.Oo_inf_Qv_eq_map hA fr hj]
  have htop : (⊤ : Subgroup orth.W).map fr.γ = OoOf δ := by
    ext x
    constructor
    · rintro ⟨w, -, rfl⟩; exact fr.mem w
    · intro hx
      obtain ⟨w, rfl⟩ := fr.surj x hx
      exact ⟨w, trivial, rfl⟩
  conv_rhs => rw [← htop]
  rw [Subgroup.relIndex_map_map_of_injective (f := fr.γ) (fixW orth (fr.img (OoOf j))) ⊤ fr.inj,
    Subgroup.relIndex_top_right]

theorem Oo_le_stab_at (hA : F53Amalgam H M S) (h : ConfR δ μ U) {j : Geo H M} (hj : j ∈ nbrs μ) :
    OoOf j ≤ stab δ :=
  (h.Oo_le_Qv_mu_at hA hj).trans (Qv_le_stab_of_mem_nbrs hA (h.sig.adj.symm : δ ∈ nbrs μ))

theorem relIndex_Oo_eq (hA : F53Amalgam H M S) (h : ConfR δ μ U) {j : Geo H M}
    (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) :
    (OoOf δ ⊓ Qv j).relIndex (OoOf δ) = (OoOf j ⊓ Qv δ).relIndex (OoOf j) := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  obtain ⟨Uj, hj'⟩ := h.exists_at hj
  rw [← h.relIndex_Zv_eq_Oo hA hj hjδ, ← hj'.relIndex_Zv_eq_Oo hA hδ (Ne.symm hjδ)]
  exact h.a_eq hA hδ hj (Ne.symm hjδ)

theorem not_Oo_le_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) {j : Geo H M}
    (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) : ¬ OoOf j ≤ Qv δ := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  obtain ⟨Uj, hj'⟩ := h.exists_at hj
  intro hle
  refine h.not_Zv_le_Qv hA hj hδ hjδ ((hj'.Zv_le_Oo_sup hA).trans (sup_le hle ?_))
  exact hj'.centerOf_le_Qv hA hδ (Ne.symm hjδ)

theorem classify (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ) {j : Geo H M}
    (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) :
    fr.img (OoOf j) = Subgroup.zpowers (swap 0 2) ∨ fr.img (OoOf j) = Subgroup.zpowers (swap 1 3) ∨
      fr.img (OoOf j) = S5That := by
  have hcard := card_img fr (h.Oo_le_stab_at hA hj)
  have hidx := h.index_fixW hA fr hj
  have hB0 : fr.img (OoOf j) ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (fr.img (OoOf j)) = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hcard] at h1
    have h2 : OoOf j ≤ Qv δ ⊓ OoOf j := Subgroup.relIndex_eq_one.mp h1
    exact h.not_Oo_le_Qv hA hj hjδ (h2.trans inf_le_left)
  refine F53Mod.offender_That (img_le_That fr (h.Oo_le_Qv_mu_at hA hj)) hB0 ?_
  rw [hidx, hcard, inf_comm (Qv δ) (OoOf j)]
  exact h.relIndex_Oo_eq hA hj hjδ

end ConfR

end CFSG.Quasithin.F53

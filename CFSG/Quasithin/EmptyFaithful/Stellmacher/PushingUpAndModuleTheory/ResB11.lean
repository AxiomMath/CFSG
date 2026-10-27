module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB5

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem exists_at (h : ConfR δ μ U) {j : Geo H M} (hj : j ∈ nbrs μ) : ∃ U' : Subgroup G, ConfR j μ U' := by
  obtain ⟨g, hg, hgδ⟩ := stab_transitive_on_nbrs (h.sig.adj.symm : δ ∈ nbrs μ) hj
  have := h.smul_stab (g := (g : G)) hg
  have e : toGeoElt μ hg = g := rfl
  rw [e, hgδ] at this
  exact ⟨_, this⟩

theorem Oo_le_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) : OoOf δ ≤ Qv δ := by
  obtain ⟨c, V₀, -, -, -, -, -, -, -, -, h9, -⟩ := h.A3 hA
  exact h9

theorem Oo_le_Qv_mu (hA : F53Amalgam H M S) (h : ConfR δ μ U) : OoOf δ ≤ Qv μ :=
  (h.Oo_le_Qv hA).trans h.hQδ

theorem frame_mem_Qv_iff (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {x : G} (hx : x ∈ stab δ) : x ∈ Qv δ ↔ ∀ o ∈ OoOf δ, x * o = o * x := by
  constructor
  · intro hxQ o ho
    obtain ⟨c, V₀, -, -, -, -, -, -, -, -, -, -, hcentral, -⟩ := h.A3 hA
    exact (hcentral o ho x hxQ).symm
  · intro hc
    rw [← fr.ker ⟨x, hx⟩]
    have hf : fr.Ψ ⟨x, hx⟩ = 1 := by
      apply (injective_iff_map_eq_one orth.act).mp orth_faithful
      ext w
      apply fr.inj
      have := fr.equiv ⟨x, hx⟩ w
      rw [this]
      have h2 := hc (fr.γ w) (fr.mem w)
      calc x * fr.γ w * x⁻¹ = fr.γ w * x * x⁻¹ := by rw [h2]
        _ = fr.γ w := by group
    exact hf

theorem Oo_le_Qv_mu_at (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i : Geo H M}
    (hi : i ∈ nbrs μ) : OoOf i ≤ Qv μ := by
  obtain ⟨U', h'⟩ := h.exists_at hi
  exact h'.Oo_le_Qv_mu hA

theorem Oo_inf_Qv_eq (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) :
    OoOf i ⊓ Qv j = OoOf i ⊓ Subgroup.centralizer (OoOf j : Set G) := by
  obtain ⟨U', hj'⟩ := h.exists_at hj
  obtain ⟨fr⟩ := hj'.exists_frame hA
  obtain ⟨c, V₀, -, -, -, -, -, -, -, -, -, -, hcentral, -⟩ := hj'.A3 hA
  ext x
  constructor
  · rintro ⟨hxi, hxj⟩
    exact ⟨hxi, Subgroup.mem_centralizer_iff.mpr fun o ho => hcentral o ho x hxj⟩
  · rintro ⟨hxi, hxc⟩
    have hxs : x ∈ stab j := Qv_le_stab_of_mem_nbrs hA hj (h.Oo_le_Qv_mu_at hA hi hxi)
    refine ⟨hxi, (frame_mem_Qv_iff hA hj' fr hxs).mpr fun o ho => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hxc o ho).symm

end ConfR

end CFSG.Quasithin.F53

module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

theorem Zv_γ₀_eq (hA : F53Amalgam H M S) : Zv (γ₀ (H ⊔ M) H M) = VZ S H := by
  have hST : IsSylowTwoOf S (stab (γ₀ (H ⊔ M) H M)) := by
    rw [stab_γ₀ hA.amalgam.le₁]; exact hA.amalgam.sylow₁
  have := Zv_eq_conjClosure hST
  rwa [stab_γ₀ hA.amalgam.le₁] at this

theorem Zv_γ₁_eq (hA : F53Amalgam H M S) : Zv (γ₁ (H ⊔ M) H M) = VZ S M := by
  have hST : IsSylowTwoOf S (stab (γ₁ (H ⊔ M) H M)) := by
    rw [stab_γ₁ hA.amalgam.le₂]; exact hA.amalgam.sylow₂
  have := Zv_eq_conjClosure hST
  rwa [stab_γ₁ hA.amalgam.le₂] at this

theorem Qv_γ₁_eq (hA : F53Amalgam H M S) : Qv (γ₁ (H ⊔ M) H M) = pCoreOf 2 M := by
  unfold Qv; rw [stab_γ₁ hA.amalgam.le₂]

omit [Finite G] in
theorem bAt_γ₀_eq {δ : Geo H M} (hδ : vtype δ = false) :
    bAt (γ₀ (H ⊔ M) H M) = bAt δ :=
  bAt_eq_of_vtype_eq (by rw [hδ]; rfl)

omit [Finite G] in
theorem bAt_γ₁_eq {δ : Geo H M} (hδ : vtype δ = true) :
    bAt (γ₁ (H ⊔ M) H M) = bAt δ :=
  bAt_eq_of_vtype_eq (by rw [hδ]; rfl)

theorem not_Zv_le_Qv_of_nbr (hA : F53Amalgam H M S) {δ μ ν : Geo H M} (hμ : μ ∈ nbrs δ)
    (hν : ν ∈ nbrs δ) (h : ¬ Zv δ ≤ Qv μ) : ¬ Zv δ ≤ Qv ν := by
  obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs hμ hν
  have hn : (g : G) ∈ Subgroup.normalizer (Zv δ : Set G) := stab_le_normalizer_Zv hA δ hg
  have hZ : conjSub (g : G) (Zv δ) = Zv δ := conjSub_eq_of_mem_normalizer hn
  intro hle
  apply h
  have hle' : conjSub (g : G) (Zv δ) ≤ conjSub (g : G) (Qv μ) := by
    rw [hZ, ← Qv_smul, hgμ]; exact hle
  exact (conjSub_le_conjSub_iff' _).mp hle'

theorem not_Zv_γ₀_le_Qv_γ₁ (hA : F53Amalgam H M S) (h1 : bAt (γ₀ (H ⊔ M) H M) = 1) :
    ¬ VZ S H ≤ pCoreOf 2 M := by
  obtain ⟨μ, hd, hn⟩ := bAt_spec hA (γ₀ (H ⊔ M) H M)
  have hμ : μ ∈ nbrs (γ₀ (H ⊔ M) H M) := by
    show (graph (H ⊔ M) H M).Adj _ μ
    rw [← CosetGeom.dist_eq_one_iff_adj]; rw [hd, h1]
  have hγ : γ₁ (H ⊔ M) H M ∈ nbrs (γ₀ (H ⊔ M) H M) := adj_γ₀_γ₁
  have := not_Zv_le_Qv_of_nbr hA hμ hγ hn
  rwa [Zv_γ₀_eq hA, Qv_γ₁_eq hA] at this

theorem zv_central_γ₁ (hA : F53Amalgam H M S) :
    Zv (γ₁ (H ⊔ M) H M) ≤ centerOf (stab (γ₁ (H ⊔ M) H M)) ↔ VZ S M ≤ centerOf M := by
  rw [Zv_γ₁_eq hA, stab_γ₁ hA.amalgam.le₂]

end F53

end CFSG.Quasithin

module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

structure Amal (H M B S : Subgroup G) : Prop where
  amalgam : AmalgamHyp (H ⊔ M) H M S
  charTwo_right : CharTwo M
  inf_eq : H ⊓ M = B
  relIndex_left : B.relIndex H = 5
  relIndex_right : B.relIndex M = 5

theorem Amal.of_frame {L1 L2 S D X : Subgroup G} (F : FA5.Frame L1 L2 S D X) :
    Amal (FA5.P1 L1 L2 S) (FA5.P2 L1 L2 S) (bigB L1 L2 S) S where
  amalgam := by
    have h := F112W.amalgamHyp_beta F.pair.hyp
    rwa [← F1.parabolic_sup_parabolic L1 L2 S] at h
  charTwo_right := F.charTwo_P2
  inf_eq := F.P1_inf_P2
  relIndex_left := F.pair.relIndex_bigB_left
  relIndex_right := F.pair.relIndex_bigB_right

namespace Amal

variable {H M B S : Subgroup G} (hA : Amal H M B S)
include hA

theorem edge_conj {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    ∃ g : ↥(H ⊔ M),
      ((stab δ = conjSub (g : G) H ∧ stab μ = conjSub (g : G) M) ∨
        (stab δ = conjSub (g : G) M ∧ stab μ = conjSub (g : G) H)) ∧
      stab δ ⊓ stab μ = conjSub (g : G) B := by
  have h₁ := hA.amalgam.le₁
  have h₂ := hA.amalgam.le₂
  obtain ⟨g, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ := exists_smul_edge
    (show (graph (H ⊔ M) H M).Adj δ μ from h)
  · refine ⟨g, Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [← h0, stab_smul, stab_γ₀ h₁]
    · rw [← h1, stab_smul, stab_γ₁ h₂]
    · rw [← h0, ← h1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, ← conjSub_inf, hA.inf_eq]
  · refine ⟨g, Or.inr ⟨?_, ?_⟩, ?_⟩
    · rw [← h1, stab_smul, stab_γ₁ h₂]
    · rw [← h0, stab_smul, stab_γ₀ h₁]
    · rw [← h0, ← h1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, inf_comm, ← conjSub_inf,
        hA.inf_eq]

theorem exists_common_sylow {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    ∃ T : Subgroup G, IsSylowTwoOf T (stab δ) ∧ IsSylowTwoOf T (stab μ) ∧
      T ≤ stab δ ⊓ stab μ := by
  obtain ⟨g, hg, he⟩ := hA.edge_conj h
  have hT : conjSub (g : G) S ≤ conjSub (g : G) B := conjSub_mono _ (hA.inf_eq ▸ hA.amalgam.T_le)
  refine ⟨conjSub (g : G) S, ?_, ?_, he ▸ hT⟩
  · rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₁ _
    · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₂ _
  · rcases hg with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₂ _
    · rw [h1]; exact isSylowTwoOf_conj hA.amalgam.sylow₁ _

theorem charTwo_stab (δ : Geo H M) : CharTwo (stab δ) := by
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, stab_smul, stab_γ₀ hA.amalgam.le₁]
    exact F53.charTwo_conjSub _ hA.amalgam.charTwo
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, stab_smul, stab_γ₁ hA.amalgam.le₂]
    exact F53.charTwo_conjSub _ hA.charTwo_right

theorem card_nbrs_false {δ : Geo H M} (hv : vtype δ = false) : Nat.card (nbrs δ) = 5 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
  have hμ : g • γ₁ (H ⊔ M) H M ∈ nbrs (g • γ₀ (H ⊔ M) H M) := (smul_adj g).mpr adj_γ₀_γ₁
  rw [CosetGeom.card_nbrs_eq_relIndex_geom hμ, stab_smul, stab_smul, stab_γ₀ hA.amalgam.le₁,
    stab_γ₁ hA.amalgam.le₂, ← conjSub_inf, hA.inf_eq, F53.relIndex_conjSub]
  exact hA.relIndex_left

theorem card_nbrs_true {δ : Geo H M} (hv : vtype δ = true) : Nat.card (nbrs δ) = 5 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  have hμ : g • γ₀ (H ⊔ M) H M ∈ nbrs (g • γ₁ (H ⊔ M) H M) :=
    (smul_adj g).mpr adj_γ₀_γ₁.symm
  rw [CosetGeom.card_nbrs_eq_relIndex_geom hμ, stab_smul, stab_smul, stab_γ₀ hA.amalgam.le₁,
    stab_γ₁ hA.amalgam.le₂, inf_comm, ← conjSub_inf, hA.inf_eq, F53.relIndex_conjSub]
  exact hA.relIndex_right

theorem card_nbrs (δ : Geo H M) : Nat.card (nbrs δ) = 5 := by
  cases hv : vtype δ
  · exact hA.card_nbrs_false hv
  · exact hA.card_nbrs_true hv

theorem Qv_le_stab_of_mem_nbrs {δ μ : Geo H M} (h : μ ∈ nbrs δ) : Qv δ ≤ stab μ := by
  have h1 := pCoreOf_stab_le_ballStab_one hA.amalgam δ
  exact h1.trans (ballStab_le_stab_of_dist_le
    (dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj δ μ from h)).le)

end Amal

end CFSG.Quasithin.Kleidman.F204

module

public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase1

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

namespace Amal

variable {H M B S : Subgroup G} (hA : Amal H M B S)
include hA

theorem exists_sylow_stab (δ : Geo H M) :
    ∃ T : Subgroup G, IsSylowTwoOf T (stab δ) ∧
      ∃ μ : Geo H M, μ ∈ nbrs δ ∧ IsSylowTwoOf T (stab μ) := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  obtain ⟨T, hT1, hT2, -⟩ := hA.exists_common_sylow (show μ ∈ nbrs δ from hμ)
  exact ⟨T, hT1, μ, hμ, hT2⟩

theorem stab_le_normalizer_Zv (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Zv δ : Set G) := by
  obtain ⟨T, hT, -⟩ := hA.exists_sylow_stab δ
  rw [Zv_eq_conjClosure hT]
  exact le_normalizer_conjClosure _ _

theorem Zv_le_centerOf_Qv (δ : Geo H M) : Zv δ ≤ centerOf (Qv δ) := by
  obtain ⟨T, hT, -⟩ := hA.exists_sylow_stab δ
  rw [Zv_eq_conjClosure hT]
  exact (conjClosure_le_centerOf_pCoreOf_of_sylowIn hT.1 hT.2.1 hT.2.2 (hA.charTwo_stab δ)
    (Z := quasithinOmegaOneCenter _) le_rfl).1

theorem isElemAbelian_Zv (δ : Geo H M) : IsElemAbelian 2 (Zv δ) := by
  obtain ⟨T, hT, -⟩ := hA.exists_sylow_stab δ
  rw [Zv_eq_conjClosure hT]
  exact (conjClosure_le_centerOf_pCoreOf_of_sylowIn hT.1 hT.2.1 hT.2.2 (hA.charTwo_stab δ)
    (Z := quasithinOmegaOneCenter _) le_rfl).2

theorem Zv_le_Qv (δ : Geo H M) : Zv δ ≤ Qv δ :=
  (hA.Zv_le_centerOf_Qv δ).trans inf_le_left

theorem omegaOneCenter_le_Zv {δ μ : Geo H M} {T : Subgroup G}
    (hT1 : IsSylowTwoOf T (stab δ)) (hT2 : IsSylowTwoOf T (stab μ)) :
    quasithinOmegaOneCenter (stab δ) ≤ quasithinOmegaOneCenter T ∧
      quasithinOmegaOneCenter T ≤ Zv δ ∧ quasithinOmegaOneCenter T ≤ Zv μ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold quasithinOmegaOneCenter
    refine Subgroup.closure_mono ?_
    rintro z ⟨hz, hz2⟩
    have hzQ : z ∈ pCoreOf 2 (stab δ) := by
      refine hA.charTwo_stab δ ⟨hz.1, ?_⟩
      exact Subgroup.centralizer_le (pCoreOf_le 2 (stab δ)) hz.2
    have hzT : z ∈ T := isSylowTwoOf_pCoreOf_le hT1 hzQ
    refine ⟨⟨hzT, ?_⟩, hz2⟩
    exact Subgroup.centralizer_le hT1.1 hz.2
  · exact le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab δ)) =>
      quasithinOmegaOneCenter T) T hT1 le_rfl
  · exact le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab μ)) =>
      quasithinOmegaOneCenter T) T hT2 le_rfl

theorem stab_ne_bot (δ : Geo H M) : stab δ ≠ ⊥ := by
  have hH : H ≠ ⊥ := by
    intro h
    have h1 : B.relIndex H = 1 := Subgroup.relIndex_eq_one.mpr (h ▸ bot_le)
    have := hA.relIndex_left
    omega
  have hM : M ≠ ⊥ := by
    intro h
    have h1 : B.relIndex M = 1 := Subgroup.relIndex_eq_one.mpr (h ▸ bot_le)
    have := hA.relIndex_right
    omega
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, stab_smul, stab_γ₀ hA.amalgam.le₁]
    exact fun h => hH ((conjSub_eq_bot_iff _).mp h)
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, stab_smul, stab_γ₁ hA.amalgam.le₂]
    exact fun h => hM ((conjSub_eq_bot_iff _).mp h)

theorem Qv_ne_bot (δ : Geo H M) : Qv δ ≠ ⊥ := by
  intro h
  apply hA.stab_ne_bot δ
  have h1 : stab δ ⊓ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) ≤ pCoreOf 2 (stab δ) :=
    hA.charTwo_stab δ
  have h2 : pCoreOf 2 (stab δ) = ⊥ := h
  rw [h2] at h1
  rw [eq_bot_iff]
  intro x hx
  have hc : x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Subgroup.mem_bot.mp hg]
    simp
  exact h1 ⟨hx, hc⟩

theorem Zv_ne_bot (δ : Geo H M) : Zv δ ≠ ⊥ := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  obtain ⟨T, hT1, hT2, -⟩ := hA.exists_common_sylow (show μ ∈ nbrs δ from hμ)
  have hTne : T ≠ ⊥ := by
    intro h
    apply hA.Qv_ne_bot δ
    exact le_bot_iff.mp (h ▸ isSylowTwoOf_pCoreOf_le hT1)
  have h1 := quasithinOmegaOneCenter_ne_bot hT1.2.1 hTne
  intro h
  exact h1 (le_bot_iff.mp ((hA.omegaOneCenter_le_Zv hT1 hT2).2.1.trans h.le))

theorem exists_not_le_Qv (δ : Geo H M) : ∃ μ : Geo H M, ¬ Zv δ ≤ Qv μ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, -, hn⟩ := exists_ballStab_eq_bot hA.amalgam
  apply hA.Zv_ne_bot δ
  have : Zv δ ≤ ballStab n δ := fun x hx =>
    mem_ballStab.mpr fun μ _ => (pCoreOf_le 2 (stab μ)) (hcon μ hx)
  rw [hn] at this
  exact le_bot_iff.mp this

theorem bAt_spec (δ : Geo H M) : ∃ μ : Geo H M, dist δ μ = bAt δ ∧ ¬ Zv δ ≤ Qv μ := by
  have hne : {n : ℕ | ∃ μ : Geo H M, dist δ μ = n ∧ ¬ Zv δ ≤ Qv μ}.Nonempty := by
    obtain ⟨μ, hμ⟩ := hA.exists_not_le_Qv δ
    exact ⟨_, μ, rfl, hμ⟩
  exact Nat.sInf_mem hne

theorem bAt_pos (δ : Geo H M) : 1 ≤ bAt δ := by
  by_contra h
  have h0 : bAt δ = 0 := by omega
  obtain ⟨μ, hμ, hn⟩ := hA.bAt_spec δ
  rw [h0] at hμ
  have : δ = μ := (dist_eq_zero_iff hA.amalgam.gen).mp hμ
  subst this
  exact hn (hA.Zv_le_Qv δ)

theorem Zv_le_stab_of_dist_le {δ μ : Geo H M} (h : dist δ μ ≤ bAt δ) : Zv δ ≤ stab μ := by
  rcases h.lt_or_eq with hlt | heq
  · exact (Zv_le_Qv_of_dist_lt hlt).trans (pCoreOf_le 2 _)
  · have hb := hA.bAt_pos δ
    obtain ⟨μ', hμ', hd⟩ := exists_adj_dist_eq hA.amalgam.gen (α := δ) (δ := μ)
      (d := bAt δ - 1) (by omega)
    have h1 : Zv δ ≤ Qv μ' := Zv_le_Qv_of_dist_lt (by omega)
    exact h1.trans (hA.Qv_le_stab_of_mem_nbrs (show μ ∈ nbrs μ' from hμ'.symm))

theorem exists_bAt_eq_bMin : ∃ δ : Geo H M, bAt δ = bMin H M := by
  have hne : (Set.range (bAt (H := H) (M := M))).Nonempty := ⟨_, γ₀ (H ⊔ M) H M, rfl⟩
  exact Nat.sInf_mem hne

theorem exists_critData {α β : Geo H M} (hα : bAt α = bMin H M)
    (hαβ : (graph (H ⊔ M) H M).Adj α β) : ∃ α' : Geo H M, IsCritData α β α' := by
  obtain ⟨μ, hd, hn⟩ := hA.bAt_spec α
  have hb := hA.bAt_pos α
  obtain ⟨β₀, hβ₀, hdβ₀⟩ := exists_adj_dist_eq hA.amalgam.gen (α := μ) (δ := α)
    (d := bAt α - 1) (by rw [CosetGeom.dist_comm]; omega)
  obtain ⟨g, hgα, hgβ⟩ := exists_stab_smul_eq hβ₀ hαβ
  refine ⟨g • μ, hαβ, hα, ?_, ?_, ?_⟩
  · have e : dist α (g • μ) = dist α μ := by
      conv_lhs => rw [← hgα]
      exact CosetGeom.dist_smul g α μ
    rw [e, hd, hα]
  · have e : dist β (g • μ) = dist β₀ μ := by
      conv_lhs => rw [← hgβ]
      exact CosetGeom.dist_smul g β₀ μ
    rw [e, CosetGeom.dist_comm, hdβ₀]
    omega
  · intro hle
    apply hn
    have h1 : Zv α = conjSub (g : G) (Zv α) := by
      conv_lhs => rw [← hgα]
      exact Zv_smul g α
    have hle' : conjSub (g : G) (Zv α) ≤ conjSub (g : G) (Qv μ) := by
      rw [← h1]; rwa [Qv_smul] at hle
    exact (conjSub_le_conjSub_iff' _).mp hle'

end Amal

end CFSG.Quasithin.Kleidman.F204

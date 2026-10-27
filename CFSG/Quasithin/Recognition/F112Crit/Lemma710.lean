module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma73
public import CFSG.Quasithin.EmptyFaithful.SzF53BasGeo

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem Vv_le_Wv {μ δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs μ) : Vv Z δ ≤ Wv Z μ :=
  le_iSup₂_of_le δ hδ le_rfl

variable [Finite G]

theorem stab_le_normalizer_Wv (hc : CritAmalgam G₀ G₁ G₂ T Z) (μ : CosetGeom G₀ G₁ G₂) :
    stab μ ≤ Subgroup.normalizer (Wv Z μ : Set G) := by
  have key : ∀ k : ↥G₀, k • μ = μ → conjSub (k : G) (Wv Z μ) ≤ Wv Z μ := by
    intro k hk
    show conjSub (k : G) (⨆ δ : CosetGeom G₀ G₁ G₂, ⨆ (_ : δ ∈ nbrs μ), Vv Z δ) ≤ Wv Z μ
    rw [conjSub_iSup]
    refine iSup_le fun δ => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hδ => ?_
    rw [← CosetGeom.Vv_smul hc.normalizes k δ]
    refine Vv_le_Wv ?_
    have h' := (CosetGeom.smul_adj k).mpr (show (graph G₀ G₁ G₂).Adj μ δ from hδ)
    rw [hk] at h'
    exact h'
  intro g hg
  obtain ⟨h, hh⟩ := CosetGeom.mem_stab.mp hg
  have hinv : (⟨g, h⟩ : ↥G₀)⁻¹ • μ = μ := by
    calc (⟨g, h⟩ : ↥G₀)⁻¹ • μ = (⟨g, h⟩ : ↥G₀)⁻¹ • (⟨g, h⟩ : ↥G₀) • μ := by rw [hh]
      _ = μ := inv_smul_smul _ _
  exact F7.mem_normalizer_of_conj_le (key (⟨g, h⟩ : ↥G₀) hh) (key (⟨g, h⟩ : ↥G₀)⁻¹ hinv)

theorem isElemAbelian_Wv (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : 4 ≤ critB G₀ G₁ G₂ Z)
    {μ : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) : IsElemAbelian 2 (Wv Z μ) :=
  (lemma65_2 hc hb hμ).2

theorem Wv_le_stab (hc : CritAmalgam G₀ G₁ G₂ T Z) {μ ν : CosetGeom G₀ G₁ G₂}
    (hμ : vtype μ = false) (hd1 : 1 ≤ CosetGeom.dist ν μ)
    (hd : CosetGeom.dist ν μ + 2 ≤ critB G₀ G₁ G₂ Z) : Wv Z μ ≤ stab ν := by
  have hG := hc.amalgam.gen
  obtain ⟨ν', hadj, hdist⟩ := CosetGeom.exists_adj_dist_eq hG
    (α := μ) (δ := ν) (d := CosetGeom.dist ν μ - 1) (by rw [CosetGeom.dist_comm μ ν]; omega)
  have hνν' : CosetGeom.dist ν' ν ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr hadj.symm).le
  have hVδ : ∀ δ ∈ nbrs μ, Vv Z δ ≤ stab ν := by
    intro δ hδ
    have hδt : vtype δ = true := vtype_eq_true_of_mem_nbrs hμ hδ
    refine Vv_le_of_forall_mem_nbrs hδt fun γ hγ => ?_
    have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδt hγ
    have hμδ : μ ∈ nbrs δ := CosetGeom.mem_nbrs_symm hδ
    have h1 : CosetGeom.dist γ μ ≤ 2 := dist_le_two_of_mem_nbrs hc hγ hμδ
    have h2 := CosetGeom.dist_triangle hG γ μ ν'
    have hk : CosetGeom.dist γ ν' + 1 ≤ critB G₀ G₁ G₂ Z := by omega
    have hball : Vv Z γ ≤ ballStab 1 ν' :=
      (le_critB_iff_at hc hγt _).mp hk ν' (by omega)
    exact hball.trans (CosetGeom.ballStab_le_stab_of_dist_le hνν')
  exact iSup₂_le fun δ hδ => hVδ δ hδ

theorem not_le_centralizer_Wv (hc : CritAmalgam G₀ G₁ G₂ T Z) {μ : CosetGeom G₀ G₁ G₂}
    (hμ : vtype μ = false) {L : Subgroup G} (hL : L ≤ stab μ)
    (htrans : ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, ∃ g : ↥G₀, (g : G) ∈ L ∧ g • δ = δ') :
    ¬ L ≤ Subgroup.centralizer (Wv Z μ : Set G) := by
  intro hLc
  obtain ⟨δ₀, hδ₀⟩ := CosetGeom.exists_adj μ
  have hδ₀' : δ₀ ∈ nbrs μ := hδ₀
  have hδ₀t : vtype δ₀ = true := vtype_eq_true_of_mem_nbrs hμ hδ₀'
  have hconst : ∀ δ ∈ nbrs μ, Vv Z δ = Vv Z δ₀ := by
    intro δ hδ
    obtain ⟨g, hgL, hgδ⟩ := htrans δ₀ hδ₀' δ hδ
    have hcent : (g : G) ∈ Subgroup.centralizer (Vv Z δ₀ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (Vv_le_Wv hδ₀')) (hLc hgL)
    rw [← hgδ, CosetGeom.Vv_smul hc.normalizes g δ₀]
    exact F7.conjSub_eq_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer (Vv Z δ₀ : Set G) hcent)
  have hstabμ : stab μ ≤ Subgroup.normalizer (Vv Z δ₀ : Set G) := by
    intro g hg
    obtain ⟨h, hh⟩ := CosetGeom.mem_stab.mp hg
    apply CosetGeom.mem_normalizer_of_conjSub_eq
    have hδ' : (⟨g, h⟩ : ↥G₀) • δ₀ ∈ nbrs μ := by
      have h' := (CosetGeom.smul_adj (⟨g, h⟩ : ↥G₀)).mpr
        (show (graph G₀ G₁ G₂).Adj μ δ₀ from hδ₀)
      rw [hh] at h'
      exact h'
    exact (CosetGeom.Vv_smul hc.normalizes (⟨g, h⟩ : ↥G₀) δ₀).symm.trans (hconst _ hδ')
  have hG0 : G₀ ≤ Subgroup.normalizer (Vv Z δ₀ : Set G) := by
    have h : stab μ ⊔ stab δ₀ ≤ Subgroup.normalizer (Vv Z δ₀ : Set G) :=
      sup_le hstabμ (lemma63_2' hc hδ₀t).2.2.2.2
    rwa [stab_sup_stab_eq hc hμ hδ₀'] at h
  have hVG0 : Vv Z δ₀ ≤ G₀ :=
    ((lemma63_2' hc hδ₀t).2.1.trans (pCoreOf_le 2 _)).trans (CosetGeom.stab_le δ₀)
  have hV0 : Vv Z δ₀ ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 hVG0 hG0 (isPGroup_of_isElemAbelian (lemma63_2' hc hδ₀t).1)
  rw [hc.amalgam.o2_trivial] at hV0
  obtain ⟨γ, hγ⟩ := CosetGeom.exists_adj δ₀
  have hγ' : γ ∈ nbrs δ₀ := hγ
  have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδ₀t hγ'
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγt
  have h1 : conjSub (g : G) Z ≤ ⊥ := by
    rw [← Zv_smul_γ₀ hc g]
    exact (Vv_le_Vv_of_mem_nbrs hδ₀t hγ').trans hV0
  exact hc.ne_bot ((conjSub_eq_bot_iff (g : G)).mp (le_bot_iff.mp h1))

theorem card_nbrs_eq (hc : CritAmalgam G₀ G₁ G₂ T Z) {μ : CosetGeom G₀ G₁ G₂}
    (hμ : vtype μ = false) : Nat.card (nbrs μ) = Nat.card (nbrs (γ₀ G₀ G₁ G₂)) := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hμ
  have hset : nbrs (g • γ₀ G₀ G₁ G₂) = (fun x => g • x) '' nbrs (γ₀ G₀ G₁ G₂) := by
    ext δ
    constructor
    · intro hδ
      have hδ' : (graph G₀ G₁ G₂).Adj (g • γ₀ G₀ G₁ G₂) δ := hδ
      refine ⟨g⁻¹ • δ, ?_, smul_inv_smul g δ⟩
      have h' := (CosetGeom.smul_adj g⁻¹).mpr hδ'
      rw [inv_smul_smul] at h'
      exact h'
    · rintro ⟨x, hx, rfl⟩
      have hx' : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) x := hx
      exact (CosetGeom.smul_adj g).mpr hx'
  rw [hset]
  exact Nat.card_image_of_injective (MulAction.injective g) _

theorem odd_card_nbrs (hc : CritAmalgam G₀ G₁ G₂ T Z) {μ : CosetGeom G₀ G₁ G₂}
    (hμ : vtype μ = false) : Odd (Nat.card (nbrs μ)) := by
  rw [card_nbrs_eq hc hμ]
  have hadj : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := CosetGeom.adj_γ₀_γ₁
  have hmul : T.relIndex (G₁ ⊓ G₂) * (G₁ ⊓ G₂).relIndex G₁ = T.relIndex G₁ :=
    Subgroup.relIndex_mul_relIndex T (G₁ ⊓ G₂) G₁ hc.amalgam.T_le inf_le_left
  have hodd : ¬ 2 ∣ (G₁ ⊓ G₂).relIndex G₁ := fun h2 =>
    F7.isSylowTwoOf_odd_relIndex hc.amalgam.sylow₁ (dvd_trans h2 (Dvd.intro_left _ hmul))
  rw [CosetGeom.card_nbrs_eq_relIndex_geom hadj, hc.stab_γ₀_eq, hc.stab_γ₁_eq]
  exact Nat.odd_iff.mpr (by omega)

end CFSG.Quasithin.F112Crit

end

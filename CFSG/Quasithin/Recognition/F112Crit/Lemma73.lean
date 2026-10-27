module

public import CFSG.Quasithin.Recognition.F112Crit.LocalAction
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

theorem stab_le_centralizer_Vv (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) : stab γ ≤ Subgroup.centralizer (Vv Z γ : Set G) := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
  rw [Zv_smul_γ₀ hc, CosetGeom.stab_smul, hc.stab_γ₀_eq, conjSub_centralizer]
  exact conjSub_mono _ hc.centralizes

theorem stab_sup_stab_eq (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ δ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (hδ : δ ∈ nbrs γ) : stab γ ⊔ stab δ = G₀ := by
  obtain ⟨g, rfl, rfl⟩ := exists_edge_conj hγ hδ
  rw [CosetGeom.stab_smul, CosetGeom.stab_smul, hc.stab_γ₀_eq, hc.stab_γ₁_eq, ← conjSub_sup,
    ← hc.amalgam.gen]
  exact conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer g.2)

theorem lemma73_1 (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) :
    stab δ ⊓ Subgroup.centralizer (Vv Z δ : Set G) = ballStab 1 δ := by
  apply le_antisymm
  · rintro g ⟨hgδ, hgc⟩
    rw [CosetGeom.mem_ballStab]
    intro δ' hδ'
    rcases (CosetGeom.dist_le_one_iff hc.amalgam.gen).mp hδ' with rfl | hadj
    · exact hgδ
    · have hγt : vtype δ' = false := vtype_eq_false_of_mem_nbrs hδ hadj
      have h1 : g ∈ stab δ ⊓ Subgroup.centralizer (Vv Z δ' : Set G) :=
        ⟨hgδ, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          (Vv_le_Vv_of_mem_nbrs hδ hadj)) hgc⟩
      rw [lemma63_3 hc hγt (CosetGeom.mem_nbrs_symm hadj)] at h1
      exact h1.1
  · intro n hn
    refine ⟨CosetGeom.ballStab_le_stab 1 δ hn, ?_⟩
    have hV : Vv Z δ ≤ Subgroup.centralizer ({n} : Set G) := by
      refine Vv_le_of_forall_mem_nbrs hδ fun γ hγ => ?_
      have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδ hγ
      have hnγ : n ∈ stab γ :=
        CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hγ).le hn
      have hcent := stab_le_centralizer_Vv hc hγt hnγ
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.mp hcent) y hy).symm
    show n ∈ Subgroup.centralizer (Vv Z δ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hV hy
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this n rfl).symm

theorem ballStab_le_centralizer_Vv (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) : ballStab 1 δ ≤ Subgroup.centralizer (Vv Z δ : Set G) := by
  rw [← lemma73_1 hc hδ]; exact inf_le_right

theorem mem_ballStab_of_centralizes (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) {g : G} (hg : g ∈ stab δ)
    (hgc : g ∈ Subgroup.centralizer (Vv Z δ : Set G)) : g ∈ ballStab 1 δ := by
  rw [← lemma73_1 hc hδ]; exact ⟨hg, hgc⟩

theorem lemma73_2 (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true)
    {p : ℕ} {X : Subgroup G} (h : IsLocalReg δ p X) {γ γ' : CosetGeom G₀ G₁ G₂}
    (hγ : γ ∈ nbrs δ) (hγ' : γ' ∈ nbrs δ) (hne : γ ≠ γ') : Vv Z γ ≠ Vv Z γ' := by
  intro heq
  have hG := hc.amalgam.gen
  have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδ hγ
  have hγ't : vtype γ' = false := vtype_eq_false_of_mem_nbrs hδ hγ'
  have e1 := lemma63_3 hc hγt (CosetGeom.mem_nbrs_symm hγ)
  have e2 := lemma63_3 hc hγ't (CosetGeom.mem_nbrs_symm hγ')
  rw [heq] at e1
  have hM : stab γ ⊓ stab δ = stab γ' ⊓ stab δ := e1.symm.trans e2
  obtain ⟨a, haX, ha⟩ := h.trans γ hγ γ' hγ'
  have haδ : (a : G) ∈ stab δ := h.le_stab haX
  have haδ' : a • δ = δ := CosetGeom.smul_eq_of_mem_stab haδ
  have hconj : conjSub (a : G) (stab γ ⊓ stab δ) = stab γ ⊓ stab δ := by
    rw [conjSub_inf, ← CosetGeom.stab_smul, ← CosetGeom.stab_smul, ha, haδ']
    exact hM.symm
  have haM : (a : G) ∈ Subgroup.normalizer ((stab γ ⊓ stab δ : Subgroup G) : Set G) :=
    CosetGeom.mem_normalizer_of_conjSub_eq hconj
  have haN : (a : G) ∉ ballStab 1 δ := by
    intro haN
    have : a • γ = γ :=
      CosetGeom.smul_eq_of_mem_stab (IsLocalReg.ker_le_stab_of_mem_nbrs hγ haN)
    exact hne (this.symm.trans ha)
  have hNM : ballStab 1 δ ≤ stab γ ⊓ stab δ := by
    rw [inf_comm]; exact h.ker_le_stab_inf hγ
  have hXM : X ≤ Subgroup.normalizer ((stab γ ⊓ stab δ : Subgroup G) : Set G) :=
    (h.X_le_sup_zpowers haX haN).trans
      (sup_le (hNM.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).mpr haM))
  have hδM : stab δ ≤ Subgroup.normalizer ((stab γ ⊓ stab δ : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨x, hx, m, hm, rfl⟩ := h.exists_mul hG hg hγ
    refine Subgroup.mul_mem _ (hXM hx) (Subgroup.le_normalizer ?_)
    rw [inf_comm]; exact hm
  have hMN : stab γ ⊓ stab δ ≤ ballStab 1 δ := by
    intro m hm
    rw [CosetGeom.mem_ballStab]
    intro μ hμ
    rcases (CosetGeom.dist_le_one_iff hG).mp hμ with rfl | hμδ
    · exact hm.2
    · obtain ⟨g, hg, hgμ⟩ := CosetGeom.stab_transitive_on_nbrs hγ hμδ
      have hconj' : conjSub (g : G) (stab γ ⊓ stab δ) = stab γ ⊓ stab δ :=
        F7.conjSub_eq_of_mem_normalizer (hδM hg)
      have hsub : stab γ ⊓ stab δ ≤ stab μ := by
        rw [← hgμ, CosetGeom.stab_smul]
        calc stab γ ⊓ stab δ = conjSub (g : G) (stab γ ⊓ stab δ) := hconj'.symm
          _ ≤ conjSub (g : G) (stab γ) := conjSub_mono _ inf_le_left
      exact hsub hm
  obtain ⟨s, hs, hsN⟩ := h.exists_mem γ hγ
  exact hsN (hMN (by rw [inf_comm]; exact hs))

theorem lemma73_3 (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true)
    {p : ℕ} {X : Subgroup G} (h : IsLocalReg δ p X) {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ)
    {x : G} (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) {y : G} (hy : y ∈ Vv Z γ)
    (hxy : x * y = y * x) : y = 1 := by
  have hG := hc.amalgam.gen
  have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδ hγ
  have hyγ : ∀ s ∈ stab γ, s ∈ Subgroup.centralizer ({y} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact (Subgroup.mem_centralizer_iff.mp (stab_le_centralizer_Vv hc hγt hs) _ hy)
  have hxC : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact hxy.symm
  have hδC : stab δ ≤ Subgroup.centralizer ({y} : Set G) :=
    (h.le_sup_zpowers hG hγ hx hxN).trans
      (sup_le (inf_le_right.trans fun s hs => hyγ s hs) ((Subgroup.zpowers_le).mpr hxC))
  have hG0 : G₀ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [← stab_sup_stab_eq hc hγt (CosetGeom.mem_nbrs_symm hγ)]
    exact sup_le (fun s hs => hyγ s hs) hδC
  have hyG0 : y ∈ Subgroup.centralizer (G₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := (Subgroup.mem_centralizer_iff.mp (hG0 hg)) y rfl
    exact this.symm
  have hN : G₀ ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mpr ((Subgroup.zpowers_le).mpr hyG0)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hyδ : y ∈ Vv Z δ := Vv_le_Vv_of_mem_nbrs hδ hγ hy
  have hpg : IsPGroup 2 (Subgroup.zpowers y) :=
    (isPGroup_of_isElemAbelian (lemma63_2' hc hδ).1).to_le ((Subgroup.zpowers_le).mpr hyδ)
  have hyG : y ∈ G₀ :=
    CosetGeom.stab_le γ (pCoreOf_le 2 _ ((lemma63_1 hc hγt).1 hy))
  have hle : Subgroup.zpowers y ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 ((Subgroup.zpowers_le).mpr hyG) hN hpg
  rw [hc.amalgam.o2_trivial] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers y))

end CFSG.Quasithin.F112Crit

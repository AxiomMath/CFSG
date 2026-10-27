module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34BL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped Pointwise

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

@[expose] def Wtri (α : Geo H M) : Subgroup G := ⨆ ν ∈ nbrs α, Vn ν

omit [Finite G] in
theorem Vn_le_Wtri {α ν : Geo H M} (h : ν ∈ nbrs α) : Vn ν ≤ Wtri α :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs α) => Vn ν) ν h le_rfl

omit [Finite G] in
theorem Wtri_le {α : Geo H M} {K : Subgroup G} (h : ∀ ν ∈ nbrs α, Vn ν ≤ K) : Wtri α ≤ K :=
  iSup₂_le h

theorem Vn_le_Qv_of_dist (hA : F53Amalgam H M S) {ν x : Geo H M}
    (h : dist ν x + 1 < bMin H M) : Vn ν ≤ Qv x := by
  refine iSup₂_le fun μ hμ => ?_
  refine Zv_le_Qv_of_dist_lt ?_
  have h1 : dist ν μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have h3 := dist_triangle hA.amalgam.gen μ ν x
  rw [CosetGeom.dist_comm μ ν] at h3
  have h4 := bMin_le_bAt (H := H) (M := M) μ
  omega

theorem Wtri_le_Qv (hA : F53Amalgam H M S) (hb5 : 5 ≤ bMin H M) {α δ : Geo H M}
    (hδ : δ ∈ nbrs α) : Wtri α ≤ Qv α ⊓ Qv δ := by
  refine Wtri_le fun ν hν => le_inf (Vn_le_Qv_of_dist hA ?_) (Vn_le_Qv_of_dist hA ?_)
  · have h1 : dist α ν = 1 := dist_eq_one_iff_adj.mpr hν
    rw [CosetGeom.dist_comm] at h1
    omega
  · have h1 : dist α ν = 1 := dist_eq_one_iff_adj.mpr hν
    have h2 : dist α δ = 1 := dist_eq_one_iff_adj.mpr hδ
    have h3 := dist_triangle hA.amalgam.gen ν α δ
    rw [CosetGeom.dist_comm ν α] at h3
    omega

omit [Finite G] in
theorem stab_le_normalizer_Qv' (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Qv δ : Set G) :=
  le_normalizer_pCoreOf 2 (stab δ)

omit [Finite G] in
theorem stab_le_normalizer_Wtri (α : Geo H M) :
    stab α ≤ Subgroup.normalizer (Wtri α : Set G) := by
  have key : ∀ x ∈ stab α, conjSub x (Wtri α) ≤ Wtri α := by
    intro x hx
    obtain ⟨hmem, hfix⟩ := mem_stab.mp hx
    unfold Wtri
    simp only [conjSub_iSup]
    refine iSup₂_le fun ν hν => ?_
    have := Vn_smul (⟨x, hmem⟩ : ↥(H ⊔ M)) ν
    simp only at this
    rw [← this]
    exact Vn_le_Wtri (smul_mem_nbrs_of_mem_stab (g := ⟨x, hmem⟩) hx hν)
  intro x hx
  refine mem_normalizer_of_conjSub_eq (le_antisymm (key x hx) ?_)
  rw [le_conjSub_iff]
  exact key x⁻¹ (inv_mem hx)

theorem Vn_le_normalizer_Wtri (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec)
    (hng : NG H M) (hp : PD δ δ') {α : Geo H M} (hα : α ∈ nbrs δ)
    (hW : ∀ γ ∈ nbrs α, γ ≠ δ → Vn γ ≤ Vn δ ⊔ Qv δ') :
    Vn δ' ≤ Subgroup.normalizer (Wtri α : Set G) := by
  obtain ⟨hl1, hl2, -, -⟩ := hss114_d hG.amalg hG.three_le hp.dist_eq
  obtain ⟨hZV, -, -, -⟩ := c3_comm_eq hG hirr h15 hng hp
  have hWle : Wtri α ≤ Vn δ ⊔ Qv δ' := Wtri_le fun ν hν => by
    by_cases h : ν = δ
    · subst h
      exact le_sup_left
    · exact hW ν hν h
  have hmul : ((Vn δ ⊔ Qv δ' : Subgroup G) : Set G) = (Vn δ : Set G) * (Qv δ' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hl1.trans (stab_le_normalizer_Qv' δ'))
  have key : ∀ y ∈ Vn δ', ∀ w ∈ Wtri α, y * w * y⁻¹ ∈ Wtri α := by
    intro y hy w hw
    have hw' : w ∈ (Vn δ : Set G) * (Qv δ' : Set G) := hmul ▸ hWle hw
    obtain ⟨v, hv, q, hq, rfl⟩ := hw'
    have hc : y * q * y⁻¹ * q⁻¹ ∈ Vn δ :=
      hZV (comm_Vn_Qv_le hG hp.vδ' (Subgroup.commutator_mem_commutator hy hq))
    have hyv : y * v * y⁻¹ ∈ Vn δ :=
      ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ (hl2 hy)) v).mp hv)
    have e : y * (v * q) * y⁻¹ = ((y * v * y⁻¹) * (y * q * y⁻¹ * q⁻¹) * v⁻¹) * (v * q) := by
      group
    rw [e]
    exact mul_mem (Vn_le_Wtri (nbrs_symm hα) (mul_mem (mul_mem hyv hc) (inv_mem hv))) hw
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨key y hy n, fun h => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ h
  have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
  rwa [e] at this

theorem case_i_false (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    (hb5 : 5 ≤ bMin H M) {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ')
    (hW : ∀ γ ∈ nbrs α, γ ≠ δ → Vn γ ≤ Vn δ ⊔ Qv δ') : False := by
  have hαδ : (graph (H ⊔ M) H M).Adj α δ := nbrs_symm hα
  have hU : Wtri α ≤ stab α ⊓ stab δ :=
    (Wtri_le_Qv hG.amalg hb5 (nbrs_symm hα)).trans
      (le_inf (inf_le_left.trans (pCoreOf_le 2 (stab α)))
        (inf_le_right.trans (pCoreOf_le 2 (stab δ))))
  have hBn := Vn_le_normalizer_Wtri hG hirr h15 hng hp hα hW
  have hXn : (stab δ ⊓ stab α) ⊔ Vn δ' ≤ Subgroup.normalizer (Wtri α : Set G) :=
    sup_le (inf_le_right.trans (stab_le_normalizer_Wtri α)) hBn
  have hXδ : (stab δ ⊓ stab α) ⊔ Vn δ' ≤ stab δ :=
    sup_le inf_le_left (hss114_d hG.amalg hG.three_le hp.dist_eq).2.1
  have hWbot : Wtri α = ⊥ := by
    refine eq_bot_of_normalizer_transitive_vertex hG.amalg hαδ hU ?_ ?_
    · intro ε hε ε' hε'
      obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨x, stab_le_normalizer_Wtri α hx, smul_eq_of_mem_stab hx, hxε⟩
    · intro ε hε ε' hε'
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      have hgX : (g : G) ∈ ((stab δ ⊓ stab α) ⊔ Vn δ') ⊔ Qv δ :=
        block_transitive hG hirr h15 hng hp hα hbad hg
      have hmulX : ((((stab δ ⊓ stab α) ⊔ Vn δ') ⊔ Qv δ : Subgroup G) : Set G) =
          (((stab δ ⊓ stab α) ⊔ Vn δ' : Subgroup G) : Set G) * (Qv δ : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (hXδ.trans (stab_le_normalizer_Qv' δ))
      have hgX' : (g : G) ∈ (((stab δ ⊓ stab α) ⊔ Vn δ' : Subgroup G) : Set G) *
          (Qv δ : Set G) := by
        rw [← hmulX]
        exact hgX
      obtain ⟨x, hxX, q, hq, hxq⟩ := hgX'
      have hxs : x ∈ stab δ := hXδ hxX
      have hqs : q ∈ stab δ := pCoreOf_le 2 (stab δ) hq
      obtain ⟨hxm, -⟩ := mem_stab.mp hxs
      obtain ⟨hqm, -⟩ := mem_stab.mp hqs
      have hqε : (⟨q, hqm⟩ : ↥(H ⊔ M)) • ε = ε :=
        smul_eq_of_mem_stab (Qv_le_stab_of_mem_nbrs hG.amalg hε hq)
      have hgeq : g = ⟨x, hxm⟩ * ⟨q, hqm⟩ := Subtype.ext hxq.symm
      refine ⟨⟨x, hxm⟩, hXn hxX, smul_eq_of_mem_stab hxs, ?_⟩
      rw [← hgε, hgeq, mul_smul, hqε]
  have h1 : Zv δ ≤ Wtri α := (Zv_le_Vn hG hp.vδ).trans (Vn_le_Wtri (nbrs_symm hα))
  exact Zv_ne_bot hG.amalg δ (le_bot_iff.mp (hWbot ▸ h1))

end S34

end F53.Stellmacher

end CFSG.Quasithin

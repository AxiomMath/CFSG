module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3A5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_smul_pair (hA : F53Amalgam H M S) {β γ β₀ γ₀ : Geo H M} (hβ : vtype β = false)
    (hβ₀ : vtype β₀ = false) (hd : dist β γ = 2) (hd₀ : dist β₀ γ₀ = 2) :
    ∃ g : ↥(H ⊔ M), g • β = β₀ ∧ g • γ = γ₀ := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_of_vtype_eq (hβ.trans hβ₀.symm)
  have hd₁ : dist β₀ (g₁ • γ) = 2 := by
    rw [hg₁, CosetGeom.dist_smul]
    exact hd
  obtain ⟨l₁, hl₁γ, hl₁β⟩ := exists_adj_dist_eq hA.amalgam.gen (α := β₀) (δ := g₁ • γ) (d := 1) hd₁
  obtain ⟨l₀, hl₀γ, hl₀β⟩ := exists_adj_dist_eq hA.amalgam.gen (α := β₀) (δ := γ₀) (d := 1) hd₀
  have hl₁n : l₁ ∈ nbrs β₀ := dist_eq_one_iff_adj.mp hl₁β
  have hl₀n : l₀ ∈ nbrs β₀ := dist_eq_one_iff_adj.mp hl₀β
  obtain ⟨h, hh, hhl⟩ := stab_transitive_on_nbrs hl₁n hl₀n
  have hhβ : h • β₀ = β₀ := smul_eq_of_mem_stab hh
  have hγ₂ : h • g₁ • γ ∈ nbrs l₀ := by
    have := (smul_adj h).mpr hl₁γ.symm
    rwa [hhl] at this
  have hd₂ : dist β₀ (h • g₁ • γ) = 2 := by
    have := CosetGeom.dist_smul h β₀ (g₁ • γ)
    rw [hhβ] at this
    exact this.trans hd₁
  have hl₀t : vtype l₀ = true := vtype_nbr_of_false hl₀n hβ₀
  have hβn : β₀ ∈ nbrs l₀ := (show (graph (H ⊔ M) H M).Adj β₀ l₀ from hl₀n).symm
  have hγ₀n : γ₀ ∈ nbrs l₀ := hl₀γ.symm
  by_cases hγ₂₀ : h • g₁ • γ = γ₀
  · refine ⟨h * g₁, ?_, ?_⟩
    · rw [mul_smul, ← hg₁, hhβ]
    · rw [mul_smul]
      exact hγ₂₀
  · have hβγ₂ : β₀ ≠ h • g₁ • γ := fun e => by
      rw [← e, CosetGeom.dist_self] at hd₂
      omega
    have hβγ₀ : β₀ ≠ γ₀ := fun e => by
      rw [← e, CosetGeom.dist_self] at hd₀
      omega
    obtain ⟨t, ht, htγ⟩ := exists_swap hA hl₀t hβγ₂ hβγ₀ hγ₂₀ hβn hγ₂ hγ₀n
    refine ⟨t * (h * g₁), ?_, ?_⟩
    · rw [mul_smul, mul_smul, ← hg₁, hhβ]
      exact smul_eq_of_mem_stab ht.2
    · rw [mul_smul, mul_smul]
      exact htγ

theorem not_vn_le_qv_of_dist (hB : B3Base H M S) {β γ : Geo H M} (hβ : vtype β = false)
    (hd : dist β γ = 2) : ¬ Vn β ≤ Qv γ := by
  have hA := hB.amalgam
  have hα : vtype (γ₁ (H ⊔ M) H M) = true := vtype_γ₁
  obtain ⟨β₀, hβ₀adj⟩ := exists_adj (γ₁ (H ⊔ M) H M)
  obtain ⟨α', hcd⟩ := exists_critData hA (hB.crit _ hα) hβ₀adj
  have hβ₀f : vtype β₀ = false := vtype_nbr_of_true hβ₀adj hα
  have hd₀ : dist β₀ α' = 2 := by
    have := hcd.dist_eq'
    rw [hB.b_eq] at this
    omega
  have hZV : Zv (γ₁ (H ⊔ M) H M) ≤ Vn β₀ :=
    le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β₀) => Zv μ) (γ₁ (H ⊔ M) H M)
      (show (γ₁ (H ⊔ M) H M) ∈ nbrs β₀ from hβ₀adj.symm) le_rfl
  obtain ⟨g, hgβ, hgγ⟩ := exists_smul_pair hA hβ hβ₀f hd hd₀
  intro hle
  apply hcd.not_le
  refine hZV.trans ?_
  rw [← hgβ, ← hgγ, Vn_smul, Qv_smul]
  exact conjSub_mono _ hle

theorem blockFacts_of_base (hB : B3Base H M S)
    (hnt : ∀ β : Geo H M, vtype β = false → ¬ Vn β ≤ Cv β) : B3Block H M S where
  three_le_bAt := three_le_bAt hB
  zv_le_qv := fun _ _ h => zv_le_qv_of_dist hB h
  zv_le_stab := fun _ _ h => zv_le_stab_of_dist hB h
  vn_le_qv := fun _ _ h => vn_le_qv_of_dist hB h
  vn_le_stab := fun _ _ h => vn_le_stab_of_dist hB h
  elemAbelian_vn := fun x => isElemAbelian_Vn hB.amalgam (by rw [hB.b_eq]) x
  card_zv_s3 := fun _ hα => card_zv_true hB hα
  zv_le_zv := fun _ _ hβ h => zv_le_zv_of_adj hB hβ h
  comm_vn_qv := fun _ hβ => comm_vn_qv_eq hB hβ
  cv_inf_zv := fun _ _ hβ h => cv_inf_zv_eq hB hnt hβ h
  kq_le_qv := fun _ _ hβ h => kq_le_qv_of_adj hB hβ h
  vn_inf_normal := fun _ _ _ hδβ hμ hμβ hμδ => vn_inf_normal_of hB hδβ hμ hμβ hμδ
  comm_vn_vn := fun _ _ h => comm_vn_vn_of_dist hB h
  not_vn_le_qv := fun _ _ hβ h => not_vn_le_qv_of_dist hB hβ h

theorem blockFacts (hB : B3Facts H M S) : B3Block H M S :=
  blockFacts_of_base hB.toB3Base fun β hβ => not_le_of_isNatSec (hB.nat β hβ)

theorem blockFactsO (hB : B3FactsO H M S) : B3Block H M S :=
  blockFacts_of_base hB.toB3Base fun β hβ => not_le_of_isOrthSec (hB.orth β hβ)

end F53B3

end CFSG.Quasithin

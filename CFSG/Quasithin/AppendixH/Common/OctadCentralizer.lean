module

public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem eq_one_of_fix_compl_octad {O : Finset (Fin 24)}
    (hO : IsOctad O) {g : S24} (hg : g ∈ M24g) (hfix : ∀ i, i ∉ O → g i = i) : g = 1 := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octadB0 hO
  have hrfix : ∀ i, B 0 i = 0 → (σ⁻¹ * g * σ) i = i := by
    intro i hBi
    have hiO : i ∉ octadB0 := by simp [octadB0, hBi]
    have hσi : σ i ∉ O := by
      intro h
      apply hiO
      have h' : σ i ∈ σ • octadB0 := by rw [hσO]; exact h
      rw [smul_finset_eq_map, Finset.mem_map_equiv] at h'
      simpa using h'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hfix (σ i) hσi]
    simp
  have hrM : (σ⁻¹ * g * σ) ∈ M24g :=
    M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hσ) hg) hσ
  have h1 : σ⁻¹ * g * σ = 1 := eq_one_of_fix_compl hrM hrfix
  calc g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
    _ = σ * 1 * σ⁻¹ := by rw [h1]
    _ = 1 := by group

theorem eq_one_of_fix_octad_of_fix_outside {O : Finset (Fin 24)}
    (hO : IsOctad O) {g : S24} (hg : g ∈ M24g) (hfixO : ∀ i ∈ O, g i = i) {p : Fin 24}
    (hp : p ∉ O) (hgp : g p = p) : g = 1 := by
  have hgfix : g ∈ octFix O := mem_octFix_iff.2 ⟨hg, hfixO⟩
  obtain ⟨k, _, huniq⟩ := octFix_regular hO hp hp
  have hgk : (⟨g, hgfix⟩ : ↥(octFix O)) = k := huniq ⟨g, hgfix⟩ hgp
  have h1k : (⟨1, (octFix O).one_mem⟩ : ↥(octFix O)) = k := huniq 1 (by simp)
  have hsub : (⟨g, hgfix⟩ : ↥(octFix O)) = 1 := by rw [hgk, ← h1k]; rfl
  exact congrArg Subtype.val hsub

theorem octStab_inf_centralizer_octFix {O : Finset (Fin 24)}
    (hO : IsOctad O) : octStab O ⊓ Subgroup.centralizer (octFix O : Set S24) = octFix O := by
  have hle : octFix O ≤ octStab O ⊓ Subgroup.centralizer (octFix O : Set S24) := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨octFix_le_octStab O hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val ((isElemAbelian_octFix hO).1.is_comm.comm ⟨h, hh⟩ ⟨g, hg⟩)
  refine le_antisymm ?_ hle
  intro g hg
  obtain ⟨hgstab, hgcent⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hgM, hgO⟩ := mem_octStab_iff.1 hgstab
  have hlt : O.card < (Finset.univ : Finset (Fin 24)).card := by
    rw [hO.1, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hgpO : g p ∉ O := by
    intro h
    apply hp
    have h' : g p ∈ g • O := by rw [hgO]; exact h
    rw [smul_finset_eq_map, Finset.mem_map_equiv] at h'
    simpa using h'
  obtain ⟨k, hk, -⟩ := octFix_regular hO hp hgpO
  let kS : S24 := (k : S24)
  have hkM : kS ∈ M24g := (mem_octFix_iff.1 k.2).1
  have hkcent : kS ∈ Subgroup.centralizer (octFix O : Set S24) :=
    (Subgroup.mem_inf.mp (hle k.2)).2
  have hM : (kS⁻¹ * g) ∈ M24g := M24g.mul_mem (M24g.inv_mem hkM) hgM
  have hcent : (kS⁻¹ * g) ∈ Subgroup.centralizer (octFix O : Set S24) :=
    (Subgroup.centralizer (octFix O : Set S24)).mul_mem
      ((Subgroup.centralizer (octFix O : Set S24)).inv_mem hkcent) hgcent
  have hhp : (kS⁻¹ * g) p = p := by
    rw [Equiv.Perm.mul_apply, ← hk]
    exact Equiv.symm_apply_apply kS p
  have hfix_out : ∀ q, q ∉ O → (kS⁻¹ * g) q = q := by
    intro q hq
    obtain ⟨c, hc, -⟩ := octFix_regular hO hp hq
    have hcomm : (kS⁻¹ * g) * (c : S24) = (c : S24) * (kS⁻¹ * g) :=
      (Subgroup.mem_centralizer_iff.1 hcent (c : S24) c.2).symm
    calc (kS⁻¹ * g) q = (kS⁻¹ * g) ((c : S24) p) := by rw [hc]
      _ = ((kS⁻¹ * g) * (c : S24)) p := rfl
      _ = ((c : S24) * (kS⁻¹ * g)) p := by rw [hcomm]
      _ = (c : S24) ((kS⁻¹ * g) p) := rfl
      _ = (c : S24) p := by rw [hhp]
      _ = q := hc
  have hh1 : kS⁻¹ * g = 1 := eq_one_of_fix_compl_octad hO hM hfix_out
  have hgk : g = kS := by
    calc g = kS * (kS⁻¹ * g) := by group
      _ = kS * 1 := by rw [hh1]
      _ = kS := by rw [mul_one]
  rw [hgk]
  exact k.2

end CFSG.ASVolI.AppH

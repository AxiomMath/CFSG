module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveWindow

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁ Vv)

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

theorem CritConfig.not_Vv_le_ballStab (hc : CritAmalgam G₀ G₁ G₂ T Z)
    {α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂} (h : CritConfig Z α α₁ α' α₂ α₃) :
    ¬ Vv Z α' ≤ ballStab 1 α₁ := by
  intro hle
  apply h.not_le
  have hV' : Vv Z α' ≤ Subgroup.centralizer (Vv Z α₁ : Set G) :=
    hle.trans (ballStab_le_centralizer_Vv hc h.vα₁)
  have hV1 : Vv Z α₁ ≤ Subgroup.centralizer (Vv Z α' : Set G) :=
    Subgroup.le_centralizer_iff.mp hV'
  have hV1' : Vv Z α₁ ≤ ballStab 1 α' := by
    rw [← lemma73_1 hc h.vα']
    exact le_inf ((h.vOne_le hc).trans inf_le_left) hV1
  exact (Vv_le_Vv_of_mem_nbrs h.vα₁ h.adj₁).trans hV1'

theorem exists_pCoreOf_nonconst (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : Odd (critB G₀ G₁ G₂ Z))
    {μ : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) :
    ∃ x ∈ pCoreOf 2 (stab μ), ∃ δ₁ ∈ nbrs μ, ∃ δ₂ ∈ nbrs μ,
      x ∉ ballStab 1 δ₁ ∧ x ∈ ballStab 1 δ₂ := by
  have hG := hc.amalgam.gen
  obtain ⟨α', hdist, hnZ⟩ := exists_dist_eq_critB hc
  have hb2 := two_le_critB hc
  obtain ⟨k, hk⟩ : ∃ k, critB G₀ G₁ G₂ Z = k + 2 := ⟨critB G₀ G₁ G₂ Z - 2, by omega⟩
  rw [hk] at hdist hb
  have hkpos : 0 < k := by
    obtain ⟨t, ht⟩ := hb
    omega
  have hα : vtype (γ₀ G₀ G₁ G₂) = false := CosetGeom.vtype_γ₀
  have hα'v : vtype α' = true := by
    rw [vtype_eq_of_dist hc hα _ α' hdist]
    exact decide_eq_true hb
  have hd1 : CosetGeom.dist α' (γ₀ G₀ G₁ G₂) = (k + 1) + 1 := by
    rw [CosetGeom.dist_comm]; exact hdist
  obtain ⟨α₁, hadj₁, hd₁⟩ := CosetGeom.exists_adj_dist_eq hG hd1
  have hα₁v : vtype α₁ = true := vtype_eq_true_of_mem_nbrs hα hadj₁
  have hd2 : CosetGeom.dist α₁ α' = k + 1 := by rw [CosetGeom.dist_comm]; exact hd₁
  obtain ⟨α₃, hadj₃, hd₃⟩ := CosetGeom.exists_adj_dist_eq hG hd2
  obtain ⟨α₂, hadj₂, hd₄⟩ := CosetGeom.exists_adj_dist_eq hG hd₁
  have hconf : CritConfig Z (γ₀ G₀ G₁ G₂) α₁ α' α₂ α₃ :=
    ⟨hα, hα₁v, hα'v, CosetGeom.mem_nbrs_symm hadj₁, hadj₂, hadj₃,
      by rw [CosetGeom.Vv_γ₀ hc.normalizes]; exact hnZ,
      lemma72_small hc hα'v (by rw [hk, hd₄]),
      lemma72_small hc hα₁v (by rw [hk, hd₃])⟩
  obtain ⟨β, hβadj, hβdist⟩ := CosetGeom.exists_adj_dist_eq hG
    (show CosetGeom.dist α' α₂ = (k - 1) + 1 by omega)
  have hVballβ : Vv Z α' ≤ ballStab 1 β := by
    intro x hx
    rw [CosetGeom.mem_ballStab]
    intro w hw
    have hK : Vv Z α' ≤ stab w := by
      refine Vv_le_of_forall_mem_nbrs hα'v fun γ hγ => ?_
      have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hα'v hγ
      refine Vv_le_stab_of_dist_le hc hγt ?_
      have e1 : CosetGeom.dist γ α' = 1 := by
        rw [CosetGeom.dist_comm]
        exact CosetGeom.dist_eq_one_iff_adj.mpr hγ
      have t1 := CosetGeom.dist_triangle hG γ α' β
      have t2 := CosetGeom.dist_triangle hG γ β w
      rw [hk]
      omega
    exact hK hx
  obtain ⟨x, hxV, hxN⟩ :=
    SetLike.not_le_iff_exists.mp (hconf.not_Vv_le_ballStab hc)
  have hxQ : x ∈ pCoreOf 2 (stab α₂) := hconf.push₂ hxV
  have hxβ : x ∈ ballStab 1 β := hVballβ hxV
  have hα₂v : vtype α₂ = false := vtype_eq_false_of_mem_nbrs hα₁v hconf.adj₂
  obtain ⟨g₁, hg₁⟩ := CosetGeom.exists_smul_eq_γ₀ hα₂v
  obtain ⟨g₂, hg₂⟩ := CosetGeom.exists_smul_eq_γ₀ hμ
  let g : ↥G₀ := g₂ * g₁⁻¹
  have hg : g • α₂ = μ := by
    rw [hg₁, hg₂]
    simp only [g, mul_smul, inv_smul_smul]
  have hconj : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) = x := by group
  refine ⟨(g : G) * x * (g : G)⁻¹, ?_, g • α₁, ?_, g • β, ?_, ?_, ?_⟩
  · rw [← hg, CosetGeom.stab_smul, pCoreOf_conjSub]
    exact mem_conjSub.mpr (by simpa [hconj] using hxQ)
  · rw [← hg]
    exact (CosetGeom.smul_adj g).mpr hconf.adj₂.symm
  · rw [← hg]
    exact (CosetGeom.smul_adj g).mpr hβadj
  · intro hmem
    rw [CosetGeom.ballStab_smul, mem_conjSub] at hmem
    exact hxN (by simpa [hconj] using hmem)
  · rw [CosetGeom.ballStab_smul, mem_conjSub]
    simpa [hconj] using hxβ

end CFSG.Quasithin.F112Crit

end

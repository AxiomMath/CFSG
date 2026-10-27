module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CommVnQv
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.PermNormal
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepD

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
  CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_noncommuting_alt_five :
    ∃ a b : Perm (Fin 5), a ∈ alternatingGroup (Fin 5) ∧ b ∈ alternatingGroup (Fin 5) ∧
      a * b ≠ b * a :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 2 3,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel,
    by decide +kernel⟩

theorem one_lt_bMin_of_s3_central {H M S : Subgroup G} (hA : F53Amalgam H M S)
    {α β α' : Geo H M} (hc : IsCritData α β α') (hα : vtype α = true)
    (hz : Zv β ≤ centerOf (stab β)) : 1 < bMin H M := by
  by_contra hle
  have hdist : dist β α' + 1 = bMin H M := hc.dist_eq'
  have hβv : vtype β = false := by
    have h := vtype_ne_of_adj hc.adj
    rw [hα] at h
    revert h
    cases vtype β <;> simp
  have hb1 : bMin H M = 1 := by omega
  have hd0 : dist β α' = 0 := by omega
  have hβα' : β = α' := (dist_eq_zero_iff hA.amalgam.gen).mp hd0
  have hnot : ¬ Zv α ≤ Qv β := by
    rw [hβα']
    exact hc.not_le
  have hαn : α ∈ nbrs β := (show (graph (H ⊔ M) H M).Adj β α from hc.adj.symm)
  have hZα : Zv α ≤ Vn β := CFSG.Quasithin.F53.Stellmacher.Zv_le_Vn_of_mem_nbrs hαn
  have hVle : Vn β ≤ stab β := by
    refine iSup_le fun μ => iSup_le fun hμ => ?_
    have hβμ : β ∈ nbrs μ := (show (graph (H ⊔ M) H M).Adj β μ from hμ).symm
    intro x hx
    exact ((Qv_le_inf hA hβμ) (Zv_le_Qv hA μ hx)).2
  have hV : ⁅Vn β, Qv β⁆ ≤ Zv β := commutator_Vn_Qv_le hA hβv hz
  have hZVn : ∀ z ∈ Zv β, ∀ v ∈ Vn β, ⁅z, v⁆ = 1 := by
    intro z hzZ v hv
    have hzc : z ∈ Subgroup.centralizer (stab β : Set G) := (hz hzZ).2
    have hcomm : v * z = z * v := Subgroup.mem_centralizer_iff.mp hzc v (hVle hv)
    rw [commutatorElement_def, ← hcomm]
    group
  have hc1 : ⁅⁅Vn β, Qv β⁆, Vn β⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_bot]
    exact hZVn g₁ (hV hg₁) g₂ hg₂
  have hQV : ⁅Qv β, Vn β⁆ ≤ Zv β := by
    refine Subgroup.commutator_le.mpr fun q hq v hv => ?_
    have h := hV (Subgroup.commutator_mem_commutator hv hq)
    have e : ⁅q, v⁆ = ⁅v, q⁆⁻¹ := by rw [commutatorElement_inv]
    rw [e]
    exact (Zv β).inv_mem h
  have hc2 : ⁅⁅Qv β, Vn β⁆, Vn β⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_bot]
    exact hZVn g₁ (hQV hg₁) g₂ hg₂
  have hc3 : ⁅⁅Vn β, Vn β⁆, Qv β⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hc1 hc2
  have hVV_stab : ⁅Vn β, Vn β⁆ ≤ stab β := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact (stab β).mul_mem
      ((stab β).mul_mem ((stab β).mul_mem (hVle hg₁) (hVle hg₂)) ((stab β).inv_mem (hVle hg₁)))
      ((stab β).inv_mem (hVle hg₂))
  have hVV : ⁅Vn β, Vn β⁆ ≤ Qv β := by
    intro c hc
    have hcC : c ∈ Subgroup.centralizer (Qv β : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hmem := Subgroup.commutator_mem_commutator hc hq
      rw [hc3, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
    exact charTwo_stab hA β ⟨hVV_stab hc, hcC⟩
  obtain ⟨n, ψ, hn, hsurj, hker⟩ := exists_quotHom hA β
  have hn5 : n = 5 := by
    rcases hn with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [hβv] at h
      exact absurd h Bool.false_ne_true
  subst hn5
  have hWn : ((Vn β).subgroupOf (stab β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (Vn β : Set G) := stab_le_normalizer_Vn β g.2
    have := (Subgroup.mem_set_normalizer_iff.mp hg (n : G)).mp hn
    simpa using this
  have hNn := Subgroup.Normal.map hWn ψ hsurj
  obtain ⟨z, hzα, hzq⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hzβ : z ∈ stab β := hVle (hZα hzα)
  have hNbot : ((Vn β).subgroupOf (stab β)).map ψ ≠ ⊥ := by
    intro hbot
    have hmem : ψ ⟨z, hzβ⟩ ∈ ((Vn β).subgroupOf (stab β)).map ψ :=
      ⟨⟨z, hzβ⟩, Subgroup.mem_subgroupOf.mpr (hZα hzα), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hzq ((hker ⟨z, hzβ⟩).mp hmem)
  have hA5 : alternatingGroup (Fin 5) ≤ ((Vn β).subgroupOf (stab β)).map ψ := by
    rcases normal_perm_five _ hNn with h | h | h
    · exact absurd h hNbot
    · exact le_of_eq h.symm
    · rw [h]
      exact le_top
  obtain ⟨a, b, haA, hbA, hab⟩ := exists_noncommuting_alt_five
  obtain ⟨wa, hwa, hψa⟩ := Subgroup.mem_map.mp (hA5 haA)
  obtain ⟨wb, hwb, hψb⟩ := Subgroup.mem_map.mp (hA5 hbA)
  have hcomm_mem : ((⁅wa, wb⁆ : ↥(stab β)) : G) ∈ Qv β := by
    have e : ((⁅wa, wb⁆ : ↥(stab β)) : G) = ⁅(wa : G), (wb : G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      simp
    rw [e]
    exact hVV (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hwa)
      (Subgroup.mem_subgroupOf.mp hwb))
  have hkey : ψ ⁅wa, wb⁆ = 1 := (hker _).mpr hcomm_mem
  rw [map_commutatorElement, hψa, hψb] at hkey
  exact hab (commutatorElement_eq_one_iff_mul_comm.mp hkey)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end

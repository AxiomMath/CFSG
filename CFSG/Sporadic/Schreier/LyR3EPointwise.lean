module

public import CFSG.Sporadic.Schreier.LyR3EFusion

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly

theorem mulAut_ext_of_C_g
    {α β : MulAut J} (hC : ∀ c ∈ lyC, α c = β c)
    (hg : α r3eG = β r3eG) : α = β := by
  have h := MonoidHom.eq_of_eqOn_dense (G := J) involution_centralizer_fusion_generator.1
    (f := (α : J →* J)) (g := (β : J →* J)) (by
      rintro x (hx | hx)
      · exact hC x hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hg)
  exact MulEquiv.ext fun x => DFunLike.congr_fun h x

theorem lyz_inv : lyz⁻¹ = lyz := by rw [lyz, a_inv']

theorem conj_lyz_fixes_C :
    ∀ c ∈ lyC, MulAut.conj lyz c = c := by
  intro c hc
  rw [MulAut.conj_apply]
  have h := congrArg Subtype.val ((Subgroup.mem_center_iff.1 zC_mem_center) ⟨c, hc⟩)
  have h' : c * lyz = lyz * c := h
  rw [← h', mul_inv_cancel_right]

theorem r3eC_mem_lyC : r3eC ∈ lyC := cStar_mem 3

theorem fixes_C_cases
    {α : MulAut J} (hα : ∀ c ∈ lyC, α c = c) :
    α = 1 ∨ α = MulAut.conj lyz := by
  have hαg : α r3eG = (α r3eG * r3eG⁻¹) * r3eG := by rw [inv_mul_cancel_right]
  set δ := α r3eG * r3eG⁻¹ with hδ
  have hδD : δ ∈ Subgroup.centralizer (r3eD0 : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC : y ∈ lyC := (r3eD0_le hy).1
    have hyg : y ∈ lyC.map (MulAut.conj r3eG).toMonoidHom := (r3eD0_le hy).2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.1 hyg
    have hcy' : r3eG * c * r3eG⁻¹ = y := by
      rw [← hcy]
      rfl
    have h3 : α y = δ * y * δ⁻¹ := by
      rw [← hcy', map_mul, map_mul, map_inv, hα c hc, hαg]
      group
    rw [hα y hyC] at h3
    calc y * δ = δ * y * δ⁻¹ * δ := by rw [← h3]
      _ = δ * y := by group
  have h18 : (r3eC * δ * r3eG) ^ 18 = 1 := by
    have h := congrArg α r3e_pow_one
    rw [map_pow, map_mul, map_mul, map_one, hα r3eC r3eC_mem_lyC, hαg] at h
    simpa [mul_assoc] using h
  rcases mem_centralizer_r3eD0 hδD with h | h | h | h
  · left
    apply mulAut_ext_of_C_g (fun c hc => by rw [hα c hc]; rfl)
    rw [hαg, h, one_mul]
    rfl
  · exact absurd (h ▸ h18) r3e_pow_z
  · exact absurd (h ▸ h18) r3e_pow_f
  · right
    apply mulAut_ext_of_C_g (fun c hc => by rw [hα c hc, conj_lyz_fixes_C c hc])
    rw [hαg, h, MulAut.conj_apply, lyz_inv, ← r3eG_conj_lyz]
    group

theorem conj_lyz_ne_one :
    MulAut.conj lyz ≠ 1 := by
  intro h
  have hg := DFunLike.congr_fun h r3eG
  rw [MulAut.conj_apply, MulAut.one_apply] at hg
  have hc : r3eG * lyz = lyz * r3eG := by
    calc r3eG * lyz = lyz * r3eG * lyz⁻¹ * lyz := by rw [hg]
      _ = lyz * r3eG := by group
  apply lyf_ne_lyz
  rw [← r3eG_conj_lyz, hc, mul_inv_cancel_right]

theorem involution_centralizer_pointwise_automorphisms_inner :
    {α : MulAut J | ∀ c ∈ lyC, α c = c} = {1, MulAut.conj lyz} ∧
      (1 : MulAut J) ≠ MulAut.conj lyz := by
  refine ⟨?_, fun h => conj_lyz_ne_one h.symm⟩
  ext α
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fixes_C_cases, ?_⟩
  rintro (rfl | rfl)
  · intro c _
    rfl
  · exact conj_lyz_fixes_C

end CFSG.Sporadic.LySchreier

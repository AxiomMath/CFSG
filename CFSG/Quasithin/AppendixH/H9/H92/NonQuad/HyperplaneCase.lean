module

public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.IndependentVectors
public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.OrbitStabilizerCount

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_le_sixteen_of_finrank_nilOrbitSpace_eq_three {E : Subgroup (GL (Fin 5) (ZMod 2))}
    {𝒩 : Submodule (ZMod 2) (Matrix (Fin 5) (Fin 5) (ZMod 2))} (h : SubOneCover E 𝒩)
    (hsq : ∀ a ∈ E, a * a = 1) {g h' : GL (Fin 5) (ZMod 2)} (hg : g ∈ E) (hh : h' ∈ E)
    {v : Fin 5 → ZMod 2}
    (hy : (((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
      ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)) *ᵥ v ≠ 0)
    (hS : Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) = 3) : Nat.card E ≤ 16 := by
  have hA : ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) ∈ 𝒩 := h.sub_one_mem g hg
  have hB : ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) ∈ 𝒩 := h.sub_one_mem h' hh
  have hp : NilPair ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)
      ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) :=
    ⟨h.mul_self _ hA, h.mul_self _ hB, h.mul_comm _ hA _ hB⟩
  have hv : v ≠ 0 := fun hv0 => hy (by rw [hv0, Matrix.mulVec_zero])
  have hWge : 4 ≤ Module.finrank (ZMod 2) (nilOrbitSpan 𝒩 v) := by
    have := finrank_nilOrbitSpace_lt h hv
    omega
  have hWle : Module.finrank (ZMod 2) (nilOrbitSpan 𝒩 v) ≤ 4 := by
    have := finrank_nilOrbitSpan_le (𝒩 := 𝒩) hv
    omega
  have hWne : nilOrbitSpan 𝒩 v ≠ ⊤ := by
    intro htop
    have : Module.finrank (ZMod 2) (nilOrbitSpan 𝒩 v) = 5 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨u, hu⟩ : ∃ u, u ∉ nilOrbitSpan 𝒩 v := by
    by_contra hcon
    exact hWne (eq_top_iff.2 fun u _ => by by_contra hu; exact hcon ⟨u, hu⟩)
  have hWu : nilOrbitSpan 𝒩 v ⊔ Submodule.span (ZMod 2) {u} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : nilOrbitSpan 𝒩 v < nilOrbitSpan 𝒩 v ⊔ Submodule.span (ZMod 2) {u} :=
      lt_of_le_of_ne le_sup_left fun heq =>
        hu (by rw [heq]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (nilOrbitSpan 𝒩 v ⊔ Submodule.span (ZMod 2) {u})
    rw [Module.finrank_fin_fun] at h2 ⊢
    omega
  have hNu : ∀ k ∈ E, ((k : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u ∈ nilOrbitSpan 𝒩 v := by
    intro k hk
    have hku : (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ u ∈
        nilOrbitSpan 𝒩 v ⊔ Submodule.span (ZMod 2) {u} := by
      rw [hWu]; exact Submodule.mem_top
    obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp hku
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exfalso
      apply hu
      have hk' : k⁻¹ ∈ E := E.inv_mem hk
      have h1 : ((k⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
          ((k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [zero_smul, add_zero] at hwt
      rw [← h1, ← hwt]
      exact mulVec_mem_nilOrbitSpan h hk' hw
    · rw [one_smul] at hwt
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwt, add_sub_cancel_right]
      exact hw
  have hkill : ∀ k ∈ E, (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v →
      ∀ w ∈ nilOrbitSpan 𝒩 v, ((k : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ w = 0 :=
    fun k hk hkv w hw => sub_one_mulVec_eq_zero_of_fix h hk hkv hw
  have hvals : ∀ k ∈ E, (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v →
      ((k : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u ∈ Submodule.span (ZMod 2)
        {(((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
          ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)) *ᵥ v} := by
    intro k hk hkv
    refine mem_span_prod_of_mulVec_eq_zero h hp hA hB hy hS (hNu k hk) ?_ ?_
    · rw [Matrix.mulVec_mulVec, h.mul_comm _ hA _ (h.sub_one_mem k hk), ← Matrix.mulVec_mulVec]
      exact hkill k hk hkv _ (hNu g hg)
    · rw [Matrix.mulVec_mulVec, h.mul_comm _ hB _ (h.sub_one_mem k hk), ← Matrix.mulVec_mulVec]
      exact hkill k hk hkv _ (hNu h' hh)
  have hinj : ∀ k₁ ∈ E, ∀ k₂ ∈ E, (k₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v →
      (k₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v →
      ((k₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u =
        ((k₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ h1 h2 h12
    have hm : k₁ * k₂ ∈ E := E.mul_mem hk₁ hk₂
    have hmv : ((k₁ * k₂ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, h2, h1]
    have hid : (((k₁ * k₂ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) =
        ((k₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) * ((k₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) +
          ((k₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) +
            ((k₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) := by
      rw [Units.val_mul]
      noncomm_ring
    have hmu : (((k₁ * k₂ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u = 0 := by
      rw [hid, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
        hkill k₁ hk₁ h1 _ (hNu k₂ hk₂), ← h12]
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact (by decide : ∀ c : ZMod 2, 0 + c + c = 0) _
    have hone : k₁ * k₂ = 1 := by
      refine eq_one_of_sub_one_mulVec_eq_zero fun w => ?_
      have hw : w ∈ nilOrbitSpan 𝒩 v ⊔ Submodule.span (ZMod 2) {u} := by
        rw [hWu]; exact Submodule.mem_top
      obtain ⟨w₁, hw₁, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hkill _ hm hmv _ hw₁, hmu, smul_zero, add_zero]
    exact (mul_left_cancel (hone.trans (hsq k₁ hk₁).symm)).symm
  have hcount := card_le_card_mul_card_of_stabilizer_embeds (E := E) (v := v) (nilOrbitSpace 𝒩 v)
    (Submodule.span (ZMod 2)
      {(((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
        ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)) *ᵥ v})
    (fun k => ((k : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ u)
    (fun k hk => mulVec_sub_self_mem_nilOrbitSpace h hk v) hvals hinj
  have hcardS : Nat.card (nilOrbitSpace 𝒩 v) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hS, Nat.card_zmod]
    norm_num
  have hcardT : Nat.card (Submodule.span (ZMod 2)
      {(((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
        ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)) *ᵥ v}) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_span_singleton hy, Nat.card_zmod]
    norm_num
  rw [hcardS, hcardT] at hcount
  omega

end CFSG.ASVolI.ChH

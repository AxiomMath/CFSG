module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CC

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt)

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem natAct_mem_of_map_eq {g : antiSp k} {X Y : Submodule k (Fin 4 → k)}
    (h : X.map (natLin g) = Y) {v : Fin 4 → k} (hv : v ∈ X) : natAct g v ∈ Y := by
  rw [← h, ← natLin_apply]
  exact Submodule.mem_map_of_mem hv

omit [CharP k 2] in
theorem spBil_isRefl : (spBil : LinearMap.BilinForm k (Fin 4 → k)).IsRefl :=
  fun x y h => by rwa [spBil_comm]

theorem not_g41Dec {G₀ : Subgroup (antiSp k)} {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : uElt 0 0 a 0 ∈ G₀) (hs : uElt 0 b 0 0 ∈ G₀) : ¬ G41DecW G₀ := by
  rintro ⟨V₁, V₂, hdim, hV₂, hdisj, hpres⟩
  have h0 : ∀ v, v ∈ V₁ → v ∈ V₂ → v = 0 := fun v h1 h2 => by
    have h3 : v ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
    rw [hdisj] at h3
    exact h3
  have hmem₂ : ∀ v, v ∈ V₂ ↔ ∀ w ∈ V₁, spBil w v = 0 := fun v => by
    rw [hV₂]
    rfl
  have ht : V₁.map (natLin (uElt 0 0 a 0)) = V₁ ∧ V₂.map (natLin (uElt 0 0 a 0)) = V₂ := by
    rcases hpres _ hl with h | h
    · exact h
    · exfalso
      obtain ⟨v, hv, hv0, hv3⟩ := exists_ne_zero_three_eq_zero hdim
      have htv : natAct (uElt 0 0 a 0) v = v := by
        rw [natAct_zl, hv3, mul_zero, zero_smul, add_zero]
      exact hv0 (h0 v hv (htv ▸ natAct_mem_of_map_eq h.1 hv))
  have he0 : ∀ X : Submodule k (Fin 4 → k), X.map (natLin (uElt 0 0 a 0)) = X →
      (∃ v ∈ X, v 3 ≠ 0) → (Pi.single 0 1 : Fin 4 → k) ∈ X := by
    rintro X hX ⟨v, hv, hv3⟩
    have h1 := natAct_mem_of_map_eq hX hv
    rw [natAct_zl] at h1
    have h2 : (a * v 3) • (Pi.single 0 1 : Fin 4 → k) ∈ X := by
      have h3 := X.sub_mem h1 hv
      rwa [add_sub_cancel_left] at h3
    have h4 := X.smul_mem (a * v 3)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero ha hv3), one_smul] at h4
  have htriv : (∀ v ∈ V₁, v 3 = 0) ∨ (∀ v ∈ V₂, v 3 = 0) := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨v, hv, hv3⟩, ⟨w, hw, hw3⟩⟩ := hc
    have h5 := congrFun (h0 _ (he0 V₁ ht.1 ⟨v, hv, hv3⟩) (he0 V₂ ht.2 ⟨w, hw, hw3⟩)) 0
    simp at h5
  have hsw : V₁.map (natLin (uElt 0 b 0 0)) = V₂ ∧ V₂.map (natLin (uElt 0 b 0 0)) = V₁ := by
    rcases hpres _ hs with h | h
    · exfalso
      refine zs_not_fix hb hdim (fun v hv hvX => h0 v hv ((hmem₂ v).2 hvX)) h.1
    · exact h
  have h3 : ∀ v ∈ V₁, v 3 = 0 := by
    rcases htriv with h | h
    · exact h
    · intro v hv
      rw [← natAct_zs_three b v]
      exact h _ (natAct_mem_of_map_eq hsw.1 hv)
  have h3' : ∀ v ∈ V₂, v 3 = 0 := by
    rcases htriv with h | h
    · intro v hv
      rw [← natAct_zs_three b v]
      exact h _ (natAct_mem_of_map_eq hsw.2 hv)
    · exact h
  have hfin := LinearMap.BilinForm.finrank_add_finrank_orthogonal spBil_isRefl V₁
  rw [← hV₂, hdim, Module.finrank_fin_fun] at hfin
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hdisj, finrank_bot, add_zero, hdim] at hsup
  set P : Submodule k (Fin 4 → k) := LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ => k) 3)
  have hle : V₁ ⊔ V₂ ≤ P := sup_le (fun v hv => h3 v hv) (fun v hv => h3' v hv)
  have hP : P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hP => ?_
    have h6 : (Pi.single 3 1 : Fin 4 → k) ∈ P := hP ▸ Submodule.mem_top
    simp [P] at h6
  have h7 := Submodule.finrank_lt hP.ne
  have h8 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h7
  omega

end CFSG.Quasithin.Ch3E213M

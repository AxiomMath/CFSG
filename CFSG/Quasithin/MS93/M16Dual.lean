module

public import CFSG.Quasithin.MS93.M16Core

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem transposeInv_rootElt (i j : Fin 3) (c : F) :
    transposeInv (rootElt i j c) = rootElt j i (-c) := by
  by_cases hij : i = j
  · subst hij
    rw [rootElt_self, rootElt_self, map_one]
  apply Subtype.ext
  rw [coe_transposeInv, dualMat, ← rootElt_neg, coe_rootElt hij, coe_rootElt (Ne.symm hij),
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem map_transposeInv_rootGroup (i j : Fin 3) :
    (rootGroup i j : Subgroup (SL3 F)).map transposeInv = rootGroup j i := by
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [transposeInv_rootElt]
    exact rootElt_mem_rootGroup _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨rootElt i j (-c), rootElt_mem_rootGroup _ _ _, ?_⟩
    rw [transposeInv_rootElt, neg_neg]

theorem transposeInv_pmat [CharP F 2] (σ : Equiv.Perm (Fin 3)) :
    transposeInv (pmat σ : SL3 F) = pmat σ := by
  apply Subtype.ext
  rw [coe_transposeInv, dualMat, pmat_inv]
  ext k l
  rw [Matrix.transpose_apply, coe_pmat_apply, coe_pmat_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem range_comp_transposeInv (ρ : SL3 F →* MulAut V) :
    (ρ.comp transposeInv).range = ρ.range := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨transposeInv g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨transposeInv g, by simp [transposeInv_transposeInv]⟩

theorem map_commOn_top_pmat [CharP F 2] (ρ : SL3 F →* MulAut V) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) :
    (G6.commOn ((rootGroup i j : Subgroup (SL3 F)).map ρ) ⊤).map (ρ (pmat σ)).toMonoidHom =
      G6.commOn ((rootGroup (σ i) (σ j) : Subgroup (SL3 F)).map ρ) ⊤ :=
  map_commOn_eq (rootGroup_conj_pmat σ i j).1 (rootGroup_conj_pmat σ i j).2
    (map_rho_eq_self (fun _ _ _ => Subgroup.mem_top _) _)

theorem map_commOn_top_rootElt (ρ : SL3 F →* MulAut V) (i j : Fin 3) (s : F) :
    (G6.commOn ((rootGroup i j : Subgroup (SL3 F)).map ρ) ⊤).map
        (ρ (rootElt i j s)).toMonoidHom =
      G6.commOn ((rootGroup i j : Subgroup (SL3 F)).map ρ) ⊤ := by
  refine map_commOn_eq ?_ ?_ (map_rho_eq_self (fun _ _ _ => Subgroup.mem_top _) _)
  · intro x hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rootElt_mem_rootGroup i j s) hx)
      (Subgroup.inv_mem _ (rootElt_mem_rootGroup i j s))
  · intro x hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (rootElt_mem_rootGroup i j s)) hx) (rootElt_mem_rootGroup i j s)

theorem commOn_rootGroup_eq_of_caseD [CharP F 2] (ρ : SL3 F →* MulAut V)
    (hD : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤ =
      G6.commOn ((rootGroup 1 2 : Subgroup (SL3 F)).map ρ) ⊤)
    (hD' : G6.commOn ((rootGroup 2 0 : Subgroup (SL3 F)).map ρ) ⊤ =
      G6.commOn ((rootGroup 2 1 : Subgroup (SL3 F)).map ρ) ⊤)
    (i j : Fin 3) (hij : i ≠ j) :
    G6.commOn ((rootGroup i j : Subgroup (SL3 F)).map ρ) ⊤ =
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤ := by
  set c := fun i j : Fin 3 => G6.commOn ((rootGroup i j : Subgroup (SL3 F)).map ρ) ⊤ with hc
  have hDσ : ∀ σ : Equiv.Perm (Fin 3), c (σ 0) (σ 2) = c (σ 1) (σ 2) := fun σ => by
    simp only [hc]
    rw [← map_commOn_top_pmat, ← map_commOn_top_pmat]
    exact congrArg (fun A => A.map (ρ (pmat σ)).toMonoidHom) hD
  have hD'σ : ∀ σ : Equiv.Perm (Fin 3), c (σ 2) (σ 0) = c (σ 2) (σ 1) := fun σ => by
    simp only [hc]
    rw [← map_commOn_top_pmat, ← map_commOn_top_pmat]
    exact congrArg (fun A => A.map (ρ (pmat σ)).toMonoidHom) hD'
  have e1 : c 1 2 = c 1 0 := by
    have := hD'σ (Equiv.swap 0 2 * Equiv.swap 1 2)
    simpa [Equiv.swap_apply_of_ne_of_ne] using this
  have e2 : c 1 0 = c 2 0 := by
    have := hDσ (Equiv.swap 0 1 * Equiv.swap 1 2)
    simpa [Equiv.swap_apply_of_ne_of_ne] using this
  have e4 : c 2 1 = c 0 1 := by
    have := hDσ (Equiv.swap 0 2 * Equiv.swap 1 2)
    simpa [Equiv.swap_apply_of_ne_of_ne] using this
  have hD₁ : c 0 2 = c 1 2 := hD
  have hD'₁ : c 2 0 = c 2 1 := hD'
  change c i j = c 0 2
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change c 0 1 = c 0 2; rw [← e4, ← hD'₁, ← e2, ← e1, ← hD₁]
  · rfl
  · change c 1 0 = c 0 2; rw [← e1, ← hD₁]
  · exact absurd rfl hij
  · change c 1 2 = c 0 2; rw [← hD₁]
  · change c 2 0 = c 0 2; rw [← e2, ← e1, ← hD₁]
  · change c 2 1 = c 0 2; rw [← hD'₁, ← e2, ← e1, ← hD₁]
  · exact absurd rfl hij

theorem rho_eq_of_caseD_caseD [CharP F 2] [Finite F] [Finite V] (ρ : SL3 F →* MulAut V)
    (hD : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤ =
      G6.commOn ((rootGroup 1 2 : Subgroup (SL3 F)).map ρ) ⊤)
    (hD' : G6.commOn ((rootGroup 2 0 : Subgroup (SL3 F)).map ρ) ⊤ =
      G6.commOn ((rootGroup 2 1 : Subgroup (SL3 F)).map ρ) ⊤)
    (hZ : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤) ≤ Nat.card F)
    (g : SL3 F) (v : V) : ρ g v = v := by
  set Z := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤ with hZdef
  have hall := commOn_rootGroup_eq_of_caseD ρ hD hD'
  have hM := map_eq_of_rootElt (ρ := ρ) (S := Z) fun i j c hij => le_of_eq (by
    rw [hZdef, ← hall i j hij, map_commOn_top_rootElt])
  have hZinv : ∀ g : SL3 F, ∀ z ∈ Z, ρ g z ∈ Z := fun g z hz => by
    rw [← hM g]
    exact rho_mem_map_rho g hz
  have hC : commV ρ.range ≤ Z := commV_le_of_rootElt02 ρ Z hZinv fun c v =>
    G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootElt_mem_rootGroup 0 2 c, rfl⟩)
      (Subgroup.mem_top v)
  have h02 : ∀ c : F, ∀ z ∈ Z, ρ (rootElt 0 2 c) z = z := fun c z hz =>
    rootElt_apply_eq_of_card_le ρ Z hZ (fun c z hz => hZinv _ z hz) (fun c c' hc hc' => by
      refine ⟨tor 1 (c' * c⁻¹) one_ne_zero (mul_ne_zero hc' (inv_ne_zero hc)), ?_,
        fun z hz => hZinv _ z hz⟩
      rw [tor_conj_rootElt]
      simp [mul_assoc, inv_mul_cancel₀ hc]) c hz
  have hfixer : fixer ρ Z = ⊤ := by
    refine eq_top_of_rootElt_mem fun i j c hij => ?_
    obtain ⟨σ, hσ0, hσ2⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
      revert i j; decide
    intro z hz
    have he : rootElt i j c = pmat σ * rootElt 0 2 c * (pmat σ)⁻¹ := by
      rw [pmat_conj_rootElt, hσ0, hσ2]
    rw [he, rho_mul, rho_mul, h02 c _ (hZinv _ z hz), rho_rho_inv]
  exact fix_of_comm_fix ρ v (fun g k =>
    (hfixer ▸ Subgroup.mem_top g : g ∈ fixer ρ Z) _ (hC (comm_mem_commV ρ k v))) g

theorem p02_mulVec_e0_apply2 [CharP F 2] :
    (((p02 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 := by
  rw [p02_mulVec]
  simp

theorem core [CharP F 2] [Finite F] [Finite V] {ρ : SL3 F →* MulAut V} {W₀ : Subgroup V}
    (hV : ∀ v : V, v ^ 2 = 1) (hVne : (⊤ : Subgroup V) ≠ ⊥) (hfixV : fixV ρ.range = ⊥)
    (hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀)
    (hgen : G6.submoduleClosure ρ.range W₀ = ⊤)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
      Nat.card F) :
    wOff ρ W₀ = ⊤ ∧ commV ρ.range = ⊤ ∧
      ∃ (dual : Bool) (β : ↥(commV ρ.range) ≃* Multiplicative (Fin 3 → F)),
        ∀ (g : SL3 F) (v w : ↥(commV ρ.range)), (w : V) = ρ g v →
          Multiplicative.toAdd (β w) =
            (if dual then dualMat g else ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
              Multiplicative.toAdd (β v) := by
  by_cases hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)).map (ρ p01).toMonoidHom
  · obtain ⟨hW, hC, β, hβ⟩ := core_caseN hV hVne hfixV hW₀ hgen hR hN
    exact ⟨hW, hC, false, β, fun g v w hvw => by simpa using hβ g v w hvw⟩
  push Not at hN
  have hW := wOff_eq_top_of_caseD hW₀ hR hgen hN
  set ρ' := ρ.comp transposeInv with hρ'
  have hrange : ρ'.range = ρ.range := range_comp_transposeInv ρ
  have hfixV' : fixV ρ'.range = ⊥ := by rw [hrange]; exact hfixV
  have hgen' : G6.submoduleClosure ρ'.range (⊤ : Subgroup V) = ⊤ :=
    eq_top_iff.mpr (le_submoduleClosure ⊤)
  have hW' : wOff ρ' (⊤ : Subgroup V) = ⊤ := by
    refine eq_top_iff.mpr ?_
    calc (⊤ : Subgroup V) = (⊤ : Subgroup V).map (ρ' p02).toMonoidHom :=
          (map_rho_eq_self (fun _ _ _ => Subgroup.mem_top _) _).symm
      _ ≤ wOff ρ' ⊤ := le_iSup₂_of_le p02 p02_mulVec_e0_apply2 le_rfl
  have hX : ∀ i j : Fin 3, (rootGroup i j : Subgroup (SL3 F)).map ρ' =
      (rootGroup j i : Subgroup (SL3 F)).map ρ := fun i j => by
    rw [hρ', ← Subgroup.map_map, map_transposeInv_rootGroup]
  have hZ : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤) ≤
      Nat.card F := by
    rw [← hW]; exact hR
  have hR' : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ') (wOff ρ' ⊤)) ≤
      Nat.card F := by
    have h := map_commOn_top_pmat ρ (Equiv.swap 0 2) 0 2
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h
    rw [hW', hX, ← h, Subgroup.card_map_of_injective (ρ _).injective]
    exact hZ
  by_cases hN' : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ') (wOff ρ' ⊤) ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ') (wOff ρ' ⊤)).map
        (ρ' p01).toMonoidHom
  · obtain ⟨-, hC', β', hβ'⟩ := core_caseN hV hVne hfixV'
      (fun _ _ _ _ => Subgroup.mem_top _) hgen' hR' hN'
    have hCC : commV ρ.range = commV ρ'.range := by rw [hrange]
    refine ⟨hW, hCC.trans hC', true, (MulEquiv.subgroupCongr hCC).trans β', fun g v w hvw => ?_⟩
    have h := hβ' (transposeInv g) ((MulEquiv.subgroupCongr hCC) v)
      ((MulEquiv.subgroupCongr hCC) w) (by
        change (w : V) = ρ (transposeInv (transposeInv g)) v
        rw [transposeInv_transposeInv]
        exact hvw)
    simp only [MulEquiv.trans_apply, ↓reduceIte]
    rw [h, coe_transposeInv]
  · push Not at hN'
    exfalso
    apply hVne
    have hDρ : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ⊤ =
        G6.commOn ((rootGroup 1 2 : Subgroup (SL3 F)).map ρ) ⊤ := by
      have h := hN
      rw [hW, p01, map_commOn_top_pmat ρ (Equiv.swap 0 1) 0 2, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
      exact h
    have hD'ρ : G6.commOn ((rootGroup 2 0 : Subgroup (SL3 F)).map ρ) ⊤ =
        G6.commOn ((rootGroup 2 1 : Subgroup (SL3 F)).map ρ) ⊤ := by
      have h := hN'
      rw [hW', hX, hρ', MonoidHom.comp_apply, p01, transposeInv_pmat,
        map_commOn_top_pmat ρ (Equiv.swap 0 1) 2 0, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
      exact h
    rw [eq_bot_iff, ← hfixV]
    intro v _
    rw [mem_fixV_range]
    intro g
    exact rho_eq_of_caseD_caseD ρ hDρ hD'ρ hZ g v

end CFSG.Quasithin.MS93.M16

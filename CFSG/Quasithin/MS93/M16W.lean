module

public import CFSG.Quasithin.MS93.M16Ind

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem cyc_apply20 : ((cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  rw [coe_cyc]
  simp

theorem apply20_eq (A : SL3 F) :
    ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 =
      (((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 := by
  rw [mulVec_e0]

section W

variable [CharP F 2] {ρ : SL3 F →* MulAut V} {W₀ : Subgroup V} [Finite F] [Finite V]
  (hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀)
  (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
    Nat.card F)
include hW₀ hR

omit [Finite F] [Finite V] hR [CharP F 2] in
theorem wOff_inv : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ wOff ρ W₀, ρ g v ∈ wOff ρ W₀ :=
  fun _ hg _ hv => rho_mem_wOff hW₀ hg hv

theorem map_R_le_wOff {g : SL3 F} (hg : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)).map
      (ρ g).toMonoidHom ≤ wOff ρ W₀ := by
  set G := ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) with hG
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : F, G 2 1 * p₁ + G 2 2 ≠ 0 := by
    by_cases h22 : G 2 2 = 0
    · refine ⟨1, ?_⟩
      have hdet := g.2
      rw [Matrix.det_fin_three] at hdet
      intro h
      rw [h22, add_zero, mul_one] at h
      change G 0 0 * G 1 1 * G 2 2 - G 0 0 * G 1 2 * G 2 1 - G 0 1 * G 1 0 * G 2 2 +
        G 0 1 * G 1 2 * G 2 0 + G 0 2 * G 1 0 * G 2 1 - G 0 2 * G 1 1 * G 2 0 = 1 at hdet
      rw [hg, h, h22] at hdet
      simp at hdet
    · exact ⟨0, by simpa using h22⟩
  set p : Fin 3 → F := ![0, p₁, 1] with hp
  have hp2 : p 2 ≠ 0 := by simp [hp]
  have hgp : ∀ c : F, (G *ᵥ (((rootElt 0 2 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p)) 2 ≠ 0 ∧
      (G *ᵥ p) 2 ≠ 0 := by
    intro c
    rw [rootElt02_mulVec]
    constructor <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp, hg] using hp₁
  rw [map_rho_le_iff]
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨t, ht, rfl⟩, w, hw, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := ht
    obtain ⟨a, ha, d, hd, rfl⟩ := Subgroup.mem_sup.mp (le_pt_sup_commOn hW₀ hp2 hw)
    have hdfix : ρ (rootElt 0 2 c) d = d :=
      qLn_fix_commOnU (wOff_inv hW₀) hR (rootGroup_le_qLn (rootElt_mem_rootGroup 0 2 c)) hd
    have he : ρ g (ρ (rootElt 0 2 c) (a * d) * (a * d)⁻¹) =
        ρ g (ρ (rootElt 0 2 c) a) * (ρ g a)⁻¹ := by
      rw [map_mul (ρ (rootElt 0 2 c)), hdfix, map_mul (ρ g), map_inv (ρ g), map_mul (ρ g),
        map_mul (ρ g), _root_.mul_inv_rev]
      group
    change ρ g (ρ (rootElt 0 2 c) (a * d) * (a * d)⁻¹) ∈ wOff ρ W₀
    rw [he]
    refine Subgroup.mul_mem _ (pt_le_wOff (hgp c).1 ?_) (Subgroup.inv_mem _
      (pt_le_wOff (hgp c).2 (rho_mem_pt hW₀ g ha)))
    exact rho_mem_pt hW₀ g (rho_mem_pt hW₀ _ ha)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem cyc_mem_wOff {r : V}
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) :
    ρ cyc r ∈ wOff ρ W₀ :=
  map_R_le_wOff hW₀ hR cyc_apply20 (rho_mem_map_rho cyc hr)

omit hR [Finite F] [Finite V] in
theorem commV_eq_closure_R (hgen : G6.submoduleClosure ρ.range W₀ = ⊤) :
    commV ρ.range = G6.submoduleClosure ρ.range
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) := by
  rw [commV_eq_closure hW₀ hgen, commU, commOnU_eq (wOff_inv hW₀),
    ← map_commOn02_p01 (wOff_inv hW₀)]
  refine le_antisymm ?_ (submoduleClosure_le_iff.mpr fun g => (map_le_submoduleClosure _ g).trans
    (iSup₂_mono' fun x hx => ⟨x, hx, Subgroup.map_mono le_sup_left⟩))
  rw [submoduleClosure_le_iff]
  intro g
  rw [Subgroup.map_sup, ← map_rho_mul]
  exact sup_le (map_le_submoduleClosure _ g) (map_le_submoduleClosure _ _)

theorem wOff_eq_top_of_caseD (hgen : G6.submoduleClosure ρ.range W₀ = ⊤)
    (hD : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) =
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)).map
        (ρ p01).toMonoidHom) :
    wOff ρ W₀ = ⊤ := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) with hRdef
  have h𝒲 := wOff_inv hW₀
  have hB01 : ∀ s : F, R.map (ρ (rootElt 0 1 s)).toMonoidHom = R := fun s =>
    map_commOn02_eq h𝒲 (rootElt_mem_ptStab (by decide) s) (rootElt_mem_lnStab (by decide) s)
  have h10 : ∀ s : F, R.map (ρ (rootElt 1 0 s)).toMonoidHom = R := fun s => by
    rw [rootElt10_eq, map_rho_mul, map_rho_mul, ← hD, hB01, ← hD]
  have hgW : ∀ g : SL3 F, R.map (ρ g).toMonoidHom ≤ wOff ρ W₀ := by
    intro g
    set G := ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) with hG
    by_cases h20 : G 2 0 = 0
    · exact map_R_le_wOff hW₀ hR h20
    by_cases h21 : G 2 1 = 0
    · have hgm : ((g * p01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
        rw [Matrix.SpecialLinearGroup.coe_mul, p01, Matrix.mul_apply, Fin.sum_univ_three]
        simp [coe_pmat_apply, ← hG, h21]
      have := map_R_le_wOff hW₀ hR hgm
      rwa [map_rho_mul, ← hD] at this
    · set s := G 2 0 / G 2 1 with hs
      have hgm : ((g * rootElt 1 0 s : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
        rw [apply20_eq, coe_mul_mulVec, rootElt_mulVec (by decide)]
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ← hG]
        simp [hs, mul_div_cancel₀ _ h21, CharTwo.add_self_eq_zero]
      have := map_R_le_wOff hW₀ hR hgm
      rwa [map_rho_mul, h10] at this
  have hC : commV ρ.range ≤ wOff ρ W₀ := by
    rw [commV_eq_closure_R hW₀ hgen, submoduleClosure_le_iff]
    exact hgW
  refine eq_top_iff.mpr ((top_le_pt_sup_commV hW₀ hgen (x := ![0, 0, 1]) (by simp)).trans
    (sup_le (pt_le_wOff (by simp)) hC))

end W

end CFSG.Quasithin.MS93.M16

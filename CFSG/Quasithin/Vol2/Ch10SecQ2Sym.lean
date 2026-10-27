module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Cls
public import CFSG.Quasithin.Vol2.Ch10SecERho
public import CFSG.Quasithin.Vol2.Ch10SecEE3Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] def eZeroTwo : Fin 5 → ZMod 2 := ![1, 0, 1, 0, 0]

theorem eZeroTwo_isEven : isEven eZeroTwo := by decide

theorem pr_eq_of_fix : ∀ b₀ b₁ : Bool, pact (pr b₀ b₁) eZeroTwo = eZeroTwo →
    b₀ = false ∧ b₁ = false := by
  decide

theorem rA_conj_sA : rA * sA * rA⁻¹ = sB := by decide

theorem sA_not_mem_alt : sA ∉ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem sB_not_mem_alt : sB ∉ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem sAsB_mem_alt : sA * sB ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem finset_eq_of_not_mem : ∀ ε : Finset (Fin 4), 0 ∉ ε → 1 ∉ ε → ε ≠ ∅ → ε ≠ {2, 3} →
    ε = {2} ∨ ε = {3} := by
  decide

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : Case2Data hyp t)

theorem mem_gam_cjSub_iff {g : G} (hg : g ∈ Subgroup.normalizer (fsuVM T L I : Set G))
    {i j : Fin 4} (hij : convI (SecA.isElemAbelian_fsuVM hyp) ⟨g, hg⟩ * D.tau i *
      (convI (SecA.isElemAbelian_fsuVM hyp) ⟨g, hg⟩)⁻¹ = D.tau j) (B : Subgroup G) :
    j ∈ gam D (cjSub g B) ↔ i ∈ gam D B := by
  rw [mem_gam, mem_gam, ← autI_cjSub _ hg B, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    ← hij]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem rho_conj_tau {ρ : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hρ : ρ = ((D.θ₁.symm rA : ↥D.K₁) : MulAut _)) : ρ * D.tau 0 * ρ⁻¹ = D.tau 1 := by
  rw [hρ, D.tau_zero, D.tau_one, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    ← map_inv, ← map_mul, ← map_mul, rA_conj_sA]

theorem tau_mem_autI_thompsonJ₁ {i : Fin 4} (hi : i = 0 ∨ i = 1) :
    D.tau i ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) := by
  rcases hi with rfl | rfl
  · exact ((D.memP₁ _ (D.θ₁.symm sA).2).mpr (by simpa using (by decide : sA ∈ eFour))).2
  · exact ((D.memP₁ _ (D.θ₁.symm sB).2).mpr (by simpa using (by decide : sB ∈ eFour))).2

theorem tau_not_mem_oTwoUpper₁ {i : Fin 4} (hi : i = 0 ∨ i = 1) : D.tau i ∉ oTwoUpper D.K₁ := by
  intro h
  have h1 := mem_alternatingGroup_of_mem_oTwoUpper D.θ₁ h
  rcases hi with rfl | rfl
  · rw [show (⟨D.tau 0, _⟩ : ↥D.K₁) = D.θ₁.symm sA from rfl, MulEquiv.apply_symm_apply] at h1
    exact sA_not_mem_alt h1
  · rw [show (⟨D.tau 1, _⟩ : ↥D.K₁) = D.θ₁.symm sB from rfl, MulEquiv.apply_symm_apply] at h1
    exact sB_not_mem_alt h1

theorem tau_ne_one₁ {i : Fin 4} (hi : i = 0 ∨ i = 1) : D.tau i ≠ 1 := fun h =>
  tau_not_mem_oTwoUpper₁ D hi (h ▸ (oTwoUpper D.K₁).one_mem)

theorem eq_false_of_fix {b₀ b₁ : Bool}
    (h : ∀ w ∈ commV D.K₁, ((D.θ₁.symm (pr b₀ b₁) : ↥D.K₁) : MulAut _) w = w) :
    b₀ = false ∧ b₁ = false := by
  refine pr_eq_of_fix b₀ b₁ ?_
  set u : ↥(commV D.K₁) := D.β₁.symm (Multiplicative.ofAdd ⟨eZeroTwo, eZeroTwo_isEven⟩)
  have h1 := crd_symm_apply D.equiv₁ (pr b₀ b₁) u
  have h2 : (⟨((D.θ₁.symm (pr b₀ b₁) : ↥D.K₁) : MulAut _) (u : _),
      commV_invariant D.K₁ _ (D.θ₁.symm (pr b₀ b₁)).2 _ u.2⟩ : ↥(commV D.K₁)) = u :=
    Subtype.ext (h u u.2)
  rw [h2, crd_symm_ofAdd] at h1
  exact h1.symm

omit [Finite G] in
theorem conj_mem_commutator_conjugate {s : G} (hs : s ∈ T) {x : G} (hx : x ∈ fsuUL T L I) :
    s⁻¹ * x * s ∈ ⁅fsuVM T L I, CFSG.conjugate L s⁆ := by
  have hVs : (fsuVM T L I).map (MulAut.conj s⁻¹).toMonoidHom = fsuVM T L I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.inv_mem _ (SecA.le_normalizer_fsuVM T L I hs))
  have h := Subgroup.map_commutator (fsuVM T L I) L (MulAut.conj s⁻¹).toMonoidHom
  rw [hVs] at h
  have hmem : s⁻¹ * x * s ∈ (⁅fsuVM T L I, L⁆ : Subgroup G).map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨x, hx, by simp⟩
  rw [h] at hmem
  exact hmem

theorem t_conj_tau (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {i : Fin 4} (hi : i = 0 ∨ i = 1) :
    ∃ j : Fin 4, (j = 2 ∨ j = 3) ∧
      convI (SecA.isElemAbelian_fsuVM hyp) ⟨t, SecA.le_normalizer_fsuVM T L I ht⟩ * D.tau i *
        (convI (SecA.isElemAbelian_fsuVM hyp) ⟨t, SecA.le_normalizer_fsuVM T L I ht⟩)⁻¹ =
          D.tau j := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  set tN : Subgroup.normalizer (fsuVM T L I : Set G) := ⟨t, SecA.le_normalizer_fsuVM T L I ht⟩
    with htN
  set c := convI hV tN with hc
  set x := c * D.tau i * c⁻¹ with hx
  have hxP : x ∈ D.P₁ ⊔ D.P₂ := by
    have h := conj_mem_autI_thompsonJ hyp (convI_mem_autI hV ht tN.2)
      (tau_mem_autI_thompsonJ₁ D hi)
    rw [D.thompsonJ_eq] at h
    exact h
  obtain ⟨ε, hε⟩ := D.exists_tauS hxP
  have hfixx : ∀ w ∈ commV D.K₁, x w = w := by
    intro w hw
    have hw2 : c⁻¹ w ∈ commV D.K₂ := by
      rw [D.mem_commV₂_iff ht]
      have e : (c⁻¹ w).val = t⁻¹ * w.val * t := by
        rw [hc, ← map_inv, convI_apply_val]
        simp [htN]
      rw [e]
      exact conj_mem_commutator_conjugate ht ((D.mem_commV₁_iff w).mp hw)
    rw [hx, MulAut.mul_apply, MulAut.mul_apply, D.triv₁ (tau_mem_K₁ D hi) hw2,
      MulAut.apply_inv_self]
  have hparts : decide (0 ∈ ε) = false ∧ decide (1 ∈ ε) = false := by
    refine eq_false_of_fix D fun w hw => ?_
    have h1 := hfixx w hw
    rw [← hε, Case2Data.tauS, MulAut.mul_apply, D.triv₂ (D.θ₂.symm _).2 hw] at h1
    exact h1
  have h0 : 0 ∉ ε := fun h => by simp [h] at hparts
  have h1 : 1 ∉ ε := fun h => by simp [h] at hparts
  have hne : ε ≠ ∅ := by
    rintro rfl
    rw [D.tauS_empty] at hε
    apply tau_ne_one₁ D hi
    calc D.tau i = c⁻¹ * (c * D.tau i * c⁻¹) * c := by group
      _ = 1 := by rw [← hx, ← hε]; group
  have hne23 : ε ≠ {2, 3} := by
    rintro rfl
    rw [D.tauS_pair23] at hε
    have hxO : x ∈ autI hV (CFSG.conjugate L t) := by
      rw [← D.oTwo₂, ← hε]
      exact symm_mem_oTwoUpper D.θ₂ sAsB_mem_alt
    have htiN : t⁻¹ ∈ Subgroup.normalizer (fsuVM T L I : Set G) := Subgroup.inv_mem _ tN.2
    have h2 := autI_cjSub hV htiN (CFSG.conjugate L t)
    have hL : cjSub t⁻¹ (CFSG.conjugate L t) = L := by
      change CFSG.conjugate (CFSG.conjugate L t) t = L
      rw [SecA.conjugate_conjugate, SecA.conjugate_eq_self_iff]
      exact SecA.mul_self_mem_normalizer h37 h38 hyp ht htn
    rw [hL] at h2
    have hτ : D.tau i ∈ autI hV L := by
      rw [← h2]
      refine Subgroup.mem_map.mpr ⟨x, hxO, ?_⟩
      have ec : convI hV ⟨t⁻¹, htiN⟩ = c⁻¹ := by rw [hc, ← map_inv]; rfl
      rw [MulEquiv.coe_toMonoidHom, ec, MulAut.conj_apply, hx]
      group
    exact tau_not_mem_oTwoUpper₁ D hi (D.oTwo₁ ▸ hτ)
  rcases finset_eq_of_not_mem ε h0 h1 hne hne23 with rfl | rfl
  · exact ⟨2, Or.inl rfl, by rw [← hε, D.tauS_singleton]⟩
  · exact ⟨3, Or.inr rfl, by rw [← hε, D.tauS_singleton]⟩

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

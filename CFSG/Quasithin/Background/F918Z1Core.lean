module

public import CFSG.Quasithin.Background.F918Z1AuxCob
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace D37Lift

variable {V Q F : Type*} [CommGroup V] [CommGroup Q] [Field F] {d r : ℕ}

@[expose] def pAdd (π : V →* Q) (β : Q ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) :
    Additive V →+ Matrix (Fin d) (Fin r) F :=
  AddMonoidHom.mk' (fun a => Multiplicative.toAdd (β (π (Additive.toMul a)))) (by
    intro a b
    simp)

theorem pAdd_apply (π : V →* Q) (β : Q ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (a : Additive V) : pAdd π β a = Multiplicative.toAdd (β (π (Additive.toMul a))) := rfl

@[expose] def actAdd (g : MulAut V) : Additive V →+ Additive V :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (g (Additive.toMul a))) (by
    intro a b
    simp)

theorem actAdd_apply (g : MulAut V) (a : Additive V) :
    actAdd g a = Additive.ofMul (g (Additive.toMul a)) := rfl

@[expose] def liftOfMatModel {D X : Subgroup (MulAut V)}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (π : V →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ fixV (D ⊔ X))
    (β : Q ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F)
    (hρ : ∀ (g : ↥D) (v : V), β (π ((g : MulAut V) v)) = Multiplicative.ofAdd
      (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        Multiplicative.toAdd (β (π v))))
    (hσ : ∀ (x : ↥X) (v : V), β (π ((x : MulAut V) v)) = Multiplicative.ofAdd
      (Multiplicative.toAdd (β (π v)) *
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ)) :
    LiftData ↥D ↥X (Additive V) F d r where
  p := pAdd π β
  ρ := ρ
  σ := σ
  ag g := actAdd (g : MulAut V)
  ax x := actAdd (x : MulAut V)
  p_surj := fun M => by
    obtain ⟨q, hq⟩ := β.surjective (Multiplicative.ofAdd M)
    obtain ⟨v, hv⟩ := hπ q
    exact ⟨Additive.ofMul v, by
      rw [pAdd_apply, toMul_ofMul, hv, hq, toAdd_ofAdd]⟩
  ag_ax := fun g x a => by
    simp only [actAdd_apply, toMul_ofMul]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm g g.2 x x.2]
  ag_fix := fun g a h => by
    have h1 : Additive.toMul a ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      rw [pAdd_apply] at h
      exact β.map_eq_one_iff.1 (by simpa using h)
    have h2 := hker h1 (g : MulAut V) (Subgroup.mem_sup_left g.2)
    rw [actAdd_apply, h2, ofMul_toMul]
  ax_fix := fun x a h => by
    have h1 : Additive.toMul a ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      rw [pAdd_apply] at h
      exact β.map_eq_one_iff.1 (by simpa using h)
    have h2 := hker h1 (x : MulAut V) (Subgroup.mem_sup_right x.2)
    rw [actAdd_apply, h2, ofMul_toMul]
  p_ag := fun g a => by
    rw [pAdd_apply, pAdd_apply, actAdd_apply, toMul_ofMul, hρ g, toAdd_ofAdd]
  p_ax := fun x a => by
    rw [pAdd_apply, pAdd_apply, actAdd_apply, toMul_ofMul, hσ x, toAdd_ofAdd]

end D37Lift

theorem ker_eq_bot_of_matModel {V Q : Type} [CommGroup V] [CommGroup Q]
    (hexp : ∀ v : V, v ^ 2 = 1) {D X : Subgroup (MulAut V)}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hV : commV (D ⊔ X) = ⊤)
    (π : V →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ fixV (D ⊔ X))
    {F : Type} [Field F] {d r : ℕ}
    (β : Q ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F)
    (hρ : ∀ (g : ↥D) (v : V), β (π ((g : MulAut V) v)) = Multiplicative.ofAdd
      (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        Multiplicative.toAdd (β (π v))))
    (hσ : ∀ (x : ↥X) (v : V), β (π ((x : MulAut V) v)) = Multiplicative.ofAdd
      (Multiplicative.toAdd (β (π v)) *
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ))
    (I_irr : ∀ W : AddSubgroup (Fin d → F),
      (∀ (g : ↥D), ∀ w ∈ W, ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    (U_irr : ∀ W : Submodule F (Fin r → F),
      (∀ (x : ↥X), ∀ w ∈ W, ((σ x : Matrix.GeneralLinearGroup (Fin r) F) :
        Matrix (Fin r) (Fin r) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hρnt : ∃ g, ρ g ≠ 1) (hσnt : ∃ x, σ x ≠ 1) :
    π.ker = ⊥ := by
  let E := D37Lift.liftOfMatModel hcomm π hπ hker β ρ σ hρ hσ
  have hA : ∀ a : Additive V, a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact hexp _
  obtain ⟨s, hs, hsg, hsx⟩ := E.exists_equivariant hA I_irr U_irr hρnt hσnt
  let K : Subgroup V :=
    { carrier := {v | ∃ M, s M = Additive.ofMul v}
      one_mem' := ⟨0, by rw [map_zero]; rfl⟩
      mul_mem' := by
        rintro _ _ ⟨M, hM⟩ ⟨N, hN⟩
        exact ⟨M + N, by rw [map_add, hM, hN]; rfl⟩
      inv_mem' := by
        rintro _ ⟨M, hM⟩
        exact ⟨-M, by rw [map_neg, hM]; rfl⟩ }
  have hKD : ∀ g ∈ D, ∀ k ∈ K, g k ∈ K := by
    rintro g hg k ⟨M, hM⟩
    refine ⟨(ρ ⟨g, hg⟩ : Matrix (Fin d) (Fin d) F) * M, ?_⟩
    have h := hsg ⟨g, hg⟩ M
    rw [hM] at h
    exact h.symm
  have hKX : ∀ x ∈ X, ∀ k ∈ K, x k ∈ K := by
    rintro x hx k ⟨M, hM⟩
    refine ⟨M * ((σ ⟨x, hx⟩ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ,
      ?_⟩
    have h := hsx ⟨x, hx⟩ M
    rw [hM] at h
    exact h.symm
  have hst : ∀ H : Subgroup (MulAut V), (∀ g ∈ H, ∀ k ∈ K, g k ∈ K) → H ≤ stabSub K := by
    intro H hH g hg u
    refine ⟨fun h => ?_, hH g hg u⟩
    have h' := hH g⁻¹ (H.inv_mem hg) _ h
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h'
  have hKinv : ∀ m ∈ D ⊔ X, ∀ k ∈ K, m k ∈ K :=
    fun m hm k hk => ((mem_stabSub.1 (sup_le (hst D hKD) (hst X hKX) hm)) k).2 hk
  have hKker : ∀ k ∈ K, π k = 1 → k = 1 := by
    rintro k ⟨M, hM⟩ h1
    have h0 : M = 0 := by
      have h2 : D37Lift.pAdd π β (s M) = M := hs M
      rw [hM, D37Lift.pAdd_apply, toMul_ofMul, h1, map_one, toAdd_one] at h2
      exact h2.symm
    rw [h0, map_zero] at hM
    exact Additive.ofMul.injective hM.symm
  have hKdec : ∀ v : V, ∃ k ∈ K, π (v * k⁻¹) = 1 := by
    intro v
    refine ⟨Additive.toMul (s (D37Lift.pAdd π β (Additive.ofMul v))),
      ⟨D37Lift.pAdd π β (Additive.ofMul v), ofMul_toMul _⟩, ?_⟩
    have h2 : D37Lift.pAdd π β (s (D37Lift.pAdd π β (Additive.ofMul v))) =
        D37Lift.pAdd π β (Additive.ofMul v) := hs _
    rw [D37Lift.pAdd_apply, D37Lift.pAdd_apply, toMul_ofMul] at h2
    have h3 : π (Additive.toMul (s (D37Lift.pAdd π β (Additive.ofMul v)))) = π v :=
      β.injective (Multiplicative.toAdd.injective h2)
    rw [map_mul, map_inv, h3, mul_inv_cancel]
  have hcommK : commV (D ⊔ X) ≤ K := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨m, hm, v, rfl⟩
    obtain ⟨k, hk, hkπ⟩ := hKdec v
    have hc : v * k⁻¹ ∈ fixV (D ⊔ X) := hker (MonoidHom.mem_ker.2 hkπ)
    have hmc : m v / m k = v / k := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← map_inv, ← map_mul]
      exact hc m hm
    have h4 : m v * v⁻¹ = m k * k⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv]
      exact div_eq_div_iff_div_eq_div.1 hmc
    rw [h4]
    exact K.mul_mem (hKinv m hm k hk) (K.inv_mem hk)
  have hKtop : K = ⊤ := top_le_iff.1 (hV ▸ hcommK)
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  exact hKker c (by rw [hKtop]; trivial) (MonoidHom.mem_ker.1 hc)

end CFSG.Quasithin

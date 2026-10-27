module

public import CFSG.Quasithin.Background.SmithB45MatIndM23Amal
public import CFSG.Quasithin.Background.SmithB45MatIndRealize
public import CFSG.Quasithin.Background.SmithB45MatIndM23Frob

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H Module

theorem forall_of_gens23
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) ↥mog23 X) {n : ℕ}
    (R : ↥mog23 →* MulAut (Multiplicative (Fin n → ZMod 2))) (Ψ : Vec n ≃ₗ[ZMod 2] X)
    (h : ∀ z s, Ψ (Matrix.toLin' (mulAutMat n (R (m23g z))) s) = ρ (m23g z) (Ψ s)) :
    ∀ g s, Ψ (Matrix.toLin' (mulAutMat n (R g)) s) = ρ g (Ψ s) := by
  have : Finite ↥mog23 := Subgroup.instFiniteSubtypeMem mog23
  refine forall_of_closure closure_m23g (fun g => ∀ s, Ψ (Matrix.toLin' (mulAutMat n (R g)) s) =
    ρ g (Ψ s)) (fun s => ?_) (fun s ⟨z, hz⟩ => hz ▸ h z) (fun g g' hg hg' s => ?_)
  · rw [map_one, map_one, Matrix.toLin'_one, map_one, LinearMap.id_apply, Module.End.one_apply]
  · rw [map_mul, map_mul, Matrix.toLin'_mul, LinearMap.comp_apply, hg,
      hg', map_mul, Module.End.mul_apply]

theorem m23_conclude
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] (ρ : Representation (ZMod 2) ↥mog23 X)
    (hdim : finrank (ZMod 2) X ≤ 36) {t d : ℕ} (ht : t < 6) (hd : d = m23Dim t)
    (Ψ : Vec d ≃ₗ[ZMod 2] X) (hΨ : ∀ z s, Ψ (lin d (m23Std t z) s) = ρ (m23g z) (Ψ s)) :
    (∀ g v, ρ g v = v) ∨
      (∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left g)) v) = ρ g (e v)) ∨
      ∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left g)) v) = ρ g (e v) := by
  have hfin := Ψ.finrank_eq
  rw [Module.finrank_fin_fun] at hfin
  interval_cases t
  · have hd' : d = 1 := hd
    subst hd'
    left
    have : Finite ↥mog23 := Subgroup.instFiniteSubtypeMem mog23
    have hgen : ∀ z v, ρ (m23g z) v = v := by
      intro z v
      obtain ⟨s, rfl⟩ := Ψ.surjective v
      rw [← hΨ, lin_m23Std_one, LinearMap.id_apply]
    exact forall_of_closure closure_m23g (fun g => ∀ v, ρ g v = v)
      (fun v => by rw [map_one, Module.End.one_apply]) (fun s ⟨z, hz⟩ => hz ▸ hgen z)
      (fun g g' hg hg' v => by rw [map_mul, Module.End.mul_apply, hg', hg])
  · have hd' : d = 11 := hd
    subst hd'
    right
    left
    refine ⟨Ψ, forall_of_gens23 ρ _ Ψ fun z s => ?_⟩
    rw [← lin_m23Std_code]
    exact hΨ z s
  · have hd' : d = 11 := hd
    subst hd'
    right
    right
    refine ⟨Ψ, forall_of_gens23 ρ _ Ψ fun z s => ?_⟩
    rw [← lin_m23Std_cocode]
    exact hΨ z s
  all_goals
    exfalso
    rw [hd] at hfin
    simp only [m23Dim] at hfin
    norm_num at hfin
    omega

theorem m23_hψ
    {X : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) ↥mog23 X) {d : ℕ}
    (M : G22 →* Matrix (Fin d) (Fin d) (ZMod 2)) (ψ : Vec d →ₗ[ZMod 2] X)
    (hψ : ∀ g v, ψ (Matrix.toLin' (M g) v) = ρ (iota22 g) (ψ v)) (cols : Bool → ℕ → List ℕ)
    (hcols : ∀ z k (hk : k < 23),
      lin d (cols z k) = Matrix.toLin' (M (mog22EquivM22 ⟨_, m23h_mem z hk⟩))) :
    ∀ z, ∀ k < 23, ∀ v, ψ (lin d (cols z k) v) = ρ (m23h z k) (ψ v) := by
  intro z k hk v
  rw [hcols z k hk, hψ]
  congr 2
  refine Subtype.ext ?_
  change ((psiS22 (mog22EquivM22 ⟨_, m23h_mem z hk⟩) : ↥mog22) : Equiv.Perm (Fin 24)) = _
  rw [psiS22, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem lin_m23Xcol_cocode
    (z : Bool) {k : ℕ}
    (hk : k < 23) :
    lin 10 (m23Xcol 2 z k) = Matrix.toLin' (rep10a (mog22EquivM22 ⟨_, m23h_mem z hk⟩)) := by
  rw [rep10a_apply, psiS22, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact lin_matOf_eq fun m => rho10_toW mog22 mog22_le_mog22plus ⟨_, m23h_mem z hk⟩
    (hasArr_m23h z hk) m

theorem lin_m23Xcol_code
    (z : Bool) {k : ℕ}
    (hk : k < 23) :
    lin 10 (m23Xcol 1 z k) = Matrix.toLin' (rep10b (mog22EquivM22 ⟨_, m23h_mem z hk⟩)) := by
  rw [rep10b_apply, psiS22, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact lin_matOf_eq fun m => rhoC10_toW mog22 mog22_le_mog22plus ⟨_, m23h_mem z hk⟩
    (hasArr_m23h z hk) m

theorem lin_m23Xcol_one
    (z : Bool) (k : ℕ) (g : G22) : lin 1 (m23Xcol 0 z k) = Matrix.toLin' (rep1 g) := by
  rw [show rep1 g = 1 from rfl, Matrix.toLin'_one]
  exact lin_eq_id fun j hj => by
    have : j = 0 := by omega
    subst this
    rfl

theorem m23_binary_small36
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) ↥mog23 X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hne : Nontrivial X) (hdim : finrank (ZMod 2) X ≤ 36) :
    (∀ g v, ρ g v = v) ∨
      (∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left g)) v) = ρ g (e v)) ∨
      ∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left g)) v) = ρ g (e v) := by
  have : FiniteDimensional (ZMod 2) X := Module.Finite.of_finite
  obtain ⟨Y, hY0, hYirr⟩ := exists_isIrreducible_subrepresentation (ρ.comp iota22)
  have hYdim : finrank (ZMod 2) Y.toSubmodule ≤ 36 := (Submodule.finrank_le _).trans hdim
  obtain ⟨i, ⟨e⟩⟩ := m22_binary_small36 Y.toSubmodule Y.toRepresentation hYirr hYdim
  let ψ : Vec (m22Dim4 i) →ₗ[ZMod 2] X :=
    Y.toSubmodule.subtype ∘ₗ e.symm.toLinearEquiv.toLinearMap
  have hψ : ∀ g v, ψ (Matrix.toLin' (m22Rep4 i g) v) = ρ (iota22 g) (ψ v) := by
    intro g v
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g v
    change e.symm (matrixBaseChange (RingHom.id (ZMod 2)) (m22Rep4 i) g v) =
      Y.toRepresentation g (e.symm v) at h1
    rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id] at h1
    change ((e.symm (Matrix.toLin' (m22Rep4 i g) v) : Y.toSubmodule) : X) =
      ρ (iota22 g) ((e.symm v : Y.toSubmodule) : X)
    rw [Matrix.toLin'_apply, h1]
    rfl
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hY0
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
    have h1 := LinearMap.congr_fun h (e ⟨y, hy⟩)
    change ((e.symm (e ⟨y, hy⟩) : Y.toSubmodule) : X) = 0 at h1
    rw [Representation.Equiv.symm_apply_apply] at h1
    exact (Submodule.mem_bot (ZMod 2)).2 h1
  fin_cases i
  · obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m23_exists_std ρ hirr hne (i := 0) (by norm_num) ψ hψ0
      (m23_hψ ρ rep1 ψ hψ _ fun z k _ => lin_m23Xcol_one z k _)
    exact m23_conclude ρ hdim ht hd Ψ hΨ
  · obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m23_exists_std ρ hirr hne (i := 2) (by norm_num) ψ hψ0
      (m23_hψ ρ rep10a ψ hψ _ fun z k hk => lin_m23Xcol_cocode z hk)
    exact m23_conclude ρ hdim ht hd Ψ hΨ
  · obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m23_exists_std ρ hirr hne (i := 1) (by norm_num) ψ hψ0
      (m23_hψ ρ rep10b ψ hψ _ fun z k hk => lin_m23Xcol_code z hk)
    exact m23_conclude ρ hdim ht hd Ψ hΨ
  · exact (m23_not34 ρ hirr hdim Y e).elim

theorem code23_rhoC11 : MathieuCode23 (rhoC11 mog23 inf_le_left).range ⊤ ⊥ :=
  ⟨0, CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords codeCoords (Γ := mog23)
    (fun _ hσ => preserves_code hσ.1) (Subgroup.zpowers_le.mpr allOnes_mem_golayC)⟩

theorem cocode23_rho11 : MathieuCocode23 (rho11 mog23 inf_le_left).range ⊤ ⊥ :=
  ⟨0, CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords cocodeCoords (Γ := mog23)
    (fun _ hσ => preserves_cocode hσ.1) golayC_le_coreMod⟩

end CFSG.Quasithin.B45Mat.Ind

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Setup.X3E CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H B45Mat B45Mat.M22 B45Mat.Ind Module Matrix

theorem mathieuSmallIrr23_holds :
    MathieuSmallIrr23 := by
  intro W _ _ hW2 L hLiso hirr hcard
  obtain ⟨θ0⟩ := hLiso
  have hV : ∀ w : W, w ^ 2 = 1 := fun w => by
    rw [sq]
    exact hW2 w
  let θ : ↥L ≃* ↥mog23 := (θ0 : ↥L ≃* ↥NativeSporadic.M23).trans mog23EquivM23.symm
  have hcardG : Nat.card ↥mog23 = 10200960 := card_mog23
  have hntW : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have : Subsingleton ↥L :=
      ⟨fun x y => Subtype.ext (MulEquiv.ext fun w => Subsingleton.elim _ _)⟩
    have h1 := Nat.card_congr θ.toEquiv
    rw [hcardG, Nat.card_of_subsingleton (1 : ↥L)] at h1
    norm_num at h1
  have : Nontrivial (F2Vec W hV) := inferInstanceAs (Nontrivial (Additive W))
  have : Finite (F2Vec W hV) := inferInstanceAs (Finite (Additive W))
  rcases m23_binary_small36 (autRepOfG hV θ) (irr_autRepOfG hV θ hirr) inferInstance
      ((finrank_autRepOfG_le hV hcard).trans (by norm_num)) with htriv | ⟨e, he⟩ | ⟨e, he⟩
  · exfalso
    have htriv' : ∀ g : ↥mog23, g = 1 := by
      intro g
      have h1 : θ.symm g = 1 := by
        refine Subtype.ext (MulEquiv.ext fun w => ?_)
        have h2 := htriv g (F2Vec.ofV hV w)
        rw [autRepOfG_apply] at h2
        exact h2
      exact θ.symm.injective (h1.trans (map_one θ.symm).symm)
    have : Subsingleton ↥mog23 := ⟨fun x y => (htriv' x).trans (htriv' y).symm⟩
    rw [Nat.card_of_subsingleton (1 : ↥mog23)] at hcardG
    norm_num at hcardG
  · left
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range' hV θ (rhoC11 mog23 inf_le_left) e.symm
      fun g v => by
        have h1 := he g (e.symm v)
        rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] at h1
        rw [← autRepOfG_apply, ← h1, LinearEquiv.symm_apply_apply]
    obtain ⟨x, hx⟩ := code23_rhoC11
    exact ⟨x, realizes_of_map_congrHom φ hφ hx⟩
  · right
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range' hV θ (rho11 mog23 inf_le_left) e.symm
      fun g v => by
        have h1 := he g (e.symm v)
        rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] at h1
        rw [← autRepOfG_apply, ← h1, LinearEquiv.symm_apply_apply]
    obtain ⟨x, hx⟩ := cocode23_rho11
    exact ⟨x, realizes_of_map_congrHom φ hφ hx⟩

end CFSG.Quasithin

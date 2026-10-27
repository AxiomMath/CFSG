module

public import CFSG.Quasithin.Background.SmithB45MatIndM24Gen
public import CFSG.Quasithin.Background.SmithB45MatIndM23

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H
  CFSG.Monster.Code Module

@[expose] def m24Xcol (i : ℕ) (z : Bool) (k : ℕ) : List ℕ :=
  matOf (m24Xd i) (m24Xc i (m24hArr z k))

theorem m24Xd_pos (i : ℕ) : 0 < m24Xd i := by
  unfold m24Xd
  split_ifs <;> norm_num

theorem m24K_eq (i : ℕ) (z : Bool) :
    m24K i z = indColsG 24 (m24Xd i) (m24pi z) (m24Xcol i z) := by
  unfold m24K indCols indColsG m24Xcol m24pi m24hArr
  rw [m24Ts_size]
  refine List.map_congr_left fun j _ => ?_
  rw [matOf, getD_map_range _ _ (Nat.mod_lt _ (m24Xd_pos i)), Nat.one_shiftLeft]

theorem m24Xcol_lt (i : ℕ) (z : Bool) (k : ℕ) :
    ∀ c < m24Xd i, (m24Xcol i z k).getD c 0 < 2 ^ m24Xd i := by
  intro c hc
  rw [m24Xcol, matOf, getD_map_range _ _ hc]
  unfold m24Xd m24Xc
  split_ifs with h0 h1
  · norm_num
  · exact actC11_lt _ _
  · exact act11_lt _ _

theorem m24Ns_zero : m24Ns 0 = [0, 1, 12, 23, 24] := rfl

theorem m24Ns_one : m24Ns 1 = [0, 11, 55, 66, 77, 121, 132, 252, 253, 264] := rfl

theorem m24Ns_two : m24Ns 2 = [0, 11, 131, 132, 143, 187, 198, 209, 253, 264] := rfl

theorem m24Typs_zero : m24Typs 0 = [0, 1, 2, 0] := rfl

theorem m24Typs_one : m24Typs 1 = [1, 3, 2, 1, 3, 2, 5, 0, 1] := rfl

theorem m24Typs_two : m24Typs 2 = [2, 5, 0, 1, 4, 2, 1, 4, 2] := rfl

theorem m24Ns_facts : ∀ i < 3, ∀ j < (m24Ns i).length - 1,
    (m24Ns i).getD (j + 1) 0 - (m24Ns i).getD j 0 = m24Dim ((m24Typs i).getD j 0) ∧
      (m24Typs i).getD j 0 < 6 := by
  intro i hi j hj
  interval_cases i
  · rw [m24Ns_zero] at hj ⊢
    rw [m24Typs_zero]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide
  · rw [m24Ns_one] at hj ⊢
    rw [m24Typs_one]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide
  · rw [m24Ns_two] at hj ⊢
    rw [m24Typs_two]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide

theorem m24_exists_std
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) ↥AutPerm X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hne : Nontrivial X) {i : ℕ} (hi : i < 3) (ψ : Vec (m24Xd i) →ₗ[ZMod 2] X) (hψ0 : ψ ≠ 0)
    (hψ : ∀ z, ∀ k < 24, ∀ v, ψ (lin (m24Xd i) (m24Xcol i z k) v) = ρ (m24h z k) (ψ v)) :
    ∃ t < 6, ∃ d, d = m24Dim t ∧ ∃ Ψ : Vec d ≃ₗ[ZMod 2] X,
      ∀ z s, Ψ (lin d (m24Std t z) s) = ρ (m24g z) (Ψ s) := by
  have : Finite ↥AutPerm := Subgroup.instFiniteSubtypeMem AutPerm
  have hK : ∀ z v, indMap ρ 24 (m24Xd i) m24t ψ (lin (24 * m24Xd i) (m24K i z) v) =
      ρ (m24g z) (indMap ρ 24 (m24Xd i) m24t ψ v) := by
    intro z v
    rw [m24K_eq]
    refine indMap_lin ρ m24t ψ (fun k hk => m24pi_lt z hk) (fun k _ => m24Xcol_lt i z k)
      (fun k hk w => ?_) v
    rw [hψ z k hk w, ← Module.End.mul_apply, ← map_mul, m24_coset_rel, map_mul,
      Module.End.mul_apply]
  have hsurj := indMap_surjective ρ closure_m24g hirr m24t ψ hK hψ0 (by norm_num)
  have hflag : m24FlagOK i = true := by
    obtain ⟨-, h0, h1, h2⟩ := m24_ind_checks
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
  have hWne : (⊤ : Submodule (ZMod 2) X) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    exact hx ((Submodule.mem_bot (ZMod 2)).1 (h ▸ Submodule.mem_top))
  obtain ⟨j, hj, Ψ, hΨ⟩ := exists_iso_of_flagOK hflag
    (fun j hj => by
      rw [(m24Ns_facts i hi j hj).1]
      exact irredPair_m24Std (m24Ns_facts i hi j hj).2)
    (fun z => ρ (m24g z)) (irredPair_of_irr24 ρ hirr) hWne _ hsurj hK
  exact ⟨_, (m24Ns_facts i hi j hj).2, _, (m24Ns_facts i hi j hj).1, Ψ, hΨ⟩

theorem forall_of_gens24 {X : Type*} [AddCommGroup X]
    [Module (ZMod 2) X] (ρ : Representation (ZMod 2) ↥AutPerm X) {n : ℕ}
    (R : ↥AutPerm →* MulAut (Multiplicative (Fin n → ZMod 2))) (Ψ : Vec n ≃ₗ[ZMod 2] X)
    (h : ∀ z s, Ψ (Matrix.toLin' (mulAutMat n (R (m24g z))) s) = ρ (m24g z) (Ψ s)) :
    ∀ g s, Ψ (Matrix.toLin' (mulAutMat n (R g)) s) = ρ g (Ψ s) := by
  have : Finite ↥AutPerm := Subgroup.instFiniteSubtypeMem AutPerm
  refine forall_of_closure closure_m24g (fun g => ∀ s, Ψ (Matrix.toLin' (mulAutMat n (R g)) s) =
    ρ g (Ψ s)) (fun s => ?_) (fun s ⟨z, hz⟩ => hz ▸ h z) (fun g g' hg hg' s => ?_)
  · rw [map_one, map_one, Matrix.toLin'_one, map_one, LinearMap.id_apply, Module.End.one_apply]
  · rw [map_mul, map_mul, Matrix.toLin'_mul, LinearMap.comp_apply, hg, hg', map_mul,
      Module.End.mul_apply]

theorem m24_conclude {X : Type} [AddCommGroup X]
    [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X] (ρ : Representation (ZMod 2) ↥AutPerm X)
    (hdim : finrank (ZMod 2) X ≤ 36) {t d : ℕ} (ht : t < 6) (hd : d = m24Dim t)
    (Ψ : Vec d ≃ₗ[ZMod 2] X) (hΨ : ∀ z s, Ψ (lin d (m24Std t z) s) = ρ (m24g z) (Ψ s)) :
    (∀ g v, ρ g v = v) ∨
      (∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rhoC11 AutPerm le_rfl g)) v) = ρ g (e v)) ∨
      ∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rho11 AutPerm le_rfl g)) v) = ρ g (e v) := by
  have hfin := Ψ.finrank_eq
  rw [Module.finrank_fin_fun] at hfin
  interval_cases t
  · have hd' : d = 1 := hd
    subst hd'
    left
    have : Finite ↥AutPerm := Subgroup.instFiniteSubtypeMem AutPerm
    have hgen : ∀ z v, ρ (m24g z) v = v := by
      intro z v
      obtain ⟨s, rfl⟩ := Ψ.surjective v
      rw [← hΨ, lin_m24Std_one, LinearMap.id_apply]
    exact forall_of_closure closure_m24g (fun g => ∀ v, ρ g v = v)
      (fun v => by rw [map_one, Module.End.one_apply]) (fun s ⟨z, hz⟩ => hz ▸ hgen z)
      (fun g g' hg hg' v => by rw [map_mul, Module.End.mul_apply, hg', hg])
  · have hd' : d = 11 := hd
    subst hd'
    right
    left
    refine ⟨Ψ, forall_of_gens24 ρ _ Ψ fun z s => ?_⟩
    rw [← lin_m24Std_code]
    exact hΨ z s
  · have hd' : d = 11 := hd
    subst hd'
    right
    right
    refine ⟨Ψ, forall_of_gens24 ρ _ Ψ fun z s => ?_⟩
    rw [← lin_m24Std_cocode]
    exact hΨ z s
  all_goals
    exfalso
    rw [hd] at hfin
    simp only [m24Dim] at hfin
    norm_num at hfin
    omega

noncomputable abbrev iota23 : ↥mog23 →* ↥AutPerm := Subgroup.inclusion inf_le_left

theorem irr_of_isIrreducible {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {τ : Representation (ZMod 2) G V} (hτ : τ.IsIrreducible) :
    ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ u ∈ U, τ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  rcases hτ.eq_bot_or_eq_top ⟨U, fun g _ hv => hU g _ hv⟩ with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

theorem m24_hψ {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) ↥AutPerm X) {d : ℕ} (R : ↥mog23 → (Vec d →ₗ[ZMod 2] Vec d))
    (ψ : Vec d →ₗ[ZMod 2] X) (hψ : ∀ g v, ψ (R g v) = ρ (iota23 g) (ψ v))
    (cols : Bool → ℕ → List ℕ)
    (hcols : ∀ z k (hk : k < 24), lin d (cols z k) = R ⟨_, m24h_mem z hk⟩) :
    ∀ z, ∀ k < 24, ∀ v, ψ (lin d (cols z k) v) = ρ (m24h z k) (ψ v) := by
  intro z k hk v
  rw [hcols z k hk, hψ]
  rfl

theorem lin_m24Xcol_one (z : Bool) (k : ℕ) : lin 1 (m24Xcol 0 z k) = LinearMap.id :=
  lin_eq_id fun j hj => by
    have : j = 0 := by omega
    subst this
    rfl

theorem lin_m24Xcol_code (z : Bool) {k : ℕ} (hk : k < 24) :
    lin 11 (m24Xcol 1 z k) =
      Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left ⟨_, m24h_mem z hk⟩)) :=
  lin_matOf_eq fun m => rhoC11_toW mog23 inf_le_left ⟨_, m24h_mem z hk⟩ (hasArr_m24h z hk) m

theorem lin_m24Xcol_cocode (z : Bool) {k : ℕ} (hk : k < 24) :
    lin 11 (m24Xcol 2 z k) =
      Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left ⟨_, m24h_mem z hk⟩)) :=
  lin_matOf_eq fun m => rho11_toW mog23 inf_le_left ⟨_, m24h_mem z hk⟩ (hasArr_m24h z hk) m

theorem m24_binary_small36
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) ↥AutPerm X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hne : Nontrivial X) (hdim : finrank (ZMod 2) X ≤ 36) :
    (∀ g v, ρ g v = v) ∨
      (∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rhoC11 AutPerm le_rfl g)) v) = ρ g (e v)) ∨
      ∃ e : Vec 11 ≃ₗ[ZMod 2] X,
        ∀ g v, e (Matrix.toLin' (mulAutMat 11 (rho11 AutPerm le_rfl g)) v) = ρ g (e v) := by
  have : FiniteDimensional (ZMod 2) X := Module.Finite.of_finite
  obtain ⟨Y, hY0, hYirr⟩ := exists_isIrreducible_subrepresentation (ρ.comp iota23)
  have hYdim : finrank (ZMod 2) Y.toSubmodule ≤ 36 := (Submodule.finrank_le _).trans hdim
  have hYne : Nontrivial Y.toSubmodule := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hY0
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
    have h1 : (⟨y, hy⟩ : Y.toSubmodule) = 0 := Subsingleton.elim _ _
    exact (Submodule.mem_bot (ZMod 2)).2 (congrArg Subtype.val h1)
  have : Finite Y.toSubmodule := Finite.of_injective _ Subtype.val_injective
  rcases m23_binary_small36 Y.toRepresentation (irr_of_isIrreducible hYirr) hYne hYdim with
    htriv | ⟨e, he⟩ | ⟨e, he⟩
  ·
    obtain ⟨y, hy0⟩ := exists_ne (0 : Y.toSubmodule)
    let ψ : Vec 1 →ₗ[ZMod 2] X := (LinearMap.proj 0).smulRight (y : X)
    have hψ0 : ψ ≠ 0 := by
      intro h
      have h1 := LinearMap.congr_fun h (Pi.single 0 1)
      simp only [ψ, LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.single_eq_same,
        one_smul, LinearMap.zero_apply] at h1
      exact hy0 (Subtype.ext h1)
    have hψ : ∀ g v, ψ ((LinearMap.id : Vec 1 →ₗ[ZMod 2] Vec 1) v) = ρ (iota23 g) (ψ v) := by
      intro g v
      have h3 : ρ (iota23 g) (y : X) = y := congrArg Subtype.val (htriv g y)
      simp only [ψ, LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
        map_smul, h3]
    obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m24_exists_std ρ hirr hne (i := 0) (by norm_num) ψ hψ0
      (m24_hψ ρ (fun _ => LinearMap.id) ψ hψ (m24Xcol 0) fun z k _ => lin_m24Xcol_one z k)
    exact m24_conclude ρ hdim ht hd Ψ hΨ
  ·
    let ψ : Vec 11 →ₗ[ZMod 2] X := Y.toSubmodule.subtype ∘ₗ e.toLinearMap
    have hψ0 : ψ ≠ 0 := by
      intro h
      obtain ⟨y, hy0⟩ := exists_ne (0 : Y.toSubmodule)
      obtain ⟨v, rfl⟩ := e.surjective y
      have h1 := LinearMap.congr_fun h v
      exact hy0 (Subtype.ext h1)
    have hψ : ∀ g v, ψ (Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left g)) v) =
        ρ (iota23 g) (ψ v) := by
      intro g v
      change ((e (Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left g)) v) :
        Y.toSubmodule) : X) = ρ (iota23 g) ((e v : Y.toSubmodule) : X)
      rw [he]
      rfl
    obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m24_exists_std ρ hirr hne (i := 1) (by norm_num) ψ hψ0
      (m24_hψ ρ _ ψ hψ (m24Xcol 1) fun z k hk => lin_m24Xcol_code z hk)
    exact m24_conclude ρ hdim ht hd Ψ hΨ
  ·
    let ψ : Vec 11 →ₗ[ZMod 2] X := Y.toSubmodule.subtype ∘ₗ e.toLinearMap
    have hψ0 : ψ ≠ 0 := by
      intro h
      obtain ⟨y, hy0⟩ := exists_ne (0 : Y.toSubmodule)
      obtain ⟨v, rfl⟩ := e.surjective y
      have h1 := LinearMap.congr_fun h v
      exact hy0 (Subtype.ext h1)
    have hψ : ∀ g v, ψ (Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left g)) v) =
        ρ (iota23 g) (ψ v) := by
      intro g v
      change ((e (Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left g)) v) :
        Y.toSubmodule) : X) = ρ (iota23 g) ((e v : Y.toSubmodule) : X)
      rw [he]
      rfl
    obtain ⟨t, ht, d, hd, Ψ, hΨ⟩ := m24_exists_std ρ hirr hne (i := 2) (by norm_num) ψ hψ0
      (m24_hψ ρ _ ψ hψ (m24Xcol 2) fun z k hk => lin_m24Xcol_cocode z hk)
    exact m24_conclude ρ hdim ht hd Ψ hΨ

theorem cocode24_rho11 : MathieuCocode24 (rho11 AutPerm le_rfl).range ⊤ ⊥ :=
  CFSG.Quasithin.H13.A5.M12.realizes_rho_of_coords cocodeCoords (Γ := AutPerm)
    (fun _ hσ => preserves_cocode hσ) golayC_le_coreMod

end CFSG.Quasithin.B45Mat.Ind

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Setup.X3E CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H CFSG.Monster.Code B45Mat B45Mat.M22 B45Mat.Ind
  Module Matrix

theorem mathieuSmallIrr24_holds :
    MathieuSmallIrr24 := by
  intro W _ _ hW2 L hLiso hirr hcard
  obtain ⟨θ0⟩ := hLiso
  have hV : ∀ w : W, w ^ 2 = 1 := fun w => by
    rw [sq]
    exact hW2 w
  let θ : ↥L ≃* ↥AutPerm := (θ0 : ↥L ≃* ↥NativeSporadic.M24).trans autPermEquivM24'.symm
  have hcardG : Nat.card ↥AutPerm = 244823040 := card_AutPerm
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
  rcases m24_binary_small36 (autRepOfG hV θ) (irr_autRepOfG hV θ hirr) inferInstance
      (finrank_autRepOfG_le hV hcard) with htriv | ⟨e, he⟩ | ⟨e, he⟩
  · exfalso
    have htriv' : ∀ g : ↥AutPerm, g = 1 := by
      intro g
      have h1 : θ.symm g = 1 := by
        refine Subtype.ext (MulEquiv.ext fun w => ?_)
        have h2 := htriv g (F2Vec.ofV hV w)
        rw [autRepOfG_apply] at h2
        exact h2
      exact θ.symm.injective (h1.trans (map_one θ.symm).symm)
    have : Subsingleton ↥AutPerm := ⟨fun x y => (htriv' x).trans (htriv' y).symm⟩
    rw [Nat.card_of_subsingleton (1 : ↥AutPerm)] at hcardG
    norm_num at hcardG
  · left
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range' hV θ (rhoC11 AutPerm le_rfl) e.symm
      fun g v => by
        have h1 := he g (e.symm v)
        rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] at h1
        rw [← autRepOfG_apply, ← h1, LinearEquiv.symm_apply_apply]
    exact realizes_of_map_congrHom φ hφ CFSG.Quasithin.H13.A5.M12.codeCoords_realizes
  · right
    obtain ⟨φ, hφ⟩ := exists_map_congrHom_eq_range' hV θ (rho11 AutPerm le_rfl) e.symm
      fun g v => by
        have h1 := he g (e.symm v)
        rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] at h1
        rw [← autRepOfG_apply, ← h1, LinearEquiv.symm_apply_apply]
    exact realizes_of_map_congrHom φ hφ cocode24_rho11

end CFSG.Quasithin

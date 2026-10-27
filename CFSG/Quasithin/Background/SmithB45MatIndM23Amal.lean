module

public import CFSG.Quasithin.Background.SmithB45MatIndM23Gen

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.H13.A5.M22Hat CFSG.Sporadic.Mathieu Module

@[expose] noncomputable def c34 (z : Bool) : List ℕ :=
  packCols (tab34 (if z then m22b else m22a))

@[expose] noncomputable def w22b (w : ℕ) : G22 := wordG m22a m22b (decW w)

theorem lin_c34
    (z : Bool) :
    lin 34 (c34 z) = Matrix.toLin' (rep34 (if z then m22b else m22a)) := by
  rw [c34, lin_packCols, untab_tab34]

theorem wmap_c34 :
    ∀ w : List Bool, wmap (fun b => lin 34 (c34 b)) w = Matrix.toLin' (rep34 (wordG m22a m22b w))
  | [] => by
    rw [wmap, wordG, map_one, Matrix.toLin'_one]
  | b :: w => by
    rw [wmap, wmap_c34 w, lin_c34, wordG, map_mul, Matrix.toLin'_mul]

theorem lin_amalMat
    (w : ℕ) :
    lin 34 (amalMat c34 w) = Matrix.toLin' (rep34 (w22b w)) := by
  rw [w22b, ← wmap_c34]
  refine lin_eq_of_toVec fun k => ?_
  rw [amalMat, getD_map_range _ _ k.isLt, toVec_wapp, toVec_one_shiftLeft]

theorem hasArr_iota22_w22b (w : ℕ) :
    HasArr ((iota22 (w22b w) : ↥mog23) : Equiv.Perm (Fin 24))
      (wordArr (psiArr (m22a : Equiv.Perm (Fin 22))) (psiArr (m22b : Equiv.Perm (Fin 22)))
        (decW w)) := by
  have h1 : ((iota22 (wordG m22a m22b (decW w)) : ↥mog23) : Equiv.Perm (Fin 24)) =
      wordG ((iota22 m22a : ↥mog23) : Equiv.Perm (Fin 24))
        ((iota22 m22b : ↥mog23) : Equiv.Perm (Fin 24)) (decW w) :=
    map_wordG ((mog23.subtype).comp iota22) m22a m22b (decW w)
  rw [w22b, h1, coe_iota22, coe_iota22]
  exact hasArr_wordArr (hasArr_psiArr _) (hasArr_psiArr _) _

theorem amal_rel :
    m23g false * iota22 (w22b amalHP1) = iota22 (w22b amalH1) * m23g false ∧
      m23g false * iota22 (w22b amalHP2) = iota22 (w22b amalH2) * m23g false := by
  have h := amal34_checks
  rw [amalOK, Bool.and_eq_true] at h
  have hrel := h.1
  rw [amalRelOK] at hrel
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hrel
  have key : ∀ w w' : ℕ, comp24 m23AArr
      (wordArr (psiArr (m22a : Equiv.Perm (Fin 22))) (psiArr (m22b : Equiv.Perm (Fin 22)))
        (decW w')) =
      comp24 (wordArr (psiArr (m22a : Equiv.Perm (Fin 22))) (psiArr (m22b : Equiv.Perm (Fin 22)))
        (decW w)) m23AArr →
      m23g false * iota22 (w22b w') = iota22 (w22b w) * m23g false := by
    intro w w' hw
    have hs : HasArr (m23g false : Equiv.Perm (Fin 24)) m23AArr := hasArr_m23g false
    refine Subtype.ext (eq_of_hasArr (hasArr_comp24 hs (hasArr_iota22_w22b w')) ?_)
    rw [hw]
    exact hasArr_comp24 (hasArr_iota22_w22b w) hs
  exact ⟨key _ _ hrel.1, key _ _ hrel.2⟩

theorem amal_homZero :
    homZeroOK 34 (fun z => if z then amalMat c34 amalHP2 else amalMat c34 amalHP1)
      (fun z => if z then amalMat c34 amalH2 else amalMat c34 amalH1) amalU (amalGW.map decW)
      amalMasks (amalP1.map decW) (amalP2.map decW) amalL1 amalL2 = true := by
  have h := amal34_checks
  rw [amalOK, Bool.and_eq_true] at h
  have hc : (fun z : Bool => if z then packCols (tab34 m22b) else packCols (tab34 m22a)) = c34 := by
    funext z
    cases z <;> rfl
  have h2 := h.2
  rw [amalCore] at h2
  rw [← hc]
  exact h2

@[expose] noncomputable def quotRepOf {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {τ : Representation (ZMod 2) G V} (Y : Subrepresentation τ) :
    Representation (ZMod 2) G (V ⧸ Y.toSubmodule) where
  toFun g := Y.toSubmodule.mapQ Y.toSubmodule (τ g) fun _ hx => Y.apply_mem_toSubmodule g hx
  map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
  map_mul' g h := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)

theorem quotRepOf_mk {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {τ : Representation (ZMod 2) G V} (Y : Subrepresentation τ) (g : G) (x : V) :
    quotRepOf Y g (Y.toSubmodule.mkQ x) = Y.toSubmodule.mkQ (τ g x) := by
  simp [quotRepOf]

section Excl


theorem exists_iota22_eq {z : Bool} {k : ℕ} (hk : k < 23) :
    ∃ g : G22, iota22 g = m23h z k := by
  refine ⟨mog22EquivM22 ⟨_, m23h_mem z hk⟩, Subtype.ext ?_⟩
  change ((psiS22 (mog22EquivM22 ⟨_, m23h_mem z hk⟩) : ↥mog22) : Equiv.Perm (Fin 24)) = _
  rw [psiS22, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem m23_not34 {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) ↥mog23 X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : finrank (ZMod 2) X ≤ 36) (Y : Subrepresentation (ρ.comp iota22))
    (e : Y.toRepresentation.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep34)) : False := by
  have : Finite ↥mog23 := Subgroup.instFiniteSubtypeMem mog23
  have : FiniteDimensional (ZMod 2) X := Module.Finite.of_finite
  have hY34 : finrank (ZMod 2) Y.toSubmodule = 34 := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  by_cases hYtop : Y.toSubmodule = ⊤
  ·
    let E : Vec 34 ≃ₗ[ZMod 2] X := e.symm.toLinearEquiv.trans (LinearEquiv.ofTop _ hYtop)
    have hE : ∀ g v, E (Matrix.toLin' (rep34 g) v) = ρ (iota22 g) (E v) := by
      intro g v
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g v
      change e.symm (matrixBaseChange (RingHom.id (ZMod 2)) rep34 g v) =
        Y.toRepresentation g (e.symm v) at h1
      rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id] at h1
      change ((e.symm (Matrix.toLin' (rep34 g) v) : Y.toSubmodule) : X) =
        ρ (iota22 g) ((e.symm v : Y.toSubmodule) : X)
      rw [Matrix.toLin'_apply, h1]
      rfl
    let S : Vec 34 →ₗ[ZMod 2] Vec 34 :=
      E.symm.toLinearMap ∘ₗ ρ (m23g false) ∘ₗ E.toLinearMap
    have hS : ∀ {w w' : ℕ}, m23g false * iota22 (w22b w') = iota22 (w22b w) * m23g false →
        ∀ v, S (Matrix.toLin' (rep34 (w22b w')) v) = Matrix.toLin' (rep34 (w22b w)) (S v) := by
      intro w w' hrel v
      change E.symm (ρ (m23g false) (E (Matrix.toLin' (rep34 (w22b w')) v))) =
        Matrix.toLin' (rep34 (w22b w)) (E.symm (ρ (m23g false) (E v)))
      rw [hE, ← Module.End.mul_apply, ← map_mul, hrel, map_mul, Module.End.mul_apply]
      apply E.injective
      rw [LinearEquiv.apply_symm_apply, hE, LinearEquiv.apply_symm_apply]
    have h0 := eq_zero_of_homZeroOK amal_homZero S (fun z v => by
      cases z
      · show S (lin 34 (amalMat c34 amalHP1) v) = lin 34 (amalMat c34 amalH1) (S v)
        rw [lin_amalMat, lin_amalMat]
        exact hS amal_rel.1 v
      · show S (lin 34 (amalMat c34 amalHP2) v) = lin 34 (amalMat c34 amalH2) (S v)
        rw [lin_amalMat, lin_amalMat]
        exact hS amal_rel.2 v)
    have h1 : S (Pi.single 0 1) = 0 := by rw [h0, LinearMap.zero_apply]
    have h2 : (Pi.single 0 1 : Vec 34) ≠ 0 := fun h => by
      have := congrFun h 0
      simp at this
    apply h2
    have h3 := congrArg E h1
    change E (E.symm (ρ (m23g false) (E (Pi.single 0 1)))) = E 0 at h3
    rw [LinearEquiv.apply_symm_apply, map_zero] at h3
    exact E.injective ((rep_injective ρ _ (h3.trans (map_zero _).symm)).trans E.map_zero.symm)
  ·
    have hq : finrank (ZMod 2) (X ⧸ Y.toSubmodule) ≤ 2 := by
      have h1 := Submodule.finrank_quotient_add_finrank Y.toSubmodule
      omega
    have htriv := isTrivial_of_finrank_le_two (quotRepOf Y) hq
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Y.toSubmodule := by
      by_contra h
      push Not at h
      exact hYtop (eq_top_iff.2 fun x _ => h x)
    have hx0 : Y.toSubmodule.mkQ x ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hx0
    let l : X →ₗ[ZMod 2] ZMod 2 := l₀ ∘ₗ Y.toSubmodule.mkQ
    have hl : l ≠ 0 := by
      intro h
      apply hl₀
      exact LinearMap.congr_fun h x
    have hlinv : ∀ g v, l (ρ (iota22 g) v) = l v := by
      intro g v
      change l₀ (Y.toSubmodule.mkQ ((ρ.comp iota22) g v)) = l₀ (Y.toSubmodule.mkQ v)
      rw [← quotRepOf_mk, htriv]
    have hle := finrank_le_of_coind ρ closure_m23g hirr (by norm_num : 0 < 23) m23t m23pi
      (fun z k hk => m23pi_lt z hk) m23pi_inj l hl (fun z k hk x => by
        obtain ⟨g, hg⟩ := exists_iota22_eq (z := z) hk
        have h1 : (m23t (m23pi z k))⁻¹ * m23g z = m23h z k * (m23t k)⁻¹ := by
          rw [m23h]
          group
        rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply, ← hg,
          hlinv])
    have h2 := Submodule.finrank_le Y.toSubmodule
    omega

end Excl

end CFSG.Quasithin.B45Mat.Ind

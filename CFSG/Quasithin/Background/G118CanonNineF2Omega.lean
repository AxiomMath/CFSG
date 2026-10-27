module

public import CFSG.Quasithin.Background.G118CanonNineF2OmegaComb
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Omega

open scoped Matrix
open CFSG.Open

section Field

theorem algebraMap_bijective :
    Function.Bijective (algebraMap (ZMod 2) (GaloisField 2 1)) := by
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
    norm_num
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨(algebraMap (ZMod 2) _).injective, ?_⟩
  rw [hcard, ZMod.card]

@[expose] noncomputable def eK : GaloisField 2 1 ≃+* ZMod 2 :=
  (RingEquiv.ofBijective (algebraMap (ZMod 2) (GaloisField 2 1)) algebraMap_bijective).symm

theorem eK_algebraMap (x : ZMod 2) : eK (algebraMap (ZMod 2) (GaloisField 2 1) x) = x :=
  (RingEquiv.ofBijective (algebraMap (ZMod 2) (GaloisField 2 1))
    algebraMap_bijective).symm_apply_apply x

theorem algebraMap_eK (k : GaloisField 2 1) : algebraMap (ZMod 2) (GaloisField 2 1) (eK k) = k :=
  (RingEquiv.ofBijective (algebraMap (ZMod 2) (GaloisField 2 1))
    algebraMap_bijective).apply_symm_apply k

theorem gf21_zero_or_one (k : GaloisField 2 1) : k = 0 ∨ k = 1 := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (eK k) with h0 | h1
  · left
    rw [← algebraMap_eK k, h0, map_zero]
  · right
    rw [← algebraMap_eK k, h1, map_one]

theorem gf21_one_add_one : (1 : GaloisField 2 1) + 1 = 0 := by
  apply eK.injective
  rw [map_add, map_one, map_zero]
  decide

@[expose] noncomputable def eKlin : GaloisField 2 1 ≃ₗ[ZMod 2] ZMod 2 :=
  { eK with
    map_smul' := fun c k => by
      show eK (c • k) = c • eK k
      rw [Algebra.smul_def, map_mul, eK_algebraMap, smul_eq_mul] }

end Field

section Transport

theorem quadMinus_eq (v : Ix → GaloisField 2 1) :
    StatedQuadMinus 2 (GaloisField 2 1) 1 1 v =
      v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
        v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + v (Sum.inr (Sum.inr 1)) ^ 2 := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]

theorem eK_quad (v : Ix → GaloisField 2 1) :
    eK (StatedQuadMinus 2 (GaloisField 2 1) 1 1 v) = qF (eK ∘ v) := by
  rw [quadMinus_eq]
  simp [qF, map_add, map_mul, map_pow, map_one]

theorem eK_mulVec (M : Matrix (Ix) (Ix) (GaloisField 2 1))
    (v : Ix → GaloisField 2 1) :
    (M.map eK) *ᵥ (eK ∘ v) = eK ∘ (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (eK : GaloisField 2 1 →+* ZMod 2) M v i).symm

theorem gl_mulVec_eq_zero (M : GL (Ix) (GaloisField 2 1))
    (w : Ix → GaloisField 2 1) (h : (M : Matrix Ix Ix (GaloisField 2 1)) *ᵥ w = 0) : w = 0 := by
  have h1 : ((M⁻¹ : GL Ix (GaloisField 2 1)) : Matrix Ix Ix (GaloisField 2 1)) *ᵥ
      ((M : Matrix Ix Ix (GaloisField 2 1)) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at h1
  exact h1.symm

theorem statedOmega_isometry (M : GL (Ix) (GaloisField 2 1))
    (hM : M ∈ StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)) :
    ∀ v, StatedQuadMinus 2 (GaloisField 2 1) 1 1 ((M : Matrix Ix Ix (GaloisField 2 1)) *ᵥ v) =
      StatedQuadMinus 2 (GaloisField 2 1) 1 1 v := by
  have hiso : ∀ g ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 (GaloisField 2 1) 1 1),
      ∀ v, StatedQuadMinus 2 (GaloisField 2 1) 1 1 ((g : Matrix Ix Ix (GaloisField 2 1)) *ᵥ v) =
        StatedQuadMinus 2 (GaloisField 2 1) 1 1 v := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact hg
    | one => intro v; simp
    | mul g h _ _ hg hh =>
      intro v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg, hh]
    | inv g _ hg =>
      intro v
      have h1 := hg (((g⁻¹ : GL Ix (GaloisField 2 1)) : Matrix Ix Ix (GaloisField 2 1)) *ᵥ v)
      have h2 : ((g : Matrix Ix Ix (GaloisField 2 1)) *
          ((g⁻¹ : GL Ix (GaloisField 2 1)) : Matrix Ix Ix (GaloisField 2 1))) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h1
      exact h1.symm
  have hMc : M ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 (GaloisField 2 1) 1 1) := by
    unfold StatedOmega at hM
    have hle : ⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 (GaloisField 2 1) 1 1),
        CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 (GaloisField 2 1) 1 1)⁆ ≤
        CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 (GaloisField 2 1) 1 1) := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    exact hle hM
  exact hiso M hMc

end Transport

section Perm

theorem permOf_mul (M N : Matrix Ix Ix (ZMod 2)) (hMQ : ∀ v, qF (M *ᵥ v) = qF v)
    (hMinj : ∀ v, M *ᵥ v = 0 → v = 0) (hNQ : ∀ v, qF (N *ᵥ v) = qF v)
    (hNinj : ∀ v, N *ᵥ v = 0 → v = 0) (j : Fin 5) :
    permOf (M * N) j = permOf M (permOf N j) := by
  have hMNQ : ∀ v, qF ((M * N) *ᵥ v) = qF v := fun v => by
    rw [← Matrix.mulVec_mulVec, hMQ, hNQ]
  have hMNinj : ∀ v, (M * N) *ᵥ v = 0 → v = 0 := fun v hv =>
    hNinj v (hMinj (N *ᵥ v) (by rw [Matrix.mulVec_mulVec]; exact hv))
  apply sv_injective
  have h1 := permOf_spec (M * N) hMNQ hMNinj j
  have h2 := permOf_spec N hNQ hNinj j
  have h3 := permOf_spec M hMQ hMinj (permOf N j)
  rw [← h1, ← Matrix.mulVec_mulVec, h2, h3]

end Perm

section Lam

@[expose] noncomputable def lamP5 : ↥(permCore 5) →ₗ[ZMod 2] (Ix → ZMod 2) :=
  (Matrix.mulVecLin Smat).comp (permCore 5).subtype

theorem lamP5_apply (y : ↥(permCore 5)) : lamP5 y = Smat *ᵥ (y : Fin 5 → ZMod 2) := rfl

theorem lamP5_bij : Function.Bijective lamP5 := by
  refine ⟨fun x y hxy => ?_, fun w => ?_⟩
  · have hxy' : Smat *ᵥ (x : Fin 5 → ZMod 2) = Smat *ᵥ (y : Fin 5 → ZMod 2) := hxy
    have hd : Smat *ᵥ ((x : Fin 5 → ZMod 2) - (y : Fin 5 → ZMod 2)) = 0 := by
      rw [Matrix.mulVec_sub, hxy', sub_self]
    have hx0 : ∑ i, (x : Fin 5 → ZMod 2) i = 0 := x.2
    have hy0 : ∑ i, (y : Fin 5 → ZMod 2) i = 0 := y.2
    have hsum : ∑ i, ((x : Fin 5 → ZMod 2) - (y : Fin 5 → ZMod 2)) i = 0 := by
      have hsplit : ∑ i, ((x : Fin 5 → ZMod 2) - (y : Fin 5 → ZMod 2)) i =
          ∑ i, (x : Fin 5 → ZMod 2) i - ∑ i, (y : Fin 5 → ZMod 2) i := by
        simp only [Pi.sub_apply]
        exact Finset.sum_sub_distrib _ _
      rw [hsplit, hx0, hy0, sub_self]
    have h0 := smat_injective_on_permCore _ hsum hd
    exact Subtype.ext (sub_eq_zero.1 h0)
  · obtain ⟨c, hc⟩ := span_sv w
    have hw : w = Smat *ᵥ c := by
      rw [smat_mulVec]
      exact hc
    by_cases hs : ∑ i, c i = 0
    · exact ⟨⟨c, hs⟩, by rw [lamP5_apply]; exact hw.symm⟩
    · have hs1 : ∑ i, c i = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hs
      refine ⟨⟨c + (fun _ : Fin 5 => (1 : ZMod 2)), ?_⟩, ?_⟩
      · show ∑ i, (c + (fun _ : Fin 5 => (1 : ZMod 2))) i = 0
        simp only [Pi.add_apply, Finset.sum_add_distrib, hs1, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin]
        decide
      · rw [lamP5_apply]
        show Smat *ᵥ (c + (fun _ : Fin 5 => (1 : ZMod 2))) = w
        have h1 : Smat *ᵥ (fun _ => (1 : ZMod 2)) = 0 := by
          rw [smat_mulVec]
          simp only [one_smul]
          exact sv_sum
        rw [Matrix.mulVec_add, h1, add_zero, ← hw]

@[expose] noncomputable def lameP5 : ↥(permCore 5) ≃ₗ[ZMod 2] (Ix → ZMod 2) :=
  LinearEquiv.ofBijective lamP5 lamP5_bij

theorem lameP5_apply (y : ↥(permCore 5)) : lameP5 y = Smat *ᵥ (y : Fin 5 → ZMod 2) := rfl

@[expose] def permActP5 (σ : Equiv.Perm (Fin 5)) (y : ↥(permCore 5)) : ↥(permCore 5) :=
  ⟨fun i => (y : Fin 5 → ZMod 2) (σ⁻¹ i), permAct_mem_permCore σ _ y.2⟩

theorem lame_intertwine (σ : Equiv.Perm (Fin 5)) (M : Matrix Ix Ix (ZMod 2))
    (hM : ∀ j, M *ᵥ sv j = sv (σ j)) (y : ↥(permCore 5)) :
    M *ᵥ lameP5 y = lameP5 (permActP5 σ y) := by
  rw [lameP5_apply, lameP5_apply]
  exact (smat_permAct σ M hM _).symm

end Lam

section Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

@[expose] noncomputable def hRof (hHI : Invariant H I) (h : ↥H) : ↥(restrictRange H I hHI) :=
  ⟨restrictHom H I hHI h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩

theorem hRof_mul (hHI : Invariant H I) (h h' : ↥H) :
    hRof hHI (h * h') = hRof hHI h * hRof hHI h' :=
  Subtype.ext (map_mul (restrictHom H I hHI) h h')

@[expose] noncomputable def omegaMat (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) : GL Ix (GaloisField 2 1) :=
  ↑(φ' (hRof hHI h))

@[expose] noncomputable def omegaMatF2 (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) : Matrix Ix Ix (ZMod 2) :=
  (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)).map eK

theorem omegaMatF2_mul (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h h' : ↥H) :
    omegaMatF2 hHI φ' (h * h') = omegaMatF2 hHI φ' h * omegaMatF2 hHI φ' h' := by
  unfold omegaMatF2 omegaMat
  rw [hRof_mul, map_mul, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem omegaMatF2_good (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) :
    (∀ v, qF (omegaMatF2 hHI φ' h *ᵥ v) = qF v) ∧
      (∀ v, omegaMatF2 hHI φ' h *ᵥ v = 0 → v = 0) := by
  have hiso := statedOmega_isometry (omegaMat hHI φ' h) (φ' (hRof hHI h)).2
  constructor
  · intro v
    have hw : eK ∘ (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v) = v :=
      funext fun i => eK_algebraMap (v i)
    have h1 : omegaMatF2 hHI φ' h *ᵥ v = eK ∘ ((omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1))
        *ᵥ (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v)) := by
      conv_lhs => rw [← hw]
      exact eK_mulVec (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) _
    rw [h1, ← eK_quad, hiso, eK_quad, hw]
  · intro v hv
    have hw : eK ∘ (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v) = v :=
      funext fun i => eK_algebraMap (v i)
    have h1 : omegaMatF2 hHI φ' h *ᵥ v = eK ∘ ((omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1))
        *ᵥ (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v)) := by
      conv_lhs => rw [← hw]
      exact eK_mulVec (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) _
    rw [h1] at hv
    have h2 : (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) *ᵥ
        (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v) = 0 := by
      funext i
      have h3 : eK (((omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) *ᵥ
          (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v)) i) = 0 := congrFun hv i
      rw [Pi.zero_apply, ← algebraMap_eK (((omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1))
          *ᵥ (algebraMap (ZMod 2) (GaloisField 2 1) ∘ v)) i), h3, map_zero]
    have h4 := gl_mulVec_eq_zero (omegaMat hHI φ' h) _ h2
    rw [← hw, h4]
    funext i
    simp

theorem omegaMatF2_perm_bij (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) : Function.Bijective (permOf (omegaMatF2 hHI φ' h)) :=
  Finite.injective_iff_bijective.1
    (permOf_injective _ (omegaMatF2_good hHI φ' h).1 (omegaMatF2_good hHI φ' h).2)

@[expose] noncomputable def omegaPermFun (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (permOf (omegaMatF2 hHI φ' h)) (omegaMatF2_perm_bij hHI φ' h)

theorem omegaPermFun_apply (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) (j : Fin 5) : omegaPermFun hHI φ' h j = permOf (omegaMatF2 hHI φ' h) j := rfl

theorem permOf_omegaMatF2_mul (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h h' : ↥H) (j : Fin 5) :
    permOf (omegaMatF2 hHI φ' (h * h')) j =
      permOf (omegaMatF2 hHI φ' h) (permOf (omegaMatF2 hHI φ' h') j) := by
  rw [omegaMatF2_mul]
  exact permOf_mul _ _ (omegaMatF2_good hHI φ' h).1 (omegaMatF2_good hHI φ' h).2
    (omegaMatF2_good hHI φ' h').1 (omegaMatF2_good hHI φ' h').2 j

theorem omegaPermFun_mul (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h h' : ↥H) :
    omegaPermFun hHI φ' (h * h') = omegaPermFun hHI φ' h * omegaPermFun hHI φ' h' := by
  apply Equiv.ext
  intro j
  rw [Equiv.Perm.mul_apply, omegaPermFun_apply, omegaPermFun_apply, omegaPermFun_apply]
  exact permOf_omegaMatF2_mul hHI φ' h h' j

@[expose] noncomputable def omegaPerm (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1))) :
    ↥H →* Equiv.Perm (Fin 5) :=
  MonoidHom.mk' (omegaPermFun hHI φ') (omegaPermFun_mul hHI φ')

theorem omegaPerm_spec (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (h : ↥H) (j : Fin 5) :
    omegaMatF2 hHI φ' h *ᵥ sv j = sv (omegaPerm hHI φ' h j) :=
  permOf_spec _ (omegaMatF2_good hHI φ' h).1 (omegaMatF2_good hHI φ' h).2 j

theorem omegaPerm_injective (hHI : Invariant H I)
    (hfaith : ∀ h : H, (∀ v ∈ I, (h : GLV V) v = v) → h = 1)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1))) :
    Function.Injective (omegaPerm hHI φ') := by
  rw [injective_iff_map_eq_one]
  intro h hh
  apply hfaith h
  have hfix : ∀ j, omegaMatF2 hHI φ' h *ᵥ sv j = sv j := by
    intro j
    have hperm : omegaPerm hHI φ' h j = j := by
      have := congrArg (fun σ : Equiv.Perm (Fin 5) => σ j) hh
      simpa using this
    rw [omegaPerm_spec, hperm]
  have hall : ∀ v, omegaMatF2 hHI φ' h *ᵥ v = v := by
    intro v
    obtain ⟨c, rfl⟩ := span_sv v
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hfix]
  have hMone : omegaMatF2 hHI φ' h = 1 := by
    ext i k
    have := congrFun (hall (Pi.single k 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  have hMkone : (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) = 1 := by
    ext i k
    have h1 : eK ((omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) i k) =
        (1 : Matrix Ix Ix (ZMod 2)) i k := by
      rw [← hMone]
      rfl
    have h2 := congrArg (algebraMap (ZMod 2) (GaloisField 2 1)) h1
    rw [algebraMap_eK] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  have hφ : φ' (hRof hHI h) = 1 := Subtype.ext (Units.ext hMkone)
  have hhR : hRof hHI h = 1 := φ'.injective (by rw [hφ, map_one])
  have hres : restrictHom H I hHI h = 1 := congrArg Subtype.val hhR
  exact (restrictHom_eq_one_iff).1 hres

theorem hom_perfect_trivial {G A : Type*} [Group G] [CommGroup A] (hG : Group.IsPerfect G)
    (f : G →* A) (x : G) : f x = 1 := by
  have hle : commutator G ≤ f.ker := by
    refine Subgroup.commutator_le.2 fun g _ k _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hx : x ∈ commutator G := by
    rw [Group.isPerfect_def.1 hG]
    exact Subgroup.mem_top x
  exact MonoidHom.mem_ker.1 (hle hx)

theorem omegaPerm_sign (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (hHperf : Group.IsPerfect ↥H) (h : ↥H) :
    Equiv.Perm.sign (omegaPerm hHI φ' h) = 1 :=
  hom_perfect_trivial hHperf (Equiv.Perm.sign.comp (omegaPerm hHI φ')) h

@[expose] noncomputable def psiF2 (ψ : ↥I ≃ₗ[ZMod 2] (Ix → GaloisField 2 1)) :
    ↥I ≃ₗ[ZMod 2] (Ix → ZMod 2) :=
  ψ.trans (LinearEquiv.piCongrRight fun _ => eKlin)

theorem psiF2_action (hHI : Invariant H I)
    (φ' : ↥(restrictRange H I hHI) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) 1 1)))
    (ψ : ↥I ≃ₗ[ZMod 2] (Ix → GaloisField 2 1))
    (hψ : ∀ (h : ↥(restrictRange H I hHI)) (v : ↥I),
      ψ ((h : GLV ↥I) v) =
        ((φ' h : GL Ix (GaloisField 2 1)) : Matrix Ix Ix (GaloisField 2 1)) *ᵥ ψ v)
    (h : ↥H) (w : ↥I) :
    psiF2 ψ (restrictHom H I hHI h w) = omegaMatF2 hHI φ' h *ᵥ psiF2 ψ w := by
  have key : ψ (restrictHom H I hHI h w) =
      (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) *ᵥ ψ w := hψ (hRof hHI h) w
  have hM := eK_mulVec (omegaMat hHI φ' h : Matrix Ix Ix (GaloisField 2 1)) (ψ w)
  rw [← key] at hM
  funext i
  exact (congrFun hM i).symm

end Omega

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isA5Module_of_natural {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hHI : Invariant H I) (φH : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (hfaith : ∀ h : H, (∀ v ∈ I, (h : GLV V) v = v) → h = 1)
    (b c : GaloisField 2 1) (hirr : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (hmod : IsNaturalMatrixModule (restrictRange H I hHI)
      (StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) b c))) :
    IsA5Module H I := by
  have hc : c = 1 := by
    rcases gf21_zero_or_one c with h | h
    · exfalso
      exact hirr 0 (by rw [h]; simp)
    · exact h
  have hb : b = 1 := by
    rcases gf21_zero_or_one b with h | h
    · exfalso
      exact hirr 1 (by rw [hc, h]; simp [gf21_one_add_one])
    · exact h
  subst hb
  subst hc
  obtain ⟨φ', ψ, hψ⟩ := hmod
  have hA5perf : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
  have hHperf : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := φH.symm.toMonoidHom) φH.symm.surjective
  have hmemA : ∀ h : H, omegaPerm hHI φ' h ∈ alternatingGroup (Fin 5) := fun h =>
    Equiv.Perm.mem_alternatingGroup.2 (omegaPerm_sign hHI φ' hHperf h)
  have hα'inj : Function.Injective ((omegaPerm hHI φ').codRestrict
      (alternatingGroup (Fin 5)) hmemA) := by
    intro h h' hh
    apply omegaPerm_injective hHI hfaith φ'
    exact congrArg Subtype.val hh
  haveI : Finite ↥H := Finite.of_equiv ↥(alternatingGroup (Fin 5)) φH.symm.toEquiv
  have hα'bij : Function.Bijective ((omegaPerm hHI φ').codRestrict
      (alternatingGroup (Fin 5)) hmemA) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hα'inj, Nat.card_congr φH.toEquiv⟩
  refine ⟨MulEquiv.ofBijective _ hα'bij, (psiF2 ψ).trans lameP5.symm, ?_⟩
  intro γ v w hvw
  have hwv : w = restrictHom H I hHI γ v := Subtype.ext (by rw [coe_restrictHom]; exact hvw)
  have hkey : psiF2 ψ w = omegaMatF2 hHI φ' γ *ᵥ psiF2 ψ v := by
    rw [hwv]
    exact psiF2_action hHI φ' ψ hψ γ v
  have hM : ∀ j, omegaMatF2 hHI φ' γ *ᵥ sv j = sv (omegaPerm hHI φ' γ j) :=
    omegaPerm_spec hHI φ' γ
  have hy : psiF2 ψ v = lameP5 (lameP5.symm (psiF2 ψ v)) := (lameP5.apply_symm_apply _).symm
  set y := lameP5.symm (psiF2 ψ v) with hy_def
  have h2 : psiF2 ψ w = lameP5 (permActP5 (omegaPerm hHI φ' γ) y) := by
    rw [hkey, hy, lame_intertwine _ _ hM y]
  have hfin : (lameP5.symm (psiF2 ψ w) : Fin 5 → ZMod 2) =
      permAct (omegaPerm hHI φ' γ) (y : Fin 5 → ZMod 2) := by
    rw [h2, LinearEquiv.symm_apply_apply]
    rfl
  exact hfin

end Main

end F2Omega

end Canon

end G11

end CFSG.Quasithin

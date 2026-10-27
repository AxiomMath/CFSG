module

public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Vol2.Ch9L34Herm9
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H.L3W9

open CFSG.Fischer Matrix CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H13.Ch9.Herm9

@[expose] noncomputable def img9 : Subgroup (MulAut W9) :=
  (rho9.comp Matrix.SpecialLinearGroup.toGL).range

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_bar (φ : K ≃+* F4) (x : K) : φ (SU3.bar 1 x) = cj (φ x) := by
  rw [SU3.bar_apply, map_pow, pow_one, pow_two]
  rfl

theorem isHerm_map (φ : K ≃+* F4) (X : HMod 1 K) : IsHerm ((mat X).map φ) := by
  intro i j
  show φ (mat X j i) = cj (φ (mat X i j))
  rw [← map_bar, herm_apply X j i]

theorem herm_symm (φ : K ≃+* F4) (m : Fin 512) :
    (SU3.conjM 1 ((herm m).map φ.symm))ᵀ = (herm m).map φ.symm := by
  ext i j
  apply φ.injective
  show φ (SU3.bar 1 (φ.symm (herm m j i))) = φ (φ.symm (herm m i j))
  rw [map_bar, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact (isHerm_herm m j i).symm

@[expose] noncomputable def hmodEquiv (φ : K ≃+* F4) : HMod 1 K ≃* W9 where
  toFun X := toW9 (code ((mat X).map φ))
  invFun w := mkH ((herm (toW9.symm w)).map φ.symm) (herm_symm φ _)
  left_inv X := by
    apply mat_injective
    show (herm (toW9.symm (toW9 (code ((mat X).map φ))))).map φ.symm = mat X
    rw [Equiv.symm_apply_apply, herm_code (isHerm_map φ X)]
    ext i j
    simp
  right_inv w := by
    show toW9 (code (((herm (toW9.symm w)).map φ.symm).map φ)) = w
    have h : ((herm (toW9.symm w)).map φ.symm).map φ = herm (toW9.symm w) := by
      ext i j
      simp
    rw [h, code_herm, Equiv.apply_symm_apply]
  map_mul' X Y := by
    show toW9 (code ((mat X + mat Y).map φ)) =
      toW9 (code ((mat X).map φ)) * toW9 (code ((mat Y).map φ))
    rw [Matrix.map_add _ (map_add φ), code_add, toW9_xor]

@[expose] noncomputable def mapGLF (φ : K ≃+* F4) : GL (Fin 3) K →* GL (Fin 3) F4 :=
  Units.map ((φ.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) K →+* Matrix (Fin 3) (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 3) (Fin 3) F4)

omit [Finite K] [CharP K 2] in
theorem coe_mapGLF (φ : K ≃+* F4) (A : GL (Fin 3) K) :
    ((mapGLF φ A : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      (A : Matrix (Fin 3) (Fin 3) K).map φ := rfl

theorem map_tw (φ : K ≃+* F4) (A X : Matrix (Fin 3) (Fin 3) K) :
    (tw 1 A X).map φ = A.map φ * X.map φ * (bar (A.map φ))ᵀ := by
  have hmm : ∀ M N : Matrix (Fin 3) (Fin 3) K, (M * N).map φ = M.map φ * N.map φ :=
    fun M N => map_mul φ.mapMatrix M N
  have h2 : ((SU3.conjM 1 A)ᵀ).map φ = (bar (A.map φ))ᵀ := by
    ext i j
    exact map_bar φ _
  show (A * X * (SU3.conjM 1 A)ᵀ).map φ = _
  rw [hmm, hmm, h2]

theorem congrHom_hmodEquiv_rhoT (φ : K ≃+* F4) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (A : GL (Fin 3) K) : congrHom (hmodEquiv φ) (rhoT hK A) = rho9 (mapGLF φ A) := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, rfl⟩ := toW9.surjective w
  refine (?_ : _ = toW9 (act (mapGLF φ A) m)).trans (rho9_toW9 _ m).symm
  show toW9 (code ((tw 1 (A : Matrix (Fin 3) (Fin 3) K)
    ((herm (toW9.symm (toW9 m))).map φ.symm)).map φ)) = toW9 (act (mapGLF φ A) m)
  rw [Equiv.symm_apply_apply, map_tw]
  have h1 : ((herm m).map φ.symm).map φ = herm m := by
    ext i j
    simp
  rw [h1]
  rfl

theorem map_img (φ : K ≃+* F4) (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (img hK).map (congrHom (hmodEquiv φ)) = img9 := by
  ext y
  constructor
  · rintro ⟨x, ⟨A, rfl⟩, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.map φ.toRingHom A, ?_⟩
    have h2 : mapGLF φ (Matrix.SpecialLinearGroup.toGL A) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map φ.toRingHom A) := by
      ext i j
      simp [coe_mapGLF]
    exact ((congrHom_hmodEquiv_rhoT φ hK (Matrix.SpecialLinearGroup.toGL A)).trans
      (congrArg rho9 h2)).symm
  · rintro ⟨B, rfl⟩
    set A := Matrix.SpecialLinearGroup.map φ.symm.toRingHom B with hA
    refine ⟨rhoT hK (Matrix.SpecialLinearGroup.toGL A), ⟨A, rfl⟩, ?_⟩
    have h2 : mapGLF φ (Matrix.SpecialLinearGroup.toGL A) = Matrix.SpecialLinearGroup.toGL B := by
      ext i j
      simp [coe_mapGLF, hA]
    exact (congrHom_hmodEquiv_rhoT φ hK (Matrix.SpecialLinearGroup.toGL A)).trans
      (congrArg rho9 h2)

theorem exists_equiv_w9 {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) : ∃ e : V ≃* W9, H.map (congrHom e) = img9 := by
  obtain ⟨K, _, _, _, hK, hr⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨e, he⟩ := exists_model hK' hr
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK', F4.card]
    norm_num
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hc
  refine ⟨e.trans (hmodEquiv φ), ?_⟩
  have hc' : congrHom (e.trans (hmodEquiv φ)) =
      (congrHom (hmodEquiv φ)).comp (congrHom e) := by
    ext x w
    rfl
  have key : ∀ X : Subgroup (MulAut (HMod 1 K)), X = img hK' →
      X.map (congrHom (hmodEquiv φ)) = img9 := by
    rintro X rfl
    exact map_img φ hK'
  exact (congrArg (fun F => H.map F) hc').trans
    ((Subgroup.map_map H (congrHom (hmodEquiv φ)) (congrHom e)).symm.trans (key _ he))

theorem card_img9 : Nat.card ↥img9 = 20160 := by
  have hF : Nat.card F4 = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  have h1 : Nat.card ↥img9 = Nat.card ↥(img hF) :=
    (congrArg (fun X : Subgroup (MulAut W9) => Nat.card ↥X)
      (map_img (RingEquiv.refl F4) hF)).symm.trans (card_map_congrHom _ _)
  rw [h1, Nat.card_congr (ModelType.imgEquivProj hF).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  decide

end CFSG.Quasithin.H.L3W9

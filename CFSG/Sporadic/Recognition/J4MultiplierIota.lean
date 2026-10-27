module

public import CFSG.Sporadic.Co1.Cover.Splitting
public import CFSG.Sporadic.Schreier.J4SGL
public import CFSG.Monster.Schur.M24
public import CFSG.Sporadic.Recognition.J4MultiplierInputs

public section

namespace CFSG.Sporadic.Recognition.J4Multiplier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.Sporadic.Co1.Cover
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.Schur CFSG.Monster.Schur.M24
  CFSG.CosetTable Matrix SemidirectProduct

abbrev PM24 : Type := TauCeti.SporadicName.M24.Group

theorem isSimpleGroup_PM24 :
    IsSimpleGroup PM24 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  exact e.symm.isSimpleGroup

theorem natCard_PM24 :
    Nat.card PM24 = 244823040 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

theorem lift_xy_mk (w : List (Fin 2 × Bool)) :
    FreeGroup.lift ![x, y] (FreeGroup.mk w) = signedWord x y (toZ w) := by
  rw [FreeGroup.lift_mk, signedWord, toZ, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> simp [letter]

theorem letter_mem_K (l : ℤ) : letter x y l ∈ K := by
  unfold letter
  split_ifs
  · exact x_mem_K
  · exact K.inv_mem x_mem_K
  · exact y_mem_K
  · exact K.inv_mem y_mem_K
  · exact K.one_mem

theorem wordCols_r4 : (wordCols (toZ r4) == idRows 11) = true := by
  decide +kernel

section Words


theorem ρGL_letter (l : ℤ) :
    (ρGL ⟨letter x y l, letter_mem_K l⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) =
      colsMatrix (letterCols l) := by
  have hxi : (ρGL ⟨x, x_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) *
      colsMatrix xInvColumns = 1 := by
    rw [ρGL_x, ← colsMatrix_comp11, comp11_x_inv, colsMatrix_idRows]
  have hyi : (ρGL ⟨y, y_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) *
      colsMatrix yInvColumns = 1 := by
    rw [ρGL_y, ← colsMatrix_comp11, comp11_y_inv, colsMatrix_idRows]
  rcases (show l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 ∨ (l ≠ 1 ∧ l ≠ -1 ∧ l ≠ 2 ∧ l ≠ -2) by omega)
    with rfl | rfl | rfl | rfl | ⟨h1, h2, h3, h4⟩
  · have e : (⟨letter x y 1, letter_mem_K 1⟩ : K) = ⟨x, x_mem_K⟩ :=
      Subtype.ext (by simp [letter])
    rw [e, ρGL_x]
    simp [letterCols]
  · have e : (⟨letter x y (-1), letter_mem_K (-1)⟩ : K) = (⟨x, x_mem_K⟩ : K)⁻¹ :=
      Subtype.ext (by simp [letter])
    rw [e, map_inv, Units.inv_eq_of_mul_eq_one_right hxi]
    simp [letterCols]
  · have e : (⟨letter x y 2, letter_mem_K 2⟩ : K) = ⟨y, y_mem_K⟩ :=
      Subtype.ext (by simp [letter])
    rw [e, ρGL_y]
    simp [letterCols]
  · have e : (⟨letter x y (-2), letter_mem_K (-2)⟩ : K) = (⟨y, y_mem_K⟩ : K)⁻¹ :=
      Subtype.ext (by simp [letter])
    rw [e, map_inv, Units.inv_eq_of_mul_eq_one_right hyi]
    simp [letterCols]
  · have e : (⟨letter x y l, letter_mem_K l⟩ : K) = 1 :=
      Subtype.ext (by simp [letter, h1, h2, h3, h4])
    rw [e, map_one, Units.val_one]
    simp [letterCols, h1, h2, h3, h4, colsMatrix_idRows]

theorem ρGL_signedWord : ∀ w : List ℤ,
    (ρGL ⟨signedWord x y w, signedWord_mem_K w⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) =
      colsMatrix (wordCols w)
  | [] => by
    have e : (⟨signedWord x y [], signedWord_mem_K []⟩ : K) = 1 :=
      Subtype.ext (by simp [signedWord])
    rw [e, map_one, Units.val_one, wordCols, colsMatrix_idRows]
  | l :: w => by
    have h : signedWord x y (l :: w) = letter x y l * signedWord x y w := by
      simp only [signedWord, List.map_cons, List.prod_cons]
    have e : (⟨signedWord x y (l :: w), signedWord_mem_K (l :: w)⟩ : K) =
        ⟨letter x y l, letter_mem_K l⟩ * ⟨signedWord x y w, signedWord_mem_K w⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul]; exact h)
    rw [e, map_mul, Units.val_mul, ρGL_letter, ρGL_signedWord w, wordCols,
      colsMatrix_comp11]

theorem x_ne_one : x ≠ 1 := by
  intro h
  have h1 : (ρGL ⟨x, x_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) = 1 := by
    have e : (⟨x, x_mem_K⟩ : K) = 1 := Subtype.ext h
    rw [e, map_one, Units.val_one]
  rw [ρGL_x] at h1
  exact colsMatrix_xColumns_ne_one h1

end Words

section Relators


theorem signedWord_eq_one {w : List ℤ} (hw : wordCols w = idRows 11) : signedWord x y w = 1 := by
  have h : ρGL ⟨signedWord x y w, signedWord_mem_K w⟩ = 1 := by
    apply Units.ext
    rw [ρGL_signedWord, hw, colsMatrix_idRows, Units.val_one]
  have h1 := ρGL_injective (h.trans (map_one ρGL).symm)
  exact congrArg Subtype.val h1

theorem lift_xy_rels :
    ∀ w ∈ [a2, b3, ab23, r4, r5, r6, r7], FreeGroup.lift ![x, y] (FreeGroup.mk w) = 1 := by
  intro w hw
  rw [lift_xy_mk]
  refine signedWord_eq_one (beq_iff_eq.1 ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)
  · exact wordCols_r4
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)
  · exact List.all_eq_true.1 wordCols_sixW _ (by decide)

end Relators

section Iota


@[expose] noncomputable def iota : PM24 →* J := liftHom ![x, y] lift_xy_rels

theorem iota_gen (i : Fin 2) : iota (gen i) = ![x, y] i := liftHom_of _ _ i

theorem iota_gen0 : iota (gen 0) = x := iota_gen 0

theorem iota_gen1 : iota (gen 1) = y := iota_gen 1

theorem iota_mem_K (p : PM24) : iota p ∈ K := by
  have hmem : p ∈ Subgroup.closure (Set.range gen) := by rw [closure_gen]; trivial
  refine Subgroup.closure_induction (p := fun p _ => iota p ∈ K) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i, rfl⟩
    rw [iota_gen]
    fin_cases i
    · exact x_mem_K
    · exact y_mem_K
  · rw [map_one]
    exact K.one_mem
  · intro p q _ _ hp hq
    rw [map_mul]
    exact K.mul_mem hp hq
  · intro p _ hp
    rw [map_inv]
    exact K.inv_mem hp

@[expose] noncomputable def iotaK : PM24 →* K := iota.codRestrict K iota_mem_K

@[expose] noncomputable def rho : PM24 →* ((Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 11 → ZMod 2)).toMonoidHom).comp
    ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (ρGL.comp iotaK))

theorem rho_apply (p : PM24) (v : Fin 11 → ZMod 2) :
    rho p v = (ρGL (iotaK p) : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ v :=
  rfl

theorem rho_gen0 (v : Fin 11 → ZMod 2) : rho (gen 0) v = j4A *ᵥ v := by
  have e : iotaK (gen 0) = ⟨x, x_mem_K⟩ := Subtype.ext iota_gen0
  rw [rho_apply, e, ρGL_x]

theorem rho_gen1 (v : Fin 11 → ZMod 2) : rho (gen 1) v = j4B *ᵥ v := by
  have e : iotaK (gen 1) = ⟨y, y_mem_K⟩ := Subtype.ext iota_gen1
  rw [rho_apply, e, ρGL_y]

theorem iota_conj (p : PM24) (v : Fin 11 → ZMod 2) :
    iota p * etaV v * (iota p)⁻¹ = etaV (rho p v) := by
  rw [rho_apply, etaV_ρGL]
  rfl

abbrev SJ : Type := Multiplicative (Fin 11 → ZMod 2) ⋊[phiOf rho] PM24

@[expose] noncomputable def theta : SJ →* J :=
  SemidirectProduct.lift etaHom iota fun p => by
    refine MonoidHom.ext fun v => ?_
    show etaHom (phiOf rho p v) = iota p * etaHom v * (iota p)⁻¹
    rw [phiOf_apply, ← etaV_eq, ← ofAdd_toAdd v, ← etaV_eq, toAdd_ofAdd]
    exact (iota_conj p _).symm

theorem theta_apply (s : SJ) : theta s = etaHom s.left * iota s.right := rfl

theorem iota_injective : Function.Injective iota := by
  have := isSimpleGroup_PM24
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal iota.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff iota).1 h
  · exfalso
    apply x_ne_one
    rw [← iota_gen0]
    exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top (gen 0))

theorem theta_injective : Function.Injective theta := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, theta_apply] at hs
  have hN : iota s.right ∈ N := by
    have hr : (etaHom s.left)⁻¹ ∈ etaHom.range :=
      etaHom.range.inv_mem ⟨s.left, rfl⟩
    rw [etaHom_range] at hr
    have e : iota s.right = (etaHom s.left)⁻¹ := eq_inv_of_mul_eq_one_right hs
    rw [e]
    exact hr
  have h1 : iota s.right = 1 := by
    have hmem : iota s.right ∈ K ⊓ N := ⟨iota_mem_K s.right, hN⟩
    rw [K_inf_N] at hmem
    exact hmem
  have hr1 : s.right = 1 := iota_injective (h1.trans (map_one iota).symm)
  rw [hr1, map_one, mul_one] at hs
  have hl1 : s.left = 1 := etaHom_injective (hs.trans (map_one etaHom).symm)
  exact Subgroup.mem_bot.2 (SemidirectProduct.ext hl1 hr1)

theorem natCard_SJ : Nat.card SJ = 2 ^ 11 * 244823040 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, natCard_PM24]
  congr 1
  rw [Nat.card_congr (Multiplicative.ofAdd :
    (Fin 11 → ZMod 2) ≃ Multiplicative (Fin 11 → ZMod 2)).symm]
  simp [Nat.card_eq_fintype_card]

theorem theta_index : theta.range.index = 173067389 := by
  have h1 := Subgroup.card_mul_index theta.range
  rw [Nat.card_congr (MonoidHom.ofInjective theta_injective).toEquiv.symm, natCard_SJ,
    card_J j4Facts] at h1
  omega

theorem odd_index_theta : Odd theta.range.index := by
  rw [theta_index]
  decide

end Iota

end CFSG.Sporadic.Recognition.J4Multiplier

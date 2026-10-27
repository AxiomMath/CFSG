module

public import CFSG.Quasithin.H13.J4Words
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.H13.J4Data
public meta import Certificates.Data.CFSGNative.H13.J4Data
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Quasithin.H13.J4Defs
import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4QuotInputs
public import Certificates.Certificate7015
public import Certificates.Certificate7018

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rowsMatrix_addRows (X Y : Array V2) :
    rowsMatrix (addRows X Y) = rowsMatrix X + rowsMatrix Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold addRows
  rw [Array.getElem?_ofFn]
  simp only [i.2, ↓reduceDIte, Option.getD_some, V2.toVec_xor, Pi.add_apply]

theorem rowsMatrix_eq_zero {X : Array V2} (h : rowsZero X = true) : rowsMatrix X = 0 := by
  ext i j
  simp only [rowsZero, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  rw [rowsMatrix_apply, V2.toVec_apply, h i i.2 j j.2, Matrix.zero_apply]
  rfl

theorem rowsMatrix_apply_of_agree {X : Array V2} {d : ℕ} {f : ℕ → ℕ → Bool}
    (h : rowsAgree X d f = true) {i j : Fin 112} (hi : (i : ℕ) < d) (hj : (j : ℕ) < d) :
    rowsMatrix X i j = if f i j then 1 else 0 := by
  simp only [rowsAgree, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [rowsMatrix_apply, V2.toVec_apply, h i hi j hj]

@[expose] def tM : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1

@[expose] def phiM : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix phiRows

@[expose] def eM : Matrix (Fin 112) (Fin 112) (ZMod 2) := (rowsMatrix eCols)ᵀ

@[expose] def gM : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix gRows

@[expose] def hM : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix hRows

theorem quotChecks_eq : quotChecks = true :=
  Certificates.certificate7015.1

theorem rowsMatrix_T :
    rowsMatrix (addRows (tOf (uvPairsOf basePairs)).1 idRows) = tM := by
  rw [rowsMatrix_addRows, prRep_t.1, rowsMatrix_idRows]; rfl

theorem quotChecks_spec :
    phiM * tM = 0 ∧ tM * eM = 0 ∧
    (∀ i j : Fin 112, (phiM * eM) i j = if (i : ℕ) < 12 ∧ i = j then 1 else 0) ∧
    tM * gM + hM * tM + eM * phiM = 1 := by
  have h := quotChecks_eq
  simp only [quotChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hE : rowsMatrix (transposeRows eCols) = eM := rowsMatrix_transposeRows eCols
  refine ⟨?_, ?_, fun i j => ?_, ?_⟩
  · have := rowsMatrix_eq_zero h1
    rwa [rowsMatrix_mulRows, rowsMatrix_T] at this
  · have := rowsMatrix_eq_zero h2
    rwa [rowsMatrix_mulRows, rowsMatrix_T, hE] at this
  · have := rowsMatrix_apply_of_agree h3 (i := i) (j := j) i.2 j.2
    rw [rowsMatrix_mulRows, hE] at this
    rw [show phiM * eM = rowsMatrix phiRows * eM from rfl, this]
    have hb : ((decide ((i : ℕ) < 12) && (i : ℕ) == j) = true) ↔ ((i : ℕ) < 12 ∧ i = j) := by
      rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Fin.val_inj]
    by_cases hc : (i : ℕ) < 12 ∧ i = j
    · rw [ite_eq_left (hb.2 hc), ite_eq_left hc]
    · rw [ite_eq_right (mt hb.1 hc), ite_eq_right hc]
  · have := congrArg rowsMatrix (eqRows_iff.1 h4)
    rwa [rowsMatrix_addRows, rowsMatrix_addRows, rowsMatrix_mulRows, rowsMatrix_mulRows,
      rowsMatrix_mulRows, rowsMatrix_T, hE, rowsMatrix_idRows] at this

theorem phiM_of_ge {i : Fin 112} (hi : 12 ≤ (i : ℕ)) (j : Fin 112) : phiM i j = 0 := by
  rw [phiM, rowsMatrix_apply,
    show phiRows[(i : ℕ)]? = none from Array.getElem?_eq_none (by simp [phiRows]; omega)]
  exact congrFun V2.toVec_zero j

theorem eM_of_ge (i : Fin 112) {j : Fin 112} (hj : 12 ≤ (j : ℕ)) : eM i j = 0 := by
  rw [eM, Matrix.transpose_apply, rowsMatrix_apply,
    show eCols[(j : ℕ)]? = none from Array.getElem?_eq_none (by simp [eCols]; omega)]
  exact congrFun V2.toVec_zero i

@[expose] def c12 : Fin 12 → Fin 112 := Fin.castLE (by norm_num)

@[expose] def phi12 : Matrix (Fin 12) (Fin 112) (ZMod 2) := phiM.submatrix c12 id

@[expose] def e12 : Matrix (Fin 112) (Fin 12) (ZMod 2) := eM.submatrix id c12

theorem sum_c12 {R : Type*} [AddCommMonoid R] (f : Fin 112 → R)
    (hf : ∀ k : Fin 112, 12 ≤ (k : ℕ) → f k = 0) : ∑ k, f k = ∑ k : Fin 12, f (c12 k) := by
  have e : ∑ k : Fin 12, f (c12 k) =
      ∑ k ∈ Finset.univ.map (Fin.castLEEmb (show 12 ≤ 112 by norm_num)), f k := by
    rw [Finset.sum_map]
    rfl
  rw [e]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hf k ?_
  by_contra h
  exact hk (Finset.mem_map.2 ⟨⟨k, by omega⟩, Finset.mem_univ _, rfl⟩)

theorem phi12_mul_tM :
    phi12 * tM = 0 := by
  ext i j
  have h := congrFun (congrFun quotChecks_spec.1 (c12 i)) j
  rw [Matrix.mul_apply] at h ⊢
  rw [Matrix.zero_apply] at h ⊢
  exact h

theorem tM_mul_e12 :
    tM * e12 = 0 := by
  ext i j
  have h := congrFun (congrFun quotChecks_spec.2.1 i) (c12 j)
  rw [Matrix.mul_apply] at h ⊢
  rw [Matrix.zero_apply] at h ⊢
  exact h

theorem phi12_mul_e12 :
    phi12 * e12 = 1 := by
  ext i j
  have h := quotChecks_spec.2.2.1 (c12 i) (c12 j)
  rw [Matrix.mul_apply] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h.trans ?_
  have hi : (c12 i : ℕ) < 12 := i.2
  have e : c12 i = c12 j ↔ i = j := ⟨fun h => Fin.ext (by simpa [c12] using congrArg Fin.val h),
    fun h => h ▸ rfl⟩
  simp only [hi, true_and, e]

theorem e12_mul_phi12 : e12 * phi12 = eM * phiM := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_c12 _ fun k hk => by rw [phiM_of_ge hk, mul_zero]]
  simp only [e12, phi12, Matrix.submatrix_apply, id]

theorem e12_mul_phi12_eq :
    e12 * phi12 = 1 - tM * gM - hM * tM := by
  rw [e12_mul_phi12, ← quotChecks_spec.2.2.2]
  abel

theorem phi12_mulVec_imT
    {x : Fin 112 → ZMod 2} (hx : x ∈ imT) :
    phi12 *ᵥ x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [Matrix.toLin'_apply, show (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1 = tM from rfl,
    Matrix.mulVec_mulVec, phi12_mul_tM, Matrix.zero_mulVec]

theorem e12_mulVec_mem_kerT
    (y : Fin 12 → ZMod 2) :
    e12 *ᵥ y ∈ kerT := by
  rw [kerT, LinearMap.mem_ker, Matrix.toLin'_apply,
    show (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1 = tM from rfl, Matrix.mulVec_mulVec,
    tM_mul_e12, Matrix.zero_mulVec]

@[expose] def coordMap :
    QT →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  (imT.comap kerT.subtype).liftQ ((Matrix.toLin' phi12).comp kerT.subtype) fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.toLin'_apply]
    exact phi12_mulVec_imT hx

@[expose] def coordInv :
    (Fin 12 → ZMod 2) →ₗ[ZMod 2] QT :=
  QT.mk.comp (LinearMap.codRestrict kerT (Matrix.toLin' e12) fun y => by
    rw [Matrix.toLin'_apply]; exact e12_mulVec_mem_kerT y)

theorem coordMap_mk (x : kerT) :
    coordMap (QT.mk x) = phi12 *ᵥ (x : Fin 112 → ZMod 2) := by
  show (imT.comap kerT.subtype).liftQ _ _ (Submodule.Quotient.mk x) = _
  rw [Submodule.liftQ_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Submodule.coe_subtype]

theorem coordInv_apply
    (y : Fin 12 → ZMod 2) :
    coordInv y = QT.mk ⟨e12 *ᵥ y, e12_mulVec_mem_kerT y⟩ := by
  simp only [coordInv, LinearMap.comp_apply]
  congr 1

theorem coordMap_coordInv
    (y : Fin 12 → ZMod 2) :
    coordMap (coordInv y) = y := by
  rw [coordInv_apply, coordMap_mk, Matrix.mulVec_mulVec, phi12_mul_e12, Matrix.one_mulVec]

theorem coordInv_coordMap (q : QT) :
    coordInv (coordMap q) = q := by
  obtain ⟨x, rfl⟩ := QT.mk_surjective q
  rw [coordMap_mk, coordInv_apply, QT.mk_eq_mk_iff]
  have hx : tM *ᵥ (x : Fin 112 → ZMod 2) = 0 := by
    have := x.2
    simp only [kerT, LinearMap.mem_ker, Matrix.toLin'_apply] at this
    exact this
  refine ⟨-(gM *ᵥ (x : Fin 112 → ZMod 2)), ?_⟩
  rw [Matrix.toLin'_apply, show (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1 = tM from rfl]
  show tM *ᵥ -(gM *ᵥ (x : Fin 112 → ZMod 2)) =
    e12 *ᵥ (phi12 *ᵥ (x : Fin 112 → ZMod 2)) - x
  rw [Matrix.mulVec_mulVec, e12_mul_phi12_eq, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.mulVec_neg]
  abel

@[expose] def coordEquiv :
    QT ≃ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  LinearEquiv.ofLinearMap coordMap coordInv (LinearMap.ext coordMap_coordInv)
    (LinearMap.ext coordInv_coordMap)

theorem finrank_QT :
    Module.finrank (ZMod 2) QT = 12 := by
  rw [coordEquiv.finrank_eq, Module.finrank_fin_fun]

@[expose] def rho : W →* LinearMap.GeneralLinearGroup (ZMod 2) QT :=
  quotAction.comp (Subgroup.inclusion W_le_centralizer)

theorem rho_mk (w : W) (x : kerT) :
    ((rho w : LinearMap.GeneralLinearGroup (ZMod 2) QT) : QT →ₗ[ZMod 2] QT) (QT.mk x) =
      QT.mk ⟨((w : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) *ᵥ x,
        mulVec_mem_kerT (W_le_centralizer w.2) x.2⟩ := by
  show quotMap _ (QT.mk x) = _
  rw [quotMap_mk]
  congr 1

@[expose] def coordConj :
    Module.End (ZMod 2) QT →* Matrix (Fin 12) (Fin 12) (ZMod 2) where
  toFun f := LinearMap.toMatrix'
    (coordEquiv.toLinearMap ∘ₗ f ∘ₗ coordEquiv.symm.toLinearMap)
  map_one' := by
    rw [Module.End.one_eq_id, LinearMap.id_comp, ← LinearEquiv.coe_trans,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  map_mul' f g := by
    rw [Module.End.mul_eq_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    ext y
    simp

theorem coordConj_injective :
    Function.Injective coordConj := by
  intro f g h
  have h' := LinearMap.toMatrix'.injective h
  ext q
  have := congrArg (fun F : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) =>
    coordEquiv.symm (F (coordEquiv q))) h'
  simpa using this

@[expose] def toGL12 :
    LinearMap.GeneralLinearGroup (ZMod 2) QT →* GL (Fin 12) (ZMod 2) :=
  (coordConj.comp (Units.coeHom _)).toHomUnits

theorem toGL12_injective :
    Function.Injective toGL12 := by
  intro f g h
  apply Units.ext
  exact coordConj_injective (congrArg Units.val h)

@[expose] def rho12 :
    W →* GL (Fin 12) (ZMod 2) := toGL12.comp rho

theorem rho12_val (w : W) :
    ((rho12 w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      phi12 * ((w : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) * e12 := by
  ext i j
  show LinearMap.toMatrix' (coordEquiv.toLinearMap ∘ₗ
    ((rho w : LinearMap.GeneralLinearGroup (ZMod 2) QT) : QT →ₗ[ZMod 2] QT) ∘ₗ
      coordEquiv.symm.toLinearMap) i j = _
  rw [LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show coordEquiv.symm (Pi.single j 1) = coordInv (Pi.single j 1) from rfl, coordInv_apply,
    rho_mk, show coordEquiv (QT.mk _) = coordMap (QT.mk _) from rfl, coordMap_mk]
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem ker_rho12 :
    rho12.ker = rho.ker := by
  ext w
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply toGL12_injective
    rw [map_one]
    exact h
  · intro h
    show toGL12 (rho w) = 1
    rw [h, map_one]

theorem card_range_rho12 :
    Nat.card rho12.range = Nat.card rho.range := by
  rw [rho12, MonoidHom.range_comp, Subgroup.card_map_of_injective toGL12_injective]

@[expose] def U12 :
    GL (Fin 12) (ZMod 2) := rho12 ⟨u, u_mem_W⟩

@[expose] def V12 :
    GL (Fin 12) (ZMod 2) := rho12 ⟨v, v_mem_W⟩

theorem range_rho12 :
    rho12.range = Subgroup.closure {U12, V12} := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := ({u, v} : Set _)),
    MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · left
      exact congrArg rho12 (Subtype.ext hw)
    · right
      exact congrArg rho12 (Subtype.ext hw)
  · rintro (rfl | rfl)
    · exact ⟨⟨u, u_mem_W⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨v, v_mem_W⟩, Or.inr rfl, rfl⟩

theorem phi12_mul_mul_e12 (A : Matrix (Fin 112) (Fin 112) (ZMod 2)) (i j : Fin 12) :
    (phi12 * A * e12) i j = (phiM * A * eM) (c12 i) (c12 j) := by
  simp only [Matrix.mul_apply, phi12, e12, Matrix.submatrix_apply, id]

theorem imageChecks_eq : imageChecks = true :=
  Certificates.certificate7015.2

theorem block_of_agree {g : GL (Fin 112) (ZMod 2)} {X : Array V2} {f : ℕ → ℕ → Bool}
    (hX : rowsMatrix X = (g : Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (h : rowsAgree (mulRows (mulRows phiRows X) (transposeRows eCols)) 12 f = true)
    (i j : Fin 12) :
    (phi12 * (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) * e12) i j = if f i j then 1 else 0 := by
  rw [phi12_mul_mul_e12, ← hX, show phiM * rowsMatrix X * eM =
    rowsMatrix (mulRows (mulRows phiRows X) (transposeRows eCols)) by
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows]; rfl]
  exact rowsMatrix_apply_of_agree h i.2 j.2

theorem rho12_eq_one_of {w : W}
    {X : Array V2}
    (hX : rowsMatrix X = ((w : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (h : rowsAgree (mulRows (mulRows phiRows X) (transposeRows eCols)) 12
      (fun a b => a == b) = true) : rho12 w = 1 := by
  apply Units.ext
  rw [rho12_val, Units.val_one]
  ext i j
  rw [block_of_agree hX h, Matrix.one_apply]
  by_cases hij : i = j
  · rw [ite_eq_left (by simp [hij]), ite_eq_left hij]
  · rw [ite_eq_right (by simpa [Fin.val_inj] using hij), ite_eq_right hij]

theorem imageChecks_spec :
    rho12 ⟨t, t_mem_W⟩ = 1 ∧ (∀ i : Fin 12, rho12 ⟨rConj i, rConj_mem_W i⟩ = 1) ∧
    (U12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) = CFSG.Sporadic.SmallF2.rowsMatrix 12 uRows12 ∧
    (V12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      CFSG.Sporadic.SmallF2.rowsMatrix 12 vRows12 := by
  have h := imageChecks_eq
  simp only [imageChecks, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨rho12_eq_one_of prRep_t.1 h1, fun i => rho12_eq_one_of (prRep_rConj i).1 (h2 i i.2),
    ?_, ?_⟩
  · rw [U12, rho12_val]
    ext i j
    rw [block_of_agree prRep_u.1 h3, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
      CFSG.Sporadic.SmallF2.toVecD_apply, Array.getD_eq_getD_getElem?]
  · rw [V12, rho12_val]
    ext i j
    rw [block_of_agree prRep_v.1 h4, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
      CFSG.Sporadic.SmallF2.toVecD_apply, Array.getD_eq_getD_getElem?]

theorem P_le_ker_rho :
    P.subgroupOf W ≤ rho.ker := by
  rw [← ker_rho12]
  intro w hw
  rw [Subgroup.mem_subgroupOf] at hw
  rw [MonoidHom.mem_ker]
  obtain ⟨w, hwW⟩ := w
  simp only at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact imageChecks_spec.1
    · exact imageChecks_spec.2.1 i
  | one => exact map_one rho12
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, hwW⟩ : W) = ⟨x, P_le_W hx⟩ * ⟨y, P_le_W hy⟩ := rfl
    rw [e, map_mul, ihx, ihy, one_mul]
  | inv x hx ihx =>
    have e : (⟨x⁻¹, hwW⟩ : W) = (⟨x, P_le_W hx⟩ : W)⁻¹ := rfl
    rw [e, map_inv, ihx, inv_one]

end CFSG.Quasithin.H13.J4

module

public import CFSG.RankThree.PartOne.KFR4.Weyl
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (map_conj_mul map_conj_one)

namespace Wey

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem map_conj_eq_self {G : Type*} [Group G] (L : Subgroup G) (g : G)
    (h1 : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (h2 : ∀ x ∈ L, g⁻¹ * x * g ∈ L) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro x hx
    refine ⟨g⁻¹ * x * g, h2 x hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

section Coord

theorem conjCoord_conjCoord (D : EvenNormPlane K E) (k : Fin 3) (v : Vs K E) :
    conjCoord D k (conjCoord D k v) = v :=
  Prod.ext (funext fun j => by by_cases h : j = k <;> simp [conjCoord_apply, h, D.sigma_sigma]) rfl

theorem conjCoord_mul_self (D : EvenNormPlane K E) (k : Fin 3) :
    conjCoord D k * conjCoord D k = 1 :=
  LinearEquiv.ext fun v => conjCoord_conjCoord D k v

theorem conjCoord_comm (D : EvenNormPlane K E) (a b : Fin 3) :
    conjCoord D a * conjCoord D b = conjCoord D b * conjCoord D a := by
  by_cases hab : a = b
  · rw [hab]
  refine LinearEquiv.ext fun v => Prod.ext (funext fun j => ?_) rfl
  by_cases ha : j = a
  · subst ha
    simp [conjCoord_apply, hab]
  · by_cases hb : j = b
    · subst hb
      simp [conjCoord_apply, ha]
    · simp [conjCoord_apply, ha, hb]

theorem conjCoord_coord_eq_zero_iff (D : EvenNormPlane K E) (k : Fin 3) (v : Vs K E)
    (j : Fin 3) : (conjCoord D k v).1 j = 0 ↔ v.1 j = 0 := by
  by_cases h : j = k <;> simp [conjCoord_apply, h]

theorem conjCoord_mem_Ufix_iff (D : EvenNormPlane K E) (k : Fin 3) (F : Finset (Fin 3))
    (v : Vs K E) : conjCoord D k v ∈ Ufix K E F ↔ v ∈ Ufix K E F := by
  show (∀ j, j ∉ F → (conjCoord D k v).1 j = 0) ↔ ∀ j, j ∉ F → v.1 j = 0
  simp only [conjCoord_coord_eq_zero_iff]

end Coord

section Short

theorem conj_mem_Supp (D : EvenNormPlane K E) (k : Fin 3) (F : Finset (Fin 3))
    {g : Vs K E ≃ₗ[K] Vs K E} (hg : g ∈ Supp D F) :
    conjCoord D k * g * (conjCoord D k)⁻¹ ∈ Supp D F := by
  obtain ⟨hgO, hg1, hg2⟩ := hg
  rw [conjCoord_inv]
  refine ⟨mul_mem (mul_mem (conjCoord_mem_O D k) hgO) (conjCoord_mem_O D k), fun v => ?_,
    fun v hv hv2 => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, conjCoord_mem_Ufix_iff, ← hg1,
      conjCoord_mem_Ufix_iff]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hg2 _ (fun j hj => (conjCoord_coord_eq_zero_iff D k v j).2 (hv j hj)) hv2,
      conjCoord_conjCoord]

theorem conj_mem_Om (D : EvenNormPlane K E) {c g : Vs K E ≃ₗ[K] Vs K E}
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D)) (hg : g ∈ Om D) :
    c * g * c⁻¹ ∈ Om D := by
  have hO : (TauCeti.QuadraticMap.orthogonalGroup (Qs D)).map (MulAut.conj c).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (Qs D) :=
    map_conj_eq_self _ c (fun x hx => mul_mem (mul_mem hc hx) (inv_mem hc))
      (fun x hx => mul_mem (mul_mem (inv_mem hc) hx) hc)
  have hmap : (Om D).map (MulAut.conj c).toMonoidHom = Om D := by
    show (⁅_, _⁆ : Subgroup _).map _ = _
    rw [Subgroup.map_commutator, hO]
  have := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hg
  rw [hmap] at this
  exact this

theorem map_conj_short (D : EvenNormPlane K E) (k : Fin 3) (F : Finset (Fin 3)) :
    (Supp D F ⊓ Om D).map (MulAut.conj (conjCoord D k)).toMonoidHom = Supp D F ⊓ Om D := by
  have h : ∀ x ∈ Supp D F ⊓ Om D, conjCoord D k * x * (conjCoord D k)⁻¹ ∈ Supp D F ⊓ Om D :=
    fun x hx => ⟨conj_mem_Supp D k F hx.1, conj_mem_Om D (conjCoord_mem_O D k) hx.2⟩
  refine map_conj_eq_self _ _ h fun x hx => ?_
  have := h x hx
  rw [conjCoord_inv] at this ⊢
  exact this

end Short

section Long

omit [Finite K] [CharP K 2] in
theorem matToG_apply (M : GL (Fin 3) E) (v : Vs K E) :
    matToG K M v = ((M : Matrix (Fin 3) (Fin 3) E).mulVec v.1, v.2) := rfl

theorem col_of_mem_suSupp {D : EvenNormPlane K E} {i j k : Fin 3} {M : GL (Fin 3) E}
    (hM : M ∈ suSupp D i j) (hki : k ≠ i) (hkj : k ≠ j) (m : Fin 3) :
    (M : Matrix (Fin 3) (Fin 3) E) m k = if m = k then 1 else 0 := by
  have h := congrFun (hM.2 k hki hkj) m
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, Pi.single_apply]

theorem row_of_mem_suSupp {D : EvenNormPlane K E} {i j k : Fin 3} {M : GL (Fin 3) E}
    (hM : M ∈ suSupp D i j) (hki : k ≠ i) (hkj : k ≠ j) (l : Fin 3) :
    (M : Matrix (Fin 3) (Fin 3) E) k l = if l = k then 1 else 0 := by
  have h := congrFun (congrFun hM.1.2 k) l
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, col_of_mem_suSupp hM hki hkj] at h
  simpa [eq_comm] using h

theorem conjCoord_comm_matToG (D : EvenNormPlane K E) {k : Fin 3} {M : GL (Fin 3) E}
    (hcol : ∀ m, (M : Matrix (Fin 3) (Fin 3) E) m k = if m = k then 1 else 0)
    (hrow : ∀ l, (M : Matrix (Fin 3) (Fin 3) E) k l = if l = k then 1 else 0) :
    conjCoord D k * matToG K M = matToG K M * conjCoord D k := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun m => ?_) rfl
  simp only [LinearEquiv.mul_apply, matToG_apply, conjCoord_apply, Matrix.mulVec, dotProduct]
  by_cases hm : m = k
  · subst hm
    have e : ∀ f : Fin 3 → E, ∑ x, (M : Matrix (Fin 3) (Fin 3) E) m x * f x = f m := fun f => by
      simp [hrow]
    rw [ite_eq_left rfl, e, e (fun x => if x = m then D.σ (v.1 x) else v.1 x), ite_eq_left rfl]
  · rw [ite_eq_right hm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = k
    · subst hl
      rw [hcol, ite_eq_right hm, zero_mul, zero_mul]
    · rw [ite_eq_right hl]

theorem conjAll_apply (D : EvenNormPlane K E) (v : Vs K E) :
    (conjCoord D 0 * conjCoord D 1 * conjCoord D 2) v = ((fun m => D.σ (v.1 m)), v.2) := by
  refine Prod.ext (funext fun m => ?_) rfl
  fin_cases m <;> simp [conjCoord_apply]

theorem conjAll_mul_matToG (D : EvenNormPlane K E) (M : GL (Fin 3) E) :
    conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * matToG K M =
      matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M) *
        (conjCoord D 0 * conjCoord D 1 * conjCoord D 2) := by
  refine LinearEquiv.ext fun v => ?_
  show (conjCoord D 0 * conjCoord D 1 * conjCoord D 2) (matToG K M v) =
    matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M)
      ((conjCoord D 0 * conjCoord D 1 * conjCoord D 2) v)
  rw [conjAll_apply, conjAll_apply]
  refine Prod.ext (funext fun m => ?_) rfl
  simp [matToG_apply, Matrix.mulVec, dotProduct, map_sum]

theorem map_sigma_mem_suSupp (D : EvenNormPlane K E) {i j : Fin 3} {M : GL (Fin 3) E}
    (hM : M ∈ suSupp D i j) :
    Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M ∈ suSupp D i j := by
  obtain ⟨⟨hdet, hu⟩, hfix⟩ := hM
  refine ⟨⟨?_, ?_⟩, fun k hki hkj => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      hdet, map_one]
  · ext a b
    have h := congrArg D.σ (congrFun (congrFun hu a) b)
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul] at h
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.GeneralLinearGroup.val_map_apply]
    simp only [AlgEquiv.coe_toRingEquiv, RingHom.coe_coe, D.sigma_sigma] at h ⊢
    rw [h, Matrix.one_apply]
    split_ifs <;> simp
  · have h := hfix k hki hkj
    rw [Matrix.mulVec_single_one] at h ⊢
    funext m
    have hm := congrFun h m
    simp only [Matrix.col_apply] at hm ⊢
    simp only [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply, hm, RingHom.coe_coe]
    rw [Pi.single_apply]
    split_ifs <;> simp

theorem map_conj_longBlock_third (D : EvenNormPlane K E) {i j k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) :
    (longBlock D i j).map (MulAut.conj (conjCoord D k)).toMonoidHom = longBlock D i j := by
  have h : ∀ x ∈ longBlock D i j, conjCoord D k * x * (conjCoord D k)⁻¹ ∈ longBlock D i j := by
    rintro _ ⟨M, hM, rfl⟩
    rw [conjCoord_comm_matToG D (col_of_mem_suSupp hM hki hkj) (row_of_mem_suSupp hM hki hkj),
      mul_inv_cancel_right]
    exact ⟨M, hM, rfl⟩
  refine map_conj_eq_self _ _ h fun x hx => ?_
  have := h x hx
  rw [conjCoord_inv] at this ⊢
  exact this

theorem tau_pair (D : EvenNormPlane K E) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) :
    conjCoord D i * conjCoord D j =
      conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * conjCoord D k := by
  refine LinearEquiv.ext fun v => ?_
  show conjCoord D i (conjCoord D j v) =
    (conjCoord D 0 * conjCoord D 1 * conjCoord D 2) (conjCoord D k v)
  rw [conjAll_apply]
  refine Prod.ext (funext fun m => ?_) rfl
  have hm : m = i ∨ m = j ∨ m = k := by
    revert hij hki hkj
    revert i j k m
    decide
  rcases hm with rfl | rfl | rfl
  · simp [conjCoord_apply, hij, hki.symm]
  · simp [conjCoord_apply, hij.symm, hkj.symm]
  · simp [conjCoord_apply, hki, hkj, D.sigma_sigma]

theorem map_conj_longBlock_pair (D : EvenNormPlane K E) {i j k : Fin 3} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (longBlock D i j).map (MulAut.conj (conjCoord D i * conjCoord D j)).toMonoidHom =
      longBlock D i j := by
  have hinv : (conjCoord D i * conjCoord D j)⁻¹ = conjCoord D i * conjCoord D j := by
    rw [mul_inv_rev, conjCoord_inv, conjCoord_inv, conjCoord_comm]
  have h : ∀ x ∈ longBlock D i j, conjCoord D i * conjCoord D j * x *
      (conjCoord D i * conjCoord D j)⁻¹ ∈ longBlock D i j := by
    rintro _ ⟨M, hM, rfl⟩
    have hc := conjCoord_comm_matToG D (col_of_mem_suSupp hM hki hkj)
      (row_of_mem_suSupp hM hki hkj)
    have key : conjCoord D i * conjCoord D j * matToG K M =
        matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M) *
          (conjCoord D i * conjCoord D j) := by
      calc conjCoord D i * conjCoord D j * matToG K M
          = conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * conjCoord D k * matToG K M := by
            rw [tau_pair D hij hki hkj]
        _ = conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * (conjCoord D k * matToG K M) :=
            mul_assoc _ _ _
        _ = conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * (matToG K M * conjCoord D k) := by
            rw [hc]
        _ = conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * matToG K M * conjCoord D k :=
            (mul_assoc _ _ _).symm
        _ = matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M) *
            (conjCoord D 0 * conjCoord D 1 * conjCoord D 2) * conjCoord D k := by
            rw [conjAll_mul_matToG]
        _ = matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M) *
            (conjCoord D 0 * conjCoord D 1 * conjCoord D 2 * conjCoord D k) := mul_assoc _ _ _
        _ = matToG K (Matrix.GeneralLinearGroup.map (D.σ : E →+* E) M) *
            (conjCoord D i * conjCoord D j) := by rw [tau_pair D hij hki hkj]
    rw [key, mul_inv_cancel_right]
    exact ⟨_, map_sigma_mem_suSupp D hM, rfl⟩
  refine map_conj_eq_self _ _ h fun x hx => ?_
  have := h x hx
  rw [hinv] at this ⊢
  exact this

theorem map_conj_m_fst (D : EvenNormPlane K E) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) :
    (longBlock D i j).map (MulAut.conj (conjCoord D i)).toMonoidHom =
      (longBlock D i j).map (MulAut.conj (conjCoord D j)).toMonoidHom := by
  have e : conjCoord D i = conjCoord D j * (conjCoord D i * conjCoord D j) := by
    rw [← mul_assoc, conjCoord_comm D j i, mul_assoc, conjCoord_mul_self, mul_one]
  rw [e, map_conj_mul, map_conj_longBlock_pair D hij hki hkj]

theorem map_conj_p_fst (D : EvenNormPlane K E) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) :
    ((longBlock D i j).map (MulAut.conj (conjCoord D j)).toMonoidHom).map
      (MulAut.conj (conjCoord D i)).toMonoidHom = longBlock D i j := by
  rw [← map_conj_mul, map_conj_longBlock_pair D hij hki hkj]

theorem map_conj_p_snd (D : EvenNormPlane K E) (i j : Fin 3) :
    ((longBlock D i j).map (MulAut.conj (conjCoord D j)).toMonoidHom).map
      (MulAut.conj (conjCoord D j)).toMonoidHom = longBlock D i j := by
  rw [← map_conj_mul, conjCoord_mul_self, map_conj_one]

theorem map_conj_p_third (D : EvenNormPlane K E) {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) :
    ((longBlock D i j).map (MulAut.conj (conjCoord D j)).toMonoidHom).map
      (MulAut.conj (conjCoord D k)).toMonoidHom =
      (longBlock D i j).map (MulAut.conj (conjCoord D j)).toMonoidHom := by
  rw [← map_conj_mul, conjCoord_comm, map_conj_mul, map_conj_longBlock_third D hki hkj]

end Long

section Hyp

variable {p : ℕ}

theorem flipVec_flipVec (k : Fin 3) (a : Fin 3 → ZMod p) : flipVec k (flipVec k a) = a := by
  funext m
  by_cases h : m = k
  · subst h
    simp [flipVec]
  · simp [flipVec, h]

theorem dot_flip_eq_zero_iff (k : Fin 3) (ρ : Root) (a : Fin 3 → ZMod p) :
    (Root.flip k ρ).vecp p ⬝ᵥ flipVec k a = 0 ↔ ρ.vecp p ⬝ᵥ a = 0 := by
  cases ρ <;> fin_cases k <;> simp [Root.flip, Root.vecp, Root.vec, flipVec, dotProduct,
    Fin.sum_univ_three, Function.update_apply, add_eq_zero_iff_eq_neg, neg_eq_iff_eq_neg]

end Hyp

end Wey

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

set_option linter.unusedSectionVars false in
theorem block_conj_flip (k : Fin 3) (ρ : Root) :
    (Block S.D ρ).map (MulAut.conj (conjCoord S.D k)).toMonoidHom = Block S.D (Root.flip k ρ) :=
  by
  cases ρ
  · exact Wey.map_conj_short S.D k {0}
  · exact Wey.map_conj_short S.D k {1}
  · exact Wey.map_conj_short S.D k {2}
  · fin_cases k
    · exact Wey.map_conj_m_fst S.D (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    · rfl
    · exact Wey.map_conj_longBlock_third S.D (i := 0) (j := 1) (k := 2) (by decide) (by decide)
  · fin_cases k
    · exact Wey.map_conj_m_fst S.D (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
    · exact Wey.map_conj_longBlock_third S.D (i := 0) (j := 2) (k := 1) (by decide) (by decide)
    · rfl
  · fin_cases k
    · exact Wey.map_conj_longBlock_third S.D (i := 1) (j := 2) (k := 0) (by decide) (by decide)
    · exact Wey.map_conj_m_fst S.D (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
    · rfl
  · fin_cases k
    · exact Wey.map_conj_p_fst S.D (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    · exact Wey.map_conj_p_snd S.D 0 1
    · exact Wey.map_conj_p_third S.D (i := 0) (j := 1) (k := 2) (by decide) (by decide)
  · fin_cases k
    · exact Wey.map_conj_p_fst S.D (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
    · exact Wey.map_conj_p_third S.D (i := 0) (j := 2) (k := 1) (by decide) (by decide)
    · exact Wey.map_conj_p_snd S.D 0 2
  · fin_cases k
    · exact Wey.map_conj_p_third S.D (i := 1) (j := 2) (k := 0) (by decide) (by decide)
    · exact Wey.map_conj_p_fst S.D (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
    · exact Wey.map_conj_p_snd S.D 1 2

set_option linter.unusedSectionVars false in
theorem hypA_conj_flip (k : Fin 3) (ρ : Root) :
    (hypA S ρ).map (MulAut.conj (conjCoord S.D k)).toMonoidHom = hypA S (Root.flip k ρ) := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨flipVec k a, (Wey.dot_flip_eq_zero_iff k ρ a).2 ha, (conj_tor S k a).symm⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨tor S (flipVec k b), ⟨flipVec k b, ?_, rfl⟩, ?_⟩
    · have := (Wey.dot_flip_eq_zero_iff k ρ (flipVec k b)).1
      rw [Wey.flipVec_flipVec] at this
      exact this hb
    · show conjCoord S.D k * tor S (flipVec k b) * (conjCoord S.D k)⁻¹ = tor S b
      rw [conj_tor, Wey.flipVec_flipVec]

end CFSG.RankThree.PartOne.KFR4

module

public import CFSG.Quasithin.Background.JonesParshallSL5Wedge
public import CFSG.Quasithin.Background.JonesParshallCurtisType
public import CFSG.Quasithin.Background.JonesParshallNatural

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

theorem coord_eq_zero_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    {x : Fin n → ZMod 2} (hx : A *ᵥ x = x) (r k : Fin n)
    (hrow : ∀ m, A r m = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r m + if m = k then 1 else 0) :
    x k = 0 := by
  have h := congrFun hx r
  simp only [mulVec, dotProduct, hrow, add_mul, Finset.sum_add_distrib, one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact add_eq_left.mp h

theorem eq_smul_single {n : ℕ} {x : Fin (n + 1) → ZMod 2}
    (h : ∀ k : Fin (n + 1), k ≠ 0 → x k = 0) : x = 0 ∨ x = Pi.single 0 1 := by
  have e : x = x 0 • Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [h i hi]
      simp [hi]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x 0) with h0 | h0
  · left
    rw [e, h0, zero_smul]
  · right
    rw [e, h0, one_smul]

theorem coe_mul5 (g h : G5) : ((g * h : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (h : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl

abbrev trivRep : Representation (ZMod 2) G5 (ZMod 2) := Representation.trivial (ZMod 2) G5 (ZMod 2)

theorem triv_fixU (x : ZMod 2) : x ∈ fixU trivRep := fun _ _ => rfl

theorem triv_gen : orbitSpan trivRep 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h := Submodule.smul_mem (orbitSpan trivRep 1) x (mem_orbitSpan_self trivRep 1)
  rwa [smul_eq_mul, mul_one] at h

theorem triv_simple : IsSimpleRep trivRep :=
  isSimpleRep_of_fixU trivRep (fun x _ => (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) x) triv_gen

theorem triv_type (s : Fin 4) : Th trivRep s 1 = 0 := by
  rw [Th_apply, Representation.trivial_apply, Representation.trivial_apply]
  decide

@[expose] def natRep : Representation (ZMod 2) G5 (Fin 5 → ZMod 2) where
  toFun g := (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVecLin
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp [mulVec_mulVec]

theorem natRep_apply (g : G5) (v : Fin 5 → ZMod 2) :
    natRep g v = (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v := rfl

@[expose] def e0 : Fin 5 → ZMod 2 := Pi.single 0 1

theorem e0_ne : e0 ≠ 0 := by decide

theorem e0_mem_fixU : e0 ∈ fixU natRep := by
  intro u hu
  have h := mem_Ugrp.mp hu
  funext i
  simp only [natRep_apply, e0, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs with hi
  · exact (h i 0).2 hi
  · exact (h i 0).1 (Fin.pos_iff_ne_zero.mpr hi)

theorem natRep_rows : ∀ s : Fin 4, ∀ m : Fin 5,
    xM s s.castSucc m =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) s.castSucc m + if m = s.succ then 1 else 0 := by
  decide +kernel

theorem natRep_fix
    {x : Fin 5 → ZMod 2} (hx : x ∈ fixU natRep) : x = 0 ∨ x = e0 := by
  refine eq_smul_single fun k hk => ?_
  obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.mpr hk
  exact coord_eq_zero_of_row (xM s) (hx _ (xE_mem s)) s.castSucc s.succ (natRep_rows s)

@[expose] def natIdx : Fin 5 → Fin 120 := ![0, 1, 8, 25, 48]

theorem natIdx_spec : ∀ i : Fin 5, toMat (bword (canW (natIdx i))) *ᵥ e0 = Pi.single i 1 := by
  decide +kernel

theorem natRep_wE (k : Fin 120) (v : Fin 5 → ZMod 2) :
    natRep (wE k) v = toMat (bword (canW k)) *ᵥ v := by
  rw [natRep_apply, wE, wordProd_coe]

theorem natRep_gen : orbitSpan natRep e0 = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 5)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, ← natIdx_spec i, ← natRep_wE]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem natRep_simple
    : IsSimpleRep natRep :=
  isSimpleRep_of_fixU natRep (fun _ hx => natRep_fix hx) natRep_gen

theorem natRep_Th_checks : ∀ s : Fin 4,
    yM s *ᵥ e0 + (xM s * yM s) *ᵥ e0 = if s = 0 then e0 else 0 := by
  decide +kernel

theorem natRep_type (s : Fin 4) : Th natRep s e0 = 0 ↔ s ≠ 0 := by
  rw [Th_apply, natRep_apply, natRep_apply, coe_mul5]
  change yM s *ᵥ e0 + (xM s * yM s) *ᵥ e0 = 0 ↔ _
  rw [natRep_Th_checks]
  split_ifs with h
  · simp [h, e0_ne]
  · simp [h]

theorem wedgeRep_apply' (g : G5) (w : Fin 10 → ZMod 2) :
    wedgeRep g w = wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w :=
  muW_apply (ZMod 2) g w

@[expose] def e01 : Fin 10 → ZMod 2 := Pi.single 0 1

theorem e01_ne : e01 ≠ 0 := by decide

theorem e01_mem_fixU : e01 ∈ fixU wedgeRep := by
  intro u hu
  have h := mem_Ugrp.mp hu
  have h00 := (h 0 0).2 rfl
  have h11 := (h 1 1).2 rfl
  have h10 := (h 1 0).1 (by decide)
  have h20 := (h 2 0).1 (by decide)
  have h30 := (h 3 0).1 (by decide)
  have h40 := (h 4 0).1 (by decide)
  have h21 := (h 2 1).1 (by decide)
  have h31 := (h 3 1).1 (by decide)
  have h41 := (h 4 1).1 (by decide)
  rw [wedgeRep_apply']
  funext k
  simp only [e01, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases k <;> simp [wedgeMat, pr5, h00, h11, h10, h20, h30, h40, h21, h31, h41]

@[expose] def rowS : Fin 10 → Fin 4 := ![0, 1, 2, 3, 0, 0, 0, 1, 1, 2]

@[expose] def rowR : Fin 10 → Fin 10 := ![0, 0, 1, 2, 1, 2, 3, 5, 6, 8]

theorem wedge_rows : ∀ k : Fin 10, k ≠ 0 → ∀ m : Fin 10,
    wedgeMat (xM (rowS k)) (rowR k) m =
      (1 : Matrix (Fin 10) (Fin 10) (ZMod 2)) (rowR k) m + if m = k then 1 else 0 := by
  decide +kernel

theorem wedge_fix
    {x : Fin 10 → ZMod 2} (hx : x ∈ fixU wedgeRep) : x = 0 ∨ x = e01 := by
  refine eq_smul_single fun k hk => ?_
  have h := hx _ (xE_mem (rowS k))
  rw [wedgeRep_apply'] at h
  exact coord_eq_zero_of_row _ h (rowR k) k (wedge_rows k hk)

@[expose] def wIdx : Fin 10 → Fin 120 := ![0, 2, 11, 28, 5, 17, 37, 38, 63, 89]

theorem wIdx_spec : ∀ k : Fin 10,
    wedgeMat (toMat (bword (canW (wIdx k)))) *ᵥ e01 = Pi.single k 1 := by
  decide +kernel

theorem wedgeRep_wE (k : Fin 120) (v : Fin 10 → ZMod 2) :
    wedgeRep (wE k) v = wedgeMat (toMat (bword (canW k))) *ᵥ v := by
  rw [wedgeRep_apply', wE, wordProd_coe]

theorem wedge_gen : orbitSpan wedgeRep e01 = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 10)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, ← wIdx_spec i, ← wedgeRep_wE]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem wedge_simple
    : IsSimpleRep wedgeRep :=
  isSimpleRep_of_fixU wedgeRep (fun _ hx => wedge_fix hx) wedge_gen

theorem wedge_Th_checks : ∀ s : Fin 4,
    wedgeMat (yM s) *ᵥ e01 + wedgeMat (xM s * yM s) *ᵥ e01 = if s = 1 then e01 else 0 := by
  decide +kernel

theorem wedge_type (s : Fin 4) : Th wedgeRep s e01 = 0 ↔ s ≠ 1 := by
  rw [Th_apply, wedgeRep_apply', wedgeRep_apply', coe_mul5]
  change wedgeMat (yM s) *ᵥ e01 + wedgeMat (xM s * yM s) *ᵥ e01 = 0 ↔ _
  rw [wedge_Th_checks]
  split_ifs with h
  · simp [h, e01_ne]
  · simp [h]

@[expose] def antiM : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem w0_toMat :
    toMat (bword (canW 119)) = antiM ∧ toMat (bword (canW 119).reverse) = antiM := by
  decide +kernel

theorem w0E_coe
    : ((wE 119 : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = antiM := by
  rw [wE, wordProd_coe]
  exact w0_toMat.1

theorem w0E_inv_coe
    : (((wE 119)⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = antiM := by
  rw [wE, wordProd_inv, wordProd_coe]
  exact w0_toMat.2

theorem antiM_mul (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i j : Fin 5) :
    (antiM * M) i j = M (Fin.rev i) j := by
  rw [mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [antiM]
  · intro k _ hk
    simp [antiM, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_antiM (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i j : Fin 5) :
    (M * antiM) i j = M i (Fin.rev j) := by
  rw [mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [antiM]
  · intro k _ hk
    have : j ≠ Fin.rev k := fun h => hk (by rw [h, Fin.rev_rev])
    simp [antiM, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def twistα : G5 ≃* G5 := (invTransposeSL 5 (ZMod 2)).trans (MulAut.conj (wE 119))

theorem twistα_coe
    (g : G5) : (twistα g : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
    antiM * ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ * antiM := by
  rw [twistα, MulEquiv.trans_apply, MulAut.conj_apply, coe_mul5, coe_mul5, invTransposeSL_coe,
    w0E_coe, w0E_inv_coe]

theorem twistα_mem
    {u : G5} (hu : u ∈ Ugrp) : twistα u ∈ Ugrp := by
  rw [mem_Ugrp, twistα_coe]
  have hL : IsLoU ((u⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ :=
    transpose_upU (Ugrp.inv_mem hu)
  intro a b
  rw [mul_antiM, antiM_mul]
  exact ⟨fun hba => (hL _ _).1 (Fin.rev_lt_rev.mpr hba), fun hab => (hL _ _).2 (by rw [hab])⟩

theorem twist_checks : ∀ s : Fin 4, antiM * (xM s)ᵀ * antiM = xM (Fin.rev s) ∧
    antiM * (yM s)ᵀ * antiM = yM (Fin.rev s) := by
  decide +kernel

theorem twistα_xE
    (s : Fin 4) : twistα (xE s) = xE (Fin.rev s) := by
  apply Subtype.ext
  rw [twistα_coe, xE_inv]
  exact (twist_checks s).1

theorem twistα_yE
    (s : Fin 4) : twistα (yE s) = yE (Fin.rev s) := by
  apply Subtype.ext
  rw [twistα_coe, yE_inv]
  exact (twist_checks s).2

theorem Th_twist
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G5 V) (s : Fin 4) :
    Th (ρ.comp twistα.toMonoidHom) s = Th ρ (Fin.rev s) :=
  Th_comp ρ twistα (twistα_xE s) (twistα_yE s)

abbrev natTw : Representation (ZMod 2) G5 (Fin 5 → ZMod 2) := natRep.comp twistα.toMonoidHom

theorem natTw_simple
    : IsSimpleRep natTw := isSimpleRep_comp natRep_simple twistα

theorem e0_mem_fixU_tw
    : e0 ∈ fixU natTw := fixU_comp natRep twistα (fun _ hu => twistα_mem hu)
  e0_mem_fixU

theorem natTw_type
    (s : Fin 4) : Th natTw s e0 = 0 ↔ s ≠ 3 := by
  rw [Th_twist, natRep_type]
  revert s
  decide

abbrev wedgeTw : Representation (ZMod 2) G5 (Fin 10 → ZMod 2) := wedgeRep.comp twistα.toMonoidHom

theorem wedgeTw_apply (g : G5) (w : Fin 10 → ZMod 2) : wedgeTw g w = wedgeRep (twistα g) w := by
  simp only [wedgeTw, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem wedgeTw_simple
    : IsSimpleRep wedgeTw := isSimpleRep_comp wedge_simple twistα

theorem e01_mem_fixU_tw
    : e01 ∈ fixU wedgeTw := fixU_comp wedgeRep twistα
  (fun _ hu => twistα_mem hu) e01_mem_fixU

theorem wedgeTw_type
    (s : Fin 4) : Th wedgeTw s e01 = 0 ↔ s ≠ 2 := by
  rw [Th_twist, wedge_type]
  revert s
  decide

end CFSG.Quasithin.JonesParshall.Curtis

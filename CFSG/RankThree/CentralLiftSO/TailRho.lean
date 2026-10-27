module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalTorusMaps
public import CFSG.RankThree.CentralLiftSO.SplitWeyl
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen

public section

namespace CFSG.RankThree.CentralLiftSO.TailO

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2W coe_sl2W coe_sl2W_inv
  sl2ConjDiag coe_sl2ConjDiag sl2Diag coe_sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (etaLin coordIdx coordIdx_inl_ne
  etaLin_of_upper etaLin_of_lower coe_transvection_zero_one coe_transvection_one_zero
  torusElt torusElt_apply torusElt_mul_etaLin swap_mul_swap_mem_signedPermGroup etaLin_eq
  etaMat_swap_args sl2Swap ne_succ_of_lt)
open CFSG.RankThree.CentralLiftSO.SplitO (mul_etaLin_of_autMat autMat_etaLin etaMat_sl2W_eq wSign
  wSign_ne_zero wSign_swap_mul_self)

variable {K L : Type} [Field K] [Field L] [Algebra K L] {r : ℕ}

section NegY

variable (K L) in
@[expose] noncomputable def negY (i : Fin r) :
    ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L) :=
  (LinearEquiv.piCongrRight fun c =>
    LinearEquiv.smulOfUnit (if c = Sum.inr i then -1 else 1 : Kˣ)).prodCongr
      (LinearEquiv.refl K L)

theorem negY_apply_fst (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) (c : Fin r ⊕ Fin r) :
    (negY K L i v).1 c = (if c = Sum.inr i then -1 else 1) * v.1 c := by
  change ((if c = Sum.inr i then -1 else 1 : Kˣ) : K) • v.1 c = _
  rw [smul_eq_mul]
  split_ifs <;> simp

theorem negY_apply_snd (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) : (negY K L i v).2 = v.2 :=
  rfl

theorem negY_negY (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) :
    negY K L i (negY K L i v) = v := by
  refine Prod.ext (funext fun c => ?_) rfl
  rw [negY_apply_fst, negY_apply_fst, ← mul_assoc]
  split_ifs <;> simp

theorem negY_mul_self (i : Fin r) : negY K L i * negY K L i = 1 :=
  LinearEquiv.ext fun v => negY_negY i v

theorem negY_inv (i : Fin r) : (negY K L i)⁻¹ = negY K L i :=
  inv_eq_of_mul_eq_one_right (negY_mul_self i)

end NegY

variable (T : NormTailData K L)

@[expose] noncomputable def hermO (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) :
    Matrix (Fin 2) (Fin 2) L :=
  herm T i (negY K L i v)

theorem hermO_eq (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) :
    hermO T i v =
      !![algebraMap K L (v.1 (.inl i)), v.2; T.bar v.2, -algebraMap K L (v.1 (.inr i))] := by
  rw [hermO, herm_eq, negY_apply_fst, negY_apply_fst, negY_apply_snd]
  simp

theorem eq_of_hermO_eq (i : Fin r) {v w : (Fin r ⊕ Fin r → K) × L}
    (h : hermO T i v = hermO T i w) (h' : ∀ c, c ≠ .inl i → c ≠ .inr i → v.1 c = w.1 c) :
    v = w := by
  have := eq_of_herm_eq T i h fun c h1 h2 => by
    rw [negY_apply_fst, negY_apply_fst, h' c h1 h2]
  rw [← negY_negY i v, this, negY_negY]

@[expose] noncomputable def rhoO (i : Fin r) :
    SpecialLinearGroup (Fin 2) L →* ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L) :=
  (MulAut.conj (negY K L i)).toMonoidHom.comp (rho T i)

theorem rhoO_apply (i : Fin r) (A : SpecialLinearGroup (Fin 2) L)
    (v : (Fin r ⊕ Fin r → K) × L) : rhoO T i A v = negY K L i (rho T i A (negY K L i v)) := by
  rw [rhoO, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, negY_inv]
  rfl

theorem hermO_rhoO (i : Fin r) (A : SpecialLinearGroup (Fin 2) L)
    (v : (Fin r ⊕ Fin r → K) × L) : hermO T i (rhoO T i A v) = act T A.1 (hermO T i v) := by
  rw [hermO, rhoO_apply, negY_negY, herm_rho]
  rfl

theorem rhoO_apply_of_ne (i : Fin r) (A : SpecialLinearGroup (Fin 2) L)
    (v : (Fin r ⊕ Fin r → K) × L) {c : Fin r ⊕ Fin r} (h1 : c ≠ .inl i) (h2 : c ≠ .inr i) :
    (rhoO T i A v).1 c = v.1 c := by
  rw [rhoO_apply, negY_apply_fst, rho_apply_of_ne T i A _ h1 h2, negY_apply_fst, ← mul_assoc]
  split_ifs <;> simp

theorem rhoO_upperSL (i : Fin r) (t : L) :
    rhoO T i (upperSL L t) =
      eichler (quadTail r (normForm T)) (hypVec K L (.inl i)) (0, -t) := by
  refine LinearEquiv.ext fun v => eq_of_hermO_eq T i ?_ fun c h1 h2 => ?_
  · rw [hermO_rhoO, coe_upperSL, hermO_eq, hermO_eq, act_fin_two, eichler_hypVec_tail_fst,
      eichler_hypVec_tail_fst, eichler_hypVec_tail_snd]
    simp only [Sum.swap_inl, ↓reduceIte, reduceCtorEq, sub_zero]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_
    · rw [map_sub, map_add, RingHom.map_mul, algebraMap_polar_normForm, algebraMap_normForm,
        map_one]
      simp only [map_neg]
      ring
    · rw [map_zero, map_one, Algebra.smul_def]
      ring
    · rw [map_one, map_add, map_smul, Algebra.smul_def, map_neg]
      ring
    · rw [map_zero, map_one]
      ring
  · rw [rhoO_apply_of_ne T i _ v h1 h2, eichler_hypVec_tail_fst, ite_eq_right h1, sub_zero]

theorem rhoO_lowerSL (i : Fin r) (t : L) :
    rhoO T i (lowerSL L t) =
      eichler (quadTail r (normForm T)) (hypVec K L (.inr i)) (0, T.bar t) := by
  refine LinearEquiv.ext fun v => eq_of_hermO_eq T i ?_ fun c h1 h2 => ?_
  · rw [hermO_rhoO, coe_lowerSL, hermO_eq, hermO_eq, act_fin_two, eichler_hypVec_tail_fst,
      eichler_hypVec_tail_fst, eichler_hypVec_tail_snd]
    simp only [Sum.swap_inr, ↓reduceIte, reduceCtorEq, sub_zero]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_
    · rw [map_zero, map_one]
      ring
    · rw [map_one, Algebra.smul_def]
      ring
    · rw [map_zero, map_one, map_add, map_smul, T.bar_bar, Algebra.smul_def]
      ring
    · rw [map_one, map_sub, map_add, RingHom.map_mul, algebraMap_polar_normForm,
        algebraMap_normForm, T.bar_bar]
      ring
  · rw [rhoO_apply_of_ne T i _ v h1 h2, eichler_hypVec_tail_fst, ite_eq_right h2, sub_zero]

theorem rhoO_diagSL (i : Fin r) (s : Lˣ) :
    rhoO T i (diagSL L s) = torusMap L (Pi.mulSingle i (normUnits T s)) (barQuot T s) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoO_apply, rho_diagSL_eq_torusMap]
  refine Prod.ext (funext fun c => ?_) rfl
  rw [negY_apply_fst]
  simp only [torusMap_apply]
  rw [negY_apply_fst]
  split_ifs <;> ring

theorem rhoO_sl2W_apply (i : Fin r) (v : (Fin r ⊕ Fin r → K) × L) :
    rhoO T i sl2W v = (fun c => if c = .inl i then -v.1 (.inr i) else if c = .inr i then
      -v.1 (.inl i) else v.1 c, -T.bar v.2) := by
  refine eq_of_hermO_eq T i ?_ fun c h1 h2 => ?_
  · rw [hermO_rhoO, coe_sl2W, hermO_eq, hermO_eq, act_fin_two]
    simp only [↓reduceIte, reduceCtorEq, map_neg, T.bar_bar]
    refine fin_two_matrix_eq ?_ ?_ ?_ ?_ <;>
      (try simp only [map_zero, map_one]) <;> ring
  · rw [rhoO_apply_of_ne T i _ v h1 h2]
    simp [h1, h2]

theorem upperSL_neg_one_mul_lowerSL_one_mul_upperSL_neg_one :
    upperSL L (-1) * lowerSL L 1 * upperSL L (-1) = (sl2W : SpecialLinearGroup (Fin 2) L) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_upperSL,
    coe_lowerSL, coe_sl2W]
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rhoO_sl2W (i : Fin r) :
    rhoO T i sl2W =
      shortWeyl (hypPairT r (normForm T) i) ((0, 1) : (Fin r ⊕ Fin r → K) × L) := by
  have hq : quadTail r (normForm T) ((0, 1) : (Fin r ⊕ Fin r → K) × L) = 1 := by
    rw [quadTail_tail, normForm_one]
  rw [← upperSL_neg_one_mul_lowerSL_one_mul_upperSL_neg_one, map_mul, map_mul, rhoO_upperSL,
    rhoO_lowerSL, shortWeyl, hq, inv_one, one_smul, hypPairT_e, hypPairT_f, neg_neg, map_one]

theorem rhoO_mem (i : Fin r) (A : SpecialLinearGroup (Fin 2) L) :
    rhoO T i A ∈ orthElementaryGroup (quadTail r (normForm T)) := by
  have h : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) L)).map (rhoO T i) ≤
      orthElementaryGroup (quadTail r (normForm T)) := by
    rw [← CFSG.LinearGroups.special_linear_elementary_generation, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, b, hab, c, rfl⟩, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change rhoO T i (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) ∈ _
      rw [transvection_zero_one, rhoO_upperSL]
      exact eichler_mem_elementaryGroup _ _ _
    · change rhoO T i (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) ∈ _
      rw [transvection_one_zero, rhoO_lowerSL]
      exact eichler_mem_elementaryGroup _ _ _
    · exact absurd rfl hab
  exact h ⟨A, trivial, rfl⟩

@[expose] noncomputable def rhoOG (i : Fin r) : SpecialLinearGroup (Fin 2) L →* G0 T r :=
  (rhoO T i).codRestrict _ (rhoO_mem T i)

theorem coe_rhoOG (i : Fin r) (A : SpecialLinearGroup (Fin 2) L) :
    (rhoOG T i A : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) = rhoO T i A :=
  rfl

section SL2

variable {F : Type} [Field F]

theorem diagSL_eq_sl2Diag (s : Fˣ) : diagSL F s = sl2Diag s :=
  rfl

theorem barSL_sl2W : barSL T sl2W = sl2W := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  rw [coe_barSL, coe_sl2W]
  fin_cases a <;> fin_cases b <;> simp

end SL2

include T in
theorem eta_eq_prodHom {i j : Fin r} (hij : i ≠ j) :
    eta L hij = (prodHom L).comp (etaLin (k := K) (coordIdx_inl_ne hij)) := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
  rintro _ ⟨a, b, hab, c, rfl⟩
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · change eta L hij (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) =
      (prodHom L).comp (etaLin (k := K) (coordIdx_inl_ne hij))
        (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c)
    rw [eta_transvection_zero_one, psi_transvection T hij c, MonoidHom.comp_apply,
      etaLin_of_upper _ (coe_transvection_zero_one _ c), prodHom_apply, hypVec_smul, hypVec,
      eichler_prod_fst, Sum.swap_inl]
  · change eta L hij (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) =
      (prodHom L).comp (etaLin (k := K) (coordIdx_inl_ne hij))
        (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c)
    rw [eta_transvection_one_zero, psi_transvection T hij.symm c, MonoidHom.comp_apply,
      etaLin_of_lower _ (coe_transvection_one_zero _ c), prodHom_apply, hypVec_smul, hypVec,
      eichler_prod_fst, Sum.swap_inl]
  · exact absurd rfl hab

include T in
theorem eta_apply_fst {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K)
    (v : (Fin r ⊕ Fin r → K) × L) : (eta L hij A v).1 = etaLin (coordIdx_inl_ne hij) A v.1 := by
  rw [eta_eq_prodHom T hij]
  rfl

theorem torusMap_fst (a : Fin r → Kˣ) (c : Lˣ) (v : (Fin r ⊕ Fin r → K) × L) :
    (torusMap L a c v).1 = torusElt r K a v.1 := by
  funext k
  rw [torusMap_apply, torusElt_apply]
  rcases k with i | i <;> rfl

include T in
theorem torusMap_mul_eta (a : Fin r → Kˣ) (c : Lˣ) {i j : Fin r} (hij : i ≠ j)
    (A : SpecialLinearGroup (Fin 2) K) :
    torusMap L a c * eta L hij A =
      eta L hij (sl2ConjDiag ((a i)⁻¹ * a j) A) * torusMap L a c := by
  have h := LinearEquiv.congr_fun (torusElt_mul_etaLin (coordIdx_inl_ne hij) a A)
  simp only [Sum.elim_inl, LinearEquiv.mul_apply] at h
  refine LinearEquiv.ext fun v => Prod.ext ?_ rfl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, torusMap_fst, eta_apply_fst T,
    eta_apply_fst T, torusMap_fst]
  exact h v.1

theorem mul_rhoO_of_hermO {g : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)}
    {j l : Fin r} {Φ : Matrix (Fin 2) (Fin 2) L → Matrix (Fin 2) (Fin 2) L}
    (hg : ∀ v, hermO T l (g v) = Φ (hermO T j v))
    (hsupp : ∀ d : (Fin r ⊕ Fin r → K) × L, (∀ c, c ≠ .inl j → c ≠ .inr j → d.1 c = 0) →
      ∀ c, c ≠ .inl l → c ≠ .inr l → (g d).1 c = 0)
    {A A' : SpecialLinearGroup (Fin 2) L} (hΦ : ∀ X, Φ (act T A.1 X) = act T A'.1 (Φ X)) :
    g * rhoO T j A = rhoO T l A' * g := by
  refine LinearEquiv.ext fun v => eq_of_hermO_eq T l ?_ fun c h1 h2 => ?_
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hermO_rhoO, hermO_rhoO, hg, hΦ]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, rhoO_apply_of_ne T l _ _ h1 h2]
    have h := hsupp (rhoO T j A v - v) (fun c' h1' h2' => by
      rw [Prod.fst_sub, Pi.sub_apply, rhoO_apply_of_ne T j A v h1' h2', sub_self]) c h1 h2
    rwa [map_sub, Prod.fst_sub, Pi.sub_apply, sub_eq_zero] at h

theorem coe_sl2ConjDiag_mul (u : Lˣ) (A : SpecialLinearGroup (Fin 2) L) :
    (sl2ConjDiag u A : Matrix (Fin 2) (Fin 2) L) * !![1, 0; 0, (u : L)] =
      !![1, 0; 0, (u : L)] * (A : Matrix (Fin 2) (Fin 2) L) := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [coe_sl2ConjDiag, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem coe_sl2ConjDiag_inv_mul (u : Lˣ) (A : SpecialLinearGroup (Fin 2) L) :
    (sl2ConjDiag u⁻¹ A : Matrix (Fin 2) (Fin 2) L) * !![(u : L), 0; 0, 1] =
      !![(u : L), 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) L) := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [coe_sl2ConjDiag, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem hermO_torusMap (j : Fin r) (a : Fin r → Kˣ) {c : Lˣ} (hc : c ∈ normOne T)
    (v : (Fin r ⊕ Fin r → K) × L) :
    hermO T j (torusMap L a c v) = (((a j)⁻¹ : Kˣ) : K) •
      act T !![((Units.map (algebraMap K L : K →* L) (a j) * c : Lˣ) : L), 0; 0, 1]
        (hermO T j v) := by
  have hc' := mul_bar_eq_one T hc
  have ha : algebraMap K L (a j) ≠ 0 := by simp
  rw [hermO_eq, hermO_eq, act_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [torusMap_apply, torusScal, Algebra.smul_def] <;>
    rw [eq_inv_mul_iff_mul_eq₀ ha]
  · linear_combination (-(algebraMap K L (a j) * algebraMap K L (a j) *
      algebraMap K L (v.1 (.inl j)))) * hc'
  · ring
  · ring

theorem torusMap_mul_rhoO (a : Fin r → Kˣ) {c : Lˣ} (hc : c ∈ normOne T) (j : Fin r)
    (A : SpecialLinearGroup (Fin 2) L) :
    torusMap L a c * rhoO T j A =
      rhoO T j (sl2ConjDiag (Units.map (algebraMap K L : K →* L) (a j) * c)⁻¹ A) *
        torusMap L a c := by
  refine mul_rhoO_of_hermO T (Φ := fun X => (((a j)⁻¹ : Kˣ) : K) •
    act T !![((Units.map (algebraMap K L : K →* L) (a j) * c : Lˣ) : L), 0; 0, 1] X)
    (fun v => hermO_torusMap T j a hc v) ?_ ?_
  · intro d hd c' h1 h2
    rw [torusMap_fst, torusElt_apply, hd c' h1 h2, mul_zero]
  · intro X
    rw [act_smul, ← act_mul, ← act_mul, coe_sl2ConjDiag_inv_mul]

theorem eta_sl2W_apply_fst {a b : Fin r} (hab : a ≠ b) (v : (Fin r ⊕ Fin r → K) × L)
    (c : Fin r ⊕ Fin r) :
    (eta L hab sl2W v).1 c =
      if c = .inl a then -v.1 (.inl b) else if c = .inl b then v.1 (.inl a)
      else if c = .inr a then -v.1 (.inr b) else if c = .inr b then v.1 (.inr a) else v.1 c := by
  rw [eta_apply, pairLin_apply, coe_sl2W_inv]
  rcases c with k | k
  · by_cases hka : k = a
    · subst hka
      simp [pairVec]
    · by_cases hkb : k = b
      · subst hkb
        simp [pairVec, hka]
      · simp [pairVec, hka, hkb]
  · by_cases hka : k = a
    · subst hka
      simp [pairVec]
    · by_cases hkb : k = b
      · subst hkb
        simp [pairVec, hka]
      · simp [pairVec, hka, hkb]

theorem eta_apply_snd {a b : Fin r} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) K)
    (v : (Fin r ⊕ Fin r → K) × L) : (eta L hab A v).2 = v.2 :=
  rfl

theorem hermO_eta_sl2W {a b : Fin r} (hab : a ≠ b) (v : (Fin r ⊕ Fin r → K) × L) :
    hermO T a (eta L hab sl2W v) =
      (-1 : K) • act T !![1, 0; 0, ((-1 : Lˣ) : L)] (hermO T b v) := by
  rw [hermO_eq, hermO_eq, act_fin_two, eta_sl2W_apply_fst, eta_sl2W_apply_fst, eta_apply_snd]
  ext p q
  fin_cases p <;> fin_cases q <;> simp

theorem eta_sl2W_mul_rhoO {a b : Fin r} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) L) :
    eta L hab sl2W * rhoO T b A = rhoO T a (sl2ConjDiag (-1) A) * eta L hab sl2W := by
  refine mul_rhoO_of_hermO T (Φ := fun X => (-1 : K) • act T !![1, 0; 0, ((-1 : Lˣ) : L)] X)
    (hermO_eta_sl2W T hab) ?_ ?_
  · intro d hd c h1 h2
    rw [eta_sl2W_apply_fst, ite_eq_right h1]
    by_cases h3 : c = .inl b
    · rw [ite_eq_left h3]
      exact hd _ (by simpa using hab) (by simp)
    · rw [ite_eq_right h3, ite_eq_right h2]
      by_cases h4 : c = .inr b
      · rw [ite_eq_left h4]
        exact hd _ (by simp) (by simpa using hab)
      · rw [ite_eq_right h4]
        exact hd c h3 h4
  · intro X
    rw [act_smul, ← act_mul, ← act_mul, coe_sl2ConjDiag_mul]

theorem hermO_map_bar (j : Fin r) (v : (Fin r ⊕ Fin r → K) × L) :
    (hermO T j v).map T.bar =
      !![algebraMap K L (v.1 (.inl j)), T.bar v.2; v.2, -algebraMap K L (v.1 (.inr j))] := by
  rw [hermO_eq]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [T.bar_bar]

theorem hermO_rhoO_sl2W_of_ne {i j : Fin r} (hij : i ≠ j) (v : (Fin r ⊕ Fin r → K) × L) :
    hermO T j (rhoO T i sl2W v) =
      act T !![1, 0; 0, ((-1 : Lˣ) : L)] ((hermO T j v).map T.bar) := by
  have hji : j ≠ i := Ne.symm hij
  rw [hermO_map_bar, hermO_eq, rhoO_sl2W_apply, act_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [hji, T.bar_bar]

theorem rhoO_sl2W_mul_rhoO {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) L) :
    rhoO T i sl2W * rhoO T j A = rhoO T j (sl2ConjDiag (-1) (barSL T A)) * rhoO T i sl2W := by
  refine mul_rhoO_of_hermO T
    (Φ := fun X => act T !![1, 0; 0, ((-1 : Lˣ) : L)] (X.map T.bar))
    (hermO_rhoO_sl2W_of_ne T hij) ?_ ?_
  · intro d hd c h1 h2
    rw [rhoO_sl2W_apply]
    dsimp only
    split_ifs with h3 h4
    · rw [hd _ (by simp) (by simpa using hij), neg_zero]
    · rw [hd _ (by simpa using hij) (by simp), neg_zero]
    · exact hd c h1 h2
  · intro X
    rw [map_act, ← act_mul, ← act_mul, coe_sl2ConjDiag_mul, coe_barSL]

theorem eta_mul_rhoO_of_ne {i a b : Fin r} (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b)
    (B : SpecialLinearGroup (Fin 2) K) (A : SpecialLinearGroup (Fin 2) L) :
    eta L hab B * rhoO T i A = rhoO T i A * eta L hab B := by
  have hai : a ≠ i := Ne.symm hia
  have hbi : b ≠ i := Ne.symm hib
  refine mul_rhoO_of_hermO T (Φ := id) (fun v => ?_) (fun d hd c h1 h2 => ?_) fun X => rfl
  · rw [hermO_eq, hermO_eq, eta_apply_snd, eta_apply, pairLin_apply]
    simp [pairVec, hia, hib]
  · rw [eta_apply, pairLin_apply]
    rcases c with k | k
    · have hki : k ≠ i := fun h => h1 (by rw [h])
      simp only [Sum.elim_inl, pairVec, Function.comp_apply]
      split_ifs <;> simp [hd, hai, hbi, hki]
    · have hki : k ≠ i := fun h => h2 (by rw [h])
      simp only [Sum.elim_inr, pairVec, Function.comp_apply]
      split_ifs <;> simp [hd, hai, hbi, hki]

include T in
theorem eta_sl2W_mul_eta {c d : Fin r} (hcd : c ≠ d) {a b a' b' : Fin r} (hab : a ≠ b)
    (hab' : a' ≠ b')
    (ha : (Equiv.swap (Sum.inl c : Fin r ⊕ Fin r) (Sum.inl d) *
      Equiv.swap (Sum.inl c : Fin r ⊕ Fin r).swap (Sum.inl d : Fin r ⊕ Fin r).swap)
        (Sum.inl a) = Sum.inl a')
    (hb : (Equiv.swap (Sum.inl c : Fin r ⊕ Fin r) (Sum.inl d) *
      Equiv.swap (Sum.inl c : Fin r ⊕ Fin r).swap (Sum.inl d : Fin r ⊕ Fin r).swap)
        (Sum.inl b) = Sum.inl b')
    {u : Kˣ} (hu : wSign (k := K) (Sum.inl d) (Sum.inl a) * u = wSign (Sum.inl d) (Sum.inl b))
    (g : SpecialLinearGroup (Fin 2) K) :
    eta L hcd sl2W * eta L hab g = eta L hab' (sl2ConjDiag u g) * eta L hcd sl2W := by
  rw [eta_eq_prodHom T hcd, eta_eq_prodHom T hab, eta_eq_prodHom T hab']
  simp only [MonoidHom.comp_apply, ← map_mul]
  rw [mul_etaLin_of_autMat (swap_mul_swap_mem_signedPermGroup (coordIdx_inl_ne hcd))
    (by rw [autMat_etaLin, etaMat_sl2W_eq (coordIdx_inl_ne hcd)]) (coordIdx_inl_ne hab)
    (coordIdx_inl_ne hab') ha hb
    (wSign_ne_zero _ _) (wSign_swap_mul_self _ _) (wSign_swap_mul_self _ _) hu g]

include T in
theorem eta_symm {i j : Fin r} (hij : i ≠ j) :
    eta L hij.symm = (eta (K := K) L hij).comp sl2Swap := by
  rw [eta_eq_prodHom T hij.symm, eta_eq_prodHom T hij, MonoidHom.comp_assoc]
  congr 1
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.comp_apply, etaLin_eq, etaLin_eq]
  exact congrArg _ (Units.ext (etaMat_swap_args (coordIdx_inl_ne hij) g))

include T in
theorem eta_sl2W_eq_tailWeylElt_inv {i : Fin r} (h : i.val + 1 < r) (a₀ : L) :
    eta L (ne_succ_of_lt h) sl2W = (tailWeylElt r (normForm T) a₀ i)⁻¹ := by
  rw [tailWeylElt_eq_prodCongr a₀ h, SplitO.weylElt_eq_etaLin_of_lt h, eta_eq_prodHom T,
    MonoidHom.comp_apply, ← prodHom_apply, map_inv, map_inv, inv_inv]

theorem rhoO_sl2W_eq_tailWeylElt {i : Fin r} (h : ¬i.val + 1 < r) :
    rhoO T i sl2W = tailWeylElt r (normForm T) 1 i := by
  rw [tailWeylElt_of_not_lt 1 h, rhoO_sl2W]

theorem torusMap_mem_tailTorus (a : Fin r → Kˣ) {c : Lˣ} (hc : c ∈ normOne T)
    (hE : torusMap L a c ∈ orthElementaryGroup (quadTail r (normForm T))) :
    torusMap L a c ∈ tailTorus r (normForm T) := by
  refine mem_tailTorus.2 ⟨hE, a, Units.mulLeftLinearEquiv K L c,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun z => ?_,
    LinearEquiv.ext fun v => Prod.ext (torusMap_fst a c v).symm rfl⟩
  rw [Units.mulLeftLinearEquiv_apply, normForm_mul, (mem_normOne T).1 hc, one_mul]

end CFSG.RankThree.CentralLiftSO.TailO

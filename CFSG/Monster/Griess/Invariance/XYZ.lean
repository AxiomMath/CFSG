module

public import CFSG.Monster.Griess.TrialityMatrix
public import CFSG.Monster.Griess.TrilinearData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix

namespace XYZInv

noncomputable abbrev oddVec (c : C₀) (i : Fin 24) (k : Fin 3) : SpaceB :=
  tbasis (.inr (.inr (.inl (c, i, k))))

@[expose] noncomputable def oddSpan (k : Fin 3) : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun q : C₀ × Fin 24 => oddVec q.1 q.2 k)

theorem oddVec_mem_oddSpan (c : C₀) (i : Fin 24) (k : Fin 3) : oddVec c i k ∈ oddSpan k :=
  Submodule.subset_span ⟨(c, i), rfl⟩

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

theorem tauB_oddVec (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB (oddVec c i k) = oddVec c i (k + 1) :=
  tauB_odd c i k

theorem tauB_symm_oddVec (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB.symm (oddVec c i (k + 1)) = oddVec c i k := by
  rw [← tauB_oddVec, LinearEquiv.symm_apply_apply]

theorem smul_tensor_eq (s : ℚ) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    s • tensor q v = tensor (s • q) v := by
  rw [tensor, tensor, smul_vecMulVec]

theorem oddVec_zero (c : C₀) (i : Fin 24) : oddVec c i 0 = inX (Xlift (rOdd c i)) :=
  tbasis_odd_zero c i

theorem oddVec_one (c : C₀) (i : Fin 24) :
    oddVec c i 1 =
      inW (tensor (sgn (((c : C) : Fin 24 → ZMod 2) i) • Spin.E 1 c) (Pi.single i 1)) := by
  rw [← smul_tensor_eq]
  exact tbasis_odd_one c i

theorem oddVec_two (c : C₀) (i : Fin 24) :
    oddVec c i 2 =
      inW (tensor (sgn (P ((c : C) : Fin 24 → ZMod 2)) • Spin.E 0 c) (Pi.single i 1)) := by
  rw [← smul_tensor_eq]
  exact tbasis_odd_two c i

theorem pair_mk_single (a : C) (i : Fin 24) :
    pair a (Submodule.Quotient.mk (Pi.single i 1)) = (a : Fin 24 → ZMod 2) i := by
  rw [pair_mk, dotProduct_single, mul_one]

theorem μ₀_aOdd (a : C₀) (i : Fin 24) : μ₀ (aOdd a i) = mOdd a i := by
  rw [aOdd, map_add, map_smul, μ₀_coe, μ₀_ΩC, smul_eq_mul, mul_one, zero_add]

theorem θ_aOdd (a : C₀) (i : Fin 24) (u : C) : θ (aOdd a i) u = θ a u := by
  rw [aOdd]
  rcases zmod2_cases (mOdd a i) with h | h
  · rw [h, zero_smul, add_zero]
  · rw [h, one_smul]
    exact θ_add_Ω _ _

theorem coe_shift_aOdd (a b : C₀) (i : Fin 24) : (shift (aOdd a i) b : C) = (b : C) + a := by
  rw [coe_shift, μ₀_aOdd, aOdd, add_assoc (b : C), add_assoc (a : C), add_self_C, add_zero]

theorem shift_aOdd_eq_iff (a b c : C₀) (i : Fin 24) : shift (aOdd a i) b = c ↔ a + b + c = 0 := by
  rw [add_eq_zero_iff' (M := C₀)]
  constructor
  · intro h
    apply Subtype.ext
    rw [← h, coe_shift_aOdd, Submodule.coe_add, add_comm]
  · intro h
    apply Subtype.ext
    rw [h, coe_shift_aOdd, Submodule.coe_add, add_comm]

theorem coe_rOdd (a : C₀) (i : Fin 24) :
    ((rOdd a i : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ 0 (aOdd a i) (thetaD (aOdd a i) + Submodule.Quotient.mk (Pi.single i 1)) := by
  rw [coe_Q_eq, centralCoord_rOdd, coordOf_rOdd]

theorem E_one_vecMul_rOdd (a b : C₀) (i : Fin 24) :
    Spin.E 1 b ᵥ* ((rOdd a i : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (θ a b + ((b : C) : Fin 24 → ZMod 2) i) • Spin.E 0 (shift (aOdd a i) b) := by
  rw [coe_rOdd, Spin.E, single_vecMul_qmatR, sgnR_rat, Spin.E]
  have hp : qPerm (aOdd a i) (thetaD (aOdd a i) + Submodule.Quotient.mk (Pi.single i 1)) (1, b) =
      (0, shift (aOdd a i) b) := by
    rw [qPerm, pair_add_right, pair_ΩC_thetaD, pair_mk_single, coe_ΩC]
    rfl
  have hs : qSign 0 (aOdd a i) (thetaD (aOdd a i) + Submodule.Quotient.mk (Pi.single i 1)) (1, b) =
      θ a b + ((b : C) : Fin 24 → ZMod 2) i := by
    rw [qSign, pair_add_right, pair_thetaD, pair_mk_single, θ_shift, θ_self, θ_aOdd, P_aOdd,
      μ₀_aOdd, coe_shift_aOdd, mOdd]
    simp only [Submodule.coe_add, Pi.add_apply]
    linear_combination (((a : C) : Fin 24 → ZMod 2) i + P ((a : C) : Fin 24 → ZMod 2)) *
      two_eq_zero'
  rw [hp, hs]

theorem E_one_vecMul_rOdd_dotProduct (a b c : C₀) (i : Fin 24) :
    (Spin.E 1 b ᵥ* ((rOdd a i : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ Spin.E 0 c =
      if a + b + c = 0 then sgn (θ a b + ((b : C) : Fin 24 → ZMod 2) i) else 0 := by
  rw [E_one_vecMul_rOdd, smul_dotProduct, E_dotProduct_E, smul_eq_mul]
  by_cases h : a + b + c = 0
  · rw [ite_eq_left (by rw [(shift_aOdd_eq_iff a b c i).2 h]), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun h' => h ((shift_aOdd_eq_iff a b c i).1 (congrArg Prod.snd h'))),
      ite_eq_right h, mul_zero]

theorem isShortCoord_rOdd (a : C₀) (i : Fin 24) : IsShortCoord (coordOf (rOdd a i)) :=
  ⟨oddMin i ((a : C) : Fin 24 → ZMod 2), oddMin_mem a i, (phi0_coordOf_rOdd a i).symm⟩

theorem uvec_rOdd (a : C₀) (i : Fin 24) (hr : IsShortCoord (coordOf (rOdd a i))) :
    oddMin i ((a : C) : Fin 24 → ZMod 2) = uvec ⟨coordOf (rOdd a i), hr⟩ ∨
      oddMin i ((a : C) : Fin 24 → ZMod 2) = -uvec ⟨coordOf (rOdd a i), hr⟩ :=
  (classOf_eq_iff (uvec_mem _) (oddMin_mem a i)).1
    ((classOf_uvec _).trans (phi0_coordOf_rOdd a i))

theorem cast_neg_one_pow_val (t : ZMod 2) : (((-1 : ℤ) ^ t.val : ℤ) : ℚ) = sgn t := by
  rcases zmod2_cases t with rfl | rfl
  · rfl
  · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, show sgn 1 = -1 from rfl]
    norm_num

theorem cast_oddMin (i : Fin 24) (d : Fin 24 → ZMod 2) (j : Fin 24) :
    ((oddMin i d j : ℤ) : ℚ) = sgn (d j) * (1 - 4 * if j = i then 1 else 0) := by
  rw [oddMin, Int.cast_mul, cast_neg_one_pow_val]
  push_cast
  rfl

theorem uQ_rOdd_mul (a : C₀) (i : Fin 24) (hr : IsShortCoord (coordOf (rOdd a i))) (j k : Fin 24) :
    uQ ⟨coordOf (rOdd a i), hr⟩ j * uQ ⟨coordOf (rOdd a i), hr⟩ k =
      sgn (((a : C) : Fin 24 → ZMod 2) j) * (1 - 4 * if j = i then 1 else 0) *
        (sgn (((a : C) : Fin 24 → ZMod 2) k) * (1 - 4 * if k = i then 1 else 0)) := by
  rw [← cast_oddMin, ← cast_oddMin]
  show ((uvec _ j : ℤ) : ℚ) * ((uvec _ k : ℤ) : ℚ) = _
  rcases uvec_rOdd a i hr with h | h
  · rw [← h]
  · rw [h, Pi.neg_apply, Pi.neg_apply, Int.cast_neg, Int.cast_neg, neg_mul_neg]


theorem T_oddVec_one_two_zero (a b c : C₀) (i j k : Fin 24) :
    T (oddVec b j 1) (oddVec c k 2) (oddVec a i 0) =
      sgn (((b : C) : Fin 24 → ZMod 2) j) * (sgn (P ((c : C) : Fin 24 → ZMod 2)) *
        (if a + b + c = 0 then sgn (θ a b + ((b : C) : Fin 24 → ZMod 2) i) else 0)) *
      ((if j = k then 1 else 0) -
        sgn (((a : C) : Fin 24 → ZMod 2) j) * (1 - 4 * if j = i then 1 else 0) *
          (sgn (((a : C) : Fin 24 → ZMod 2) k) * (1 - 4 * if k = i then 1 else 0)) / 4) / 8 := by
  have hr := isShortCoord_rOdd a i
  rw [oddVec_one, oddVec_two, oddVec_zero, T_tensor_tensor_Xlift _ _ _ _ hr, smul_vecMul,
    smul_dotProduct, dotProduct_smul, E_one_vecMul_rOdd_dotProduct, single_dotProduct_single,
    single_dotProduct, single_dotProduct, one_mul, one_mul, uQ_rOdd_mul a i hr j k, smul_eq_mul,
    smul_eq_mul]

@[expose] def xyzBracket (i j k : Fin 24) : ℚ :=
  (-(1 / 4) + (if i = j then 1 else 0) + (if i = k then 1 else 0) + (if j = k then 1 else 0) -
    4 * (if i = j ∧ j = k then 1 else 0)) / 8

@[expose] noncomputable def xyzVal (a b c : C₀) (i j k : Fin 24) : ℚ :=
  if a + b + c = 0 then
    sgn (θ a b + P ((c : C) : Fin 24 → ZMod 2) + ((b : C) : Fin 24 → ZMod 2) i +
      ((c : C) : Fin 24 → ZMod 2) j + ((a : C) : Fin 24 → ZMod 2) k) * xyzBracket i j k
  else 0

theorem xyzBracket_cycle (i j k : Fin 24) : xyzBracket k i j = xyzBracket i j k := by
  unfold xyzBracket
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik, Ne.symm hik]
  · by_cases hik : i = k
    · subst hik
      simp [hij, Ne.symm hij]
    · by_cases hjk : j = k
      · subst hjk
        simp [hij, Ne.symm hij]
      · simp [hij, hik, hjk, Ne.symm hik, Ne.symm hjk]

private theorem xyz_arith_ℚ (X Y Z W Aj Ak : ℚ) (hAj : Aj * Aj = 1) (i j k : Fin 24)
    (hjk : j = k → Aj = Ak) :
    W * (Y * (X * Z)) * ((if j = k then 1 else 0) -
      Aj * (1 - 4 * (if j = i then 1 else 0)) * (Ak * (1 - 4 * (if k = i then 1 else 0))) / 4) /
        8 = X * Y * Z * (Aj * W) * Ak * xyzBracket i j k := by
  unfold xyzBracket
  by_cases hjk' : j = k
  · subst hjk'
    obtain rfl := hjk rfl
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, and_self]
      linear_combination (-(W * X * Y * Z) / 8) * hAj
    · simp only [hij, Ne.symm hij, ite_true, ite_false, and_true]
      linear_combination (-(W * X * Y * Z) / 8) * hAj
  · by_cases hij : i = j
    · subst hij
      have hik : ¬ i = k := hjk'
      simp only [hik, Ne.symm hik, ite_true, ite_false, and_false]
      ring
    · by_cases hik : i = k
      · subst hik
        simp only [hij, Ne.symm hij, ite_true, ite_false, and_false]
        ring
      · simp only [hij, hik, hjk', Ne.symm hij, Ne.symm hik, ite_false, and_false]
        ring

private theorem xyz_arith (t p bi bj aj ak : ZMod 2) (i j k : Fin 24) (hjk : j = k → aj = ak) :
    sgn bj * (sgn p * sgn (t + bi)) * ((if j = k then 1 else 0) -
      sgn aj * (1 - 4 * (if j = i then 1 else 0)) * (sgn ak * (1 - 4 * (if k = i then 1 else 0))) /
        4) / 8 = sgn (t + p + bi + (aj + bj) + ak) * xyzBracket i j k := by
  simp only [sgn_add]
  exact xyz_arith_ℚ _ _ _ _ _ _ (sgn_mul_self aj) i j k (fun h => by rw [hjk h])

theorem T_oddVec_XYZ (a b c : C₀) (i j k : Fin 24) :
    T (oddVec a i 0) (oddVec b j 1) (oddVec c k 2) = xyzVal a b c i j k := by
  rw [T_cycle (oddVec a i 0), T_oddVec_one_two_zero, xyzVal]
  by_cases h : a + b + c = 0
  · have hc : ((c : C) : Fin 24 → ZMod 2) j =
        ((a : C) : Fin 24 → ZMod 2) j + ((b : C) : Fin 24 → ZMod 2) j := by
      rw [(add_eq_zero_iff' (M := C₀)).1 h]
      rfl
    rw [ite_eq_left h, ite_eq_left h, hc]
    exact xyz_arith _ _ _ _ _ _ i j k (fun h' => by rw [h'])
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero, zero_mul, zero_div]

theorem θ_add_left_self_add_P (a b : C) :
    θ (a + b) a + P (b : Fin 24 → ZMod 2) = θ a b + P ((a + b : C) : Fin 24 → ZMod 2) := by
  rw [θ_add_left, θ_self, Submodule.coe_add, P_add a.2 b.2, A_self_mid a.2 b.2,
    ← θ_add_θ_swap a b]
  linear_combination (-θ a b) * two_eq_zero'

theorem xyzVal_cycle (a b c : C₀) (i j k : Fin 24) : xyzVal c a b k i j = xyzVal a b c i j k := by
  have hiff : c + a + b = 0 ↔ a + b + c = 0 := by rw [add_rotate]
  unfold xyzVal
  by_cases h : a + b + c = 0
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, xyzBracket_cycle]
    obtain rfl := (add_eq_zero_iff' (M := C₀)).1 h
    refine congrArg (fun t : ZMod 2 => sgn t * xyzBracket i j k) ?_
    have e := θ_add_left_self_add_P (a : C) (b : C)
    simp only [Submodule.coe_add] at e ⊢
    linear_combination e
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]

theorem T_tauB_oddVec_XYZ (a b c : C₀) (i j k : Fin 24) :
    T (tauB (oddVec a i 0)) (tauB (oddVec b j 1)) (tauB (oddVec c k 2)) =
      T (oddVec a i 0) (oddVec b j 1) (oddVec c k 2) := by
  rw [tauB_oddVec, tauB_oddVec, tauB_oddVec]
  show T (oddVec a i 1) (oddVec b j 2) (oddVec c k 0) = _
  rw [← T_cycle (oddVec c k 0), T_oddVec_XYZ, T_oddVec_XYZ, xyzVal_cycle]

theorem tauB_symm_oddVec_zero (c : C₀) (i : Fin 24) : tauB.symm (oddVec c i 0) = oddVec c i 2 :=
  tauB_symm_oddVec c i 2

theorem tauB_symm_oddVec_one (c : C₀) (i : Fin 24) : tauB.symm (oddVec c i 1) = oddVec c i 0 :=
  tauB_symm_oddVec c i 0

theorem tauB_symm_oddVec_two (c : C₀) (i : Fin 24) : tauB.symm (oddVec c i 2) = oddVec c i 1 :=
  tauB_symm_oddVec c i 1

theorem T_tauB_symm_oddVec_XYZ (a b c : C₀) (i j k : Fin 24) :
    T (tauB.symm (oddVec a i 0)) (tauB.symm (oddVec b j 1)) (tauB.symm (oddVec c k 2)) =
      T (oddVec a i 0) (oddVec b j 1) (oddVec c k 2) := by
  rw [tauB_symm_oddVec_zero, tauB_symm_oddVec_one, tauB_symm_oddVec_two, T_cycle (oddVec a i 2),
    T_oddVec_XYZ, T_oddVec_XYZ]
  exact (xyzVal_cycle b c a j k i).symm

theorem trilinear_eq_of_mem_span₃ {F G : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ}
    {s₁ s₂ s₃ : Set SpaceB} (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ∀ z ∈ s₃, F x y z = G x y z)
    {u v w : SpaceB} (hu : u ∈ Submodule.span ℚ s₁) (hv : v ∈ Submodule.span ℚ s₂)
    (hw : w ∈ Submodule.span ℚ s₃) : F u v w = G u v w := by
  have h3 : ∀ x ∈ s₁, ∀ y ∈ s₂, F x y w = G x y w := fun x hx y hy =>
    LinearMap.eqOn_span (fun z hz => h x hx y hy z hz) hw
  have h2 : ∀ x ∈ s₁, F x v w = G x v w := fun x hx =>
    LinearMap.eqOn_span (f := (F x).flip w) (g := (G x).flip w) (fun y hy => h3 x hx y hy) hv
  exact LinearMap.eqOn_span (f := (F.flip v).flip w) (g := (G.flip v).flip w)
    (fun x hx => h2 x hx) hu

@[expose] noncomputable def Tcomp₃ (g : SpaceB →ₗ[ℚ] SpaceB) :
    SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ :=
  (T.compl₁₂ g g).compr₂ (LinearMap.lcomp ℚ ℚ g)

theorem Tcomp₃_apply (g : SpaceB →ₗ[ℚ] SpaceB) (u v w : SpaceB) :
    Tcomp₃ g u v w = T (g u) (g v) (g w) := rfl

end XYZInv

open XYZInv

theorem triality_Griess_XYZ_invariance :
    (∀ {u v w : SpaceB}, u ∈ oddSpan 0 → v ∈ oddSpan 1 → w ∈ oddSpan 2 →
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
    ∀ (a b c : C₀) (i j k : Fin 24),
      T (oddVec a i 0) (oddVec b j 1) (oddVec c k 2) =
        if a + b + c = 0 then
          sgn (θ a b + P ((c : C) : Fin 24 → ZMod 2) + ((b : C) : Fin 24 → ZMod 2) i +
            ((c : C) : Fin 24 → ZMod 2) j + ((a : C) : Fin 24 → ZMod 2) k) *
          ((-(1 / 4) + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
            (if j = k then 1 else 0) - 4 * (if i = j ∧ j = k then 1 else 0)) / 8)
        else 0 := by
  refine ⟨fun {u v w} hu hv hw => ⟨?_, ?_⟩, T_oddVec_XYZ⟩
  · have e : T (tauB u) (tauB v) (tauB w) = Tcomp₃ (tauB : SpaceB →ₗ[ℚ] SpaceB) u v w := by
      rw [Tcomp₃_apply]
      rfl
    rw [e]
    refine trilinear_eq_of_mem_span₃ ?_ hu hv hw
    rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨c, k⟩, rfl⟩
    rw [Tcomp₃_apply]
    exact T_tauB_oddVec_XYZ a b c i j k
  · have e : T (tauB.symm u) (tauB.symm v) (tauB.symm w) =
        Tcomp₃ (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) u v w := by
      rw [Tcomp₃_apply]
      rfl
    rw [e]
    refine trilinear_eq_of_mem_span₃ ?_ hu hv hw
    rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨c, k⟩, rfl⟩
    rw [Tcomp₃_apply]
    exact T_tauB_symm_oddVec_XYZ a b c i j k

end CFSG.Monster.Griess

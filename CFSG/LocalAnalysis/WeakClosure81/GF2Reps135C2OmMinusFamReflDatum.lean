module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFNW

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private noncomputable abbrev w135c2_omfMRefl_R (n : ℕ) (b c : K) :
    Vm n K ≃ₗ[K] Vm n K :=
  CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_reflect_eVec {n : ℕ} (i : Fin (n - 1)) :
    w135c2_omfMRefl_R n b c (eVec n i) = eVec n i := by
  change CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)
      (eVec n i) = eVec n i
  exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    (polar_planeVec_eVec n b c planeOne i)

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_reflect_fVec {n : ℕ} (i : Fin (n - 1)) :
    w135c2_omfMRefl_R n b c (fVec n i) = fVec n i := by
  change CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)
      (fVec n i) = fVec n i
  exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    (polar_planeVec_fVec n b c planeOne i)

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_reflect_planeVec {n : ℕ} (p : Fin 2 → K) :
    w135c2_omfMRefl_R n b c (planeVec n p) = planeVec n (planeRefl b c planeOne p) := by
  change CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus n K b c) (planeVec n planeOne)
      (planeVec n p) = planeVec n (planeRefl b c planeOne p)
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by
    rw [quadMinus_planeVec', planeNorm_planeOne]; exact one_ne_zero)]
  rw [polar_planeVec_planeVec, polarPlane_comm, quadMinus_planeVec', planeNorm_planeOne,
    div_one, planeRefl, planeNorm_planeOne, div_one, planeVec_sub, planeVec_smul]

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_eichler_conj {n : ℕ} (u w : Vm n K) :
    w135c2_omfMRefl_R n b c * CFSG.ClassicalGroups.Orthogonal.eichler (quadMinus n K b c) u w *
        w135c2_omfMRefl_R n b c =
      CFSG.ClassicalGroups.Orthogonal.eichler (quadMinus n K b c)
        (w135c2_omfMRefl_R n b c u) (w135c2_omfMRefl_R n b c w) := by
  have h := CFSG.ClassicalGroups.Orthogonal.eichler_conj
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (quadMinus n K b c)
      (planeVec n planeOne)) u w
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_inv] at h
  exact h

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_R_mul_self (n : ℕ) :
    w135c2_omfMRefl_R n b c * w135c2_omfMRefl_R n b c = 1 :=
  CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (quadMinus n K b c) (planeVec n planeOne)

private theorem w135c2_omfMRefl_spinAction (n : ℕ) (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (g : spinGroup (quadMinus n K b c)) :
    spinAction (quadMinus n K b c) (omMinusReflAut n hn hirrQ g) =
      w135c2_omfMRefl_R n b c * spinAction (quadMinus n K b c) g * w135c2_omfMRefl_R n b c :=
  spinAction_omMinusReflAut hn hirrQ g

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_commute_basis {n : ℕ} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K} (h : omqnfActs n b c π s T) :
    ∀ j : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      w135c2_omfMRefl_R n b c (T (Pi.single j 1)) =
        T (w135c2_omfMRefl_R n b c (Pi.single j 1)) := by
  have hfr : ∀ x : Fin (n - 1) ⊕ Fin (n - 1),
      w135c2_omfMRefl_R n b c (omqnfFrame n K x) = omqnfFrame n K x := by
    intro x
    rcases x with a | a
    · change w135c2_omfMRefl_R n b c (eVec n a) = eVec n a
      exact w135c2_omfMRefl_reflect_eVec a
    · change w135c2_omfMRefl_R n b c (fVec n a) = fVec n a
      exact w135c2_omfMRefl_reflect_fVec a
  have hpl : ∀ p : Fin 2 → K,
      w135c2_omfMRefl_R n b c (planeVec n p) = planeVec n (planeRefl b c planeOne p) :=
    fun p => w135c2_omfMRefl_reflect_planeVec p
  intro j
  rcases j with a | a | t
  · change w135c2_omfMRefl_R n b c (T (omqnfFrame n K (Sum.inl a))) =
      T (w135c2_omfMRefl_R n b c (omqnfFrame n K (Sum.inl a)))
    rw [h.1 (Sum.inl a), hfr (Sum.inl a), h.1 (Sum.inl a),
      hfr (spMonoPerm π s (Sum.inl a))]
  · change w135c2_omfMRefl_R n b c (T (omqnfFrame n K (Sum.inr a))) =
      T (w135c2_omfMRefl_R n b c (omqnfFrame n K (Sum.inr a)))
    rw [h.1 (Sum.inr a), hfr (Sum.inr a), h.1 (Sum.inr a),
      hfr (spMonoPerm π s (Sum.inr a))]
  · have hq : (Pi.single (Sum.inr (Sum.inr t)) (1 : K) : Vm n K) =
        planeVec n (Pi.single t 1) := by
      funext x
      rcases x with i | i | u <;> simp [planeVec, Pi.single_apply, Sum.inr.injEq]
    rw [hq]
    rw [h.2 (Pi.single t 1), hpl (Pi.single t 1),
      h.2 (planeRefl b c planeOne (Pi.single t 1)),
      hpl (if ∏ a, s a = 1 then Pi.single t 1 else planeRefl b c planeOne (Pi.single t 1))]
    by_cases hprod : ∏ a, s a = 1 <;> simp [hprod]

omit [Finite K] [CharP K 2] in
private theorem w135c2_omfMRefl_commute {n : ℕ} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K} (h : omqnfActs n b c π s T) :
    w135c2_omfMRefl_R n b c * T = T * w135c2_omfMRefl_R n b c := by
  have key := w135c2_omfMRefl_commute_basis h
  refine LinearEquiv.ext fun v => ?_
  have hlin : ((w135c2_omfMRefl_R n b c * T : Vm n K ≃ₗ[K] Vm n K) :
        Vm n K →ₗ[K] Vm n K) =
      ((T * w135c2_omfMRefl_R n b c : Vm n K ≃ₗ[K] Vm n K) :
        Vm n K →ₗ[K] Vm n K) := by
    refine LinearMap.pi_ext fun j x => ?_
    have hx : (Pi.single j x : Vm n K) = x • Pi.single j 1 := by
      rw [← Pi.single_smul']; simp
    rw [hx]
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_smul, key j]
  exact congrArg (fun f : Vm n K →ₗ[K] Vm n K => f v) hlin

private theorem w135c2_omfMRefl_twShortRoot {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    omMinusReflAut n hn hirrQ (twShortRoot n hirrQ i s (.ofAdd p)) =
      twShortRoot n hirrQ i s (.ofAdd (planeRefl b c planeOne p)) := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [w135c2_omfMRefl_spinAction n hn hirrQ, spinAction_twShortRoot_eq_eichler,
    spinAction_twShortRoot_eq_eichler, w135c2_omfMRefl_eichler_conj]
  congr 1
  · cases s
    · exact w135c2_omfMRefl_reflect_fVec i
    · exact w135c2_omfMRefl_reflect_eVec i
  · exact w135c2_omfMRefl_reflect_planeVec p

private theorem w135c2_omfMRefl_longRoot {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i j : Fin (n - 1)) (hij : i ≠ j)
    (s t : Bool) (a : K) :
    omMinusReflAut n hn hirrQ ((minusFrame n b c).longRoot hij s t (.ofAdd a)) =
      (minusFrame n b c).longRoot hij s t (.ofAdd a) := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [w135c2_omfMRefl_spinAction n hn hirrQ,
    (minusFrame n b c).spinAction_longRoot_eq_eichler hij s t a,
    w135c2_omfMRefl_eichler_conj]
  congr 1
  · cases t
    · exact w135c2_omfMRefl_reflect_fVec j
    · exact w135c2_omfMRefl_reflect_eVec j
  · rw [map_smul]
    congr 1
    cases s
    · exact w135c2_omfMRefl_reflect_fVec i
    · exact w135c2_omfMRefl_reflect_eVec i

private theorem w135c2_omfMRefl_le_comap_longRootGroup {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : Fin (n - 1) → ℤ) :
    (minusFrame n b c).longRootGroup v ≤
      ((minusFrame n b c).longRootGroup v).comap (omMinusReflAut n hn hirrQ).toMonoidHom := by
  rw [HypFrame.longRootGroup]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun s => iSup_le fun t =>
    iSup_le fun hv => ?_
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_comap]
  change omMinusReflAut n hn hirrQ ((minusFrame n b c).longRoot hij s t a) ∈ _
  rw [← ofAdd_toAdd a, w135c2_omfMRefl_longRoot hn hirrQ i j hij s t (Multiplicative.toAdd a)]
  exact Subgroup.mem_iSup_of_mem i <| Subgroup.mem_iSup_of_mem j <|
    Subgroup.mem_iSup_of_mem hij <| Subgroup.mem_iSup_of_mem s <| Subgroup.mem_iSup_of_mem t <|
      Subgroup.mem_iSup_of_mem hv ⟨Multiplicative.toAdd a, rfl⟩

private theorem w135c2_omfMRefl_le_comap_twShortRootGroup {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : Fin (n - 1) → ℤ) :
    twShortRootGroup n hirrQ v ≤
      (twShortRootGroup n hirrQ v).comap (omMinusReflAut n hn hirrQ).toMonoidHom := by
  rw [twShortRootGroup]
  refine iSup_le fun i => iSup_le fun s => iSup_le fun hv => ?_
  rintro x ⟨p, rfl⟩
  rw [Subgroup.mem_comap]
  change omMinusReflAut n hn hirrQ ((twShortRoot n hirrQ i s) p) ∈ _
  rw [← ofAdd_toAdd p, w135c2_omfMRefl_twShortRoot hn hirrQ i s (Multiplicative.toAdd p)]
  exact Subgroup.mem_iSup_of_mem i <| Subgroup.mem_iSup_of_mem s <|
    Subgroup.mem_iSup_of_mem hv ⟨planeRefl b c planeOne (Multiplicative.toAdd p), rfl⟩

private theorem w135c2_omfMRefl_map_minusRootGroup_le {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (γ : Fin (n - 1) → ℤ) :
    (minusRootGroup n hirrQ γ).map (omMinusReflAut n hn hirrQ).toMonoidHom ≤
      minusRootGroup n hirrQ γ := by
  rw [minusRootGroup]
  refine (Subgroup.map_le_iff_le_comap).mpr (sup_le ?_ ?_)
  · exact (w135c2_omfMRefl_le_comap_longRootGroup hn hirrQ (toStdB (n - 1) γ)).trans
      (Subgroup.comap_mono le_sup_left)
  · exact (w135c2_omfMRefl_le_comap_twShortRootGroup hn hirrQ (toStdB (n - 1) γ)).trans
      (Subgroup.comap_mono le_sup_right)

private theorem w135c2_omfMRefl_mem_minusRootGroup {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (γ : Fin (n - 1) → ℤ)
    {x : spinGroup (quadMinus n K b c)} (hx : x ∈ minusRootGroup n hirrQ γ) :
    omMinusReflAut n hn hirrQ x ∈ minusRootGroup n hirrQ γ :=
  w135c2_omfMRefl_map_minusRootGroup_le hn hirrQ γ (Subgroup.mem_map_of_mem _ hx)

private theorem w135c2_omfMRefl_le_comap_posUnipotent {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.LieType.Steinberg.posUnipotent (minusDatum n hirrQ) ≤
      (CFSG.LieType.Steinberg.posUnipotent (minusDatum n hirrQ)).comap
        (omMinusReflAut n hn hirrQ).toMonoidHom := by
  rw [CFSG.LieType.Steinberg.posUnipotent]
  refine iSup_le fun γ => iSup_le fun hγ => ?_
  rintro x hx
  rw [Subgroup.mem_comap]
  exact Subgroup.mem_iSup_of_mem γ <| Subgroup.mem_iSup_of_mem hγ
    (w135c2_omfMRefl_mem_minusRootGroup hn hirrQ γ hx)

private theorem w135c2_omfMRefl_eq_zero_or_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rwa [Fintype.card_eq_nat_card]
  have huniv : ({0, 1} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]; simp [zero_ne_one]
  have hx : x ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

private theorem w135c2_omfMRefl_c_eq_one {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : c = 1 := by
  rcases w135c2_omfMRefl_eq_zero_or_one hK c with h | h
  · exact absurd h (by simpa using hirrQ 0)
  · exact h

private theorem w135c2_omfMRefl_b_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hK : Nat.card K = 2) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 := by
  have hc : c = 1 := w135c2_omfMRefl_c_eq_one hK hirrQ
  rcases w135c2_omfMRefl_eq_zero_or_one hK b with h | h
  · exfalso
    apply hirrQ 1
    rw [h, hc]
    simp only [pow_two, mul_one, add_zero]
    rw [one_add_one_eq_two]
    exact CharTwo.two_eq_zero
  · exact h

private theorem w135c2_omfMRefl_planeRefl_sub {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hK : Nat.card K = 2) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    planeRefl b c planeOne ![0, 1] - ![0, 1] = planeOne := by
  have hb : b = 1 := w135c2_omfMRefl_b_eq_one hK hirrQ
  have hpol : polarPlane b c ![0, 1] planeOne = 1 := by
    rw [hb]
    simp [polarPlane, planeOne, CharTwo.two_eq_zero]
  rw [planeRefl, hpol, planeNorm_planeOne, div_one, one_smul]
  funext t
  fin_cases t <;> simp [planeOne, CharTwo.neg_eq]

private theorem w135c2_omfMRefl_shortPosHom {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (p : Fin 2 → K) :
    omMinusReflAut n hn hirrQ (shortPosHom n hirrQ i (.ofAdd p)) =
      shortPosHom n hirrQ i (.ofAdd (planeRefl b c planeOne p)) :=
  w135c2_omfMRefl_twShortRoot hn hirrQ i true p

theorem omMinusReflAut_nW {n : ℕ} (hn : 4 ≤ n) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (w : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group) :
    omMinusReflAut n hn hirrQ ((SmallO8mCurtis.curtisDatum n hn hirrQ).nW w) =
      (SmallO8mCurtis.curtisDatum n hn hirrQ).nW w := by
  obtain ⟨π, s, hs, hr, hact⟩ := omqnf_exists_acts_nW hn hirrQ w
  have hcomm := w135c2_omfMRefl_commute hact
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [w135c2_omfMRefl_spinAction n hn hirrQ, hcomm, mul_assoc,
    w135c2_omfMRefl_R_mul_self n, mul_one]

theorem omMinusReflAut_mem_U {n : ℕ} (hn : 4 ≤ n) (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u : spinGroup (quadMinus n K b c)} (hu : u ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).U) :
    omMinusReflAut n hn hirrQ u ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).U := by
  change u ∈ CFSG.LieType.Steinberg.posUnipotent (minusDatum n hirrQ) at hu
  change omMinusReflAut n hn hirrQ u ∈
    CFSG.LieType.Steinberg.posUnipotent (minusDatum n hirrQ)
  exact (Subgroup.mem_comap).mp (w135c2_omfMRefl_le_comap_posUnipotent hn hirrQ hu)

theorem omMinusReflAut_shortPosHom_mul_inv (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    omMinusReflAut n hn hirrQ
        (shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd ![0, 1])) *
        (shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd ![0, 1]))⁻¹ =
      shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd planeOne) := by
  have hpq : planeRefl b c planeOne ![0, 1] - ![0, 1] = planeOne :=
    w135c2_omfMRefl_planeRefl_sub hK hirrQ
  rw [w135c2_omfMRefl_shortPosHom hn hirrQ ⟨n - 2, by omega⟩ ![0, 1]]
  rw [← map_inv, ← map_mul]
  congr 1
  rw [← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg, hpq]

end CFSG.LocalAnalysis.WeakClosure81

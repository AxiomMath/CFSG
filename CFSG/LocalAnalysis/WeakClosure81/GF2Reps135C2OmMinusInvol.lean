module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusStd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mCurtis
open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private noncomputable def ommInvolA : spinGroup (quadMinus 4 K b c) :=
  (o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1

private noncomputable def ommInvolTheta : spinGroup (quadMinus 4 K b c) :=
  (ommInvolA hirrQ)⁻¹ * (o8mDatum hirrQ).n 0 * (ommInvolA hirrQ)

private theorem ommInvol_n0_minusVec (m : Fin 3) (s : Bool) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (minusVec 4 m s) =
      minusVec 4 (Equiv.swap (0 : Fin 3) 1 m) s := by
  rw [o8mDatum_n hirrQ 0]
  exact CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_minusVec
    (n := 4) (hirr := hirrQ) (k := 0) (by norm_num) m s

private theorem ommInvol_n0_eVec (i : Fin 3) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (eVec 4 i) =
      eVec 4 (Equiv.swap (0 : Fin 3) 1 i) := by
  simpa using ommInvol_n0_minusVec hirrQ i true

private theorem ommInvol_n0_fVec (i : Fin 3) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (fVec 4 i) =
      fVec 4 (Equiv.swap (0 : Fin 3) 1 i) := by
  simpa using ommInvol_n0_minusVec hirrQ i false

private theorem ommInvol_n1_minusVec (m : Fin 3) (s : Bool) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 1) (minusVec 4 m s) =
      minusVec 4 (Equiv.swap (1 : Fin 3) 2 m) s := by
  rw [o8mDatum_n hirrQ 1]
  exact CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_minusVec
    (n := 4) (hirr := hirrQ) (k := 1) (by norm_num) m s

private theorem ommInvol_n2_minusVec_of_ne {m : Fin 3} (hm : m ≠ 2) (s : Bool) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (minusVec 4 m s) = minusVec 4 m s := by
  rw [o8mDatum_n hirrQ 2, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num), shortWeyl]
  cases s
  · simpa using spinAction_shortWeylElt_fVec_of_ne 4 hirrQ hm planeOne
  · simpa using spinAction_shortWeylElt_eVec_of_ne 4 hirrQ hm planeOne

private theorem ommInvol_n2_minusVec_two (s : Bool) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (minusVec 4 2 s) =
      minusVec 4 2 (!s) := by
  rw [o8mDatum_n hirrQ 2, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
  cases s
  · simp only [Bool.not_false, minusVec_false, minusVec_true]
    rw [spinAction_shortWeyl_fVec 4 hirrQ 2]
    funext a
    exact CharTwo.neg_eq _
  · simp only [Bool.not_true, minusVec_true, minusVec_false]
    rw [spinAction_shortWeyl_eVec 4 hirrQ 2]
    funext a
    exact CharTwo.neg_eq _

private theorem ommInvol_n0_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (planeVec 4 p) = planeVec 4 p := by
  rw [o8mDatum_n hirrQ 0]
  exact CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_planeVec
    (n := 4) (hirr := hirrQ) (k := 0) (by norm_num) p

private theorem ommInvol_n1_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 1) (planeVec 4 p) = planeVec 4 p := by
  rw [o8mDatum_n hirrQ 1]
  exact CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_planeVec
    (n := 4) (hirr := hirrQ) (k := 1) (by norm_num) p

private theorem ommInvol_n2_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (planeVec 4 p) =
      planeVec 4 (planeRefl b c planeOne p) := by
  rw [o8mDatum_n hirrQ 2, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
  exact spinAction_shortWeyl_planeVec 4 hirrQ 2 p

private theorem ommInvol_n0_eVec_two :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (eVec 4 2) = eVec 4 2 := by
  have h := ommInvol_n0_minusVec hirrQ 2 true
  rw [show Equiv.swap (0 : Fin 3) 1 (2 : Fin 3) = 2 from
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  simpa using h

private theorem ommInvol_n0_fVec_two :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (fVec 4 2) = fVec 4 2 := by
  have h := ommInvol_n0_minusVec hirrQ 2 false
  rw [show Equiv.swap (0 : Fin 3) 1 (2 : Fin 3) = 2 from
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  simpa using h

private theorem ommInvolA_minusVec_two (s : Bool) :
    spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (minusVec 4 2 s) = minusVec 4 2 s := by
  unfold ommInvolA
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, ommInvol_n1_minusVec]
  rw [show Equiv.swap (1 : Fin 3) 2 (2 : Fin 3) = 1 from Equiv.swap_apply_right (1 : Fin 3) 2]
  rw [ommInvol_n2_minusVec_of_ne hirrQ (by decide : (1 : Fin 3) ≠ 2), ommInvol_n1_minusVec]
  rw [show Equiv.swap (1 : Fin 3) 2 (1 : Fin 3) = 2 from Equiv.swap_apply_left (1 : Fin 3) 2]

private theorem ommInvolA_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (planeVec 4 p) =
      planeVec 4 (planeRefl b c planeOne p) := by
  unfold ommInvolA
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply,
    ommInvol_n1_planeVec, ommInvol_n2_planeVec, ommInvol_n1_planeVec]

private theorem ommInvolTheta_eVec_two :
    spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ) (eVec 4 2) = eVec 4 2 := by
  have hA : spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (eVec 4 2) = eVec 4 2 := by
    simpa using ommInvolA_minusVec_two hirrQ true
  unfold ommInvolTheta
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, map_inv, hA,
    ommInvol_n0_eVec_two]
  have key : (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ))⁻¹
      (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (eVec 4 2)) = eVec 4 2 :=
    LinearEquiv.symm_apply_apply _ _
  simpa [hA] using key

private theorem ommInvolTheta_fVec_two :
    spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ) (fVec 4 2) = fVec 4 2 := by
  have hA : spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (fVec 4 2) = fVec 4 2 := by
    simpa using ommInvolA_minusVec_two hirrQ false
  unfold ommInvolTheta
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, map_inv, hA,
    ommInvol_n0_fVec_two]
  have key : (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ))⁻¹
      (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (fVec 4 2)) = fVec 4 2 :=
    LinearEquiv.symm_apply_apply _ _
  simpa [hA] using key

private theorem ommInvolTheta_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ) (planeVec 4 p) = planeVec 4 p := by
  have hA : spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (planeVec 4 p) =
      planeVec 4 (planeRefl b c planeOne p) := ommInvolA_planeVec hirrQ p
  unfold ommInvolTheta
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, map_inv, hA,
    ommInvol_n0_planeVec]
  have key : (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ))⁻¹
      (spinAction (quadMinus 4 K b c) (ommInvolA hirrQ) (planeVec 4 p)) = planeVec 4 p :=
    LinearEquiv.symm_apply_apply _ _
  simpa [hA] using key

private theorem ommInvolTheta_mem_orthogonalGroup :
    spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact map_spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ) v

private def ommInvolS0 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → Fin 3 ⊕ Fin 3 ⊕ Fin 2
  | .inl i => .inl (Equiv.swap (0 : Fin 3) 1 i)
  | .inr (.inl i) => .inr (.inl (Equiv.swap (0 : Fin 3) 1 i))
  | .inr (.inr t) => .inr (.inr t)

private noncomputable def ommInvolT0 : Vm 4 K →ₗ[K] Vm 4 K where
  toFun v := fun a => v (ommInvolS0 a)
  map_add' v w := by funext a; rfl
  map_smul' r v := by funext a; rfl

omit [Finite K] [CharP K 2] in
private theorem ommInvolT0_apply (v : Vm 4 K) (a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    ommInvolT0 v a = v (ommInvolS0 a) := rfl

private theorem ommInvolS0_invol : Function.Involutive ommInvolS0 := by
  intro x
  rcases x with i | i | t <;> simp [ommInvolS0]

omit [Finite K] [CharP K 2] in
private theorem ommInvol_single_swap {ι : Type*} [DecidableEq ι] {σ : ι → ι}
    (hσ : Function.Involutive σ) (b a : ι) :
    (Pi.single (σ b) (1 : K) : ι → K) a = (Pi.single b (1 : K) : ι → K) (σ a) := by
  simp only [Pi.single_apply]
  by_cases h : a = σ b
  · rw [if_pos h, if_pos (show σ a = b by rw [h, hσ])]
  · rw [if_neg h, if_neg (show ¬σ a = b by intro h2; exact h (by rw [← h2, hσ]))]

omit [Finite K] [CharP K 2] in
private theorem ommInvol_single_inr_inr (t : Fin 2) :
    (Pi.single (.inr (.inr t)) (1 : K) : Vm 4 K) = planeVec 4 (Pi.single t 1) := by
  funext a
  rcases a with i | i | s <;> simp [planeVec, Pi.single_apply, Sum.inr.injEq]

private theorem ommInvol_n0_apply (v : Vm 4 K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) v = ommInvolT0 v := by
  have h : (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) :
      Vm 4 K →ₗ[K] Vm 4 K) = ommInvolT0 := by
    apply (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Fin 2)).ext
    intro a
    rw [Pi.basisFun_apply]
    rcases a with i | i | t
    · change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (eVec 4 i) =
        ommInvolT0 (eVec 4 i)
      rw [ommInvol_n0_eVec]
      funext b
      rw [ommInvolT0_apply]
      exact ommInvol_single_swap ommInvolS0_invol (.inl i) b
    · change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (fVec 4 i) =
        ommInvolT0 (fVec 4 i)
      rw [ommInvol_n0_fVec]
      funext b
      rw [ommInvolT0_apply]
      exact ommInvol_single_swap ommInvolS0_invol (.inr (.inl i)) b
    · rw [ommInvol_single_inr_inr t]
      change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (planeVec 4 (Pi.single t 1)) =
        ommInvolT0 (planeVec 4 (Pi.single t 1))
      rw [ommInvol_n0_planeVec]
      funext b
      rw [ommInvolT0_apply, ← ommInvol_single_inr_inr t]
      exact ommInvol_single_swap ommInvolS0_invol (.inr (.inr t)) b
  exact LinearMap.congr_fun h v

private theorem ommInvol_n0_sub (v : Vm 4 K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) v - v =
      (v (.inl 1) + v (.inl 0)) • (eVec 4 0 + eVec 4 1) +
        (v (.inr (.inl 1)) + v (.inr (.inl 0))) • (fVec 4 0 + fVec 4 1) := by
  rw [ommInvol_n0_apply]
  funext a
  rcases a with i | i | t
  · fin_cases i
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, CharTwo.sub_eq_add]
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, CharTwo.sub_eq_add]
      ring
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, 
        show Equiv.swap (0 : Fin 3) 1 2 = 2 from by decide]
  · fin_cases i
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, CharTwo.sub_eq_add]
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, CharTwo.sub_eq_add]
      ring
    · simp [ommInvolT0_apply, ommInvolS0, eVec, fVec, 
        show Equiv.swap (0 : Fin 3) 1 2 = 2 from by decide]
  · fin_cases t <;> simp [ommInvolT0_apply, ommInvolS0, eVec, fVec]

private theorem ommInvol_n0_commSpace_eq :
    commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)) =
      Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1]) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) v - v ∈
      Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1])
    rw [ommInvol_n0_sub]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (Set.mem_range_self 0)
    · exact Submodule.subset_span (Set.mem_range_self 1)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · have h : eVec 4 0 + eVec 4 1 =
          spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (eVec 4 0) - eVec 4 0 := by
        rw [ommInvol_n0_eVec]
        simp only [Equiv.swap_apply_left]
        rw [sub_eq_add_vec K (eVec 4 1) (eVec 4 0), add_comm]
      rw [h]
      exact sub_mem_commSpace _ _
    · have h : fVec 4 0 + fVec 4 1 =
          spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (fVec 4 0) - fVec 4 0 := by
        rw [ommInvol_n0_fVec]
        simp only [Equiv.swap_apply_left]
        rw [sub_eq_add_vec K (fVec 4 1) (fVec 4 0), add_comm]
      rw [h]
      exact sub_mem_commSpace _ _

omit [Finite K] [CharP K 2] in
private theorem ommInvol_n0_linearIndependent :
    LinearIndependent K (![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1] : Fin 2 → Vm 4 K) := by
  rw [LinearIndependent.pair_iff (R := K)]
  intro c d h
  have h1 := congrFun h (.inl 0)
  have h2 := congrFun h (.inr (.inl 0))
  simp [eVec, fVec] at h1 h2
  exact ⟨h1, h2⟩

private theorem ommInvol_n0_finrank_commSpace :
    finrank K (commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0))) = 2 := by
  rw [ommInvol_n0_commSpace_eq, finrank_span_eq_card ommInvol_n0_linearIndependent]
  simp

private theorem ommInvol_n0_vanish (x : Vm 4 K)
    (hx : x ∈ commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0))) :
    quadMinus 4 K b c x = 0 := by
  rw [ommInvol_n0_commSpace_eq] at hx
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨d, hd⟩ := hx
  rw [Fin.sum_univ_two] at hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  rw [← hd, QuadraticMap.map_add (f := quadMinus 4 K b c),
    QuadraticMap.map_smul (quadMinus 4 K b c), QuadraticMap.map_smul (quadMinus 4 K b c)]
  have ha : quadMinus 4 K b c (eVec 4 0 + eVec 4 1) = 0 := by
    rw [QuadraticMap.map_add (f := quadMinus 4 K b c), quadMinus_eVec, quadMinus_eVec,
      polar_eVec_eVec]
    simp
  have hb : quadMinus 4 K b c (fVec 4 0 + fVec 4 1) = 0 := by
    rw [QuadraticMap.map_add (f := quadMinus 4 K b c), quadMinus_fVec, quadMinus_fVec,
      polar_fVec_fVec]
    simp
  have hab : polar (quadMinus 4 K b c) (eVec 4 0 + eVec 4 1) (fVec 4 0 + fVec 4 1) = 0 := by
    rw [polar_add_left, polar_add_right, polar_add_right, polar_eVec_fVec, polar_eVec_fVec,
      polar_eVec_fVec, polar_eVec_fVec]
    simp [CharTwo.add_self_eq_zero]
  rw [ha, hb, polar_smul_left, polar_smul_right, hab]
  simp

private theorem ommInvol_n0_mem_orthogonalGroup :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact map_spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) v

private theorem ommInvol_n0_spinAction_sq :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) *
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) = 1 := by
  apply LinearEquiv.ext
  intro v
  change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) v) = v
  rw [ommInvol_n0_apply, ommInvol_n0_apply]
  funext a
  rw [ommInvolT0_apply, ommInvolT0_apply, ommInvolS0_invol a]

private theorem ommInvol_n0_sq_self : (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 0 = 1 := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
  rw [map_mul, map_one]
  exact ommInvol_n0_spinAction_sq hirrQ

private theorem ommInvol_n0_type :
    suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)) =
        SuzukiLetter.a ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0))) = 2 :=
  ⟨suzukiLetter_eq_a_iff.mpr ⟨by rw [ommInvol_n0_finrank_commSpace]; decide,
      ommInvol_n0_vanish hirrQ⟩,
    ommInvol_n0_finrank_commSpace hirrQ⟩

omit [Finite K] in
private theorem ommInvol_planeRefl_single (t : Fin 2) :
    planeRefl b c planeOne (Pi.single t (1 : K)) + Pi.single t 1 =
      (if t = 1 then b else 0) • planeOne := by
  rw [planeRefl, planeNorm_planeOne, div_one]
  have hp : polarPlane b c (Pi.single t (1 : K)) planeOne =
      b * (if t = 1 then 1 else 0) := by
    fin_cases t <;> simp [polarPlane, planeOne, CharTwo.two_eq_zero]
  rw [hp]
  funext a
  fin_cases a <;> fin_cases t <;>
    simp [planeOne, CharTwo.sub_eq_add, CharTwo.add_self_eq_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]

private noncomputable def ommInvolT2 (b' : K) : Vm 4 K →ₗ[K] Vm 4 K where
  toFun v := (v (.inr (.inl 2)) + v (.inl 2)) • (eVec 4 2 + fVec 4 2) +
    (b' * v (.inr (.inr 1))) • planeVec 4 planeOne
  map_add' v w := by
    funext a
    simp [smul_add, mul_add, add_mul, mul_assoc]
    ring
  map_smul' r v := by
    funext a
    simp [smul_add, mul_add, add_mul, mul_assoc, mul_left_comm,
      RingHom.id_apply]

private theorem ommInvol_n2_plane_sub (t : Fin 2) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (planeVec 4 (Pi.single t 1)) -
      planeVec 4 (Pi.single t 1) = (b * (if t = 1 then 1 else 0)) • planeVec 4 planeOne := by
  rw [ommInvol_n2_planeVec]
  rw [show planeVec 4 (planeRefl b c planeOne (Pi.single t 1)) - planeVec 4 (Pi.single t 1) =
      planeVec 4 (planeRefl b c planeOne (Pi.single t 1) + Pi.single t 1) from by
    rw [CharTwo.sub_eq_add, ← planeVec_add]]
  rw [ommInvol_planeRefl_single, planeVec_smul,
    show (if t = 1 then b else 0) = b * (if t = 1 then 1 else 0) from by
      fin_cases t <;> simp]

private theorem ommInvol_n2_single_inl {i : Fin 3} (hi : i ≠ 2) :
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) : Vm 4 K →ₗ[K] Vm 4 K)
      (Pi.single (.inl i) (1 : K) : Vm 4 K) = Pi.single (.inl i) (1 : K) := by
  have h := ommInvol_n2_minusVec_of_ne hirrQ hi true
  simpa [eVec] using h

private theorem ommInvol_n2_single_inl_two :
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) : Vm 4 K →ₗ[K] Vm 4 K)
      (Pi.single (.inl (2 : Fin 3)) (1 : K) : Vm 4 K) = Pi.single (.inr (.inl 2)) (1 : K) := by
  have h := ommInvol_n2_minusVec_two hirrQ true
  simpa [eVec, fVec] using h

private theorem ommInvol_n2_single_inr_inl {i : Fin 3} (hi : i ≠ 2) :
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) : Vm 4 K →ₗ[K] Vm 4 K)
      (Pi.single (.inr (.inl i)) (1 : K) : Vm 4 K) = Pi.single (.inr (.inl i)) (1 : K) := by
  have h := ommInvol_n2_minusVec_of_ne hirrQ hi false
  simpa [fVec] using h

private theorem ommInvol_n2_single_inr_inl_two :
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) : Vm 4 K →ₗ[K] Vm 4 K)
      (Pi.single (.inr (.inl (2 : Fin 3))) (1 : K) : Vm 4 K) =
        Pi.single (.inl 2) (1 : K) := by
  have h := ommInvol_n2_minusVec_two hirrQ false
  simpa [eVec, fVec] using h

private theorem ommInvol_n2_sub_single_inl (i : Fin 3) :
    ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
        Vm 4 K →ₗ[K] Vm 4 K) (Pi.single (.inl i) (1 : K) : Vm 4 K)) =
      ommInvolT2 b (Pi.single (.inl i) (1 : K) : Vm 4 K) := by
  fin_cases i
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inl (0 : Fin 3)) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inl (0 : Fin 3)) (1 : K))
    simp only [LinearMap.sub_apply, Module.End.one_apply,
      ommInvol_n2_single_inl hirrQ (by decide : (0 : Fin 3) ≠ 2)]
    simp [ommInvolT2, eVec, fVec]
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inl (1 : Fin 3)) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inl (1 : Fin 3)) (1 : K))
    simp only [LinearMap.sub_apply, Module.End.one_apply,
      ommInvol_n2_single_inl hirrQ (by decide : (1 : Fin 3) ≠ 2)]
    simp [ommInvolT2, eVec, fVec]
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inl (2 : Fin 3)) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inl (2 : Fin 3)) (1 : K))
    rw [LinearMap.sub_apply, Module.End.one_apply, ommInvol_n2_single_inl_two]
    simp [ommInvolT2, eVec, fVec, CharTwo.sub_eq_add, add_comm]

private theorem ommInvol_n2_sub_single_inr_inl (i : Fin 3) :
    ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
        Vm 4 K →ₗ[K] Vm 4 K) (Pi.single (.inr (.inl i)) (1 : K) : Vm 4 K)) =
      ommInvolT2 b (Pi.single (.inr (.inl i)) (1 : K) : Vm 4 K) := by
  fin_cases i
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inr (.inl (0 : Fin 3))) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inr (.inl (0 : Fin 3))) (1 : K))
    simp only [LinearMap.sub_apply, Module.End.one_apply,
      ommInvol_n2_single_inr_inl hirrQ (by decide : (0 : Fin 3) ≠ 2)]
    simp [ommInvolT2, eVec, fVec]
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inr (.inl (1 : Fin 3))) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inr (.inl (1 : Fin 3))) (1 : K))
    simp only [LinearMap.sub_apply, Module.End.one_apply,
      ommInvol_n2_single_inr_inl hirrQ (by decide : (1 : Fin 3) ≠ 2)]
    simp [ommInvolT2, eVec, fVec]
  · change ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
          Vm 4 K →ₗ[K] Vm 4 K)) (Pi.single (.inr (.inl (2 : Fin 3))) (1 : K) : Vm 4 K) =
        ommInvolT2 b (Pi.single (.inr (.inl (2 : Fin 3))) (1 : K))
    rw [LinearMap.sub_apply, Module.End.one_apply, ommInvol_n2_single_inr_inl_two]
    simp [ommInvolT2, eVec, fVec, CharTwo.sub_eq_add, add_comm]

private theorem ommInvol_n2_sub_single_inr_inr (t : Fin 2) :
    ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
        Vm 4 K →ₗ[K] Vm 4 K) (Pi.single (.inr (.inr t)) (1 : K) : Vm 4 K)) =
      ommInvolT2 b (Pi.single (.inr (.inr t)) (1 : K) : Vm 4 K) := by
  rw [ommInvol_single_inr_inr t]
  rw [show ((spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 :
        Vm 4 K →ₗ[K] Vm 4 K) (planeVec 4 (Pi.single t (1 : K)))) =
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (planeVec 4 (Pi.single t (1 : K))) -
        planeVec 4 (Pi.single t (1 : K)) from rfl]
  rw [ommInvol_n2_plane_sub hirrQ t]
  funext a
  fin_cases a <;> fin_cases t <;>
    simp [ommInvolT2, planeVec, planeOne, CharTwo.add_self_eq_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem ommInvol_n2_sub_linearMap :
    (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) - 1 : Vm 4 K →ₗ[K] Vm 4 K) =
      ommInvolT2 b := by
  apply (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Fin 2)).ext
  intro e
  rw [Pi.basisFun_apply]
  rcases e with i | i | t
  · exact ommInvol_n2_sub_single_inl hirrQ i
  · exact ommInvol_n2_sub_single_inr_inl hirrQ i
  · exact ommInvol_n2_sub_single_inr_inr hirrQ t

private theorem ommInvol_n2_sub (v : Vm 4 K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v - v = ommInvolT2 b v :=
  LinearMap.congr_fun (ommInvol_n2_sub_linearMap hirrQ) v

private theorem ommInvol_n2_commSpace_le :
    commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) ≤
      Submodule.span K (Set.range ![eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v - v ∈
    Submodule.span K (Set.range ![eVec 4 2 + fVec 4 2, planeVec 4 planeOne])
  rw [ommInvol_n2_sub]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span (Set.mem_range_self 0)
  · exact Submodule.subset_span (Set.mem_range_self 1)

private theorem ommInvol_n2_span_le :
    Submodule.span K (Set.range ![eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) ≤
      commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) := by
  rw [Submodule.span_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · have h : eVec 4 2 + fVec 4 2 =
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (eVec 4 2) - eVec 4 2 := by
      rw [show eVec 4 2 = minusVec 4 2 true from rfl, ommInvol_n2_minusVec_two]
      simp only [Bool.not_true, minusVec_false]
      rw [sub_eq_add_vec K (fVec 4 2) (minusVec 4 2 true), add_comm]
    rw [h]
    exact sub_mem_commSpace _ _
  · have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ
    have h : planeVec 4 planeOne =
        b⁻¹ • (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)
          (planeVec 4 (Pi.single (1 : Fin 2) 1)) - planeVec 4 (Pi.single (1 : Fin 2) 1)) := by
      rw [ommInvol_n2_plane_sub]
      simp only [↓reduceIte, mul_one]
      rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (sub_mem_commSpace _ _)

private theorem ommInvol_n2_commSpace_eq :
    commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) =
      Submodule.span K (Set.range ![eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) :=
  le_antisymm (ommInvol_n2_commSpace_le hirrQ) (ommInvol_n2_span_le hirrQ)

omit [Finite K] [CharP K 2] in
private theorem ommInvol_n2_linearIndependent :
    LinearIndependent K (![eVec 4 2 + fVec 4 2, planeVec 4 planeOne] : Fin 2 → Vm 4 K) := by
  rw [LinearIndependent.pair_iff (R := K)]
  intro c d h
  have h1 := congrFun h (.inl 2)
  have h2 := congrFun h (.inr (.inr 0))
  simp [eVec, fVec, planeVec, planeOne] at h1 h2
  exact ⟨h1, h2⟩

private theorem ommInvol_n2_finrank_commSpace :
    finrank K (commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2))) = 2 := by
  rw [ommInvol_n2_commSpace_eq, finrank_span_eq_card ommInvol_n2_linearIndependent]
  simp

private theorem ommInvol_n2_nonvanish :
    ∃ x ∈ commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)),
      quadMinus 4 K b c x ≠ 0 := by
  refine ⟨spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)
    (planeVec 4 (Pi.single (1 : Fin 2) 1)) - planeVec 4 (Pi.single (1 : Fin 2) 1),
    sub_mem_commSpace _ _, ?_⟩
  rw [ommInvol_n2_plane_sub]
  simp only [↓reduceIte, mul_one]
  rw [QuadraticMap.map_smul (quadMinus 4 K b c), quadMinus_planeVec', planeNorm_planeOne,
    smul_eq_mul, mul_one]
  exact mul_ne_zero (CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ)
    (CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ)

private theorem ommInvol_n2_mem_orthogonalGroup :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact map_spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v

private theorem ommInvol_n2_type :
    suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) =
        SuzukiLetter.c ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2))) = 2 :=
  ⟨suzukiLetter_eq_c_iff.mpr ⟨by rw [ommInvol_n2_finrank_commSpace]; decide,
      ommInvol_n2_nonvanish hirrQ⟩,
    ommInvol_n2_finrank_commSpace hirrQ⟩

private theorem ommInvol_n02_apply (v : Vm 4 K) :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) v =
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)
        (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v) := by
  simp only [map_mul, LinearEquiv.mul_apply]

private theorem ommInvol_n02_mem_orthogonalGroup :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact map_spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) v

private theorem ommInvol_n02_commSpace_le :
    commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) ≤
      Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1,
        eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  change spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) v - v ∈
    Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1,
      eVec 4 2 + fVec 4 2, planeVec 4 planeOne])
  rw [ommInvol_n02_apply]
  rw [show spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)
        (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v) - v =
      (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)
          (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v) -
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v) +
      (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v - v) from by abel]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 : spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)
          (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v) -
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v ∈
        commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)) :=
      sub_mem_commSpace _ _
    rw [ommInvol_n0_commSpace_eq] at h1
    refine Submodule.span_mono ?_ h1
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_range_self (0 : Fin 4)
    · exact Set.mem_range_self (1 : Fin 4)
  · have h2 : spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v - v ∈
        commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) :=
      sub_mem_commSpace _ _
    rw [ommInvol_n2_commSpace_eq] at h2
    refine Submodule.span_mono ?_ h2
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_range_self (2 : Fin 4)
    · exact Set.mem_range_self (3 : Fin 4)

private theorem ommInvol_n2_planeVec_single_one :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)
        (planeVec 4 (Pi.single (1 : Fin 2) 1)) = planeVec 4 (Pi.single (1 : Fin 2) 1) +
          b • planeVec 4 planeOne := by
  have h := ommInvol_n2_plane_sub hirrQ (1 : Fin 2)
  rw [show (b * if (1 : Fin 2) = 1 then 1 else 0) = b from by simp] at h
  rw [sub_eq_iff_eq_add] at h
  rwa [add_comm] at h

private theorem ommInvol_n02_span_mem_zero :
    eVec 4 0 + eVec 4 1 ∈ commSpace (spinAction (quadMinus 4 K b c)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) := by
  have h : eVec 4 0 + eVec 4 1 =
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
          (eVec 4 0) - eVec 4 0 := by
    rw [ommInvol_n02_apply,
      show spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (eVec 4 0) = eVec 4 0
        from ommInvol_n2_single_inl hirrQ (by decide : (0 : Fin 3) ≠ 2),
      ommInvol_n0_eVec]
    simp only [Equiv.swap_apply_left]
    rw [sub_eq_add_vec K (eVec 4 1) (eVec 4 0), add_comm]
  rw [h]
  exact sub_mem_commSpace _ _

private theorem ommInvol_n02_span_mem_one :
    fVec 4 0 + fVec 4 1 ∈ commSpace (spinAction (quadMinus 4 K b c)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) := by
  have h : fVec 4 0 + fVec 4 1 =
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
          (fVec 4 0) - fVec 4 0 := by
    rw [ommInvol_n02_apply,
      show spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (fVec 4 0) = fVec 4 0
        from ommInvol_n2_single_inr_inl hirrQ (by decide : (0 : Fin 3) ≠ 2),
      ommInvol_n0_fVec]
    simp only [Equiv.swap_apply_left]
    rw [sub_eq_add_vec K (fVec 4 1) (fVec 4 0), add_comm]
  rw [h]
  exact sub_mem_commSpace _ _

private theorem ommInvol_n02_span_mem_two :
    eVec 4 2 + fVec 4 2 ∈ commSpace (spinAction (quadMinus 4 K b c)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) := by
  have h : eVec 4 2 + fVec 4 2 =
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
          (eVec 4 2) - eVec 4 2 := by
    rw [ommInvol_n02_apply,
      show spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (eVec 4 2) = fVec 4 2
        from ommInvol_n2_single_inl_two hirrQ]
    rw [show spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) (fVec 4 2) = fVec 4 2
        from ommInvol_n0_fVec_two hirrQ]
    rw [show eVec 4 2 = minusVec 4 2 true from rfl]
    rw [show (fVec 4 2 : Vm 4 K) = minusVec 4 2 false from rfl]
    rw [sub_eq_add_vec K (minusVec 4 2 false) (minusVec 4 2 true), add_comm]
  rw [h]
  exact sub_mem_commSpace _ _

private theorem ommInvol_n02_span_mem_three :
    planeVec 4 planeOne ∈ commSpace (spinAction (quadMinus 4 K b c)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) := by
  have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ
  have h : planeVec 4 planeOne =
      b⁻¹ • (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
        (planeVec 4 (Pi.single (1 : Fin 2) 1)) - planeVec 4 (Pi.single (1 : Fin 2) 1)) := by
    rw [ommInvol_n02_apply, ommInvol_n2_planeVec_single_one hirrQ, map_add, map_smul,
      ommInvol_n0_planeVec, ommInvol_n0_planeVec]
    rw [show planeVec 4 (Pi.single (1 : Fin 2) 1) + b • planeVec 4 (planeOne : Fin 2 → K) -
          planeVec 4 (Pi.single (1 : Fin 2) 1) = b • planeVec 4 (planeOne : Fin 2 → K) from by
      abel]
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (sub_mem_commSpace _ _)

private theorem ommInvol_n02_span_le :
    Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1,
        eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) ≤
      commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) := by
  rw [Submodule.span_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · simpa using ommInvol_n02_span_mem_zero hirrQ
  · simpa using ommInvol_n02_span_mem_one hirrQ
  · simpa using ommInvol_n02_span_mem_two hirrQ
  · simpa using ommInvol_n02_span_mem_three hirrQ

private theorem ommInvol_n02_commSpace_eq :
    commSpace (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) =
      Submodule.span K (Set.range ![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1,
        eVec 4 2 + fVec 4 2, planeVec 4 planeOne]) :=
  le_antisymm (ommInvol_n02_commSpace_le hirrQ) (ommInvol_n02_span_le hirrQ)

omit [Finite K] [CharP K 2] in
private theorem ommInvol_n02_linearIndependent :
    LinearIndependent K (![eVec 4 0 + eVec 4 1, fVec 4 0 + fVec 4 1, eVec 4 2 + fVec 4 2,
      planeVec 4 planeOne] : Fin 4 → Vm 4 K) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg (.inl 0)
  have h1 := congrFun hg (.inr (.inl 0))
  have h2 := congrFun hg (.inl 2)
  have h3 := congrFun hg (.inr (.inr 0))
  simp [Fin.sum_univ_four, eVec, fVec, planeVec, planeOne] at h0 h1 h2 h3
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem ommInvol_n02_finrank_commSpace :
    finrank K (commSpace (spinAction (quadMinus 4 K b c)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2))) = 4 := by
  rw [ommInvol_n02_commSpace_eq, finrank_span_eq_card ommInvol_n02_linearIndependent]
  simp

private theorem ommInvol_n02_nonvanish :
    ∃ x ∈ commSpace (spinAction (quadMinus 4 K b c)
        ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)),
      quadMinus 4 K b c x ≠ 0 := by
  refine ⟨spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
    (planeVec 4 (Pi.single (1 : Fin 2) 1)) - planeVec 4 (Pi.single (1 : Fin 2) 1),
    sub_mem_commSpace _ _, ?_⟩
  have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ
  rw [ommInvol_n02_apply, ommInvol_n2_planeVec_single_one hirrQ, map_add, map_smul,
    ommInvol_n0_planeVec, ommInvol_n0_planeVec]
  have hsimp : planeVec 4 (Pi.single (1 : Fin 2) 1) + b • planeVec 4 (planeOne : Fin 2 → K) -
      planeVec 4 (Pi.single (1 : Fin 2) 1) = b • planeVec 4 (planeOne : Fin 2 → K) := by
    abel
  rw [hsimp, QuadraticMap.map_smul (quadMinus 4 K b c), quadMinus_planeVec', planeNorm_planeOne,
    smul_eq_mul, mul_one]
  exact mul_ne_zero hb hb

private theorem ommInvol_n02_type :
    suzukiLetter (quadMinus 4 K b c)
        (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) =
        SuzukiLetter.c ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c)
        ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2))) = 4 :=
  ⟨suzukiLetter_eq_c_iff.mpr ⟨by rw [ommInvol_n02_finrank_commSpace]; decide,
      ommInvol_n02_nonvanish hirrQ⟩,
    ommInvol_n02_finrank_commSpace hirrQ⟩

omit [Finite K] [CharP K 2] in
private theorem ommInvol_commSpace_one_eq_bot :
    commSpace (1 : Vm 4 K ≃ₗ[K] Vm 4 K) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

omit [Finite K] [CharP K 2] in
private theorem ommInvol_spinAction_ne_one {n : spinGroup (quadMinus 4 K b c)}
    (h : finrank K (commSpace (spinAction (quadMinus 4 K b c) n)) ≠ 0) :
    spinAction (quadMinus 4 K b c) n ≠ 1 := by
  intro h1
  apply h
  rw [h1, ommInvol_commSpace_one_eq_bot, finrank_bot]

private theorem ommInvol_n0_orderOf :
    orderOf (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0)) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact ommInvol_n0_spinAction_sq hirrQ)
    (ommInvol_spinAction_ne_one (n := (o8mDatum hirrQ).n 0)
      (by rw [ommInvol_n0_finrank_commSpace]; norm_num))

omit [Finite K] in
private theorem ommInvol_shortWeyl_sq (i : Fin 3) :
    shortWeyl 4 hirrQ i * shortWeyl 4 hirrQ i = 1 := by
  have hneg : (-planeOne : Fin 2 → K) = planeOne := by
    funext t; fin_cases t <;> simp [planeOne, CharTwo.neg_eq]
  have h : shortWeyl 4 hirrQ i = (shortWeyl 4 hirrQ i)⁻¹ := by
    conv_lhs => rw [show shortWeyl 4 hirrQ i = shortWeylElt 4 hirrQ i (-planeOne) from by
      rw [shortWeyl, hneg]]
    rw [shortWeylElt_neg, ← shortWeyl]
  nth_rewrite 1 [h]
  exact inv_mul_cancel (shortWeyl 4 hirrQ i)

private theorem ommInvol_n2_sq_self : (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 2 = 1 := by
  rw [o8mDatum_n hirrQ 2, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
  exact ommInvol_shortWeyl_sq hirrQ 2

private theorem ommInvol_n2_spinAction_sq :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) *
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) = 1 := by
  rw [← map_mul, ommInvol_n2_sq_self hirrQ, map_one]

private theorem ommInvol_n2_orderOf :
    orderOf (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2)) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact ommInvol_n2_spinAction_sq hirrQ)
    (ommInvol_spinAction_ne_one (n := (o8mDatum hirrQ).n 2)
      (by rw [ommInvol_n2_finrank_commSpace]; norm_num))

omit [Finite K] [CharP K 2] in
private theorem ommInvol_T0_T2 (v : Vm 4 K) :
    ommInvolT0 (ommInvolT2 b v) = ommInvolT2 b (ommInvolT0 v) := by
  funext a
  rcases a with i | i | t
  · fin_cases i <;> simp [ommInvolT0_apply, ommInvolT2, ommInvolS0, eVec, fVec, planeVec,
      planeOne, show Equiv.swap (0 : Fin 3) 1 2 = 2 from by decide]
  · fin_cases i <;> simp [ommInvolT0_apply, ommInvolT2, ommInvolS0, eVec, fVec, planeVec,
      planeOne, show Equiv.swap (0 : Fin 3) 1 2 = 2 from by decide]
  · fin_cases t <;> simp [ommInvolT0_apply, ommInvolT2, ommInvolS0, eVec, fVec, planeVec,
      planeOne, show Equiv.swap (0 : Fin 3) 1 2 = 2 from by decide]

private theorem ommInvol_n0_commute_n2_spin :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) *
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) =
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) *
        spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0) := by
  ext v
  simp only [LinearEquiv.mul_apply]
  rw [ommInvol_n0_apply, ommInvol_n0_apply]
  have h2 : spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) (ommInvolT0 v) =
      ommInvolT0 v + ommInvolT2 b (ommInvolT0 v) := by
    rw [← ommInvol_n2_sub (b := b) (c := c) hirrQ]
    abel_nf
  have h1 : spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 2) v =
      v + ommInvolT2 b v := by
    rw [← ommInvol_n2_sub (b := b) (c := c) hirrQ]
    abel_nf
  rw [h1, h2, map_add, ommInvol_T0_T2]

private theorem ommInvol_n0_commute_n2 :
    Commute ((o8mDatum hirrQ).n 0) ((o8mDatum hirrQ).n 2) := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
  rw [map_mul, map_mul]
  exact ommInvol_n0_commute_n2_spin hirrQ

private theorem ommInvol_n02_sq_self :
    ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) *
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) = 1 := by
  have hcomm := (ommInvol_n0_commute_n2 hirrQ).eq
  calc ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) *
        ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
      = (o8mDatum hirrQ).n 0 * ((o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 0) *
          (o8mDatum hirrQ).n 2 := by group
    _ = (o8mDatum hirrQ).n 0 * ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) *
          (o8mDatum hirrQ).n 2 := by rw [← hcomm]
    _ = ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 0) *
          ((o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 2) := by group
    _ = 1 := by rw [ommInvol_n0_sq_self hirrQ, ommInvol_n2_sq_self hirrQ, one_mul]

private theorem ommInvol_n02_spinAction_sq :
    spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) *
      spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) = 1 := by
  rw [← map_mul, ommInvol_n02_sq_self hirrQ, map_one]

private theorem ommInvol_n02_orderOf :
    orderOf (spinAction (quadMinus 4 K b c) ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact ommInvol_n02_spinAction_sq hirrQ)
    (ommInvol_spinAction_ne_one (n := (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2)
      (by rw [ommInvol_n02_finrank_commSpace]; norm_num))

private theorem ommInvol_conj_of_type {y : spinGroup (quadMinus 4 K b c)}
    (hdim : finrank K (Vm 4 K) = 8)
    (htΩ : spinAction (quadMinus 4 K b c) y ∈ omegaGroup (quadMinus 4 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ))
    (ht2 : orderOf (spinAction (quadMinus 4 K b c) y) = 2)
    (hnot : ¬(suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) = .a ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 4))
    {s : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hs2 : orderOf s = 2)
    (hletter : suzukiLetter (quadMinus 4 K b c) s =
      suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y))
    (hrank : finrank K (commSpace s) =
      finrank K (commSpace (spinAction (quadMinus 4 K b c) y)))
    (n : spinGroup (quadMinus 4 K b c)) (hn : spinAction (quadMinus 4 K b c) n = s) :
    ∃ g : spinGroup (quadMinus 4 K b c), g * y * g⁻¹ = n := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have hset := omega_conj_eq_of_not_typeA_half hQ hdim htΩ ht2 hnot
  have hmem : s ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c),
      g * spinAction (quadMinus 4 K b c) y * g⁻¹ = x} :=
    (isConj_iff_suzukiLetter_eq hQ htΩ.1 ht2 hsO hs2).mpr ⟨hletter, hrank⟩
  rw [← hset] at hmem
  obtain ⟨g, hgΩ, hconj⟩ := hmem
  obtain ⟨h, hh⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
    (n := 4) hirrQ (by norm_num) hgΩ
  refine ⟨h, ?_⟩
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
  rw [map_mul, map_mul, map_inv, hh, hn]
  exact hconj

private theorem ommInvol_exists_conj_letter_a {y : spinGroup (quadMinus 4 K b c)}
    (ht1 : spinAction (quadMinus 4 K b c) y ≠ 1)
    (ht2 : orderOf (spinAction (quadMinus 4 K b c) y) = 2)
    (htΩ : spinAction (quadMinus 4 K b c) y ∈ omegaGroup (quadMinus 4 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ))
    (hdim : finrank K (Vm 4 K) = 8)
    (hsuz : suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) = .a) :
    ∃ g : spinGroup (quadMinus 4 K b c), g * y * g⁻¹ = (o8mDatum hirrQ).n 0 := by
  have hzero : ∀ x ∈ commSpace (spinAction (quadMinus 4 K b c) y),
      quadMinus 4 K b c x = 0 := (suzukiLetter_eq_a_iff.mp hsuz).2
  have hr3 : finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) ≤ 3 :=
    CFSG.StandardType.GGOppRadOmega.finrank_le_of_quadMinus hirrQ hzero
  have hr_even : Even (finrank K (commSpace (spinAction (quadMinus 4 K b c) y))) := htΩ.2
  have hr_ge : 1 ≤ finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) :=
    one_le_finrank_commSpace ht1
  have hr2 : finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 2 := by
    obtain ⟨k, hk⟩ := hr_even
    omega
  have hnot : ¬(suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) = .a ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 4) := by
    intro h
    rw [hr2] at h
    exact absurd h.2 (by norm_num)
  obtain ⟨g, hg⟩ := ommInvol_conj_of_type hirrQ hdim htΩ ht2 hnot
    (ommInvol_n0_mem_orthogonalGroup hirrQ) (ommInvol_n0_orderOf hirrQ)
    ((ommInvol_n0_type hirrQ).1.trans hsuz.symm)
    ((ommInvol_n0_type hirrQ).2.trans hr2.symm) ((o8mDatum hirrQ).n 0) rfl
  exact ⟨g, hg⟩

private theorem ommInvol_exists_conj_letter_c {y : spinGroup (quadMinus 4 K b c)}
    (htt : spinAction (quadMinus 4 K b c) y * spinAction (quadMinus 4 K b c) y = 1)
    (ht1 : spinAction (quadMinus 4 K b c) y ≠ 1)
    (ht2 : orderOf (spinAction (quadMinus 4 K b c) y) = 2)
    (htΩ : spinAction (quadMinus 4 K b c) y ∈ omegaGroup (quadMinus 4 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ))
    (hdim : finrank K (Vm 4 K) = 8)
    (hsuz : suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) = .c) :
    ∃ g : spinGroup (quadMinus 4 K b c), g * y * g⁻¹ = (o8mDatum hirrQ).n 2 ∨
      g * y * g⁻¹ = (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2 := by
  have hr_even : Even (finrank K (commSpace (spinAction (quadMinus 4 K b c) y))) := htΩ.2
  have hr_le : finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) ≤ 4 := by
    have := two_mul_finrank_commSpace_le htt
    rw [hdim] at this
    omega
  have hr_ge : 1 ≤ finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) :=
    one_le_finrank_commSpace ht1
  have hr24 : finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 2 ∨
      finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 4 := by
    obtain ⟨k, hk⟩ := hr_even
    omega
  have hnot : ¬(suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) = .a ∧
      finrank K (commSpace (spinAction (quadMinus 4 K b c) y)) = 4) := by
    intro h
    rw [hsuz] at h
    exact absurd h.1 (by decide)
  rcases hr24 with hr2 | hr4
  · obtain ⟨g, hg⟩ := ommInvol_conj_of_type hirrQ hdim htΩ ht2 hnot
      (ommInvol_n2_mem_orthogonalGroup hirrQ) (ommInvol_n2_orderOf hirrQ)
      ((ommInvol_n2_type hirrQ).1.trans hsuz.symm)
      ((ommInvol_n2_type hirrQ).2.trans hr2.symm) ((o8mDatum hirrQ).n 2) rfl
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := ommInvol_conj_of_type hirrQ hdim htΩ ht2 hnot
      (ommInvol_n02_mem_orthogonalGroup hirrQ) (ommInvol_n02_orderOf hirrQ)
      ((ommInvol_n02_type hirrQ).1.trans hsuz.symm)
      ((ommInvol_n02_type hirrQ).2.trans hr4.symm)
      ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) rfl
    exact ⟨g, Or.inr hg⟩

theorem omMinus_exists_conj_weyl {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1)
    (hy1 : y ≠ 1) :
    ∃ g : spinGroup (quadMinus 4 K b c),
      g * y * g⁻¹ = (o8mDatum hirrQ).n 0 ∨ g * y * g⁻¹ = (o8mDatum hirrQ).n 2 ∨
        g * y * g⁻¹ = (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2 := by
  have hdim : finrank K (Vm 4 K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have htt : spinAction (quadMinus 4 K b c) y * spinAction (quadMinus 4 K b c) y = 1 := by
    rw [← map_mul, hy, map_one]
  have ht1 : spinAction (quadMinus 4 K b c) y ≠ 1 := by
    intro h
    exact hy1 (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
      (by rw [h, map_one]))
  have htE : spinAction (quadMinus 4 K b c) y ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus 4 K b c) := by
    rw [← range_spinAction_quadMinus (n := 4) (by norm_num) hirrQ]
    exact ⟨y, rfl⟩
  have htΩ : spinAction (quadMinus 4 K b c) y ∈ omegaGroup (quadMinus 4 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ) :=
    CFSG.StandardType.RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup
      (hirr := hirrQ) (by norm_num) htE
  have ht2 : orderOf (spinAction (quadMinus 4 K b c) y) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  rcases hsuz : suzukiLetter (quadMinus 4 K b c) (spinAction (quadMinus 4 K b c) y) with _ | _ | _
  · obtain ⟨g, hg⟩ := ommInvol_exists_conj_letter_a hirrQ ht1 ht2 htΩ hdim hsuz
    exact ⟨g, Or.inl hg⟩
  · exfalso
    have hodd : Odd (finrank K (commSpace (spinAction (quadMinus 4 K b c) y))) :=
      suzukiLetter_eq_b_iff.mp hsuz
    exact Nat.not_odd_iff_even.mpr htΩ.2 hodd
  · obtain ⟨g, hg⟩ := ommInvol_exists_conj_letter_c hirrQ htt ht1 ht2 htΩ hdim hsuz
    rcases hg with hg | hg
    · exact ⟨g, Or.inr (Or.inl hg)⟩
    · exact ⟨g, Or.inr (Or.inr hg)⟩

theorem omMinus_commute_theta_X_short :
    ∀ x ∈ (o8mDatum hirrQ).X 2,
      Commute (((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)⁻¹ *
        (o8mDatum hirrQ).n 0 * ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1))
        x := by
  intro x hx
  change Commute (ommInvolTheta hirrQ) x
  have hx' : x ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range := by
    rw [o8mDatum_X hirrQ 2,
      minusRootGroup_single_of_not_lt 4 hirrQ (k := 2) (by norm_num)] at hx
    exact Subgroup.mem_sup_left hx
  have hcomm := commute_short_roots_of_fix_block (n := 4) hirrQ 2
    (spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ))
    (ommInvolTheta_mem_orthogonalGroup hirrQ) (ommInvolTheta_eVec_two hirrQ)
    (ommInvolTheta_fVec_two hirrQ) (ommInvolTheta_planeVec hirrQ) x hx'
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
  rw [map_mul, map_mul]
  exact hcomm

theorem omMinus_commute_theta_n_short :
    Commute (((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)⁻¹ *
      (o8mDatum hirrQ).n 0 * ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1))
      ((o8mDatum hirrQ).n 2) := by
  change Commute (ommInvolTheta hirrQ) ((o8mDatum hirrQ).n 2)
  have hx' : (o8mDatum hirrQ).n 2 ∈
      (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range := by
    rw [o8mDatum_n hirrQ 2, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
    exact shortWeyl_mem 4 hirrQ 2
  have hcomm := commute_short_roots_of_fix_block (n := 4) hirrQ 2
    (spinAction (quadMinus 4 K b c) (ommInvolTheta hirrQ))
    (ommInvolTheta_mem_orthogonalGroup hirrQ) (ommInvolTheta_eVec_two hirrQ)
    (ommInvolTheta_fVec_two hirrQ) (ommInvolTheta_planeVec hirrQ) ((o8mDatum hirrQ).n 2) hx'
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
  rw [map_mul, map_mul]
  exact hcomm

end CFSG.LocalAnalysis.WeakClosure81

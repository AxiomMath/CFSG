module

public import CFSG.Monster.Existence.Census.Rigid
public import CFSG.Monster.B.TwoA.Census.CosetSquares
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public import CFSG.Monster.B.Cbar.FourGroupSpin
public import CFSG.Monster.B.Cbar.Fusion
public import CFSG.Monster.Generated.Centralizer
public import CFSG.Monster.Visible.Faithful
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import CFSG.Monster.Existence.Census.Rigid
public meta import CFSG.Monster.B.TwoA.Census.CosetSquares
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public import CFSG.Monster.Existence.Census.TrialityWitnessesInputs
public import Certificates.Certificate6024
public import Certificates.Certificate6023
public import Certificates.Certificate6007
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import Certificates.Certificate10091Base
public import Certificates.Certificate1020Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

theorem tauB_pow_two_eq_inv : tauB ^ 2 = tauB⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact tauB_pow_three)

theorem inv_tauB_pow_two : (tauB ^ 2)⁻¹ = tauB := by rw [tauB_pow_two_eq_inv, inv_inv]

theorem tauB_inv_mul_xmat_mul : tauB⁻¹ * xmat * tauB = rhoEquiv wQ := by
  have h := triality_four_group_spin_identification.2.2.2.2.1
  rw [← h, xmatTau2, tauB_pow_two_eq_inv, inv_inv]

theorem tauB_mul_xmat_mul_inv : tauB * xmat * tauB⁻¹ = rhoEquiv (zQ * wQ) := by
  have h := triality_four_group_spin_identification.2.2.2.2.2.1
  rw [← h, xmatTau]

theorem mem_Gvis_of_comm_xmat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) (h : g * xmat = xmat * g) :
    g ∈ Gvis := by
  have : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
    ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 h⟩
  rw [Gmat_inf_centralizer_xmat] at this
  exact this

theorem tau_conj_mem_Gvis {E : SpaceB ≃ₗ[ℚ] SpaceB} (hE : E ∈ Gvis)
    (hW : E * rhoEquiv wQ = rhoEquiv wQ * E) : tauB * E * tauB⁻¹ ∈ Gvis := by
  have hxτ : xmat = tauB * rhoEquiv wQ * tauB⁻¹ := by
    rw [← tauB_inv_mul_xmat_mul]
    group
  refine mem_Gvis_of_comm_xmat (mul_mem (mul_mem tauB_mem_Gmat (Hmat_le_Gmat hE))
    (inv_mem tauB_mem_Gmat)) ?_
  calc tauB * E * tauB⁻¹ * xmat = tauB * (E * rhoEquiv wQ) * tauB⁻¹ := by rw [hxτ]; group
    _ = tauB * (rhoEquiv wQ * E) * tauB⁻¹ := by rw [hW]
    _ = xmat * (tauB * E * tauB⁻¹) := by rw [hxτ]; group

theorem tau_sq_conj_mem_Gvis {E : SpaceB ≃ₗ[ℚ] SpaceB} (hE : E ∈ Gvis)
    (hW : E * rhoEquiv wQ = rhoEquiv wQ * E) : tauB ^ 2 * E * (tauB ^ 2)⁻¹ ∈ Gvis := by
  have hxE : E * xmat = xmat * E := by
    have h := Gvis_conj_xmat hE
    calc E * xmat = E * xmat * E⁻¹ * E := by group
      _ = xmat * E := by rw [h]
  have hzw : E * rhoEquiv (zQ * wQ) = rhoEquiv (zQ * wQ) * E := by
    rw [rhoEquiv_mul, ← show xmat = rhoEquiv zQ from rfl]
    calc E * (rhoEquiv wQ * xmat) = (E * rhoEquiv wQ) * xmat := by group
      _ = rhoEquiv wQ * (E * xmat) := by rw [hW]; group
      _ = rhoEquiv wQ * (xmat * E) := by rw [hxE]
      _ = rhoEquiv wQ * xmat * E := by group
  have hxτ : xmat = tauB ^ 2 * rhoEquiv (zQ * wQ) * (tauB ^ 2)⁻¹ := by
    rw [← tauB_mul_xmat_mul_inv, tauB_pow_two_eq_inv]
    group
  refine mem_Gvis_of_comm_xmat (mul_mem (mul_mem (pow_mem tauB_mem_Gmat 2) (Hmat_le_Gmat hE))
    (inv_mem (pow_mem tauB_mem_Gmat 2))) ?_
  calc tauB ^ 2 * E * (tauB ^ 2)⁻¹ * xmat = tauB ^ 2 * (E * rhoEquiv (zQ * wQ)) * (tauB ^ 2)⁻¹ := by
        rw [hxτ]; group
    _ = tauB ^ 2 * (rhoEquiv (zQ * wQ) * E) * (tauB ^ 2)⁻¹ := by rw [hzw]
    _ = xmat * (tauB ^ 2 * E * (tauB ^ 2)⁻¹) := by rw [hxτ]; group


theorem pauliQ_omega : pauliQ (false, 63, 0) = wQ := by
  rw [pauliQ, wQ, XQ_eq]
  congr 1
  refine SpinCoord.ext rfl ?_ ?_
  · rw [toSC_a, pauli_a, ← ΩC_eq_toC]
  · rw [toSC_δ, pauli_d, ΩC_eq_toC, thetaD_toC]
    rfl

theorem conj_mul_mul_mul {G : Type*} [Group G] (a b c w : G) :
    a * b * c * w * (a * b * c)⁻¹ = a * (b * (c * w * c⁻¹) * b⁻¹) * a⁻¹ := by group

theorem comm_wQ_of
    (i : ℕ) (q₁ q₂ : Model.Pauli)
    (h : Model.conjPauliN q₁ (alphaN i (Model.conjPauliN q₂ (false, 63, 0))) = (false, 63, 0)) :
    (rhoEquiv (pauliQ q₁) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ q₂)) *
        rhoEquiv wQ =
      rhoEquiv wQ * (rhoEquiv (pauliQ q₁) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) *
        rhoEquiv (pauliQ q₂)) := by
  have hq : conjQ (rhoPair (pauliQ q₁)) (conjQ (cosetPair i) (conjQ (rhoPair (pauliQ q₂)) wQ)) =
      wQ := by
    have s1 : conjQ (rhoPair (pauliQ q₂)) wQ = pauliQ (Model.conjPauliN q₂ (false, 63, 0)) := by
      rw [← pauliQ_omega]
      exact conjQ_rhoPair_toQ q₂ _
    have s2 := conjQ_cosetPair i (Model.conjPauliN q₂ (false, 63, 0))
    have s3 := conjQ_rhoPair_toQ q₁ (alphaN i (Model.conjPauliN q₂ (false, 63, 0)))
    have h1 : conjQ (cosetPair i) (conjQ (rhoPair (pauliQ q₂)) wQ) =
        pauliQ (alphaN i (Model.conjPauliN q₂ (false, 63, 0))) :=
      (congrArg (conjQ (cosetPair i)) s1).trans s2
    have h2 : conjQ (rhoPair (pauliQ q₁))
        (conjQ (cosetPair i) (conjQ (rhoPair (pauliQ q₂)) wQ)) =
        pauliQ (Model.conjPauliN q₁ (alphaN i (Model.conjPauliN q₂ (false, 63, 0)))) :=
      (congrArg (conjQ (rhoPair (pauliQ q₁))) h1).trans s3
    exact h2.trans ((congrArg pauliQ h).trans pauliQ_omega)
  have e2 := thetaEquiv_conj_rhoEquiv (rhoPair (pauliQ q₂)) wQ
  have e1 := thetaEquiv_conj_rhoEquiv (cosetPair i) (conjQ (rhoPair (pauliQ q₂)) wQ)
  have e0 := thetaEquiv_conj_rhoEquiv (rhoPair (pauliQ q₁))
    (conjQ (cosetPair i) (conjQ (rhoPair (pauliQ q₂)) wQ))
  have e0' := e0.trans (congrArg rhoEquiv hq)
  have key : (rhoEquiv (pauliQ q₁) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ q₂)) *
      rhoEquiv wQ * (rhoEquiv (pauliQ q₁) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) *
        rhoEquiv (pauliQ q₂))⁻¹ = rhoEquiv wQ := by
    have hc : (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) = thetaEquiv (cosetPair i) := coe_cosetRep i
    have ha : rhoEquiv (pauliQ q₁) = thetaEquiv (rhoPair (pauliQ q₁)) := rfl
    have hb : rhoEquiv (pauliQ q₂) = thetaEquiv (rhoPair (pauliQ q₂)) := rfl
    rw [hc, ha, hb, conj_mul_mul_mul]
    exact (congrArg (fun t => thetaEquiv (rhoPair (pauliQ q₁)) *
      (thetaEquiv (cosetPair i) * t * (thetaEquiv (cosetPair i))⁻¹) *
        (thetaEquiv (rhoPair (pauliQ q₁)))⁻¹) e2).trans
      ((congrArg (fun t => thetaEquiv (rhoPair (pauliQ q₁)) * t *
        (thetaEquiv (rhoPair (pauliQ q₁)))⁻¹) e1).trans e0')
  exact mul_inv_eq_iff_eq_mul.1 key

@[expose] def hWord (i : ℕ) : List Native.Gen :=
  [Native.Gen.sign (cosetA i), Native.Gen.perm (cosetArr i)]

theorem wordLin_hWord
    (i : ℕ) : wordLin (hWord i) = (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [hWord, wordLin_cons, wordLin_cons, wordLin_nil, one_mul,
    Native.Gen.toLin_perm_of _ (seedAut (monoSeed.getD i 0)) (repPerm_cosetArr i),
    Native.Gen.toLin_sign, coe_cosetRep, cosetPair_eq i, thetaEquiv_mul]
  rfl

theorem cosetA_one : cosetA 1 = 3 := by decide

theorem cosetA_two : cosetA 2 = 734 := by decide

theorem cosetArr_one : cosetArr 1 = idArr := by decide

theorem cosetArr_two : cosetArr 2 = idArr := by decide

theorem hWord_one : hWord 1 = [Native.Gen.sign 3, Native.Gen.perm idArr] := by
  rw [hWord, cosetA_one, cosetArr_one]

theorem hWord_two : hWord 2 = [Native.Gen.sign 734, Native.Gen.perm idArr] := by
  rw [hWord, cosetA_two, cosetArr_two]

theorem check_one : checkRigid (Native.mkCtx ())
    (Native.Gen.tauPow 1 ++ [Native.Gen.sign 3, Native.Gen.perm idArr] ++ Native.Gen.tauPow 2)
    [Native.Gen.rho (false, 3, 60)] = true :=
  Certificates.certificate6024.1

theorem check_two : checkRigid (Native.mkCtx ())
    (Native.Gen.tauPow 1 ++ ([Native.Gen.sign 3, Native.Gen.perm idArr] ++
      [Native.Gen.rho (false, 63, 0)]) ++ Native.Gen.tauPow 2)
    [Native.Gen.rho (true, 60, 60)] = true :=
  Certificates.certificate6024.2.1

theorem check_three : checkRigid (Native.mkCtx ())
    (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 3, Native.Gen.perm idArr] ++
      [Native.Gen.rho (false, 60, 48)]) ++ Native.Gen.tauPow 1)
    [Native.Gen.rho (true, 3, 48)] = true :=
  Certificates.certificate6024.2.2.1

theorem check_four : checkRigid (Native.mkCtx ())
    (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 734, Native.Gen.perm idArr] ++
      [Native.Gen.rho (false, 734, 0)]) ++ Native.Gen.tauPow 1)
    [Native.Gen.rho (true, 734, 0)] = true :=
  Certificates.certificate6024.2.2.2.1

theorem wordLin_tau_conj (e f : ℕ) (w : List Native.Gen) :
    wordLin (Native.Gen.tauPow e ++ w ++ Native.Gen.tauPow f) = tauB ^ f * wordLin w * tauB ^ e := by
  rw [wordLin_append, wordLin_append, wordLin_tauPow, wordLin_tauPow, mul_assoc]

theorem wordLin_rho (q : Model.Pauli) : wordLin [Native.Gen.rho q] = rhoEquiv (pauliQ q) := by
  rw [wordLin_cons, wordLin_nil, one_mul]
  rfl

theorem eq_of_check_word
    {a : SpaceB ≃ₗ[ℚ] SpaceB} {q : Model.Pauli} {w : List Native.Gen}
    (ha : a ∈ Gvis) (hw : a = wordLin w)
    (hc : checkRigid (Native.mkCtx ()) w [Native.Gen.rho q] = true) : a = rhoEquiv (pauliQ q) := by
  refine eq_of_fix_rigidKeys ha (rhoEquiv_mem_Gvis _) fun k hk => ?_
  have h := checkRigid_sound hc k hk
  rw [hw, h, wordLin_rho]

theorem rhoEquiv_one' : rhoEquiv (1 : Q) = 1 :=
  (congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one

theorem rhoEquiv_pauliQ_zero : rhoEquiv (pauliQ (false, 0, 0)) = 1 := by
  rw [pauliQ_false_zero]
  exact rhoEquiv_one'

theorem comm_cosetRep
    (i : ℕ) (h : alphaN i (false, 63, 0) = (false, 63, 0)) :
    (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv wQ = rhoEquiv wQ * cosetRep i := by
  have := comm_wQ_of i (false, 0, 0) (false, 0, 0) (by
    have e : Model.conjPauliN (false, 0, 0) (false, 63, 0) = (false, 63, 0) := by decide
    rw [e, h, e])
  rwa [rhoEquiv_pauliQ_zero, one_mul, mul_one] at this

theorem comm_rho_cosetRep
    (i : ℕ) (q : Model.Pauli)
    (h : Model.conjPauliN q (alphaN i (false, 63, 0)) = (false, 63, 0)) :
    (rhoEquiv (pauliQ q) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB)) * rhoEquiv wQ =
      rhoEquiv wQ * (rhoEquiv (pauliQ q) * cosetRep i) := by
  have := comm_wQ_of i q (false, 0, 0) (by
    have e : Model.conjPauliN (false, 0, 0) (false, 63, 0) = (false, 63, 0) := by decide
    rw [e, h])
  rwa [rhoEquiv_pauliQ_zero, mul_one] at this

theorem cosetRep_comm_rho
    (i : ℕ) (y : Model.Pauli) (h : alphaN i y = y) :
    (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ y) =
      rhoEquiv (pauliQ y) * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have e := thetaEquiv_conj_rhoEquiv (cosetPair i) (pauliQ y)
  have e' := e.trans (congrArg rhoEquiv ((conjQ_cosetPair i y).trans (congrArg pauliQ h)))
  exact mul_inv_eq_iff_eq_mul.1 e'

theorem trialityWitness_one :
    tauB ^ 2 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (tauB ^ 2)⁻¹ = rhoEquiv (qP 0 3 60) := by
  have ha : tauB ^ 2 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (tauB ^ 2)⁻¹ ∈ Gvis :=
    tau_sq_conj_mem_Gvis (cosetRep 1).2
      (comm_cosetRep 1 Certificates.certificate6024.2.2.2.2.1)
  rw [show qP 0 3 60 = pauliQ (false, 3, 60) from rfl]
  refine eq_of_check_word (w := Native.Gen.tauPow 1 ++ hWord 1 ++ Native.Gen.tauPow 2) ha ?_ ?_
  · rw [wordLin_tau_conj, wordLin_hWord, inv_tauB_pow_two, pow_one]
  · rw [hWord_one]
    exact check_one

theorem trialityWitness_two :
    tauB ^ 2 * (rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * (tauB ^ 2)⁻¹ =
      rhoEquiv (qP 1 60 60) := by
  have hE : rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis :=
    Gvis.mul_mem (rhoEquiv_mem_Gvis _) (cosetRep 1).2
  have ha := tau_sq_conj_mem_Gvis hE
    (comm_rho_cosetRep 1 (false, 63, 0)
      Certificates.certificate6024.2.2.2.2.2.1)
  rw [show qP 1 60 60 = pauliQ (true, 60, 60) from rfl,
    show qP 0 63 0 = pauliQ (false, 63, 0) from rfl] at *
  refine eq_of_check_word (w := Native.Gen.tauPow 1 ++
    (hWord 1 ++ [Native.Gen.rho (false, 63, 0)]) ++ Native.Gen.tauPow 2) ha ?_ ?_
  · rw [wordLin_tau_conj, wordLin_append, wordLin_hWord, wordLin_rho, inv_tauB_pow_two, pow_one]
  · rw [hWord_one] 
    exact check_two

theorem trialityWitness_three :
    tauB * (rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 3 48) := by
  have hE : rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis :=
    Gvis.mul_mem (rhoEquiv_mem_Gvis _) (cosetRep 1).2
  have ha := tau_conj_mem_Gvis hE
    (comm_rho_cosetRep 1 (false, 60, 48)
      Certificates.certificate6024.2.2.2.2.2.2.1)
  rw [show qP 1 3 48 = pauliQ (true, 3, 48) from rfl,
    show qP 0 60 48 = pauliQ (false, 60, 48) from rfl] at *
  refine eq_of_check_word (w := Native.Gen.tauPow 2 ++
    (hWord 1 ++ [Native.Gen.rho (false, 60, 48)]) ++ Native.Gen.tauPow 1) ha ?_ ?_
  · rw [wordLin_tau_conj, wordLin_append, wordLin_hWord, wordLin_rho, ← tauB_pow_two_eq_inv]
    rw [pow_one]
  · rw [hWord_one]
    exact check_three

theorem trialityWitness_four :
    tauB * (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 734 0) := by
  have hE : rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis :=
    Gvis.mul_mem (rhoEquiv_mem_Gvis _) (cosetRep 2).2
  have ha := tau_conj_mem_Gvis hE
    (comm_rho_cosetRep 2 (false, 734, 0)
      Certificates.certificate6024.2.2.2.2.2.2.2.1)
  rw [show qP 1 734 0 = pauliQ (true, 734, 0) from rfl,
    show qP 0 734 0 = pauliQ (false, 734, 0) from rfl] at *
  refine eq_of_check_word (w := Native.Gen.tauPow 2 ++
    (hWord 2 ++ [Native.Gen.rho (false, 734, 0)]) ++ Native.Gen.tauPow 1) ha ?_ ?_
  · rw [wordLin_tau_conj, wordLin_append, wordLin_hWord, wordLin_rho, ← tauB_pow_two_eq_inv]
    rw [pow_one]
  · rw [hWord_two]
    exact check_four

theorem qP_zero_zero_of_even {k : ℕ} (hk : k % 2 = 0) : qP k 0 0 = 1 := by
  rw [qP, show (k % 2 == 1) = false by simp [hk]]
  exact pauliQ_false_zero

theorem qP_self_mul (s A D : ℕ) :
    qP s A D * qP s A D = qP (s + s + Model.popcN 12 (A &&& D)) 0 0 := by
  rw [qP_mul, Nat.xor_self, Nat.xor_self]

theorem qP_ne_one {s A D : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12)
    (h : A ≠ 0 ∨ D ≠ 0) : qP s A D ≠ 1 := by
  intro h1
  have h2 : qP s A D = qP 0 0 0 := h1.trans (qP_zero_zero_of_even rfl).symm
  obtain ⟨-, h3, h4⟩ := qP_injective hs hA hD (by norm_num) (by norm_num) (by norm_num) h2
  rcases h with h | h
  · exact h h3
  · exact h h4

theorem trialityTargets_involutions :
    ∀ q ∈ [qP 0 3 60, qP 1 60 60, qP 1 3 48, qP 1 734 0], q ≠ 1 ∧ q * q = 1 := by
  intro q hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨qP_ne_one (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      by rw [qP_self_mul]; exact qP_zero_zero_of_even (by decide)⟩
  · exact ⟨qP_ne_one (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      by rw [qP_self_mul]; exact qP_zero_zero_of_even (by decide)⟩
  · exact ⟨qP_ne_one (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      by rw [qP_self_mul]; exact qP_zero_zero_of_even (by decide)⟩
  · exact ⟨qP_ne_one (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      by rw [qP_self_mul]; exact qP_zero_zero_of_even (by decide)⟩

theorem tauData_witnesses :
    tauData.map (fun w => (w.cosetIndex, w.sourceQ, w.trialityPower, w.target)) =
      [(1, 0, 2, (0, 3, 60)), (1, 63, 2, (1, 60, 60)), (1, 196668, 1, (1, 3, 48)),
        (2, 734, 1, (1, 734, 0))] :=
  Certificates.certificate6024.2.2.2.2.2.2.2.2

theorem visible_involution_triality_witnesses :
    tauB ^ 2 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (tauB ^ 2)⁻¹ = rhoEquiv (qP 0 3 60) ∧
    tauB ^ 2 * (rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * (tauB ^ 2)⁻¹ =
      rhoEquiv (qP 1 60 60) ∧
    tauB * (rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 3 48) ∧
    tauB * (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 734 0) ∧
    ∀ q ∈ [qP 0 3 60, qP 1 60 60, qP 1 3 48, qP 1 734 0], q ≠ 1 ∧ q * q = 1 :=
  ⟨trialityWitness_one, trialityWitness_two, trialityWitness_three, trialityWitness_four,
    trialityTargets_involutions⟩

end CFSG.Monster.Existence.Census

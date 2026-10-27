module

public import CFSG.Monster.B.Final.PairNodes
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3049
public import Certificates.Certificate3109
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B.Rep4371
  CFSG.Monster.B.Short

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def KB :
    Subgroup NativeSporadic.B := Subgroup.closure {cB, dB}

@[expose] noncomputable def LB
    (ι : NativeSporadic.B →* Sbp) : Subgroup Sbp :=
  KB.map (etaS gSeq ι)

@[expose] noncomputable def eE (i : Fin 22) : Ebar :=
  ⟨(eS gSeq i).unop, eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i⟩

theorem pinned_B_max2_native_certificate_data
    (ι : NativeSporadic.B →* Sbp) :
    max2Prog = [(1, 2, 3), (3, 2, 4), (3, 3, 5), (5, 5, 3), (3, 4, 2), (2, 2, 3), (2, 3, 4),
      (4, 4, 5), (5, 5, 3), (3, 3, 4), (1, 4, 3), (3, 3, 1)] ∧
    cB = progRegs bA₁ bA₂ 1 ∧ dB = progRegs bA₁ bA₂ 2 ∧ KB = Subgroup.closure {cB, dB} ∧
    zS ι = ι (dB ^ 24) ∧
    (∀ i, eS gSeq i = (wordS gSeq (basisWord.take (basisLens.getD i 0)))⁻¹ * op (gSeq 0) *
      wordS gSeq (basisWord.take (basisLens.getD i 0))) ∧
    WS gSeq = wordS gSeq parityWord24 ∧
    zqS gSeq = op xbar * (Dyadic.bridgeZE.map (eS gSeq)).prod ∧
    uS gSeq ι = ι (wordTwo cB dB bridgeU * (wordTwo cB dB bridgeV)⁻¹) *
      (WS gSeq * ((WS gSeq)⁻¹ * zS ι * WS gSeq * op xbar) ^ 3 * zqS gSeq) ∧
    (∀ s, etaS gSeq ι s = (uS gSeq ι)⁻¹ * ι s * uS gSeq ι) ∧ LB ι = KB.map (etaS gSeq ι) ∧
    (∀ i j : Fin 22, Max2.decMat CFSG.Monster.B.gramRows i j =
      if (CFSG.Monster.B.gramRows[(i : ℕ)]!).testBit j then 1 else 0) ∧
    ((Max2.R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      Max2.decMat Max2.Native.r1Rows ∧
    ((Max2.R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      Max2.decMat Max2.Native.r2Rows :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, etaS_apply gSeq ι, rfl,
    fun i j => by rw [Max2.decMat, Matrix.of_apply, Code.bvec_apply], Max2.coe_R1u, Max2.coe_R2u⟩

theorem pauliQ_zero : pauliQ (false, 0, 0) = 1 := by
  have h : toSC (false, 0, 0) = ⟨0, 0, 0⟩ := SpinCoord.ext rfl toC_zero toD_zero
  rw [pauliQ, h]
  exact (spinEquiv_s_eq_one_iff 0).2 rfl

theorem gSeq_zero_mul_self : gSeq 0 * gSeq 0 = 1 := by
  have hq : qElt 1 * qElt 1 = 1 := by
    have h : pauliQ (Model.qPauli 1) * pauliQ (Model.qPauli 1) = 1 := by
      rw [← pauliQ_mul, show (Model.qPauli 1).mul (Model.qPauli 1) = (false, 0, 0) by decide,
        pauliQ_zero]
    rw [qElt_eq]
    exact h
  have e : (⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ * ⟨rhoEquiv (qElt 1),
      rhoEquiv_qElt_mem_Cgen 1⟩ : Cgen) = 1 := by
    apply Subtype.ext
    show rhoEquiv (qElt 1) * rhoEquiv (qElt 1) = 1
    rw [← rhoEquiv_mul, hq, rhoEquiv_one']
  rw [gSeq_zero, ← map_mul, e, map_one]

theorem dB_pow_ne
    (n : ℕ) (h : dMat ^ n ≠ 1) : dB ^ n ≠ 1 := fun h' => h (by
  rw [← bMat_dB, ← map_pow, h', map_one])

theorem natCard_unop {G : Type*} [Group G] (H : Subgroup Gᵐᵒᵖ) : Nat.card H.unop = Nat.card H :=
  Nat.card_congr (MulOpposite.opEquiv.subtypeEquiv fun _ => Subgroup.mem_unop)

section Max2Nodes

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)
  (ι : NativeSporadic.B →* Sbp)
  (hιβ : ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹)

include hιβ in
theorem iota_injective_of : Function.Injective ι := by
  intro X Y h
  apply bMat_injective
  have e := congrArg (fun s => Tmat⁻¹ * ((betaRow β s : MatBˣ) : MatB) * Tmat) h
  simp only [hιβ] at e
  calc bMat X = (Tmat⁻¹ * Tmat) * bMat X * (Tmat⁻¹ * Tmat) := by
        rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]
    _ = Tmat⁻¹ * (Tmat * bMat X * Tmat⁻¹) * Tmat := by simp only [Matrix.mul_assoc]
    _ = Tmat⁻¹ * (Tmat * bMat Y * Tmat⁻¹) * Tmat := e
    _ = (Tmat⁻¹ * Tmat) * bMat Y * (Tmat⁻¹ * Tmat) := by simp only [Matrix.mul_assoc]
    _ = bMat Y := by rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]

include hβ hιβ in
theorem LB_unop_le_Jbar :
    (LB ι).unop ≤ Jbar := by
  rw [LB, KB, MonoidHom.map_closure, Set.image_pair, Subgroup.unop_closure, Subgroup.closure_le]
  rintro y (hy | hy)
  · have : y = (etaS gSeq ι cB).unop := by rw [← hy, unop_op]
    rw [this]
    exact eta_cB_mem_Jbar β hβ.injective gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  · have : y = (etaS gSeq ι dB).unop := by rw [← (Set.mem_singleton_iff.1 hy), unop_op]
    rw [this]
    exact eta_dB_mem_Jbar β hβ.injective gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ

include hβ in
theorem linearIndependent_eE :
    LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar (eE i)) :=
  linearIndependent_psi_of_cert (fun i => (eS gSeq i).unop)
    (fun i => eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i)
    (gram_rel β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar)

include hβ in
theorem conj_eta_rows
    (s : NativeSporadic.B) (G' : MatB) (rows : Array ℕ)
    (rows' : List ℕ)
    (hrows : ∀ i < 22, rows[i]! = rows'.getD i 0)
    (hs : ((betaRow β (etaS gSeq ι s) : MatBˣ) : MatB) = G')
    (hJ : (etaS gSeq ι s).unop ∈ Jbar)
    (hc : ∀ i j, i < 22 → j < 22 →
      KC.BM.e0 ᵥ* (G'⁻¹ * Em Qn i * G' * Em Qn j) =
      KC.BM.e0 ᵥ* (Em Qn j * Xm Qn ^ Dyadic.actK rows' i j * (G'⁻¹ * Em Qn i * G')))
    (i : Fin 22) :
    ∃ h : ((etaS gSeq ι s)⁻¹ * eS gSeq i * etaS gSeq ι s).unop ∈ Ebar,
      psiBar ⟨_, h⟩ = Multiplicative.ofAdd (∑ j, Max2.decMat rows i j •
        Multiplicative.toAdd (psiBar (eE j))) := by
  have hJ' : (etaS gSeq ι s).unop⁻¹ ∈ Jbar := Jbar.inv_mem hJ
  have hx : ((etaS gSeq ι s)⁻¹ * eS gSeq i * etaS gSeq ι s).unop =
      ((etaS gSeq ι s).unop⁻¹)⁻¹ * (eS gSeq i).unop * (etaS gSeq ι s).unop⁻¹ := by
    rw [unop_mul, unop_mul, unop_inv, inv_inv, mul_assoc]
  have hmem := conj_mem_Ebar hJ' (eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i)
  refine ⟨hx ▸ hmem, ?_⟩
  have e : (⟨((etaS gSeq ι s)⁻¹ * eS gSeq i * etaS gSeq ι s).unop, hx ▸ hmem⟩ : Ebar) =
      ⟨((etaS gSeq ι s).unop⁻¹)⁻¹ * (eS gSeq i).unop * (etaS gSeq ι s).unop⁻¹, hmem⟩ :=
    Subtype.ext hx
  rw [e]
  exact conj_rows β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar (etaS gSeq ι s) G' rows rows' hrows hs
    hJ' hc i

end Max2Nodes

theorem cB_ne_one :
    cB ≠ 1 := fun h =>
  pinned_facts.2.1 (by rw [← bMat_cB, h, map_one])

theorem orderOf_cB : orderOf cB = 2 :=
  orderOf_eq_prime (by rw [sq]; exact cB_mul_self) cB_ne_one

theorem orderOf_dB :
    orderOf dB = 48 := by
  obtain ⟨-, -, hd48, hd24, hd16, -⟩ := pinned_facts
  have hdd : dB ^ 48 = 1 := by
    apply bMat_injective
    rw [map_pow, bMat_dB, map_one]
    exact hd48
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hdd fun p hp hpd => ?_
  have hp' : p = 2 ∨ p = 3 := by
    have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h48] at hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  rcases hp' with rfl | rfl
  · exact dB_pow_ne 24 hd24
  · exact dB_pow_ne 16 hd16

theorem KB_le_centralizer :
    KB ≤ Subgroup.centralizer {dB ^ 24} := by
  have hD : dB ^ 24 * cB = cB * dB ^ 24 := by
    apply bMat_injective
    rw [map_mul, map_mul, map_pow, bMat_dB, bMat_cB]
    exact pinned_facts.2.2.2.2.2.1
  rw [KB, Subgroup.closure_le]
  rintro y (rfl | hy)
  · exact Subgroup.mem_centralizer_singleton_iff.2 hD.symm
  · rw [Set.mem_singleton_iff.1 hy]
    exact Subgroup.mem_centralizer_singleton_iff.2 (Commute.self_pow dB 24).eq

theorem isUnit_gram : IsUnit (Max2.decMat CFSG.Monster.B.gramRows) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
    (by rw [← decMat_mulRows, gram_mul_inv_check, decMat_idRows] :
      Max2.decMat CFSG.Monster.B.gramRows * Max2.decMat gramInvRows = 1))

section Max2Nodes

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)
  (ι : NativeSporadic.B →* Sbp)
  (hιβ : ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹)

include hβ in
theorem commutator_e_eq_xbar :
    (op (gSeq 0))⁻¹ * ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1))⁻¹ * op (gSeq 0) *
      ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1)) = op xbar := by
  have he2 : op (gSeq 0) * op (gSeq 0) = 1 := by
    rw [← op_mul, gSeq_zero_mul_self, op_one]
  have hei : (op (gSeq 0))⁻¹ = op (gSeq 0) := inv_eq_of_mul_eq_one_right he2
  have hf2 : ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1)) *
      ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1)) = 1 := by
    calc ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1)) *
          ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1))
        = (op (gSeq 1))⁻¹ * (op (gSeq 0) * op (gSeq 0)) * op (gSeq 1) := by group
      _ = 1 := by rw [he2, mul_one, inv_mul_cancel]
  rw [inv_eq_of_mul_eq_one_right hf2, hei, op_xbar_eq β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar,
    xS, sq]
  simp only [mul_assoc]

include hβ in
theorem commutator_eS (i j : Fin 22) :
    (eS gSeq i)⁻¹ * (eS gSeq j)⁻¹ * eS gSeq i * eS gSeq j =
      op xbar ^ (Max2.decMat CFSG.Monster.B.gramRows i j).val := by
  obtain ⟨hX2, -⟩ := max2_matrix_facts (Qn_isUnit β gSeq hβ.gen)
  have hXm := betaRow_xbar β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar
  have hgr := gram_rel β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar
  have hxx : xbar * xbar = 1 := by
    have h : op xbar * op xbar = 1 := by
      apply betaRow_inj hβ.injective
      rw [map_mul, Units.val_mul, hXm, ← sq, hX2, map_one, Units.val_one]
    rw [← op_mul, ← op_one] at h
    exact op_injective h
  have hpow : ∀ n : ℕ, n < 2 → xbar ^ n * xbar ^ n = 1 := by
    intro n hn
    interval_cases n
    · simp
    · rw [pow_one, hxx]
  have hcomm : ∀ (y : Cbar) (n : ℕ), y ∈ Ebar → y * xbar ^ n = xbar ^ n * y := fun y n hy =>
    ((Commute.pow_right (xbar_comm_of_mem_Ebar hy) n)).eq
  have swap : ∀ (a b : Cbar) (n : ℕ), n < 2 → a * b = b * a * xbar ^ n →
      b * a = a * b * xbar ^ n := by
    intro a b n hn h
    calc b * a = b * a * (xbar ^ n * xbar ^ n) := by rw [hpow n hn, mul_one]
      _ = (b * a * xbar ^ n) * xbar ^ n := (mul_assoc _ _ _).symm
      _ = a * b * xbar ^ n := by rw [← h]
  have comm_op : ∀ (a b : Cbar) (n : ℕ), a ∈ Ebar → b ∈ Ebar → b * a = a * b * xbar ^ n →
      (op a)⁻¹ * (op b)⁻¹ * op a * op b = op xbar ^ n := by
    intro a b n ha hb h
    have e2 : a * b * xbar ^ n * b⁻¹ * a⁻¹ = xbar ^ n := by
      have h1 := hcomm _ n (Ebar.inv_mem hb)
      have h2 := hcomm _ n ha
      calc a * b * xbar ^ n * b⁻¹ * a⁻¹ = a * b * (xbar ^ n * b⁻¹) * a⁻¹ := by
            simp only [mul_assoc]
        _ = a * b * (b⁻¹ * xbar ^ n) * a⁻¹ := by rw [h1]
        _ = (a * xbar ^ n) * a⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]
        _ = xbar ^ n := by rw [h2, mul_inv_cancel_right]
    calc (op a)⁻¹ * (op b)⁻¹ * op a * op b = op (b * a * b⁻¹ * a⁻¹) := by
          simp only [op_mul, op_inv, mul_assoc]
      _ = op (a * b * xbar ^ n * b⁻¹ * a⁻¹) := by rw [h]
      _ = op xbar ^ n := by rw [e2, op_pow]
  have haE := eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i
  have hbE := eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar j
  have hba : (eS gSeq j).unop * (eS gSeq i).unop =
      (eS gSeq i).unop * (eS gSeq j).unop *
        xbar ^ (Max2.decMat CFSG.Monster.B.gramRows i j).val := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact swap _ _ _ (ZMod.val_lt _) (hgr i j hij)
    · rw [gram_diag, ZMod.val_zero, pow_zero, mul_one]
    · rw [gram_symm]
      exact hgr j i hji
  have h := comm_op _ _ _ haE hbE hba
  rwa [op_unop, op_unop] at h

include hβ hιβ in
theorem orderOf_zWx :
    orderOf ((WS gSeq)⁻¹ * zS ι * WS gSeq * op xbar) = 5 := by
  obtain ⟨-, -, hk5, hk1, -⟩ := max2_matrix_facts (Qn_isUnit β gSeq hβ.gen)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [orderOf_betaRow hβ.injective, betaRow_kS gSeq ι β hβ.gen hιβ
    (op_xbar_eq β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar)]
  exact orderOf_eq_prime hk5 hk1

include hβ hιβ in
theorem z_conj_u :
    (uS gSeq ι)⁻¹ * zS ι * uS gSeq ι = op xbar := by
  obtain ⟨-, -, -, -, -, -, huzu, -⟩ := max2_matrix_facts (Qn_isUnit β gSeq hβ.gen)
  apply betaRow_inj hβ.injective
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    betaRow_uS gSeq ι β hβ.gen hιβ (op_xbar_eq β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar),
    betaRow_zS ι β hιβ, betaRow_xbar β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar]
  exact huzu

include hβ hιβ in
theorem file_eta :
    ((betaRow β (etaS gSeq ι cB) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.G1.rows ∧
    ((betaRow β (etaS gSeq ι dB) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.G2.rows := by
  obtain ⟨-, -, -, hG1, hG2⟩ := max2_file_facts (Qn_isUnit β gSeq hβ.gen)
  exact ⟨(betaRow_eta_cB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ).trans hG1,
    (betaRow_eta_dB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ).trans hG2⟩

include hβ hιβ in
theorem file_xconj :
    ((betaRow β (op xbar) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.Xb.rows ∧
    (((betaRow β (uS gSeq ι) : MatBˣ) : MatB))⁻¹ * Tmat = Dyadic.rowsK KC.BM.Max2.C.rows ∧
    Tmat⁻¹ * ((betaRow β (uS gSeq ι) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.Ci.rows := by
  obtain ⟨hXr, hCr, hCir, -⟩ := max2_file_facts (Qn_isUnit β gSeq hβ.gen)
  have hx := op_xbar_eq β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar
  have hu := betaRow_uS gSeq ι β hβ.gen hιβ hx
  refine ⟨(betaRow_xbar β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar).trans hXr, ?_, ?_⟩
  · rw [hu, ← C0m]
    exact hCr
  · rw [hu, ← C0m_inv gSeq ι β hβ.gen hιβ hx]
    exact hCir

include hβ hιβ in
theorem pinned_B_max2_native_centralizer_and_quotient_action :
    orderOf cB = 2 ∧ orderOf dB = 48 ∧ KB ≤ Subgroup.centralizer {dB ^ 24} ∧
    ((betaRow β (op (gSeq 0)) : MatBˣ) : MatB) = Qn 0 ∧
    (op (gSeq 0))⁻¹ * ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1))⁻¹ * op (gSeq 0) *
      ((op (gSeq 1))⁻¹ * op (gSeq 0) * op (gSeq 1)) = op xbar ∧
    (∃ b : Module.Basis (Fin 22) (ZMod 2) (Wv (phi0 (coordOf rStar))),
      ∀ i, b i = Multiplicative.toAdd (psiBar (eE i))) ∧
    (∀ i j : Fin 22, (eS gSeq i)⁻¹ * (eS gSeq j)⁻¹ * eS gSeq i * eS gSeq j =
      op xbar ^ (Max2.decMat CFSG.Monster.B.gramRows i j).val) ∧
    IsUnit (Max2.decMat CFSG.Monster.B.gramRows) ∧
    orderOf ((WS gSeq)⁻¹ * zS ι * WS gSeq * op xbar) = 5 ∧
    (uS gSeq ι)⁻¹ * zS ι * uS gSeq ι = op xbar ∧
    (LB ι).unop ≤ Jbar ∧
    (∀ i : Fin 22, ∃ h : ((etaS gSeq ι cB)⁻¹ * eS gSeq i * etaS gSeq ι cB).unop ∈ Ebar,
      psiBar ⟨_, h⟩ = Multiplicative.ofAdd (∑ j, Max2.decMat Max2.Native.r1Rows i j •
        Multiplicative.toAdd (psiBar (eE j)))) ∧
    (∀ i : Fin 22, ∃ h : ((etaS gSeq ι dB)⁻¹ * eS gSeq i * etaS gSeq ι dB).unop ∈ Ebar,
      psiBar ⟨_, h⟩ = Multiplicative.ofAdd (∑ j, Max2.decMat Max2.Native.r2Rows i j •
        Multiplicative.toAdd (psiBar (eE j)))) ∧
    (((betaRow β (etaS gSeq ι cB) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.G1.rows ∧
      ((betaRow β (etaS gSeq ι dB) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.G2.rows) ∧
    (((betaRow β (op xbar) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.Xb.rows ∧
      (((betaRow β (uS gSeq ι) : MatBˣ) : MatB))⁻¹ * Tmat = Dyadic.rowsK KC.BM.Max2.C.rows ∧
      Tmat⁻¹ * ((betaRow β (uS gSeq ι) : MatBˣ) : MatB) = Dyadic.rowsK KC.BM.Max2.Ci.rows) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc1r, hc2r, -⟩ := max2_matrix_facts (Qn_isUnit β gSeq hβ.gen)
  have hinj := hβ.injective
  exact ⟨orderOf_cB, orderOf_dB, KB_le_centralizer, hβ.gen 0 (by norm_num),
    commutator_e_eq_xbar hβ,
    ⟨psiBasis _ _ (linearIndependent_eE hβ), psiBasis_apply _ _ (linearIndependent_eE hβ)⟩,
    commutator_eS hβ, isUnit_gram, orderOf_zWx hβ ι hιβ, z_conj_u hβ ι hιβ,
    LB_unop_le_Jbar hβ ι hιβ,
    conj_eta_rows hβ ι cB _ Max2.Native.r1Rows quotRows1 r1Rows_eq
      (betaRow_eta_cB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ)
      (eta_cB_mem_Jbar β hinj gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ) hc1r,
    conj_eta_rows hβ ι dB _ Max2.Native.r2Rows quotRows2 r2Rows_eq
      (betaRow_eta_dB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ)
      (eta_dB_mem_Jbar β hinj gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ) hc2r,
    file_eta hβ ι hιβ, file_xconj hβ ι hιβ⟩

include hβ hιβ in
theorem pinned_B_max2_quotient_exact_order :
    (∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ (LB ι).unop ∧ jbarToKv g = k) ∧
    ∃ b : Module.Basis (Fin 22) (ZMod 2) (Wv (phi0 (coordOf rStar))),
      (∀ i, b i = Multiplicative.toAdd (psiBar (eE i))) ∧ Function.Injective (kvGL b) ∧
      (kvGL b).range = Subgroup.closure {Max2.R1u, Max2.R2u} ∧
      Nat.card (Subgroup.closure ({Max2.R1u, Max2.R2u} : Set (GL (Fin 22) (ZMod 2)))) =
        42305421312000 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc1r, hc2r, -⟩ := max2_matrix_facts (Qn_isUnit β gSeq hβ.gen)
  have hinj := hβ.injective
  have hηc := betaRow_eta_cB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  have hηd := betaRow_eta_dB β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  have hcJ := eta_cB_mem_Jbar β hinj gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  have hdJ := eta_dB_mem_Jbar β hinj gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  set e : Fin 22 → Cbar := fun i => (eS gSeq i).unop with he_def
  have he : ∀ i, e i ∈ Ebar := fun i => eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i
  have hind := linearIndependent_eE hβ
  set a' : Cbar := (etaS gSeq ι cB).unop⁻¹ with ha'
  set b' : Cbar := (etaS gSeq ι dB).unop⁻¹ with hb'
  have haJ : a' ∈ Jbar := Jbar.inv_mem hcJ
  have hbJ : b' ∈ Jbar := Jbar.inv_mem hdJ
  have haL : a' ∈ (LB ι).unop := by
    show op a' ∈ KB.map (etaS gSeq ι)
    rw [ha', op_inv, op_unop, ← map_inv]
    exact Subgroup.mem_map_of_mem _ (KB.inv_mem (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hbL : b' ∈ (LB ι).unop := by
    show op b' ∈ KB.map (etaS gSeq ι)
    rw [hb', op_inv, op_unop, ← map_inv]
    exact Subgroup.mem_map_of_mem _
      (KB.inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have hR1 := conj_rows β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar (etaS gSeq ι cB) _
    Max2.Native.r1Rows quotRows1 r1Rows_eq hηc haJ hc1r
  have hR2 := conj_rows β gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar (etaS gSeq ι dB) _
    Max2.Native.r2Rows quotRows2 r2Rows_eq hηd hbJ hc2r
  rw [← Max2.coe_R1u] at hR1
  rw [← Max2.coe_R2u] at hR2
  have honto := jbarToKv_onto_of_max2 (LB ι).unop haL hbL haJ hbJ e he hind hR1 hR2
  refine ⟨honto, psiBasis e he hind, psiBasis_apply e he hind, kvGL_injective
    KvAct_injective_rStar _, ?_⟩
  have h1 : kvGL (psiBasis e he hind) (jbarToKv ⟨a', haJ⟩) = Max2.R1u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind haJ _ hR1])
  have h2 : kvGL (psiBasis e he hind) (jbarToKv ⟨b', hbJ⟩) = Max2.R2u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind hbJ _ hR2])
  have hle : Subgroup.closure ({Max2.R1u, Max2.R2u} : Set (GL (Fin 22) (ZMod 2))) ≤
      (kvGL (psiBasis e he hind)).range := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact ⟨_, h1⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨_, h2⟩
  have hcard : Nat.card (kvGL (psiBasis e he hind)).range = 42305421312000 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (kvGL_injective KvAct_injective_rStar _), Subgroup.card_top, natCard_Kstab_rStar]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact Max2.card_closure_R12_ge)
  exact ⟨heq.symm, by rw [heq, hcard]⟩

include hβ hιβ in
theorem pinned_B_max2_full_native_centralizer_and_two_part :
    (LB ι).unop = Jbar ∧ Nat.card KB = 354883595661213696000 ∧
    2 ^ 41 ∣ Nat.card NativeSporadic.B ∧
    Jbar.op.map (MulAut.conj (uS gSeq ι)).toMonoidHom ≤ ι.range := by
  have hinj := hβ.injective
  have hLJ : (LB ι).unop = Jbar :=
    le_antisymm (LB_unop_le_Jbar hβ ι hιβ)
      (Jbar_le_eta β hinj gSeq hβ.gen gSeq_zero_mem gSeq_mem_Jbar ι hιβ)
  have hηinj : Function.Injective (etaS gSeq ι) :=
    (MulAut.conj (uS gSeq ι)⁻¹).injective.comp (iota_injective_of ι hιβ)
  have hK : Nat.card KB = 354883595661213696000 := by
    rw [← Subgroup.card_map_of_injective hηinj, ← LB, ← natCard_unop, hLJ, natCard_Jbar]
  refine ⟨hLJ, hK, ?_, ?_⟩
  · have h1 : 2 ^ 41 ∣ Nat.card KB := by
      rw [hK]
      exact ⟨161382375, by norm_num⟩
    exact h1.trans (Subgroup.card_subgroup_dvd_card KB)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxL : x ∈ LB ι := by
      rw [← hLJ] at hx
      exact (Subgroup.mem_op.1 hx : x.unop ∈ (LB ι).unop)
    obtain ⟨k, -, rfl⟩ := hxL
    refine ⟨k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, etaS_apply]
    group

end Max2Nodes

end CFSG.Monster.B

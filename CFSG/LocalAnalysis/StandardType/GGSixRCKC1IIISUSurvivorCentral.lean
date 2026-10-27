module
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUSurvivor
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport

public section
namespace CFSG.StandardType.RCKC1

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.StandardType.RCKK1IIISU CFSG.StandardType.LieKnownR2.Short
  CFSG.QuasithinUnique.B113Lie.Sp

theorem eq_zero_of_two_unitary_trace_tests (a : SUF)
    (h1 : a + SUσ a = 0)
    (hω : SUσ suOmega * a + suOmega * SUσ a = 0) : a = 0 := by
  have hfix : SUσ a = a := by
    have heq := eq_neg_of_add_eq_zero_right h1
    simpa only [CharTwo.neg_eq] using heq
  rw [hfix, ← add_mul, add_comm (SUσ suOmega) suOmega,
    rckSUc_omega_add_sigma_omega, one_mul] at hω
  exact hω

theorem eq_zero_of_two_prime_field_tests (b : SUF)
    (h1 : SUσ b = 0 ∨ SUσ b = 1)
    (hω : suOmega * SUσ b = 0 ∨ suOmega * SUσ b = 1) : b = 0 := by
  rcases h1 with h0 | h1
  · exact (map_eq_zero SUσ).mp h0
  · rw [h1, mul_one] at hω
    rcases hω with h0 | h1'
    · exact (rckSUc_omega_ne_zero h0).elim
    · have hfix : SUσ suOmega = suOmega := by rw [h1', map_one]
      exact (rckSUc_omega_ne_sigma_omega hfix.symm).elim


theorem unitary_eichler_conjugate_sub
    {k : ℕ} (hk : 4 ≤ k) {e a : Fin k → SUF} {c : SUF} {s q : SUG k}
    (hse : natRep (SU SUσ k) s e = e)
    (hq : ∀ v, natRep (SU SUσ k) q v =
      v + (suH rckSU_suF_card k).β e v • (a + c • e) +
        (suH rckSU_suF_card k).β a v • e) (x : Fin k → SUF) :
    natRep (SU SUσ k) (s * q * s⁻¹) x - natRep (SU SUσ k) q x =
      (suH rckSU_suF_card k).β e x • (natRep (SU SUσ k) s a - a) +
        (suH rckSU_suF_card k).β (natRep (SU SUσ k) s a - a) x • e := by
  let H := suH rckSU_suF_card k
  have hiso : ∀ (g : SUG k) (u v : Fin k → SUF),
      H.β (natRep (SU SUσ k) g u) (natRep (SU SUσ k) g v) = H.β u v :=
    CFSG.StandardType.GGOppRadSpU.isIsometric_natRep_SU SUσ
      (unitaryInvolution_involutive rckSU_suF_card) k
  have hrev : natRep (SU SUσ k) s (natRep (SU SUσ k) s⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have heval : H.β e (natRep (SU SUσ k) s⁻¹ x) = H.β e x := by
    have h := hiso s e (natRep (SU SUσ k) s⁻¹ x)
    rw [hse, hrev] at h
    exact h.symm
  have haval : H.β a (natRep (SU SUσ k) s⁻¹ x) = H.β (natRep (SU SUσ k) s a) x := by
    have h := hiso s a (natRep (SU SUσ k) s⁻¹ x)
    rw [hrev] at h
    exact h.symm
  have hq' : natRep (SU SUσ k) q (natRep (SU SUσ k) s⁻¹ x) =
      natRep (SU SUσ k) s⁻¹ x + H.β e x • (a + c • e) +
        H.β (natRep (SU SUσ k) s a) x • e := by
    rw [hq]
    rw [heval, haval]
  have hconj : natRep (SU SUσ k) (s * q * s⁻¹) x =
      x + H.β e x • (natRep (SU SUσ k) s a + c • e) +
        H.β (natRep (SU SUσ k) s a) x • e := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hq',
      map_add, map_add, map_smul, map_smul, map_add, map_smul, hse, hrev]
  rw [hconj, hq]
  change _ = H.β e x • (natRep (SU SUσ k) s a - a) +
    H.β (natRep (SU SUσ k) s a - a) x • e
  rw [ReflForm.β_sub_left, smul_sub, sub_smul]
  simp only [smul_add, smul_smul]
  abel


theorem unitary_conjugate_sub_eq_zero_or_nilpotent
    {k : ℕ} (hk : 4 ≤ k) {s q : SUG k}
    (hq : q ∈ rckSU_Q hk)
    (hN : s * q * s⁻¹ * q⁻¹ ∈ Subgroup.zpowers (suR hk)) (x : Fin k → SUF) :
    (natRep (SU SUσ k) (s * q * s⁻¹) x - natRep (SU SUσ k) q x = 0) ∨
      (natRep (SU SUσ k) (s * q * s⁻¹) x - natRep (SU SUσ k) q x =
        rckSU_Nlin hk x) := by
  have hrOrd : orderOf (suR hk) = 2 :=
    orderOf_eq_prime (rckSU_suR_sq hk) (suR_ne_one hk)
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hrOrd).mp hN with h1 | hr
  · left
    have hs : s * q * s⁻¹ = q := by
      calc s * q * s⁻¹ = (s * q * s⁻¹ * q⁻¹) * q := by group
        _ = q := by rw [h1, one_mul]
    rw [hs, sub_self]
  · right
    have hs : s * q * s⁻¹ = suR hk * q := by
      calc s * q * s⁻¹ = (s * q * s⁻¹ * q⁻¹) * q := by group
        _ = suR hk * q := by rw [hr]
    have hqfix : ∀ y ∈ rckSU_A hk, natRep (SU SUσ k) q y = y := (mem_rad.mp hq).1
    have hqcomm : q * suR hk = suR hk * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (rckSU_Q_le_centralizer hk hq)
    have hNrq : rckSU_Nlin hk (natRep (SU SUσ k) q x) = rckSU_Nlin hk x := by
      have hiso := CFSG.StandardType.GGOppRadSpU.isIsometric_natRep_SU SUσ
        (unitaryInvolution_involutive rckSU_suF_card) k
      have hqinv : ∀ y ∈ rckSU_A hk, natRep (SU SUσ k) q⁻¹ y = y :=
        (mem_rad.mp (Subgroup.inv_mem _ hq)).1
      apply sub_eq_zero.mp
      apply (suH rckSU_suF_card k).nondeg
      intro y
      rw [ReflForm.β_sub_left, rckSU_N_selfAdjoint, rckSU_N_selfAdjoint]
      have hI := hiso q⁻¹ (natRep (SU SUσ k) q x) (rckSU_Nlin hk y)
      rw [show natRep (SU SUσ k) q⁻¹ (natRep (SU SUσ k) q x) = x from by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply],
        hqinv _ (show rckSU_Nlin hk y ∈ rckSU_A hk from ⟨y, rfl⟩)] at hI
      have hEq : (suH rckSU_suF_card k).β (natRep (SU SUσ k) q x) (rckSU_Nlin hk y) =
          (suH rckSU_suF_card k).β x (rckSU_Nlin hk y) := hI.symm
      exact sub_eq_zero.mpr hEq
    rw [hs, map_mul, Module.End.mul_apply, natRep_apply, rckSUc_suR_eq,
      Matrix.add_mulVec, Matrix.one_mulVec]
    change natRep (SU SUσ k) q x + rckSU_Nlin hk (natRep (SU SUσ k) q x) -
      natRep (SU SUσ k) q x = _
    rw [hNrq]
    abel


theorem eq_zero_of_unitary_plane_eichler_tests
    {k : ℕ} (hk : 4 ≤ k) {t : Fin k → SUF} (ht : t ∈ rckSU_U hk)
    (hTests : ∀ l : SUF, ∀ x : Fin k → SUF,
      ((suH rckSU_suF_card k).β (l • rckSU_std (sI0 hk)) x • t +
          (suH rckSU_suF_card k).β t x • (l • rckSU_std (sI0 hk)) = 0) ∨
        ((suH rckSU_suF_card k).β (l • rckSU_std (sI0 hk)) x • t +
          (suH rckSU_suF_card k).β t x • (l • rckSU_std (sI0 hk)) = rckSU_Nlin hk x)) :
    t = 0 := by
  let e₀ : Fin k → SUF := rckSU_std (sI0 hk)
  let e₁ : Fin k → SUF := rckSU_std (sI1 hk)
  obtain ⟨a, b, htEq⟩ := Submodule.mem_span_pair.mp ht
  have hE : t = a • e₀ + b • e₁ := htEq.symm
  have h01 : sI0 hk ≠ sI1 hk := fun h => rckSUc_e_zero_ne_one hk (by simpa [rckSUc_e] using h)
  have hdual0 : (suH rckSU_suF_card k).β e₀ (rckSU_std (Fin.rev (sI0 hk))) = 1 := by
    rw [rckSU_suH_std]
    simp
  have hdual1 : (suH rckSU_suF_card k).β e₀ (rckSU_std (Fin.rev (sI1 hk))) = 0 := by
    rw [rckSU_suH_std]
    simp only [Fin.rev_inj, if_neg h01]
  have hdual10 : (suH rckSU_suF_card k).β e₁ (rckSU_std (Fin.rev (sI0 hk))) = 0 := by
    rw [rckSU_suH_std]
    simp only [Fin.rev_inj, if_neg h01.symm]
  have hdual11 : (suH rckSU_suF_card k).β e₁ (rckSU_std (Fin.rev (sI1 hk))) = 1 := by
    rw [rckSU_suH_std]
    simp
  have hN0 : rckSU_Nlin hk (rckSU_std (Fin.rev (sI0 hk))) = e₁ := by
    rw [rckSU_Nlin_apply]
    simp [e₁, rckSU_std, rckSUc_e, rckSUc_e', Pi.single_apply, eq_comm, h01]
  have hN1 : rckSU_Nlin hk (rckSU_std (Fin.rev (sI1 hk))) = e₀ := by
    rw [rckSU_Nlin_apply]
    simp [e₀, rckSU_std, rckSUc_e, rckSUc_e', Pi.single_apply, eq_comm, h01]
  have hBT0 : (suH rckSU_suF_card k).β t (rckSU_std (Fin.rev (sI0 hk))) = SUσ a := by
    rw [hE, ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left, hdual0, hdual10]
    simp only [suH, CFSG.StandardType.GGOppRadSpU.suForm_σ, mul_one, mul_zero, add_zero]
  have hBT1 : (suH rckSU_suF_card k).β t (rckSU_std (Fin.rev (sI1 hk))) = SUσ b := by
    rw [hE, ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left, hdual1, hdual11]
    simp only [suH, CFSG.StandardType.GGOppRadSpU.suForm_σ, mul_one, mul_zero, zero_add]
  have hbTests (l : SUF) : l * SUσ b = 0 ∨ l * SUσ b = 1 := by
    have h := hTests l (rckSU_std (Fin.rev (sI1 hk)))
    rw [ReflForm.smul_left, hdual1, mul_zero, zero_smul, zero_add, hBT1, smul_smul, hN1] at h
    rcases h with h0 | h1
    · left
      have hx := congrFun h0 (sI0 hk)
      simpa [e₀, rckSU_std, smul_eq_mul, mul_comm] using hx
    · right
      have hx := congrFun h1 (sI0 hk)
      simpa [e₀, rckSU_std, smul_eq_mul, mul_comm] using hx
  have hb : b = 0 := eq_zero_of_two_prime_field_tests b
    (by simpa using hbTests 1) (hbTests suOmega)
  have haTests (l : SUF) : SUσ l * a + l * SUσ a = 0 := by
    have h := hTests l (rckSU_std (Fin.rev (sI0 hk)))
    have hBeta : (suH rckSU_suF_card k).β (l • e₀)
        (rckSU_std (Fin.rev (sI0 hk))) = SUσ l := by
      rw [ReflForm.smul_left, hdual0, mul_one]
      rfl
    have h' : ((SUσ l • t + SUσ a • (l • e₀) = 0) ∨
        (SUσ l • t + SUσ a • (l • e₀) = e₁)) := by
      change ((suH rckSU_suF_card k).β (l • e₀)
        (rckSU_std (Fin.rev (sI0 hk))) • t +
        (suH rckSU_suF_card k).β t (rckSU_std (Fin.rev (sI0 hk))) • (l • e₀) = 0) ∨
        ((suH rckSU_suF_card k).β (l • e₀)
          (rckSU_std (Fin.rev (sI0 hk))) • t +
          (suH rckSU_suF_card k).β t (rckSU_std (Fin.rev (sI0 hk))) • (l • e₀) =
            rckSU_Nlin hk (rckSU_std (Fin.rev (sI0 hk)))) at h
      rw [hBeta, hBT0, hN0] at h
      exact h
    have hleft : (suH rckSU_suF_card k).σ l • t + SUσ a • (l • e₀) =
        (SUσ l * a + l * SUσ a) • e₀ := by
      rw [hE, hb, zero_smul, add_zero, smul_smul, smul_smul, ← add_smul]
      congr 1
      simp only [suH, CFSG.StandardType.GGOppRadSpU.suForm_σ]
      ring
    have hleft' : SUσ l • t + SUσ a • (l • e₀) =
        (SUσ l * a + l * SUσ a) • e₀ := hleft
    rw [hleft'] at h'
    rcases h' with h0 | h1
    · have hx := congrFun h0 (sI0 hk)
      simpa [e₀, rckSU_std, smul_eq_mul] using hx
    · have hx := congrFun h1 (sI0 hk)
      simpa [e₀, e₁, rckSU_std, smul_eq_mul, Pi.single_apply, h01.symm] using hx
  have ha : a = 0 := eq_zero_of_two_unitary_trace_tests a
    (by simpa using haTests 1) (haTests suOmega)
  rw [hE, ha, hb, zero_smul, zero_smul, add_zero]


theorem rckSU_fixes_perp_of_coreComm
    {k : ℕ} (hk : 4 ≤ k) (V : Subgroup (SUG k))
    (hrV : suR hk ∈ V) (hVab : CFSG.Open.IsElemAbelian 2 V)
    (hN : ∀ v ∈ V, ∀ y ∈ CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({suR hk} : Set (SUG k))),
        v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers (suR hk))
    {s : SUG k} (hsV : s ∈ V) :
    ∀ a ∈ (suH rckSU_suF_card k).perp (rckSU_U hk),
      natRep (SU SUσ k) s a = a := by
  have hsQ := rckSU_mem_Q_of_coreComm hk V hrV hVab hN hsV
  have hfixU : ∀ e ∈ rckSU_U hk, natRep (SU SUσ k) s e = e := by
    intro e he
    exact (mem_rad.mp hsQ).1 e (by rwa [rckSU_U_eq_range hk] at he)
  intro a ha
  have ht : natRep (SU SUσ k) s a - a ∈ rckSU_U hk := by
    have h := (mem_rad.mp hsQ).2 a (by rwa [rckSU_U_eq_range hk] at ha)
    rwa [← rckSU_U_eq_range hk] at h
  apply sub_eq_zero.mp
  apply eq_zero_of_unitary_plane_eichler_tests hk ht
  intro l x
  have he : l • rckSU_std (sI0 hk) ∈ rckSU_U hk :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨c, q, hqQ, hc, hq⟩ := rckSU_eichler_mem_Q hk he ha
  have hComm := hN s hsV q (rckSU_Q_le_pCoreOf hk hqQ)
  have hTest := unitary_conjugate_sub_eq_zero_or_nilpotent hk hqQ hComm x
  rw [unitary_eichler_conjugate_sub hk (hfixU _ he) hq x] at hTest
  exact hTest

theorem unitary_sub_mem_plane_of_fix_perp
    {k : ℕ} (hk : 4 ≤ k) {s : SUG k}
    (hfix : ∀ z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk),
      natRep (SU SUσ k) s z = z) (x : Fin k → SUF) :
    natRep (SU SUσ k) s x - x ∈ rckSU_U hk := by
  let H := suH rckSU_suF_card k
  have hmem : natRep (SU SUσ k) s x - x ∈ H.perp (H.perp (rckSU_U hk)) := by
    rw [ReflForm.mem_perp]
    intro z hz
    have hiso := CFSG.StandardType.GGOppRadSpU.isIsometric_natRep_SU SUσ
      (unitaryInvolution_involutive rckSU_suF_card) k s z x
    change H.β (natRep (SU SUσ k) s z) (natRep (SU SUσ k) s x) = H.β z x at hiso
    rw [hfix z hz] at hiso
    rw [ReflForm.β_sub_right, hiso, sub_self]
  rwa [ReflForm.perp_perp] at hmem

theorem mem_suZ0_of_fix_planePerp
    {k : ℕ} (hk : 4 ≤ k) {s : SUG k}
    (hfix : ∀ z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk),
      natRep (SU SUσ k) s z = z) : s ∈ suZ0 hk := by
  classical
  let H := suH rckSU_suF_card k
  let e₀ := rckSU_std (k := k) (rckSUc_e hk 0)
  let e₁ := rckSU_std (k := k) (rckSUc_e hk 1)
  let d₀ := rckSU_std (k := k) (rckSUc_e' hk 0)
  let d₁ := rckSU_std (k := k) (rckSUc_e' hk 1)
  have ht0 := unitary_sub_mem_plane_of_fix_perp hk hfix d₀
  have ht1 := unitary_sub_mem_plane_of_fix_perp hk hfix d₁
  obtain ⟨a, c, ht0⟩ := Submodule.mem_span_pair.mp ht0
  obtain ⟨b, d, ht1⟩ := Submodule.mem_span_pair.mp ht1
  have hcol0 : natRep (SU SUσ k) s d₀ = d₀ + (a • e₀ + c • e₁) := by
    change a • e₀ + c • e₁ = natRep (SU SUσ k) s d₀ - d₀ at ht0
    exact (sub_eq_iff_eq_add.mp ht0.symm).trans (add_comm _ _)
  have hcol1 : natRep (SU SUσ k) s d₁ = d₁ + (b • e₀ + d • e₁) := by
    change b • e₀ + d • e₁ = natRep (SU SUσ k) s d₁ - d₁ at ht1
    exact (sub_eq_iff_eq_add.mp ht1.symm).trans (add_comm _ _)
  have h01 : rckSUc_e hk 0 ≠ rckSUc_e hk 1 := rckSUc_e_zero_ne_one hk
  have hp00 : H.β e₀ d₀ = 1 := by
    rw [rckSU_suH_std]
    simp [rckSUc_e']
  have hp01 : H.β e₀ d₁ = 0 := by
    rw [rckSU_suH_std]
    simp only [rckSUc_e', Fin.rev_inj, if_neg h01]
  have hp10 : H.β e₁ d₀ = 0 := by
    rw [rckSU_suH_std]
    simp only [rckSUc_e', Fin.rev_inj, if_neg h01.symm]
  have hp11 : H.β e₁ d₁ = 1 := by
    rw [rckSU_suH_std]
    simp [rckSUc_e']
  have hrev (x y : Fin k → SUF) : H.β y x = SUσ (H.β x y) :=
    CFSG.StandardType.GGOppRadSpU.suForm_symm SUσ
      (unitaryInvolution_involutive rckSU_suF_card) x y
  have hq00 : H.β d₀ e₀ = 1 := by rw [hrev, hp00, map_one]
  have hq01 : H.β d₀ e₁ = 0 := by rw [hrev, hp10, map_zero]
  have hq10 : H.β d₁ e₀ = 0 := by rw [hrev, hp01, map_zero]
  have hq11 : H.β d₁ e₁ = 1 := by rw [hrev, hp11, map_one]
  have hu0 : a • e₀ + c • e₁ ∈ rckSU_U hk := by
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [e₀, rckSUc_e])))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [e₁, rckSUc_e])))
  have hu1 : b • e₀ + d • e₁ ∈ rckSU_U hk := by
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [e₀, rckSUc_e])))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [e₁, rckSUc_e])))
  have hiso (x y : Fin k → SUF) :
      H.β (natRep (SU SUσ k) s x) (natRep (SU SUσ k) s y) = H.β x y :=
    CFSG.StandardType.GGOppRadSpU.isIsometric_natRep_SU SUσ
      (unitaryInvolution_involutive rckSU_suF_card) k s x y
  have hσa : SUσ a = a := by
    have h := hiso d₀ d₀
    rw [hcol0, ReflForm.add_left,
      H.add_right d₀ d₀ (a • e₀ + c • e₁),
      H.add_right (a • e₀ + c • e₁) d₀ (a • e₀ + c • e₁),
      rckSU_U_isTotallyIsotropic hk hu0 _ hu0,
      ReflForm.add_right, ReflForm.smul_right, ReflForm.smul_right,
      ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
      hq00, hq01, hp00, hp10] at h
    change H.β d₀ d₀ + (a * 1 + c * 0) +
      (SUσ a * 1 + SUσ c * 0 + 0) = H.β d₀ d₀ at h
    have h0 : a + SUσ a = 0 := by
      have h' : H.β d₀ d₀ + (a + SUσ a) = H.β d₀ d₀ + 0 := by
        simpa only [mul_one, mul_zero, add_zero, zero_add, add_assoc] using h
      exact add_left_cancel h'
    exact (eq_neg_of_add_eq_zero_right h0).trans (CharTwo.neg_eq a)
  have hσd : SUσ d = d := by
    have h := hiso d₁ d₁
    rw [hcol1, ReflForm.add_left,
      H.add_right d₁ d₁ (b • e₀ + d • e₁),
      H.add_right (b • e₀ + d • e₁) d₁ (b • e₀ + d • e₁),
      rckSU_U_isTotallyIsotropic hk hu1 _ hu1,
      ReflForm.add_right, ReflForm.smul_right, ReflForm.smul_right,
      ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
      hq10, hq11, hp01, hp11] at h
    change H.β d₁ d₁ + (b * 0 + d * 1) +
      (SUσ b * 0 + SUσ d * 1 + 0) = H.β d₁ d₁ at h
    have h0 : d + SUσ d = 0 := by
      have h' : H.β d₁ d₁ + (d + SUσ d) = H.β d₁ d₁ + 0 := by
        simpa only [mul_one, mul_zero, add_zero, zero_add, add_assoc] using h
      exact add_left_cancel h'
    exact (eq_neg_of_add_eq_zero_right h0).trans (CharTwo.neg_eq d)
  have hc : c = SUσ b := by
    have h := hiso d₀ d₁
    rw [hcol0, hcol1, ReflForm.add_left,
      H.add_right d₀ d₁ (b • e₀ + d • e₁),
      H.add_right (a • e₀ + c • e₁) d₁ (b • e₀ + d • e₁),
      rckSU_U_isTotallyIsotropic hk hu1 _ hu0,
      ReflForm.add_right, ReflForm.smul_right, ReflForm.smul_right,
      ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
      hq00, hq01, hp01, hp11] at h
    change H.β d₀ d₁ + (b * 1 + d * 0) +
      (SUσ a * 0 + SUσ c * 1 + 0) = H.β d₀ d₁ at h
    have h0 : b + SUσ c = 0 := by
      have h' : H.β d₀ d₁ + (b + SUσ c) = H.β d₀ d₁ + 0 := by
        simpa only [mul_one, mul_zero, add_zero, zero_add, add_assoc] using h
      exact add_left_cancel h'
    have hσc : SUσ c = b :=
      (eq_neg_of_add_eq_zero_right h0).trans (CharTwo.neg_eq b)
    have h' := congrArg SUσ hσc
    simpa only [rckSUc_sigma_involutive] using h'
  let A : Matrix (Fin 2) (Fin 2) SUF := !![a, b; c, d]
  have hA : conjTr SUσ A = A := by
    ext i j
    fin_cases i <;> fin_cases j
    · change SUσ a = a
      exact hσa
    · change SUσ c = b
      rw [hc, rckSUc_sigma_involutive]
    · change SUσ b = c
      exact hc.symm
    · change SUσ d = d
      exact hσd
  obtain ⟨v, hv⟩ := rckSUc_Ato_surjective (⟨A, rckSUc_mem_herm.mpr hA⟩ : rckSUc_herm)
  have hAv : rckSUc_A v = A := congrArg Subtype.val hv
  have ha : rckSUc_alpha (v 0) = a := by
    simpa [rckSUc_A, A] using congrFun (congrFun hAv 0) 0
  have hb : rckSUc_beta v = b := by
    simpa [rckSUc_A, A] using congrFun (congrFun hAv 0) 1
  have hd : rckSUc_alpha (v 3) = d := by
    simpa [rckSUc_A, A] using congrFun (congrFun hAv 1) 1
  have hZ (x : Fin k → SUF) : natRep (SU SUσ k) (suZ hk v) x =
      x + (a * x (rckSUc_e' hk 0) + b * x (rckSUc_e' hk 1)) • e₀ +
        (c * x (rckSUc_e' hk 0) + d * x (rckSUc_e' hk 1)) • e₁ := by
    change ((suZ hk v : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).mulVec x = _
    rw [suZ_val, rckSUc_M_eq_suCorner]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, rckSUc_M, Matrix.single_mulVec_eq,
      ha, hb, hd, ← hc]
    change x +
      (((a * x (rckSUc_e' hk 0)) • e₀ + (b * x (rckSUc_e' hk 1)) • e₀) +
        (c * x (rckSUc_e' hk 0)) • e₁ + (d * x (rckSUc_e' hk 1)) • e₁) = _
    simp only [add_smul, add_assoc]
  have hsame (j : Fin k) : natRep (SU SUσ k) s (rckSU_std j) =
      natRep (SU SUσ k) (suZ hk v) (rckSU_std j) := by
    rw [hZ]
    by_cases hj0 : j = rckSUc_e' hk 0
    · subst j
      simpa [d₀, rckSU_std, Pi.single_apply, eq_comm, add_assoc,
        rckSUc_e'_zero_ne_one hk] using hcol0
    by_cases hj1 : j = rckSUc_e' hk 1
    · subst j
      simpa [d₁, rckSU_std, Pi.single_apply, eq_comm, add_assoc,
        rckSUc_e'_zero_ne_one hk] using hcol1
    have hperp : rckSU_std j ∈ H.perp (rckSU_U hk) := by
      rw [rckSU_mem_perp_U_iff]
      simp [rckSU_std, Pi.single_apply, eq_comm, hj0, hj1]
    rw [hfix _ hperp]
    simp [rckSU_std, Pi.single_apply, eq_comm, hj0, hj1]
  have hseq : s = suZ hk v := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    have h := congrFun (hsame j) i
    change (((s : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).mulVec
      (Pi.single j 1)) i =
      (((suZ hk v : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).mulVec
        (Pi.single j 1)) i at h
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h
  rw [hseq]
  exact ⟨v, rfl⟩

theorem rckSU_elemAbelian_le_suZ0
    {k : ℕ} (hk : 4 ≤ k) (V : Subgroup (SUG k))
    (hrV : suR hk ∈ V) (hVab : CFSG.Open.IsElemAbelian 2 V)
    (hN : ∀ v ∈ V, ∀ y ∈ CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({suR hk} : Set (SUG k))),
        v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers (suR hk)) : V ≤ suZ0 hk := by
  intro s hs
  exact mem_suZ0_of_fix_planePerp hk (rckSU_fixes_perp_of_coreComm hk V hrV hVab hN hs)

theorem rckSU_core_le_centralizer_of_fourAt
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)}
    (hFour : FourAt (⊤ : Subgroup (SUG k)) V (suR hk))
    (hCore : CoreCommAt (⊤ : Subgroup (SUG k)) V (suR hk)) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) ≤
      Subgroup.centralizer (V : Set (SUG k)) := by
  apply rckSU_core_le_centralizer_of_le_suZ0 hk
  apply rckSU_elemAbelian_le_suZ0 hk V hFour.1 hFour.2.2.1
  intro v hv y hy
  apply hCore v hv y
  simpa only [top_inf_eq] using hy

theorem rckSU_fix_suR_iff_mem_perp
    {k : ℕ} (hk : 4 ≤ k) (z : Fin k → SUF) :
    natRep (SU SUσ k) (suR hk) z = z ↔
      z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk) := by
  constructor
  · intro hz
    have hN : rckSU_Nlin hk z = 0 := by
      have hR : natRep (SU SUσ k) (suR hk) z = z + rckSU_Nlin hk z := by
        rw [natRep_apply, rckSUc_suR_eq, Matrix.add_mulVec, Matrix.one_mulVec]
        rfl
      rw [hR] at hz
      exact add_left_cancel (hz.trans (add_zero z).symm)
    rw [rckSU_Nlin_apply] at hN
    rw [rckSU_mem_perp_U_iff]
    have h01 : sI0 hk ≠ sI1 hk := by
      simpa only [rckSUc_e, Matrix.cons_val_zero, Matrix.cons_val_one] using
        rckSUc_e_zero_ne_one hk
    constructor
    · have h := congrFun hN (sI1 hk)
      simpa [rckSU_std, Pi.single_apply, rckSUc_e', rckSUc_e,
        h01, h01.symm] using h
    · have h := congrFun hN (sI0 hk)
      simpa [rckSU_std, Pi.single_apply, rckSUc_e', rckSUc_e,
        h01, h01.symm] using h
  · exact rckSU_suR_fixes_perp hk

theorem rckSU_fixes_fixed_space_of_coreComm
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)}
    (hFour : FourAt (⊤ : Subgroup (SUG k)) V (suR hk))
    (hCore : CoreCommAt (⊤ : Subgroup (SUG k)) V (suR hk)) :
    ∀ v ∈ V, ∀ z : Fin k → SUF,
      natRep (SU SUσ k) (suR hk) z = z → natRep (SU SUσ k) v z = z := by
  intro v hv z hz
  apply rckSU_fixes_perp_of_coreComm hk V hFour.1 hFour.2.2.1
  · intro w hw y hy
    apply hCore w hw y
    simpa only [top_inf_eq] using hy
  · exact hv
  · exact (rckSU_fix_suR_iff_mem_perp hk z).mp hz

end CFSG.StandardType.RCKC1

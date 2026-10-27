module

public import Certificates.Kernel.Y442.Model
public import Certificates.Data.Kernel.B433Alt.Fix

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.YGroups
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelY442 CFSG.KC.YModel.Sem

section

theorem apP_spec : ∀ (w : List ℕ), (∀ c ∈ w, c < 10) → ∀ (P X u r : ℕ), u < P → (hr : r < 31671) →
    (apP CFSG.KD.YMY432F.Nf P w X).testBit (2 ^ 15 * u + r) =
      X.testBit (2 ^ 15 * u + (rho432F (evalWord (yGen 4 3 2) w) ⟨r, hr⟩ : ℕ))
  | [], _, P, X, u, r, _, hr => by
    change X.testBit _ = _
    rw [evalWord_nil, map_one]
    rfl
  | c :: w, hw, P, X, u, r, hu, hr => by
    have hc : c < 10 := hw c List.mem_cons_self
    have e : apP CFSG.KD.YMY432F.Nf P (c :: w) X = apP CFSG.KD.YMY432F.Nf P w
        (netApply 15 (wid 15) (repU (wid 15) P) (CFSG.KD.YMY432F.Nf c) X) :=
      CFSG.KC.Benes.strictN_eq _ _
    rw [e, apP_spec w (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) P _ u r hu hr]
    set q := rho432F (evalWord (yGen 4 3 2) w) ⟨r, hr⟩
    obtain ⟨hv, hρ, -⟩ := net_spec hc
    have h1 := (testBit_netApply (W := 2 ^ 15) (P := P) rfl hv X).1 u hu q (by omega)
    rw [wid_eq, h1, hρ q, evalWord_cons, map_mul, Equiv.Perm.mul_apply]

theorem apP1_spec {w : List ℕ} (hw : ∀ c ∈ w, c < 10) (X : ℕ) (r : Fin 31671) :
    (apP CFSG.KD.YMY432F.Nf 1 w X).testBit r =
      X.testBit (rho432F (evalWord (yGen 4 3 2) w) r : ℕ) := by
  have h := apP_spec w hw 1 X 0 r (by norm_num) r.2
  simpa using h

end

section

@[expose] noncomputable def dT : YGroup 4 3 2 := evalWord (yGen 4 3 2) dWL

@[expose] noncomputable def d0 : Equiv.Perm (Fin 31671) := rho432F dT

@[expose] noncomputable def eOf (x : Fin 31671) : YGroup 4 3 2 := Classical.choose (transitive_zero x)

theorem eOf_spec (x : Fin 31671) : rho432F (eOf x) 0 = x := Classical.choose_spec (transitive_zero x)

@[expose] noncomputable def lab (x : Fin 31671) : Equiv.Perm (Fin 31671) :=
  rho432F (eOf x) * d0 * (rho432F (eOf x))⁻¹

@[expose] def JComm : Prop := ∀ c ∈ tL, rho432F (yGen 4 3 2 c) * d0 = d0 * rho432F (yGen 4 3 2 c)

structure LabFacts : Prop where
  comm : JComm
  sq : d0 * d0 = 1
  fix0 : d0 0 = 0
  ord3 : ∀ x : Fin 31671, d0 x ≠ x → (d0 * lab x) ^ 3 = 1
  ne0 : ∀ x : Fin 31671, x ≠ 0 → lab x ≠ d0

theorem J_comm (hcJ : JComm) {j : YGroup 4 3 2} (hj : j ∈ Y442Tw.lsub tL) :
    rho432F j * d0 = d0 * rho432F j := by
  induction hj using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact hcJ c hc
  | one => rw [map_one, one_mul, mul_one]
  | mul x y _ _ hx hy => rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    rw [map_inv]
    calc (rho432F x)⁻¹ * d0 = (rho432F x)⁻¹ * (d0 * rho432F x) * (rho432F x)⁻¹ := by group
      _ = (rho432F x)⁻¹ * (rho432F x * d0) * (rho432F x)⁻¹ := by rw [hx]
      _ = d0 * (rho432F x)⁻¹ := by group

theorem lab_eq (hcJ : JComm) {e : YGroup 4 3 2} {x : Fin 31671} (h : rho432F e 0 = x) :
    lab x = rho432F e * d0 * (rho432F e)⁻¹ := by
  have hj : (eOf x)⁻¹ * e ∈ Y442Tw.lsub tL := by
    apply stab_zero
    rw [map_mul, Equiv.Perm.mul_apply, h, map_inv, Equiv.Perm.inv_eq_iff_eq, eOf_spec]
  have hc := J_comm hcJ hj
  have e1 : rho432F e = rho432F (eOf x) * rho432F ((eOf x)⁻¹ * e) := by
    rw [← map_mul]
    group
  rw [lab, e1]
  calc rho432F (eOf x) * d0 * (rho432F (eOf x))⁻¹
      = rho432F (eOf x) * (d0 * rho432F ((eOf x)⁻¹ * e)) * (rho432F ((eOf x)⁻¹ * e))⁻¹ *
          (rho432F (eOf x))⁻¹ := by group
    _ = rho432F (eOf x) * (rho432F ((eOf x)⁻¹ * e) * d0) * (rho432F ((eOf x)⁻¹ * e))⁻¹ *
          (rho432F (eOf x))⁻¹ := by rw [hc]
    _ = _ := by group

theorem lab_zero (hcJ : JComm) : lab 0 = d0 := by
  rw [lab_eq hcJ (e := 1) (by simp)]
  simp

theorem lab_conj (hcJ : JComm) (g : YGroup 4 3 2) (x : Fin 31671) :
    lab (rho432F g x) = rho432F g * lab x * (rho432F g)⁻¹ := by
  rw [lab_eq hcJ (e := g * eOf x) (by rw [map_mul, Equiv.Perm.mul_apply, eOf_spec]), lab, map_mul]
  group

variable (hL : LabFacts)
include hL

theorem lab_mem (x : Fin 31671) : ∃ g, lab x = rho432F g :=
  ⟨eOf x * dT * (eOf x)⁻¹, by rw [lab, d0, map_mul, map_mul, map_inv]⟩

theorem lab_sq (x : Fin 31671) : lab x * lab x = 1 := by
  rw [lab]
  calc rho432F (eOf x) * d0 * (rho432F (eOf x))⁻¹ * (rho432F (eOf x) * d0 * (rho432F (eOf x))⁻¹)
      = rho432F (eOf x) * (d0 * d0) * (rho432F (eOf x))⁻¹ := by group
    _ = 1 := by rw [hL.sq]; group

theorem lab_self (x : Fin 31671) : lab x x = x := by
  rw [lab, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.2 (eOf_spec x).symm,
    hL.fix0, eOf_spec]

theorem lab_inj {x y : Fin 31671} (h : lab x = lab y) : x = y := by
  set e := eOf y
  have hy : rho432F e⁻¹ y = 0 := by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, eOf_spec]
  have hz : lab (rho432F e⁻¹ x) = d0 := by
    rw [lab_conj hL.comm, h, ← lab_conj hL.comm e⁻¹ y, hy, lab_zero hL.comm]
  have h0 : rho432F e⁻¹ x = 0 := by
    by_contra hne
    exact hL.ne0 _ hne hz
  rw [map_inv, Equiv.Perm.inv_eq_iff_eq] at h0
  rw [h0, eOf_spec]

theorem lab_lab (x y : Fin 31671) : lab (lab x y) = lab x * lab y * (lab x)⁻¹ := by
  obtain ⟨g, hg⟩ := lab_mem hL x
  rw [hg, lab_conj hL.comm]

theorem lab_symm {ω p : Fin 31671} (h : lab ω p ≠ p) : lab ω p = lab p ω := by
  set e := eOf p
  set ω' := (rho432F e)⁻¹ ω
  have hω : rho432F e ω' = ω := by simp [ω']
  have hlω : lab ω = rho432F e * lab ω' * (rho432F e)⁻¹ := by rw [← hω, lab_conj hL.comm]
  have hlp : lab p = rho432F e * d0 * (rho432F e)⁻¹ := lab_eq hL.comm (eOf_spec p)
  have hp0 : (rho432F e)⁻¹ p = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, eOf_spec]
  have e1 : lab ω p = rho432F e (lab ω' 0) := by
    rw [hlω, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hp0]
  have e2 : lab p ω = rho432F e (d0 ω') := by
    rw [hlp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have h' : lab ω' 0 ≠ 0 := by
    intro h0
    apply h
    rw [e1, h0, eOf_spec]
  rw [e1, e2]
  congr 1
  have hd0 : ∀ x, lab (d0 x) = d0 * lab x * d0⁻¹ := fun x => lab_conj hL.comm dT x
  by_cases hf : d0 ω' = ω'
  · exfalso
    apply h'
    have hc : d0 * lab ω' * d0⁻¹ = lab ω' := by rw [← hd0, hf]
    have hcomm : lab ω' * d0 = d0 * lab ω' := by
      calc lab ω' * d0 = d0 * lab ω' * d0⁻¹ * d0 := by rw [hc]
        _ = d0 * lab ω' := by group
    have hl : lab (lab ω' 0) = lab 0 := by
      rw [lab_lab hL, lab_zero hL.comm, hcomm]
      group
    exact lab_inj hL hl
  ·
    have h3 := hL.ord3 ω' hf
    have hd : d0⁻¹ = d0 := inv_eq_of_mul_eq_one_right hL.sq
    have hLi : (lab ω')⁻¹ = lab ω' := inv_eq_of_mul_eq_one_right (lab_sq hL ω')
    have key : lab ω' * d0 * (lab ω')⁻¹ = d0 * lab ω' * d0⁻¹ := by
      rw [hd, hLi]
      have h2 : d0 * lab ω' * (d0 * lab ω') = (d0 * lab ω')⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← h3, pow_succ, sq]
      rw [mul_inv_rev, hLi, hd] at h2
      have h4 := congrArg (d0 * ·) h2
      simp only [← mul_assoc, hL.sq, one_mul] at h4
      exact h4
    refine lab_inj hL ?_
    rw [lab_lab hL, lab_zero hL.comm, hd0, key]

theorem not_mem_of_hub {M : Subgroup (Equiv.Perm (Fin 31671))} {Y : Set (Fin 31671)}
    (hY : ∀ σ ∈ M, ∀ r, r ∈ Y ↔ σ r ∈ Y) {p ω : Fin 31671} (hne : lab p ω ≠ ω)
    (hside : lab p ω ∈ Y ↔ p ∉ Y) : lab ω ∉ M := by
  intro hm
  have hs := (lab_symm hL hne).symm
  have h1 := hY _ hm p
  rw [hs] at h1
  tauto

end

end CertificateChecks.KernelB433

end

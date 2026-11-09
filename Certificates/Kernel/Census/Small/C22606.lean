module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
public import Certificates.Kernel.Census.Small.SEList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

namespace C22606

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus

@[expose] noncomputable def xc : Nat := Nat.land (Nat.shiftRight invRepT (Nat.mul 9 1)) 511

theorem enc_x : (SE.invRep 1).enc = xc := enc_invRep 1

@[expose] noncomputable def cent (c : Nat) : Bool := Nat.beq (mulT c xc) (mulT xc c)

theorem cent_iff (s : SE) : s * SE.invRep 1 = SE.invRep 1 * s ↔ cent s.enc = true := by
  rw [se_eq_iff, enc_mulT, enc_mulT, enc_x, cent, Nat.beq_eq]

@[expose] noncomputable def cE (c : Nat) : Bool := predEK c && cent c && !predFK c
@[expose] noncomputable def cF (c : Nat) : Bool := predFK c && cent c && !predEK c
@[expose] noncomputable def nE (c : Nat) : Bool := predEK c && !cent c
@[expose] noncomputable def nF (c : Nat) : Bool := predFK c && !cent c

@[expose] noncomputable def chk1 : Bool :=
  (codesP cE).all fun a => (codesP cE).all fun b => predFK (mulT (invK a) b)

@[expose] noncomputable def chk2 : Bool :=
  (codesP nE).all fun a => (codesP nE).all fun b => cent (mulT (invK a) b)

@[expose] noncomputable def chk3 : Bool :=
  (codesP cF).all fun a => (codesP cF).all fun b => predEK (mulT (invK a) b)

@[expose] noncomputable def chk4 : Bool :=
  (codesP nF).all fun a => (codesP nF).all fun b => cent (mulT (invK a) b)

theorem chk1_ok : chk1 = true := by quickRfl
theorem chk2_ok : chk2 = true := by quickRfl
theorem chk3_ok : chk3 = true := by quickRfl
theorem chk4_ok : chk4 = true := by quickRfl

theorem enc_quo (a b : SE) : (a⁻¹ * b).enc = mulT (invK a.enc) b.enc := by
  rw [enc_mulT, enc_inv]

theorem part1 : ∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
    e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predF e₁ → ¬ SE.predF e₂ →
      SE.predF (e₁⁻¹ * e₂) := by
  intro e₁ e₂ h1 h2 h3 h4 h5 h6
  have hP : ∀ s : SE, (SE.predE s ∧ s * SE.invRep 1 = SE.invRep 1 * s ∧ ¬ SE.predF s) →
      cE s.enc = true := fun s hs =>
    band3 ((predE_iff s).1 hs.1) ((cent_iff s).1 hs.2.1) (bnot_of (mt (predF_iff s).2 hs.2.2))
  exact pair_of (R := fun s t => SE.predF (s⁻¹ * t)) (r := fun a b => predFK (mulT (invK a) b))
    (p := cE) (q := cE) hP hP
    (fun s t h => (predF_iff _).2 (by rw [enc_quo]; exact h)) chk1_ok e₁ e₂ ⟨h1, h3, h5⟩
    ⟨h2, h4, h6⟩

theorem part2 : ∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
    e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
      e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂) := by
  intro e₁ e₂ h1 h2 h3 h4
  have hP : ∀ s : SE, (SE.predE s ∧ s * SE.invRep 1 ≠ SE.invRep 1 * s) → nE s.enc = true :=
    fun s hs => band2 ((predE_iff s).1 hs.1) (bnot_of (mt (cent_iff s).2 hs.2))
  exact pair_of (R := fun s t => s⁻¹ * t * SE.invRep 1 = SE.invRep 1 * (s⁻¹ * t))
    (r := fun a b => cent (mulT (invK a) b)) (p := nE) (q := nE) hP hP
    (fun s t h => (cent_iff _).2 (by rw [enc_quo]; exact h)) chk2_ok e₁ e₂ ⟨h1, h3⟩ ⟨h2, h4⟩

theorem part3 : ∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
    e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predE e₁ → ¬ SE.predE e₂ →
      SE.predE (e₁⁻¹ * e₂) := by
  intro e₁ e₂ h1 h2 h3 h4 h5 h6
  have hP : ∀ s : SE, (SE.predF s ∧ s * SE.invRep 1 = SE.invRep 1 * s ∧ ¬ SE.predE s) →
      cF s.enc = true := fun s hs =>
    band3 ((predF_iff s).1 hs.1) ((cent_iff s).1 hs.2.1) (bnot_of (mt (predE_iff s).2 hs.2.2))
  exact pair_of (R := fun s t => SE.predE (s⁻¹ * t)) (r := fun a b => predEK (mulT (invK a) b))
    (p := cF) (q := cF) hP hP
    (fun s t h => (predE_iff _).2 (by rw [enc_quo]; exact h)) chk3_ok e₁ e₂ ⟨h1, h3, h5⟩
    ⟨h2, h4, h6⟩

theorem part4 : ∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
    e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
      e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂) := by
  intro e₁ e₂ h1 h2 h3 h4
  have hP : ∀ s : SE, (SE.predF s ∧ s * SE.invRep 1 ≠ SE.invRep 1 * s) → nF s.enc = true :=
    fun s hs => band2 ((predF_iff s).1 hs.1) (bnot_of (mt (cent_iff s).2 hs.2))
  exact pair_of (R := fun s t => s⁻¹ * t * SE.invRep 1 = SE.invRep 1 * (s⁻¹ * t))
    (r := fun a b => cent (mulT (invK a) b)) (p := nF) (q := nF) hP hP
    (fun s t h => (cent_iff _).2 (by rw [enc_quo]; exact h)) chk4_ok e₁ e₂ ⟨h1, h3⟩ ⟨h2, h4⟩

end C22606

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22606 :
    (∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predF e₁ → ¬ SE.predF e₂ →
        SE.predF (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
        e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predE e₁ → ¬ SE.predE e₂ →
        SE.predE (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
        e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂)) :=
  ⟨C22606.part1, C22606.part2, C22606.part3, C22606.part4⟩

end CertificateChecks.KernelCensus

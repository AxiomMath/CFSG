module

public import Certificates.Kernel.Co2Census.CCFib
public import Certificates.Kernel.Co2Census.HP
public import CFSG.Sporadic.Co2Smith.CInvar

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem zCz_eq : zCz = cE 256 0 := Subtype.ext cElt_z.symm

theorem repK_zCz : repK ((zCz : Cz) : K) (mulV (SK 0) (QKt 256)) := by
  rw [zCz_eq]
  exact repK_cE QK_eq (by norm_num) 0

theorem piC_zCz : piC zCz = 1 := by
  rw [zCz_eq, piC_cE, sElt_zero]

theorem repK_one' : repK ((1 : Cz) : K) IDP := by
  rw [Subgroup.coe_one]
  exact repK_one

theorem piC_one' : piC 1 = sElt 0 := by
  rw [map_one, sElt_zero]

theorem QK_lt' {e : ℕ} (he : e < 512) : QKt e < 2 ^ 484 := by
  rw [QK_eq e he]
  exact nfS_lt _ _

theorem repK_qElt' {e : ℕ} (he : e < 512) : repK (qElt e) (QKt e) := by
  rw [QK_eq e he]
  exact repK_qElt he

theorem repK_qE {e : ℕ} (he : e < 512) : repK (((qE e : CFSG.pCore 2 Cz) : Cz) : K) (QKt e) := by
  rw [QK_eq e he]
  exact repK_qElt he

theorem sum_range_one (x : ℕ) : (((List.range 1).filter fun _ => true).map fun _ => x).sum = x := by
  simp only [List.range_one, List.filter_cons, List.filter_nil, ite_true, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem ceInv_eqK {y : Cz} {R : ℕ} (hy : repK (y : K) R) : ceInv y = ceK QKt R := by
  have h1 : ceInv y = (((List.range 1).filter fun _ => true).map fun _ =>
      ((List.range 512).filter fun e => Nat.beq (mulV (QKt e) R) (mulV R (QKt e))).length).sum := by
    unfold ceInv
    exact card_eq_cnt_aux 512 1 (fun e _ => qE e) exists_qE
      (fun e e' n n' he he' _ _ h => ⟨qE_injOn he he' h, by omega⟩)
      (fun q : CFSG.pCore 2 Cz => (q : Cz) * y = y * q)
      (fun e _ => Nat.beq (mulV (QKt e) R) (mulV R (QKt e))) (fun _ => true)
      (fun _ _ _ _ _ => rfl) (fun e he n _ _ => by
        rw [Nat.beq_eq]
        exact (cz_eq_iff (repK_czmul (repK_qE he) hy) (repK_czmul hy (repK_qE he))).symm)
  rw [h1, sum_range_one, ceK]
  apply congrArg List.length
  apply List.filter_congr
  intro e _
  rw [letB_eq]

theorem invEInv_eqK {y : Cz} {R : ℕ} (hy : repK (y : K) R) : invEInv y = invEK QKt R := by
  have h1 : invEInv y = (((List.range 1).filter fun _ => true).map fun _ =>
      ((List.range 512).filter fun e =>
        Nat.beq (mulV (mulV R (QKt e)) (mulV R (QKt e))) IDP).length).sum := by
    unfold invEInv
    exact card_eq_cnt_aux 512 1 (fun e _ => qE e) exists_qE
      (fun e e' n n' he he' _ _ h => ⟨qE_injOn he he' h, by omega⟩)
      (fun q : CFSG.pCore 2 Cz => y * q * (y * q) = 1)
      (fun e _ => Nat.beq (mulV (mulV R (QKt e)) (mulV R (QKt e))) IDP) (fun _ => true)
      (fun _ _ _ _ _ => rfl) (fun e he n _ _ => by
        rw [Nat.beq_eq]
        have hq := repK_czmul hy (repK_qE he)
        exact (cz_eq_iff (repK_czmul hq hq) repK_one').symm)
  rw [h1, sum_range_one, invEK]
  apply congrArg List.length
  apply List.filter_congr
  intro e _
  rw [letB_eq]

theorem rep_facts {er nr ce ie : ℕ} (her : er < 512)
    (h : (repOKC (mulV (SK nr) (QKt er)) (mulV (SK 0) (QKt 256)) &&
      Nat.beq (ceK QKt (mulV (SK nr) (QKt er))) ce &&
      Nat.beq (invEK QKt (mulV (SK nr) (QKt er))) ie) = true) :
    cE er nr * cE er nr = 1 ∧ cE er nr ≠ 1 ∧ cE er nr ≠ zCz ∧ ceInv (cE er nr) = ce ∧
      invEInv (cE er nr) = ie := by
  have hr := repK_cE QK_eq her nr
  unfold repOKC at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨(cz_eq_iff (repK_czmul hr hr) repK_one').2 h1, fun e => ?_, fun e => ?_,
    (ceInv_eqK hr).trans h4, (invEInv_eqK hr).trans h5⟩
  · exact Nat.ne_of_beq_eq_false h2 ((cz_eq_iff hr repK_one').1 e)
  · exact Nat.ne_of_beq_eq_false h3 ((cz_eq_iff hr repK_zCz).1 e)

end CC

end CertificateChecks.KernelCo2Census

end

module

public import Certificates.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.Psi
public import Certificates.Kernel.Co2Smith.ElemK
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Smith.GlCosetInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native CFSG.KS CFSG.KS.Raw

theorem let_ok : glLetOK = true := by
  have h := let_k
  have hz := glZ_eq
  have e1 : (glCzLet.all fun k => commRows glRows[k]! glZ) =
      glCzLet.all fun k => commK (LP k) zK := by
    refine all_congr_mem fun k hk => ?_
    have hk' : k < 22 := by simp [glCzLet] at hk; omega
    rw [glRows_get hk', hz, commRows_unpack]
    rfl
  have e2 : (glC0Let.all fun k => commRows glRows[k]! glAl && commRows glRows[k]! glGa) =
      glC0Let.all fun k => commK (LP k) alK && commK (LP k) gaK := by
    refine all_congr_mem fun k hk => ?_
    have hk' : k < 22 := by simp [glC0Let] at hk; omega
    rw [glRows_get hk', glAl_eq, glGa_eq, commRows_unpack, commRows_unpack]
  unfold glLetOK
  rw [e1, e2, glRows_size, el_eqs.2.2.2, hz, commRows_unpack]
  exact h

theorem ord_ok : glOrdOK = true := by
  have h := ord_k
  unfold glOrdOK
  rw [glAl_eq, glGa_eq, powRows_unpack, idRows_eq, beq_unpack, mulRows_unpack, beq_unpack,
    glConj_unpack, mulRows_unpack, beq_unpack, glMaps_unpack _ (by norm_num) (by norm_num),
    glMaps_unpack _ (by norm_num) (by norm_num)]
  exact h

theorem pt_ok : glPtOK = true := by
  have h := pt_k
  obtain ⟨-, -, -, -, -, -, e34, e0⟩ := frame_eqs
  obtain ⟨-, -, -, -, e43, -, -, -⟩ := frame_eqs
  have eB : glB3 = unpackR 22 b3K := by rw [glB3, e34, e43, mulRows_unpack]; rfl
  have eV : glV = unpackR 22 vK := by rw [glV, el_eqs.2.2.2, e0, mulRows_unpack, mulRows_unpack]; rfl
  have eV1 : glV1 = unpackR 22 v1K := by
    rw [glV1, eB, eV, mulRows_unpack, mulRows_unpack, mulRows_unpack]; rfl
  have e1 : ((List.range 11).all fun k => glMaps glRows[k]! 80 80) =
      (List.range 11).all fun k => mapsK (LP k) 80 80 := by
    refine all_congr_mem fun k hk => ?_
    rw [glRows_get (by simp at hk; omega), glMaps_unpack _ (by norm_num) (by norm_num)]
  unfold glPtOK
  rw [e1, el_eqs.2.2.2, eV, eV1, mulRows_unpack, idRows_eq, beq_unpack, mulRows_unpack, beq_unpack,
    glMaps_unpack _ (by norm_num) (by norm_num), glMaps_unpack _ (by norm_num) (by norm_num),
    glMaps_unpack _ (by norm_num) (by norm_num)]
  exact h

theorem c_ok : glCOK = true := by
  have h := cVal_k
  have hpp := CFSG.KC.Misc.ArrEnum.pp_of_permB sz_ok CK_permB
  have hp : CFSG.KC.Enum.permOK 2300 12 (mask 12) (2300 * 12) CK CIK = true :=
    CFSG.KS.PinvS.permOK_pinvS hpp.1 hpp.2
  unfold cValK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hc : CK = cP := rfl
  unfold glCOK
  rw [cWord_ok, cInv_eq, cArr_eq, CFSG.KS.Raw.Orb.isInvA_unpack hp, CFSG.KS.Raw.Orb.unpack_get
    (by norm_num), CFSG.KS.Raw.Orb.unpack_get (by norm_num), CFSG.KS.Raw.Orb.unpack_get
    (by norm_num), hc]
  simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩, Nat.eq_of_beq_eq_true h3⟩

theorem arc_ok : glArcOK = true := by
  have h := arc_k
  unfold arcK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold glArcOK
  have e3 : glPermOK (unpackR 22 (wK LP [0])) (glPermArr (unpackR 22 (wK LP [0]))) = true :=
    permOK_of h3
  rw [glAl_eq, glGa_eq, glZ_eq, permOK_of h1, permOK_of h2, e3]
  rfl

theorem gen_ok : glGenOK = true := by
  have h := gen_k
  have key : ∀ (L : List (List Nat)) (x : Nat), x < 2300 → (L.all fun w => w.all (· < 22) &&
      mapsK (wK LP w) 80 80 && mapsK (wK LP w) x x) = true →
      (L.all fun w => glMaps (glR w) 80 80 && glMaps (glR w) x x) = true := by
    intro L x hx hL
    simp only [List.all_eq_true, Bool.and_eq_true] at hL ⊢
    intro w hw
    obtain ⟨⟨hl, h80⟩, hxx⟩ := hL w hw
    have hl' : ∀ k ∈ w, k < 22 := fun k hk => of_decide_eq_true (hl k hk)
    rw [glR_eq hl', glMaps_unpack _ (by norm_num) (by norm_num), glMaps_unpack _ hx hx]
    exact ⟨h80, hxx⟩
  unfold elGenK at h
  simp only [Bool.and_eq_true] at h
  unfold glGenOK
  simp only [Bool.and_eq_true]
  exact ⟨key _ _ (by norm_num) h.1, key _ _ (by norm_num) h.2⟩

theorem elem_ok : glElemOK = true := by
  unfold glElemOK
  rw [let_ok, ord_ok, pt_ok, c_ok, arc_ok, gen_ok]
  rfl

end CertificateChecks.KernelCo2Smith
